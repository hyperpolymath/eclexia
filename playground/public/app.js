const codeInput = document.querySelector("#code-input");
const codeHighlight = document.querySelector("#code-highlight");
const modeSelect = document.querySelector("#mode-select");
const exampleSelect = document.querySelector("#example-select");
const runBtn = document.querySelector("#run-btn");
const shareBtn = document.querySelector("#share-btn");
const outputEl = document.querySelector("#output");
const resourceChart = document.querySelector("#resource-chart");
const shadowList = document.querySelector("#shadow-list");
const stageList = document.querySelector("#stage-list");
const stepOutput = document.querySelector("#step-output");
const stepPrev = document.querySelector("#step-prev");
const stepNext = document.querySelector("#step-next");
const stepIndicator = document.querySelector("#step-indicator");

const KEYWORDS = [
  "def",
  "fn",
  "type",
  "struct",
  "const",
  "let",
  "if",
  "else",
  "match",
  "return",
  "while",
  "for",
  "in",
  "impl",
  "trait",
];

let disassemblySteps = [];
let currentStep = 0;

function escapeHtml(input) {
  return input
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;");
}

function highlightCode(source) {
  const escaped = escapeHtml(source);
  return escaped
    .replace(/\/\/.*$/gm, '<span class="token-comment">$&</span>')
    .replace(/"([^"\\]|\\.)*"/g, '<span class="token-string">$&</span>')
    .replace(/\b\d+(?:\.\d+)?\b/g, '<span class="token-number">$&</span>')
    .replace(
      new RegExp(`\\b(${KEYWORDS.join("|")})\\b`, "g"),
      '<span class="token-keyword">$1</span>'
    );
}

function syncEditor() {
  codeHighlight.innerHTML = `${highlightCode(codeInput.value)}\n`;
  codeHighlight.scrollTop = codeInput.scrollTop;
  codeHighlight.scrollLeft = codeInput.scrollLeft;
}

function setOutput(text, ok = true) {
  outputEl.textContent = text;
  outputEl.classList.toggle("ok", ok);
  outputEl.classList.toggle("warn", !ok);
}

function renderResources(resourceUsage = {}) {
  resourceChart.innerHTML = "";
  const entries = Object.entries(resourceUsage);
  if (entries.length === 0) {
    resourceChart.textContent = "No numeric resource data returned for this run.";
    return;
  }

  const values = entries
    .map(([, value]) => Number(value))
    .filter((value) => Number.isFinite(value));
  const max = Math.max(...values, 1);

  for (const [key, value] of entries) {
    const numeric = Number(value);
    const row = document.createElement("div");
    row.className = "chart-row";

    const label = document.createElement("span");
    label.textContent = key;

    const shell = document.createElement("div");
    shell.className = "bar-shell";

    const fill = document.createElement("div");
    fill.className = "bar-fill";
    const width = Number.isFinite(numeric) ? (numeric / max) * 100 : 0;
    fill.style.width = `${Math.max(width, 2)}%`;
    shell.appendChild(fill);

    const amount = document.createElement("span");
    amount.textContent = Number.isFinite(numeric) ? numeric.toFixed(4) : String(value);

    row.append(label, shell, amount);
    resourceChart.appendChild(row);
  }
}

function renderShadowPrices(shadowPrices = {}) {
  shadowList.innerHTML = "";
  const entries = Object.entries(shadowPrices);
  if (entries.length === 0) {
    shadowList.textContent = "No shadow price data returned for this run.";
    return;
  }

  for (const [key, value] of entries) {
    const row = document.createElement("div");
    row.className = "key-value-item";

    const k = document.createElement("span");
    k.textContent = key;

    const v = document.createElement("strong");
    const numeric = Number(value);
    v.textContent = Number.isFinite(numeric) ? numeric.toFixed(6) : String(value);

    row.append(k, v);
    shadowList.appendChild(row);
  }
}

function renderStages(stages = []) {
  stageList.innerHTML = "";
  if (!stages || stages.length === 0) {
    stageList.textContent = "No stage timing data available.";
    return;
  }

  for (const stage of stages) {
    const row = document.createElement("div");
    row.className = "stage-row";

    const name = document.createElement("span");
    name.textContent = stage.name;

    const value = document.createElement("strong");
    value.textContent = `${Number(stage.ms).toFixed(3)} ms`;

    row.append(name, value);
    stageList.appendChild(row);
  }
}

function setDisassembly(raw = "") {
  disassemblySteps = raw
    .split(/\r?\n/)
    .map((line) => line.trimEnd())
    .filter((line) => line.length > 0);
  currentStep = 0;
  renderStep();
}

function renderStep() {
  if (disassemblySteps.length === 0) {
    stepOutput.textContent = "No disassembly available.";
    stepIndicator.textContent = "No step data";
    return;
  }

  stepOutput.textContent = disassemblySteps[currentStep];
  stepIndicator.textContent = `Step ${currentStep + 1} / ${disassemblySteps.length}`;
}

async function runPlayground() {
  runBtn.disabled = true;
  setOutput("Running...");

  try {
    const response = await fetch("/api/run", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({
        code: codeInput.value,
        mode: modeSelect.value,
      }),
    });

    const payload = await response.json();

    if (!response.ok || !payload.ok) {
      const message = payload.error || payload.stderr || "Execution failed.";
      setOutput(message, false);
      renderResources({});
      renderShadowPrices({});
      renderStages([]);
      setDisassembly(payload.disassembly || "");
      return;
    }

    const profile = payload.profile || {};
    const profileSummary = [
      `Mode: ${payload.mode}`,
      profile.total_ms ? `Total: ${Number(profile.total_ms).toFixed(3)} ms` : null,
      profile.result ? `Result: ${profile.result}` : null,
      profile.program_output ? `Program Output:\n${profile.program_output}` : null,
      payload.stdout ? `Raw stdout:\n${payload.stdout}` : null,
      payload.stderr ? `Raw stderr:\n${payload.stderr}` : null,
    ]
      .filter(Boolean)
      .join("\n\n");

    setOutput(profileSummary || "Completed.", true);
    renderResources(profile.resource_usage || {});
    renderShadowPrices(profile.shadow_prices || {});
    renderStages(profile.stages || []);
    setDisassembly(payload.disassembly || "");
  } catch (error) {
    setOutput(`Unexpected error: ${error}`, false);
  } finally {
    runBtn.disabled = false;
  }
}

function applySharedCodeFromUrl() {
  const params = new URLSearchParams(window.location.search);
  const shared = params.get("code");
  if (!shared) return false;
  try {
    codeInput.value = decodeURIComponent(shared);
    syncEditor();
    return true;
  } catch {
    return false;
  }
}

function updateShareUrl() {
  const url = new URL(window.location.href);
  url.searchParams.set("code", encodeURIComponent(codeInput.value));
  window.history.replaceState({}, "", url);
  navigator.clipboard
    .writeText(url.toString())
    .then(() => setOutput("Share URL copied to clipboard."))
    .catch(() => setOutput(`Share URL: ${url.toString()}`));
}

async function loadExamples() {
  const response = await fetch("/api/examples");
  const payload = await response.json();

  if (!payload.examples || payload.examples.length === 0) {
    return;
  }

  for (const ex of payload.examples) {
    const option = document.createElement("option");
    option.value = ex.id;
    option.textContent = ex.title;
    option.dataset.code = ex.code;
    exampleSelect.appendChild(option);
  }

  const hasShared = applySharedCodeFromUrl();
  if (!hasShared) {
    codeInput.value = payload.examples[0].code;
    syncEditor();
  }

  exampleSelect.addEventListener("change", () => {
    const selected = exampleSelect.selectedOptions[0];
    const exampleCode = selected?.dataset.code ?? "";
    codeInput.value = exampleCode;
    syncEditor();
  });
}

runBtn.addEventListener("click", runPlayground);
shareBtn.addEventListener("click", updateShareUrl);
codeInput.addEventListener("input", syncEditor);
codeInput.addEventListener("scroll", syncEditor);

stepPrev.addEventListener("click", () => {
  if (disassemblySteps.length === 0) return;
  currentStep = Math.max(0, currentStep - 1);
  renderStep();
});

stepNext.addEventListener("click", () => {
  if (disassemblySteps.length === 0) return;
  currentStep = Math.min(disassemblySteps.length - 1, currentStep + 1);
  renderStep();
});

if ("serviceWorker" in navigator) {
  window.addEventListener("load", () => {
    navigator.serviceWorker.register("/service-worker.js").catch(() => {});
  });
}

loadExamples()
  .then(() => {
    syncEditor();
    setOutput("Ready.");
  })
  .catch((err) => {
    setOutput(`Failed to load examples: ${err}`, false);
  });
