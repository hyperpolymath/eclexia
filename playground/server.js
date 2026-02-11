#!/usr/bin/env node

const http = require("http");
const fs = require("fs/promises");
const path = require("path");
const os = require("os");
const { spawn } = require("child_process");

const HOST = process.env.PLAYGROUND_HOST || "127.0.0.1";
const PORT = Number(process.env.PLAYGROUND_PORT || 4173);
const ROOT = path.resolve(__dirname, "public");
const REPO_ROOT = path.resolve(__dirname, "..");
const ECLEXIA_BIN = process.env.ECLEXIA_BIN || path.join(REPO_ROOT, "target", "debug", "eclexia");

const MIME = {
  ".html": "text/html; charset=utf-8",
  ".css": "text/css; charset=utf-8",
  ".js": "application/javascript; charset=utf-8",
  ".json": "application/json; charset=utf-8",
  ".webmanifest": "application/manifest+json; charset=utf-8",
  ".svg": "image/svg+xml",
};

function json(res, code, payload) {
  const data = JSON.stringify(payload, null, 2);
  res.writeHead(code, {
    "Content-Type": "application/json; charset=utf-8",
    "Content-Length": Buffer.byteLength(data),
    "Cache-Control": "no-store",
  });
  res.end(data);
}

function runCmd(bin, args, opts = {}) {
  return new Promise((resolve) => {
    const child = spawn(bin, args, {
      cwd: REPO_ROOT,
      stdio: ["ignore", "pipe", "pipe"],
      ...opts,
    });

    let stdout = "";
    let stderr = "";
    child.stdout.on("data", (chunk) => (stdout += chunk.toString()));
    child.stderr.on("data", (chunk) => (stderr += chunk.toString()));

    const timeout = setTimeout(() => {
      child.kill("SIGKILL");
      resolve({ ok: false, code: -1, stdout, stderr: `${stderr}\nTimed out.`.trim() });
    }, 30000);

    child.on("close", (code) => {
      clearTimeout(timeout);
      resolve({ ok: code === 0, code, stdout, stderr });
    });

    child.on("error", (err) => {
      clearTimeout(timeout);
      resolve({ ok: false, code: -1, stdout, stderr: String(err) });
    });
  });
}

async function ensureBinary() {
  try {
    await fs.access(ECLEXIA_BIN);
    return;
  } catch {
    const build = await runCmd("cargo", ["build", "-p", "eclexia"]);
    if (!build.ok) {
      throw new Error(`Failed to build eclexia binary.\n${build.stderr || build.stdout}`);
    }
  }
}

function safeStepLines(disassembly = "") {
  return disassembly
    .split(/\r?\n/)
    .map((line) => line.trim())
    .filter((line) => line.length > 0)
    .slice(0, 2000);
}

async function executeMode(code, mode) {
  await ensureBinary();

  const tempDir = await fs.mkdtemp(path.join(os.tmpdir(), "eclexia-playground-"));
  const sourcePath = path.join(tempDir, "main.ecl");
  const bytecodePath = path.join(tempDir, "main.eclb");
  const profilePath = path.join(tempDir, "profile.json");

  await fs.writeFile(sourcePath, code, "utf8");

  try {
    if (mode === "interpret") {
      const run = await runCmd(ECLEXIA_BIN, [
        "profile",
        sourcePath,
        "--format",
        "json",
        "--observe-shadow",
        "--carbon-report",
      ]);

      if (!run.ok) {
        return {
          ok: false,
          mode,
          stdout: run.stdout,
          stderr: run.stderr,
          error: "Interpret mode failed.",
        };
      }

      let profile;
      try {
        profile = JSON.parse(run.stdout);
      } catch {
        return {
          ok: false,
          mode,
          stdout: run.stdout,
          stderr: run.stderr,
          error: "Interpreter profile output was not valid JSON.",
        };
      }

      return {
        ok: true,
        mode,
        stdout: run.stdout,
        stderr: run.stderr,
        profile,
        disassembly: "",
        steps: [],
      };
    }

    const build = await runCmd(ECLEXIA_BIN, ["build", sourcePath, "--output", bytecodePath]);
    if (!build.ok) {
      return {
        ok: false,
        mode,
        stdout: build.stdout,
        stderr: build.stderr,
        error: "Compilation failed.",
      };
    }

    const disasm = await runCmd(ECLEXIA_BIN, ["disasm", sourcePath]);
    const disassembly = disasm.stdout || disasm.stderr || "";

    if (mode === "step") {
      return {
        ok: disasm.ok,
        mode,
        stdout: build.stdout,
        stderr: `${build.stderr}\n${disasm.stderr}`.trim(),
        profile: null,
        disassembly,
        steps: safeStepLines(disassembly),
        error: disasm.ok ? null : "Disassembly failed.",
      };
    }

    const prof = await runCmd(ECLEXIA_BIN, [
      "profile",
      bytecodePath,
      "--format",
      "json",
      "--output",
      profilePath,
      "--observe-shadow",
      "--carbon-report",
    ]);

    if (!prof.ok) {
      return {
        ok: false,
        mode,
        stdout: `${build.stdout}\n${prof.stdout}`.trim(),
        stderr: `${build.stderr}\n${prof.stderr}`.trim(),
        disassembly,
        steps: safeStepLines(disassembly),
        error: "Compile-profile mode failed.",
      };
    }

    const profileRaw = await fs.readFile(profilePath, "utf8");
    const profile = JSON.parse(profileRaw);

    return {
      ok: true,
      mode,
      stdout: `${build.stdout}\n${prof.stdout}`.trim(),
      stderr: `${build.stderr}\n${prof.stderr}`.trim(),
      profile,
      disassembly,
      steps: safeStepLines(disassembly),
    };
  } finally {
    await fs.rm(tempDir, { recursive: true, force: true });
  }
}

async function serveStatic(req, res) {
  const url = new URL(req.url, `http://${HOST}:${PORT}`);
  let pathname = url.pathname;
  if (pathname === "/") {
    pathname = "/index.html";
  }

  const candidate = path.resolve(ROOT, `.${pathname}`);
  if (!candidate.startsWith(ROOT)) {
    res.writeHead(403);
    res.end("Forbidden");
    return;
  }

  try {
    const data = await fs.readFile(candidate);
    const ext = path.extname(candidate);
    res.writeHead(200, {
      "Content-Type": MIME[ext] || "application/octet-stream",
      "Cache-Control": ext === ".html" ? "no-cache" : "public, max-age=300",
    });
    res.end(data);
  } catch {
    try {
      const index = await fs.readFile(path.join(ROOT, "index.html"));
      res.writeHead(200, {
        "Content-Type": "text/html; charset=utf-8",
        "Cache-Control": "no-cache",
      });
      res.end(index);
    } catch {
      res.writeHead(404);
      res.end("Not found");
    }
  }
}

function readRequestBody(req) {
  return new Promise((resolve, reject) => {
    let data = "";
    req.on("data", (chunk) => {
      data += chunk.toString();
      if (data.length > 2_000_000) {
        reject(new Error("Request too large"));
      }
    });
    req.on("end", () => resolve(data));
    req.on("error", reject);
  });
}

const server = http.createServer(async (req, res) => {
  const url = new URL(req.url, `http://${HOST}:${PORT}`);

  if (req.method === "GET" && url.pathname === "/api/examples") {
    try {
      const raw = await fs.readFile(path.join(ROOT, "examples.json"), "utf8");
      json(res, 200, JSON.parse(raw));
    } catch (err) {
      json(res, 500, { ok: false, error: String(err) });
    }
    return;
  }

  if (req.method === "POST" && url.pathname === "/api/run") {
    try {
      const body = await readRequestBody(req);
      const payload = JSON.parse(body || "{}");
      const code = typeof payload.code === "string" ? payload.code : "";
      const mode = payload.mode === "compile" || payload.mode === "step" ? payload.mode : "interpret";

      if (!code.trim()) {
        json(res, 400, { ok: false, error: "Code cannot be empty." });
        return;
      }

      const result = await executeMode(code, mode);
      json(res, result.ok ? 200 : 400, result);
    } catch (err) {
      json(res, 500, { ok: false, error: String(err) });
    }
    return;
  }

  serveStatic(req, res);
});

server.listen(PORT, HOST, () => {
  console.log(`Eclexia Playground running at http://${HOST}:${PORT}`);
});
