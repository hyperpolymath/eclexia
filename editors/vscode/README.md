# Eclexia for Visual Studio Code

Language support for [Eclexia](https://github.com/hyperpolymath/eclexia) - the Economics-as-Code programming language with shadow pricing and resource awareness.

## Features

### Syntax Highlighting
- **Keywords**: `fn`, `let`, `if`, `match`, `resource`, `adaptive`, `shadow`
- **Annotations**: `@requires`, `@provides`, `@builtin`, `@test`, `@bench`
- **Dimensional literals**: `10J`, `5kWh`, `100gCO2`, `2.5kg·m²/s²`
- **Comments**: Line (`//`) and block (`/* */`)

### Language Server Protocol (LSP)
- **Diagnostics**: Real-time syntax and type errors
- **Hover**: Symbol information with types and documentation
- **Go to Definition**: Jump to symbol definitions
- **Find References**: Find all usages of a symbol
- **Completion**: Context-aware code completion with keywords
- **Document Symbols**: Outline view of functions, types, and constants
- **Rename**: Rename symbols across files
- **Formatting**: Auto-format Eclexia code

### Editor Features
- **Bracket matching**: Auto-close `{}`, `[]`, `()`
- **Auto-indentation**: Smart indentation based on braces
- **Comment toggling**: `Ctrl+/` for line comments

## Requirements

- **Eclexia compiler**: Install from [eclexia repository](https://github.com/hyperpolymath/eclexia)
- The `eclexia` binary must be in your PATH

## Installation

### From VSIX (Recommended)
1. Download the latest `.vsix` file from [releases](https://github.com/hyperpolymath/eclexia/releases)
2. In VSCode, press `Ctrl+Shift+P` and run "Extensions: Install from VSIX..."
3. Select the downloaded `.vsix` file

### From Source
```bash
cd editors/vscode
npm install
npm run package  # Creates eclexia-0.1.0.vsix
code --install-extension eclexia-0.1.0.vsix
```

## Configuration

Configure the extension in VSCode settings (`Ctrl+,`):

```json
{
  "eclexia.lsp.path": "eclexia",
  "eclexia.lsp.trace": "off"
}
```

### Settings

- **`eclexia.lsp.path`**: Path to the `eclexia` executable (default: `"eclexia"`)
- **`eclexia.lsp.trace`**: LSP trace level - `"off"`, `"messages"`, or `"verbose"` (default: `"off"`)

## Commands

- **Eclexia: Restart Server** (`Ctrl+Shift+P` → "Eclexia: Restart Server")
  - Restart the LSP server (useful after updating Eclexia)

## Usage Example

Create a file `example.ecl`:

```eclexia
/// Calculate optimal algorithm based on carbon intensity.
adaptive fn optimize_sort(data: [Int]) -> [Int] {
    @requires(10kWh, 5s)
    @provides(sorted_data: [Int])

    fast: {
        // Use quicksort when carbon intensity is low
        quicksort(data)
    }

    slow: {
        // Use heapsort when carbon intensity is high (more energy-efficient)
        heapsort(data)
    }
}

resource energy {
    dimension: Energy,
    budget: 100kWh,
    shadow: compute_carbon_price(),
}
```

The extension will provide:
- ✅ Syntax highlighting for `adaptive`, `resource`, `@requires`, `@provides`
- ✅ Dimensional literal highlighting (`10kWh`, `5s`, `100kWh`)
- ✅ Hover information on `optimize_sort`
- ✅ Completion for keywords and symbols
- ✅ Real-time diagnostics for errors

## Troubleshooting

### LSP Server Not Starting

1. **Check PATH**: Verify `eclexia` is in your PATH:
   ```bash
   which eclexia  # Linux/Mac
   where eclexia  # Windows
   ```

2. **Check Version**: Ensure you have a recent version:
   ```bash
   eclexia --version
   ```

3. **View Logs**: Enable tracing in settings:
   ```json
   {
     "eclexia.lsp.trace": "verbose"
   }
   ```
   Then check the "Eclexia Language Server" output panel.

4. **Restart Server**: Run "Eclexia: Restart Server" command

### Syntax Highlighting Not Working

- Ensure the file has `.ecl` extension
- Reload VSCode: `Ctrl+Shift+P` → "Developer: Reload Window"

## License

PMPL-1.0-or-later

## Links

- [Eclexia Repository](https://github.com/hyperpolymath/eclexia)
- [Issue Tracker](https://github.com/hyperpolymath/eclexia/issues)
- [Documentation](https://github.com/hyperpolymath/eclexia/blob/main/README.adoc)
