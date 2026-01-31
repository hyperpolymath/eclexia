# Eclexia Language Server

Language Server Protocol (LSP) implementation for the Eclexia programming language.

## Features

### Implemented ✅

- **Text Document Synchronization** - Keeps editor and server state in sync
- **Diagnostic Reporting** - Real-time syntax and type error reporting
  - Parse errors from `eclexia-parser`
  - Type errors from `eclexia-typeck`
  - Line:column accurate error positioning
- **Server Capabilities** - Proper LSP initialization and shutdown

### Planned ⏳

- **Hover Information** - Show type information and documentation on hover
- **Code Completion** - Auto-complete identifiers, keywords, and methods
- **Go to Definition** - Navigate to symbol definitions
- **Find References** - Find all usages of a symbol
- **Document Symbols** - Outline view of functions, types, and constants
- **Code Formatting** - Pretty-print Eclexia code
- **Rename Refactoring** - Rename symbols across files
- **Signature Help** - Show function parameter information

## Usage

### Running the Server

```bash
cargo build --release
./target/release/eclexia-lsp
```

The server communicates via stdin/stdout using the LSP protocol.

### VS Code Integration

Create a VS Code extension that launches the LSP server:

```javascript
// extension.js
const { LanguageClient } = require('vscode-languageclient/node');

function activate(context) {
    const serverOptions = {
        command: 'eclexia-lsp',
        args: []
    };

    const clientOptions = {
        documentSelector: [{ scheme: 'file', language: 'eclexia' }]
    };

    const client = new LanguageClient(
        'eclexia',
        'Eclexia Language Server',
        serverOptions,
        clientOptions
    );

    client.start();
}
```

### Neovim Integration

Add to your Neovim config:

```lua
require'lspconfig'.configs.eclexia = {
  default_config = {
    cmd = {'eclexia-lsp'},
    filetypes = {'eclexia'},
    root_dir = function(fname)
      return vim.fn.getcwd()
    end,
  },
}

require'lspconfig'.eclexia.setup{}
```

## Architecture

```
┌─────────────────────────────────────────┐
│           IDE/Editor Client             │
│   (VS Code, Neovim, Emacs, IntelliJ)    │
└───────────────┬─────────────────────────┘
                │ LSP Protocol (JSON-RPC)
                │ via stdin/stdout
┌───────────────▼─────────────────────────┐
│         Eclexia Language Server         │
│                                         │
│  ┌───────────────────────────────────┐  │
│  │  Document State (DashMap)         │  │
│  │  - URI → (text, version)          │  │
│  └───────────────────────────────────┘  │
│                                         │
│  ┌───────────────────────────────────┐  │
│  │  Analysis Pipeline                │  │
│  │  1. Parse (eclexia-parser)        │  │
│  │  2. Type Check (eclexia-typeck)   │  │
│  │  3. Symbol Resolution (TODO)      │  │
│  └───────────────────────────────────┘  │
│                                         │
│  ┌───────────────────────────────────┐  │
│  │  Features                         │  │
│  │  - Diagnostics ✅                │  │
│  │  - Hover ⏳                       │  │
│  │  - Completion ⏳                  │  │
│  │  - Definition ⏳                  │  │
│  │  - References ⏳                  │  │
│  └───────────────────────────────────┘  │
└─────────────────────────────────────────┘
```

## Dependencies

| Crate | Purpose |
|-------|---------|
| `tower-lsp` | LSP server framework |
| `tokio` | Async runtime |
| `dashmap` | Concurrent document storage |
| `eclexia-parser` | Syntax parsing |
| `eclexia-typeck` | Type checking |
| `eclexia-ast` | AST definitions and spans |

## Development

### Adding New Features

1. Implement the LSP method in `server.rs`
2. Update server capabilities in `initialize()`
3. Add any necessary state to `EclexiaLanguageServer`
4. Test with a compatible LSP client

### Testing

Test the LSP server with any LSP client:

```bash
# Terminal 1: Start the server
cargo run --bin eclexia-lsp

# Terminal 2: Send LSP messages
echo '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}' | cargo run --bin eclexia-lsp
```

Or use the [LSP Inspector](https://github.com/microsoft/language-server-protocol/tree/main/inspector)for visual testing.

## Implementation Status

**Overall:** 30% complete

| Feature | Status | Notes |
|---------|--------|-------|
| Text Sync | ✅ 100% | Full document sync |
| Diagnostics | ✅ 100% | Parse and type errors |
| Hover | ⏳ 0% | Needs symbol resolution |
| Completion | ⏳ 0% | Needs scope tracking |
| Definition | ⏳ 0% | Needs symbol table |
| References | ⏳ 0% | Needs usage tracking |
| Symbols | ⏳ 0% | Needs AST traversal |
| Formatting | ⏳ 0% | Needs pretty printer |
| Rename | ⏳ 0% | Needs symbol resolution |

## Next Steps

1. **Symbol Resolution**
   - Build symbol table from AST
   - Track scopes and bindings
   - Resolve references to definitions

2. **Hover Information**
   - Extract type information from type checker
   - Format documentation comments
   - Show resource annotations

3. **Code Completion**
   - Suggest identifiers in scope
   - Offer keyword completions
   - Complete method names from types

4. **Go to Definition**
   - Map references to definition locations
   - Handle cross-file navigation
   - Support multiple definitions (overloads)

5. **Find References**
   - Track all symbol usages
   - Filter by scope and file
   - Show usage context

## License

AGPL-3.0-or-later
