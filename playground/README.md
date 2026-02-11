# Eclexia Playground

A local PWA playground for Eclexia with server-side execution modes.

## Features
- PWA shell (manifest + service worker).
- Web REPL/editor with syntax highlighting.
- Example loader.
- Share-by-URL support.
- Execution modes:
  - `interpret` (profile JSON from source execution)
  - `compile` (build + profile bytecode)
  - `step` (bytecode disassembly step navigation)
- Resource and shadow-price visual panels.

## Run Locally
1. Ensure `node` and Rust toolchain are available.
2. From repo root:
   - `node playground/server.js`
3. Open: `http://127.0.0.1:4173`

Optional environment variables:
- `PLAYGROUND_HOST` (default `127.0.0.1`)
- `PLAYGROUND_PORT` (default `4173`)
- `ECLEXIA_BIN` (default `target/debug/eclexia`)

## Notes
- First run may build `eclexia` automatically if binary is missing.
- `step` mode currently uses disassembly-based stepping.
