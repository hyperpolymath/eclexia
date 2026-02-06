# Package Specification (package.toml)

## Format

Every Eclexia package must have a `package.toml` file in its root directory.

## Example

```toml
[package]
name = "my-package"
version = "0.1.0"
authors = ["Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>"]
edition = "2025"
description = "A sample Eclexia package"
license = "AGPL-3.0-or-later"
repository = "https://github.com/hyperpolymath/my-package"

[dependencies]
core = "0.1"
collections = "0.1"

[dev-dependencies]
test-utils = "0.1"

[build]
output = "bin"  # or "lib"
entry = "src/main.ecl"

[resources]
# Resource budgets for adaptive function selection
energy = "1J"    # Maximum energy per execution
time = "100ms"   # Maximum latency per execution
memory = "10MB"  # Maximum memory allocation
carbon = "1gCO2e"  # Maximum carbon emissions

[features]
default = ["std"]
std = []
no-std = []
```

## Fields

### [package]
- `name`: Package name (required)
- `version`: Semantic version (required)
- `authors`: List of authors (required)
- `edition`: Eclexia edition year (required)
- `description`: Short package description
- `license`: SPDX license identifier
- `repository`: URL to source repository

### [dependencies]
- Key-value pairs of dependency name to version constraint
- Versions follow semver: `"0.1"`, `"^0.1.0"`, `"~0.1.0"`, `">=0.1, <0.2"`

### [dev-dependencies]
- Dependencies only needed for development/testing
- Same format as [dependencies]

### [build]
- `output`: Build output type (`"bin"` or `"lib"`)
- `entry`: Entry point file path

### [resources]
- `energy`: Maximum energy budget per execution
- `time`: Maximum latency budget per execution
- `memory`: Maximum memory budget per execution
- `carbon`: Maximum carbon emissions budget per execution

### [features]
- Named feature flags for conditional compilation
- `default`: Features enabled by default
