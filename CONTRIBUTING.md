# Contributing to Eclexia

Thank you for your interest in contributing to Eclexia! This document provides guidelines and information for contributors.

## Table of Contents

- [Getting Started](#getting-started)
- [How to Contribute](#how-to-contribute)
- [Development Workflow](#development-workflow)
- [Code Standards](#code-standards)
- [Pull Request Process](#pull-request-process)

---

## Getting Started

### Prerequisites

Before contributing, ensure you have:

- Git installed
- A GitHub account
- Familiarity with the project's purpose and structure

### Setting Up Your Environment

```bash
# Clone the repository
git clone https://github.com/hyperpolymath/eclexia.git
cd eclexia

# Using Nix (recommended for reproducibility)
nix develop

# Or using toolbox/distrobox
toolbox create eclexia-dev
toolbox enter eclexia-dev
# Install dependencies manually

# Verify setup
just check   # or: cargo check / mix compile / etc.
just test    # Run test suite
```

### Repository Structure

```
eclexia/
├── src/                 # Source code (Perimeter 1-2)
├── lib/                 # Library code (Perimeter 1-2)
├── extensions/          # Extensions (Perimeter 2)
├── plugins/             # Plugins (Perimeter 2)
├── tools/               # Tooling (Perimeter 2)
├── docs/                # Documentation (Perimeter 3)
│   ├── architecture/    # ADRs, specs (Perimeter 2)
│   └── proposals/       # RFCs (Perimeter 3)
├── examples/            # Examples (Perimeter 3)
├── spec/                # Spec tests (Perimeter 3)
├── tests/               # Test suite (Perimeter 2-3)
├── .well-known/         # Protocol files (Perimeter 1-3)
├── .github/             # GitHub config (Perimeter 1)
│   ├── ISSUE_TEMPLATE/
│   └── workflows/
├── CHANGELOG.md
├── CODE_OF_CONDUCT.md
├── CONTRIBUTING.md      # This file
├── GOVERNANCE.md
├── LICENSE
├── MAINTAINERS.md
├── README.adoc
├── SECURITY.md
├── flake.nix            # Nix flake (Perimeter 1)
└── justfile             # Task runner (Perimeter 1)
```

---

## How to Contribute

### Reporting Bugs

**Before reporting**:
1. Search existing issues
2. Check if it's already fixed in `main`
3. Determine which perimeter the bug affects

**When reporting**:

Use the [bug report template](.github/ISSUE_TEMPLATE/bug_report.md) and include:

- Clear, descriptive title
- Environment details (OS, versions, toolchain)
- Steps to reproduce
- Expected vs actual behaviour
- Logs, screenshots, or minimal reproduction

### Suggesting Features

**Before suggesting**:
1. Check the [roadmap](ROADMAP.md) if available
2. Search existing issues and discussions
3. Consider which perimeter the feature belongs to

**When suggesting**:

Use the [feature request template](.github/ISSUE_TEMPLATE/feature_request.md) and include:

- Problem statement (what pain point does this solve?)
- Proposed solution
- Alternatives considered
- Which perimeter this affects

### Your First Contribution

Look for issues labelled:

- [`good first issue`](https://github.com/hyperpolymath/eclexia/labels/good%20first%20issue) — Simple Perimeter 3 tasks
- [`help wanted`](https://github.com/hyperpolymath/eclexia/labels/help%20wanted) — Community help needed
- [`documentation`](https://github.com/hyperpolymath/eclexia/labels/documentation) — Docs improvements
- [`perimeter-3`](https://github.com/hyperpolymath/eclexia/labels/perimeter-3) — Community sandbox scope

---

## Development Workflow

### Branch Naming

```
docs/short-description       # Documentation (P3)
test/what-added              # Test additions (P3)
feat/short-description       # New features (P2)
fix/issue-number-description # Bug fixes (P2)
refactor/what-changed        # Code improvements (P2)
security/what-fixed          # Security fixes (P1-2)
```

### Commit Messages

We follow [Conventional Commits](https://www.conventionalcommits.org/):

```
<type>(<scope>): <description>

[optional body]

[optional footer]
```

**Types**:
- `feat`: New feature
- `fix`: Bug fix
- `docs`: Documentation only
- `style`: Formatting, no code change
- `refactor`: Code change that neither fixes a bug nor adds a feature
- `perf`: Performance improvement
- `test`: Adding or correcting tests
- `chore`: Maintenance tasks

**Examples**:
```
feat(auth): add OAuth2 support for GitHub
fix(parser): handle edge case with empty input
docs(readme): update installation instructions
```

---

## Code Standards

### General Guidelines

- Follow existing code style and patterns
- Write clear, self-documenting code
- Add tests for new functionality
- Update documentation as needed
- Keep commits atomic and focused

### Security

Please review our [Security Policy](SECURITY.md) and ensure your contributions:

- Do not introduce security vulnerabilities
- Follow secure coding practices
- Do not commit secrets or credentials

---

## Pull Request Process

1. **Fork** the repository and create your branch from `main`
2. **Make** your changes following our guidelines
3. **Test** your changes thoroughly
4. **Commit** with clear, conventional commit messages
5. **Push** to your fork
6. **Open** a pull request with:
   - Clear description of changes
   - Reference to related issues
   - Screenshots/examples if applicable
7. **Respond** to review feedback promptly

### Review Criteria

Pull requests are evaluated on:

- Code quality and style consistency
- Test coverage
- Documentation updates
- Security considerations
- Alignment with project goals

---

## Questions?

- Open a [Discussion](https://github.com/hyperpolymath/eclexia/discussions) for general questions
- Check existing issues for similar questions
- Review the [README](README.adoc) for project overview

---

## Code of Conduct

By participating in this project, you agree to abide by our [Code of Conduct](CODE_OF_CONDUCT.md).

---

*Thank you for contributing to Eclexia!*
