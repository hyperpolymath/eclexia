# Eclexia Wiki

This folder is a wiki source set designed for three audiences:

- lay people evaluating the project
- language users writing Eclexia programs
- developers contributing to compiler/runtime/tooling internals

## Main Pages

1. [Home](Home.md)
2. [For Laypeople](For-Laypeople.md)
3. [For Users](For-Users.md)
4. [For Developers](For-Developers.md)
5. [Architecture](Architecture.md)
6. [Testing and Benchmarking](Testing-and-Benchmarking.md)
7. [Troubleshooting](Troubleshooting.md)
8. [Glossary](Glossary.md)
9. [FAQ](FAQ.md)

## README vs Wiki

Keep in `README.adoc`:

- project identity and short pitch
- quick start commands
- high-level doc index and contribution/security/license links

Move to wiki:

- subsystem deep dives
- operational playbooks
- contributor onboarding paths
- FAQ, troubleshooting, and glossary
- benchmark and verification navigation

## Source Mapping

| Canonical Source | Wiki Destination |
| --- | --- |
| `../QUICK_STATUS.md` | [Home](Home.md), [FAQ](FAQ.md) |
| `../GETTING_STARTED.md` | [For Users](For-Users.md) |
| `../SPECIFICATION.md` | [For Developers](For-Developers.md), [Architecture](Architecture.md) |
| `../proofs/PROOFS.md` + `../proofs/FORMAL_VERIFICATION.md` | [For Developers](For-Developers.md), [Glossary](Glossary.md) |
| `../roadmap/IMPLEMENTATION_ROADMAP.md` + `../reports/TOOLCHAIN_STATUS.md` | [Architecture](Architecture.md), [Testing and Benchmarking](Testing-and-Benchmarking.md) |
