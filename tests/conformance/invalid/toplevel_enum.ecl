// SPDX-License-Identifier: MPL-2.0
// Invalid: `enum` is not a supported top-level item shorthand (use `type`).
//
// Regression for a parser error-recovery infinite loop (found by fuzzing):
// `enum` is a recovery stop-token but `parse_item` rejects it, which used to
// spin forever accumulating errors until OOM. This must now fail fast with a
// parse error rather than hang.

enum Foo {}
