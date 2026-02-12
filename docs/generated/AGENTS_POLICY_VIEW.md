# AGENTS Policy View (Generated)

This file is generated. Do not edit manually.

- Source: `policy/odeu.instructions.v1.json`
- Policy schema: `odeu.instructions.v1`
- Policy hash: `b411864e4e2d22a6c654539f3d1531bf63b80cfc9a0368bd8248d8a32f1a8845`
- Rule count: `1`

## Rule Summary

| Priority | Kind | Rule ID | Rule Version | Code | Effect |
| --- | --- | --- | --- | --- | --- |
| `1000` | `allow` | `default_allow_after_hard_gates` | `1` | `ALLOW_HARD_GATED_ACTION` | `allow_action` |

## Rule Details

### `default_allow_after_hard_gates`

- Kind: `allow`
- Priority: `1000`
- Rule version: `1`
- Code: `ALLOW_HARD_GATED_ACTION`
- Effect: `allow_action`
- Message: Allow actions that pass capability/mode/approval hard gates.
- `when` expression:
```json
{
  "args": [
    {
      "args": [
        "read_only"
      ],
      "atom": "mode_is"
    },
    {
      "args": [
        "writes_allowed"
      ],
      "atom": "mode_is"
    }
  ],
  "op": "or"
}
```
- `then` payload:
```json
{
  "effect": "allow_action",
  "params": {}
}
```
