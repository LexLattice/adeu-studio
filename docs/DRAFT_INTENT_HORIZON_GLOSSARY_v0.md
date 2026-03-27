# Draft Intent Horizon Glossary v0

Status: working doctrine note after `V41` family closeout on `main`.

This note defines common horizon-sensitive terms that are easy to over-read in planning
and architecture docs.

It does not authorize runtime behavior, schema release, or implementation by itself.

## Purpose

- reduce over-closure pressure in family and architecture docs;
- distinguish local scope statements from global prohibition;
- give later reviews one explicit reading for common planning terms.

## Terms

### `bounded`

`bounded` means:

- explicitly scoped for the current family or slice;
- intentionally limited in what it claims to solve;
- not automatically exhaustive over the whole broader architecture space.

It does not mean:

- globally maximal;
- permanently frozen against future widening.

### `complete on main`

`complete on main` means:

- the named family or path ladder has no remaining default paths in the current repo
  state.

It does not mean:

- no future family may build on it;
- all broader architecture seams have been exhausted.

### `closed`

`closed` means:

- the named path or family is no longer the active default implementation frontier.

It does not mean:

- retroactively forbidden to inspect;
- impossible to consume from successor work.

### `deferred`

`deferred` means:

- not selected or not solved in the current family/slice;
- still live for later explicit selection unless separately forbidden.

It does not mean:

- rejected forever.

### `forbidden`

`forbidden` means:

- explicitly not authorized by the governing lock or equally strong authority source
  for the current horizon.

It should not be inferred from:

- silence;
- mere absence from scope;
- planning deferral language by itself.

### `authorized`

`authorized` means:

- explicitly permitted by the governing authority surface for the current horizon.

Planning docs may record absence of authorization without themselves becoming the final
authorizing surface.

### `not solved` / `did not attempt`

`not solved` and `did not attempt` mean:

- outside the accepted shipped scope of the current family;
- candidate territory for later explicit family selection.

They should not be over-read as:

- proof that the seam is invalid;
- proof that no lawful path exists there.

### `next family selection required`

`next family selection required` means:

- later widening must pass through an explicit successor authority surface;
- future work should not be smuggled in as "just another patch" on top of a closed
  family.

It does not mean:

- the future family is already selected;
- the successor family’s shape is already settled.
