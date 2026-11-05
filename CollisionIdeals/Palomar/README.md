# Palomar submission entries

Two proposed entries correspond to the two active manuscripts:

- **Paper I:** generic-degree-three collision geometry and Galois group
  $S_3$. [Challenge](PaperOne/Challenge.lean) ·
  [Solution](PaperOne/Solution.lean) · [Comparator](PaperOne/comparator.json) ·
  [Metadata](PaperOne/formalization.yaml).
- **Paper II:** the explicit planar secant projector and generic-degree-two
  collision rigidity. [Challenge](PaperTwo/Challenge.lean) ·
  [Solution](PaperTwo/Solution.lean) · [Comparator](PaperTwo/comparator.json) ·
  [Metadata](PaperTwo/formalization.yaml).

Each **Challenge** states the theorem using only Mathlib. Its **Solution**
reuses the project's proofs. The transparent definitions repeated in these
independent surfaces denote the same shared objects, not competing
constructions; their notation and canonical owners are recorded in the
[semantic parity dictionary](../../SEMANTIC-PARITY.md).

The Challenge's `sorry` is the intentional proof-comparison placeholder.
Both proved Solution declarations have been audited with
only `propext`, `Classical.choice`, and `Quot.sound` as axioms.

## Verification status

The main development pins Lean 4.28.0 and Mathlib v4.28.0. For submission, use
the separate Lean 4.35 release at the exact commit listed below, not the main
branch's older toolchain.

Both entries passed the [fresh protected preflight](https://github.com/what-social-construct/jacobian-collision-geometry/actions/runs/41967486280)
on November 4, 2026, with no errors or warnings. Comparator, Lean, NanoDa,
and con-ron accepted both entries. The compared statements retain their
explicit literature inputs. No submission or registration has been made.

The reviewed manuscript package at release
[`70eaa4c`](https://github.com/what-social-construct/jacobian-collision-geometry/tree/70eaa4cf78444e6a634b5ba0d95e4ff0a6903c8c)
also [passed its exact-package preflight](https://github.com/what-social-construct/jacobian-collision-geometry/actions/runs/42102758671)
on November 5, 2026.

The final public abstracts and matching Alpöge/Gao background references are
in release [`67872a1`](https://github.com/what-social-construct/jacobian-collision-geometry/tree/67872a1b3e6c6a85e6c93ac0079b023282bc1510).
Its [exact-package preflight](https://github.com/what-social-construct/jacobian-collision-geometry/actions/runs/42132640389)
is the verification record for this metadata refresh. No Lean proofs,
manuscripts, toolchain files, or Comparator configurations changed from
`70eaa4c`; verification evidence remains commit-specific.

## Submission inputs

Use repository `what-social-construct/jacobian-collision-geometry`, commit
`67872a1b3e6c6a85e6c93ac0079b023282bc1510`, and the repository-root project
for both entries. Confirm that its exact-package preflight has accepted both
entries before submitting. Submit the configurations separately:

| Entry | Comparator configuration | Metadata in the release |
|---|---|---|
| Paper I | `CollisionIdeals/Palomar/PaperOne/comparator.json` | `formalization.yaml` |
| Paper II | `CollisionIdeals/Palomar/PaperTwo/comparator.json` | `CollisionIdeals/Palomar/PaperTwo/formalization.yaml` |
