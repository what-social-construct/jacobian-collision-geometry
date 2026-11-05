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
The Paper I Solution and canonical endpoint have been audited with
only `propext`, `Classical.choice`, and `Quot.sound` as axioms.

## Verification status

The main development pins Lean 4.28.0 and Mathlib v4.28.0. The targeted
Paper I build passed on November 4, 2026. Removing its redundant
`finiteNormal` parameter strengthened the compared statement, so the earlier
release preflight does not cover the current version. A fresh release
preflight and protected Comparator/NanoDa replay remain pending before
submission.
