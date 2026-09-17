# Palomar entries

This directory contains exactly two proposed Palomar entries, one for each
active manuscript.

| Entry | Compared theorem | Files |
|---|---|---|
| Paper I | `CollisionIdeals.Palomar.PaperOne.genericDegreeThreeS3Collision` | `PaperOne/Challenge.lean`, `PaperOne/Solution.lean`, `PaperOne/comparator.json`, `PaperOne/formalization.yaml` |
| Paper II | `CollisionIdeals.Palomar.PaperTwo.explicitPlanarSecantProjector`; `CollisionIdeals.Palomar.PaperTwo.quadraticPlanarCollisionRigidity` | `PaperTwo/Challenge.lean`, `PaperTwo/Solution.lean`, `PaperTwo/comparator.json`, `PaperTwo/formalization.yaml` |

Each Challenge is Mathlib-only and restates the required transparent
definitions locally. Each Solution connects that statement surface to the
project's substantive modules. The duplicate definitions denote the same
objects and use the canonical manuscript notation recorded in
`SEMANTIC-PARITY.md`; they exist only because a Palomar Challenge may not
transitively import the project implementation.

The repository pins Lean 4.28.0 and Mathlib v4.28.0, satisfying Palomar's
current toolchain minimum. Both challenge/solution pairs build locally;
Palomar's protected Comparator and NanoDa replay remains the authoritative
submission check.
