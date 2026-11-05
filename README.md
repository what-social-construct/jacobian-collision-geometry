# Jacobian collision geometry: two-paper submission release

[Paper I (PDF)](paper/paper1.pdf) · [Paper II (PDF)](paper/paper2.pdf) · [Object correspondence](SEMANTIC-PARITY.md)

This focused release contains two companion manuscripts and the Lean dependencies
of their compared theorems. Paper I identifies the residual generic collision
factor and its $S_3$ normal-closure symmetry in generic degree three and ambient
dimension three. Paper II constructs the explicit planar secant projector and
excludes generic degree two using Keller--Galois rigidity.

Rigidity is an explicit literature-theorem parameter, not an installed Lean
axiom or a theorem proved here. The full planar Jacobian conjecture is not
claimed. The broader boundary research is not part of this release.

## Two independent entries

- **Paper I:** [Challenge](CollisionIdeals/Palomar/PaperOne/Challenge.lean) /
  [Solution](CollisionIdeals/Palomar/PaperOne/Solution.lean) /
  [Comparator](CollisionIdeals/Palomar/PaperOne/comparator.json) /
  [Metadata](formalization.yaml).
  The compared declaration is
  `CollisionIdeals.Palomar.PaperOne.genericDegreeThreeS3Collision`.
- **Paper II:** [Challenge](CollisionIdeals/Palomar/PaperTwo/Challenge.lean) /
  [Solution](CollisionIdeals/Palomar/PaperTwo/Solution.lean) /
  [Comparator](CollisionIdeals/Palomar/PaperTwo/comparator.json) /
  [Metadata](CollisionIdeals/Palomar/PaperTwo/formalization.yaml).
  The compared declarations are
  `CollisionIdeals.Palomar.PaperTwo.explicitPlanarSecantProjector` and
  `CollisionIdeals.Palomar.PaperTwo.quadraticPlanarCollisionRigidity`.

Each Mathlib-only Challenge deliberately restates the shared objects and leaves
an intentional `sorry` comparison placeholder. Each Solution reuses the common
proof development. These are independent statement surfaces, not competing
constructions.

Paper I accepts an arbitrary supplied normal closure and derives its finiteness.
Its [canonical endpoint](CollisionIdeals/ComplexThree/Cubic/Canonical.lean)
constructs the closure internally. Both retain diagonal compatibility.

## Toolchain and verification

This release pins Lean 4.35.0 and Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679` (v4.35.0).

```bash
lake build
lake check-build
lake env lean MigrationAudit.lean
```

The refreshed release passed the combined 2751-job local build, `lake check-build`,
and the downstream declaration audits on November 4, 2026. The proved endpoints
use only `propext`, `Classical.choice`, and `Quot.sound`.
Both entries subsequently passed the
[protected preflight at `ccbba13`](https://github.com/what-social-construct/jacobian-collision-geometry/actions/runs/41967486280),
with no errors or warnings in either mechanical report. That immutable run
records the proof verification before this manuscript/metadata refresh.

The [two-entry workflow](.github/workflows/papers-palomar-preflight.yml) invokes
the official verifier at an immutable revision, with a separate Comparator
configuration and metadata path for each entry. Each push checks the exact
release commit; consult its workflow run for package-specific evidence.
Running this workflow is not a Palomar submission or registration.

The manuscripts are copied unchanged from the
[reviewed main snapshot `15bfc1e`](https://github.com/what-social-construct/jacobian-collision-geometry/tree/15bfc1e6a19ece495e159f931d53defc0ca2edcc),
which documents the main Lean 4.28 development. This branch ports the same
mathematical constructions to Lean 4.35 for submission. The main snapshot also
contains the optional research modules omitted here.

Both papers place their Lean correspondence after the mathematical
conclusion. Paper II retains the compact marked-normal-closure vanishing
criterion; its longer boundary/conormal discussion is preserved only in the
main research tree. Proposition 6.1's component proofs remain in that main
development and are not among this release's compared declarations.

## License

The repository software uses the [MIT License](LICENSE), except the credited
[normal-closure finiteness adaptation](CollisionIdeals/General/Galois/FiniteNormalClosure.lean),
which retains [Apache-2.0 terms](CollisionIdeals/General/Galois/AXIOM-STACKS-LICENSE).
The manuscripts use [CC BY 4.0](paper/LICENSE).
