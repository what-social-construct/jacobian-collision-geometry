# Generic Degree Three in JC(3)

[Paper I (PDF)](paper/paper1.pdf) · [LaTeX source](paper/paper1.tex) · [object correspondence](SEMANTIC-PARITY.md)

This focused release contains Paper I and the Lean dependencies of its cubic
collision theorem. For a three-dimensional Keller map of generic degree three,
classical Keller--Galois rigidity excludes the normal branch; the residual
generic collision factor is the normal closure, with Galois group $S_3$.
Rigidity is an explicit theorem hypothesis, not an additional Lean axiom.

The [full repository at the source revision](https://github.com/what-social-construct/jacobian-collision-geometry/tree/135e601649a056b0512443972d5246e872836638)
contains the shared development, Paper II, and optional research modules.
They are not part of this focused release. The manuscript includes the latest
explicit example and release-specific toolchain notes.

## Compared theorem

`CollisionIdeals.Palomar.PaperOne.genericDegreeThreeS3Collision` receives a
Keller map, generic degree three, the rigidity hypothesis, and a supplied finite
normal closure. It derives the diagonal-compatible generic collision product,
obstruction nonvanishing, and the $S_3$ identification.

The separate canonical endpoint,
`CollisionIdeals.complexThreeGenericDegreeThreeS3Collision`, constructs the
normal closure internally. These are distinct interfaces to the same cubic
construction. The compared statement is the Keller specialization of
Theorem 3.3, not every statement in the manuscript.

## Build and verification

This release pins Lean 4.35.0 and Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679` (v4.35.0).

```bash
lake build CollisionIdeals.Palomar.PaperOne.Challenge \
  CollisionIdeals.ComplexThree.Cubic.Canonical \
  CollisionIdeals.Palomar.PaperOne.Solution
lake check-build
lake env lean MigrationAudit.lean
```

These checks passed locally. The audit reports only `propext`,
`Classical.choice`, and `Quot.sound` for the proved endpoints.
The Challenge's intentional `sorry` is the comparison target; the Solution
and its proof dependencies contain no proof holes. Nonblocking linter and
deprecation warnings remain.

On Linux with Bubblewrap installed, the direct comparison command is:

```bash
lake comparator --config CollisionIdeals/Palomar/PaperOne/comparator.json
```

The branch workflow invokes Palomar's pinned official reusable workflow in
full mode, including the protected statement comparison and external-kernel
checks. Its GitHub Actions report determines the preflight result.
Running this workflow does not submit or register the paper with Palomar.
The root `formalization.yaml` is the metadata entry for this release.

To rebuild the manuscript:

```bash
cd paper
latexmk -pdf paper1.tex
```

## License

The Lean code and repository software use the [MIT License](LICENSE).
The manuscript uses [CC BY 4.0](paper/LICENSE).
