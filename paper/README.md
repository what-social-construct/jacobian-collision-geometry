# Companion manuscripts

This release contains the reviewed sources and PDFs of two papers:

- [`paper1.tex`](paper1.tex) / [`paper1.pdf`](paper1.pdf): *Generic Degree
  Three in JC(3): Collision Geometry and Galois Group S3*.
- [`paper2.tex`](paper2.tex) / [`paper2.pdf`](paper2.pdf): *Generic Degree
  Two in JC(2): Secant Projectors and Galois Rigidity*.

The files are synchronized verbatim with main manuscript commit
[`15bfc1e`](https://github.com/what-social-construct/jacobian-collision-geometry/tree/15bfc1e6a19ece495e159f931d53defc0ca2edcc/paper).
Both papers put their Lean correspondence after the mathematical conclusion.
Paper II restates and cites Paper I's shared construction, with the same
notation, rather than repeating its proofs.

The compared claims are Paper I's Theorem 3.3 (Keller specialization) and
Paper II's Theorems 3.2 and 5.3. Paper II's compact normal-closure criterion
is retained as Proposition 6.1, separately from those compared declarations.
Its component proofs and the broader boundary/conormal research are indexed
in the [main semantic parity table](https://github.com/what-social-construct/jacobian-collision-geometry/blob/15bfc1e6a19ece495e159f931d53defc0ca2edcc/SEMANTIC-PARITY.md).
The [preserved boundary excerpt](https://github.com/what-social-construct/jacobian-collision-geometry/blob/15bfc1e6a19ece495e159f931d53defc0ca2edcc/CollisionIdeals/Planar/Research/Vanishing/BOUNDARY-CRITERIA.tex)
is not part of this focused release.

Build from this directory with `latexmk -pdf paper1.tex` and
`latexmk -pdf paper2.tex`. The papers share [`references.bib`](references.bib)
and are licensed under [CC BY 4.0](LICENSE).
