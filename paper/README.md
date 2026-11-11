# Companion manuscripts

This directory contains the two active papers:

- [`paper1.tex`](paper1.tex) / [`paper1.pdf`](paper1.pdf): *Generic Degree
  Three in $JC(3)$: Collision Geometry and Galois Group $S_3$*.
- [`paper2.tex`](paper2.tex) / [`paper2.pdf`](paper2.pdf): *Planar Secant
  Projectors and Galois Fixed Loci*.

Paper II uses exactly the shared notation

```math
A,S,I_R,I_\Delta,C_F,R_F,\mathrm{Obs}(F),\bar\mu_F,B,K,L,q_F
```

from Paper I. It briefly restates the needed dimension-independent theorem
statements and cites Paper I; it does not repeat their proofs. Its new
planar notation is $\delta_F$ for the ordered secant determinant,
$e_F$ for the diagonal projector, and $p_F=1-e_F$ for the
off-diagonal projector.
The same projector gives a fixed-locus certificate in the all-conjugate
algebra $E$ and a finite étale $G$-cover over its invariant algebra $E^G$.
The paper does not identify $E^G$ with the polynomial target ring $B$.

Paper II retains the marked-normal-closure criterion
$p_F=0\iff\mathrm{Obs}(F)=0\iff L/K\text{ normal}\iff H=1$,
with Keller--Galois rigidity explicit. This criterion has no generic-degree
restriction; normality closes its degree-two application. Universal planar
vanishing is not asserted.

The longer target-boundary and conormal development is retained in the
[planar research folder](../CollisionIdeals/Planar/Research/Vanishing/README.md),
including its [preserved manuscript excerpt](../CollisionIdeals/Planar/Research/Vanishing/BOUNDARY-CRITERIA.tex).
It is not part of the Paper II proof. The protected Comparator selection
still covers the explicit projector and quadratic exclusion (Theorems
3.2 and 6.3), not the new fixed-locus and cover results.

Build both papers from this directory:

```bash
latexmk -pdf paper1.tex
latexmk -pdf paper2.tex
```

The papers share [`references.bib`](references.bib). The former combined and
boundary/inertia manuscripts are inactive historical artifacts in
[`../manuscript-archive/`](../manuscript-archive/). Repository-wide notation
and theorem correspondence are maintained in
[`../SEMANTIC-PARITY.md`](../SEMANTIC-PARITY.md).
