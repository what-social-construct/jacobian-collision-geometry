# Companion manuscripts

This directory contains the two active papers:

- [`paper1.tex`](paper1.tex) / [`paper1.pdf`](paper1.pdf): *Generic Degree
  Three in $JC(3)$: Collision Geometry and Galois Group $S_3$*.
- [`paper2.tex`](paper2.tex) / [`paper2.pdf`](paper2.pdf): *Generic Degree
  Two in $JC(2)$: Secant Projectors and Galois Rigidity*.

Paper II uses exactly the shared notation

```math
A,S,I_R,I_\Delta,C_F,R_F,\operatorname{Obs}(F),\bar\mu_F,B,K,L,q_F
```

from Paper I. It briefly restates the needed dimension-independent theorem
statements and cites Paper I; it does not repeat their proofs. Its new
planar notation is $\delta_F$ for the ordered secant determinant,
$e_F$ for the diagonal projector, and $p_F=1-e_F$ for the
off-diagonal projector.

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
