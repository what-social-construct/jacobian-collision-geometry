# Collision Geometry and the Jacobian Conjecture

**[Paper I (PDF)](paper/paper1.pdf)** · **[Paper II (PDF)](paper/paper2.pdf)** · [LaTeX sources](paper/) · [semantic parity](SEMANTIC-PARITY.md) · [manuscript archive](manuscript-archive/)

This repository contains two companion manuscripts and a Lean 4
formalization of collision geometry beyond the diagonal. Paper I identifies
the (S_3) normal-closure symmetry of generic-degree-three counterexamples to
(JC(3)). Paper II constructs an explicit planar secant projector and uses
Keller--Galois rigidity to exclude generic degree two for Keller maps in
(JC(2)).

## Shared collision objects

For a polynomial map

```math
F=(F_1,\ldots,F_n):\mathbb A^n_{\mathbb C}\longrightarrow
\mathbb A^n_{\mathbb C},
```

put

```math
A=\mathbb C[x_1,\ldots,x_n],\qquad
S=\mathbb C[x_1,\ldots,x_n,y_1,\ldots,y_n].
```

The collision and diagonal ideals are

```math
I_R(F)=\bigl(F_i(x)-F_i(y)\bigr)_{i=1}^n,
\qquad
I_\Delta=\bigl(x_i-y_i\bigr)_{i=1}^n.
```

Since (I_R(F)\subseteq I_\Delta), the quotient map
(q_F:S\twoheadrightarrow C_F:=S/I_R(F)) carries (I_\Delta) to

```math
\operatorname{Obs}(F)
=q_F(I_\Delta)
\cong I_\Delta/I_R(F)
=\ker(\bar\mu_F),
```

where (ar\mu_F:C_F\to A) is diagonal evaluation. Thus

```math
F\text{ is a polynomial automorphism}
\quad\Longleftrightarrow\quad
I_R(F)=I_\Delta
\quad\Longleftrightarrow\quad
\operatorname{Obs}(F)=0
```

over (mathbb C), with the reverse implication using Ax--Grothendieck.
Both manuscripts use this notation unchanged.

Writing

```math
B=\mathbb C[F_1,\ldots,F_n]\subseteq A,
\qquad K=\operatorname{Frac}(B),
\qquad L=\operatorname{Frac}(A),
```

finite generic degree gives a compatible identification

```math
K\otimes_BC_F\simeq_K L\otimes_KL,
```

under which the base-changed diagonal map is tensor multiplication.

## The two papers

### Paper I: generic degree three in (JC(3))

For ambient dimension (3) and generic degree ([L:K]=3), nonautomorphy
is automatic, so the counterexample condition is equivalent to the Keller
condition. Keller--Galois rigidity excludes the normal cubic branch. In the
nonnormal branch the residual generic collision factor is the normal closure
(N) of (L/K), and

```math
K\otimes_BC_F\simeq_K L\times N,
\qquad
\operatorname{Gal}(N/K)\cong S_3.
```

The first factor is the diagonal. The second is the residual generic factor.

### Paper II: generic degree two in (JC(2))

Paper II restates and cites the dimension-independent results from Paper I;
it does not reprove them. For a planar Keller map with
(det JF=c\in\mathbb C^\times), ordered divided differences give a secant
determinant (delta_F) and the canonical off-diagonal projector

```math
p_F=1-c^{-1}q_F(\delta_F)\in C_F,
\qquad
\operatorname{Obs}(F)=C_Fp_F.
```

Generic degree two yields

```math
K\otimes_BC_F\simeq_KL\times L,
```

so the residual factor forces (operatorname{Obs}(F)\ne0) and (p_F\ne0).
But a separable quadratic extension is Galois; Keller--Galois rigidity makes
the map an automorphism, forcing (operatorname{Obs}(F)=0) and (p_F=0).
Hence no planar Keller map has generic degree two.

This is the generic-degree-two case, not a proof of all of (JC(2)).
Possible counterexamples of ambient dimension two must have nonnormal generic
degree at least three.

## Lean organization and status

The stable public modules follow the same ownership split as the manuscripts:

| Layer | Modules | Role |
|---|---|---|
| collision geometry | `CollisionIdeals.General.Collision` | (I_R), (I_\Delta), (C_F), (operatorname{Obs}(F)), and diagonal evaluation |
| generic fiber | `CollisionIdeals.General.GenericFiber` | (B\subseteq A), (K\subseteq L), generic base change, and marked-root decompositions |
| automorphism interfaces | `CollisionIdeals.General.Automorphism` | automorphism criteria and the named Keller--Galois rigidity input |
| cubic specialization | `CollisionIdeals.ComplexThree.Cubic` | nonnormal cubic residual factor, normal closure, and (S_3) |
| planar secant | `CollisionIdeals.Planar.ExplicitSecant` | canonical divided differences, (delta_F), and (p_F) |
| quadratic specialization | `CollisionIdeals.Planar.GenericDegreeTwo` | nonvanishing, rigidity vanishing, and the final contradiction |

`ComplexKellerGaloisRigidity n` is a proposition representing the classical
literature theorem. It is neither installed as an axiom nor proved in this
repository; every theorem using it receives a proof explicitly. The focused
Paper II spine uses no normalization, boundary, inertia, purity, or
finite-étale assumptions.

The previous full-(JC(2)) boundary/inertia manuscript is retained in
[`manuscript-archive/`](manuscript-archive/), and its opt-in Lean research
modules remain outside the stable `CollisionIdeals.Planar` import spine.
Detailed object correspondence and remaining research gaps are tracked in
[`SEMANTIC-PARITY.md`](SEMANTIC-PARITY.md).

## Palomar layout

The repository contains exactly two proposed Palomar entries, one for each
paper:

- `CollisionIdeals.Palomar.PaperOne`
- `CollisionIdeals.Palomar.PaperTwo`

Each has a Mathlib-only `Challenge.lean`, a project-backed `Solution.lean`, a
`comparator.json`, and `formalization.yaml`. The repository is currently
pinned to Lean 4.24, while Palomar presently requires Lean 4.28 or newer; the
toolchain migration remains necessary before submission.

## Build

From the repository root:

```bash
lake build
```

From `paper/`:

```bash
latexmk -pdf paper1.tex
latexmk -pdf paper2.tex
```

## License

Lean source and other software are licensed under the [MIT License](LICENSE).
The active manuscripts in [`paper/`](paper/) are licensed under
[CC BY 4.0](paper/LICENSE).
