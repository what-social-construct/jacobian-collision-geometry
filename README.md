# Collision Geometry and the Jacobian Conjecture

**[Paper I (PDF)](paper/paper1.pdf)** · **[Paper II (PDF)](paper/paper2.pdf)** · [LaTeX sources](paper/) · [semantic parity](SEMANTIC-PARITY.md) · [manuscript archive](manuscript-archive/)

We study the scheme of pairs with the same image under a polynomial map,
and the ideal measuring its departure from the diagonal. This repository
contains two companion manuscripts and their Lean 4 formalization. Paper I identifies
the $S_3$ normal-closure symmetry of generic-degree-three counterexamples to
$JC(3)$. Paper II constructs an explicit planar secant projector and uses
Keller--Galois rigidity to exclude generic degree two for Keller maps in
$JC(2)$.

## Start here

- **Paper I:** [main Lean theorem](CollisionIdeals/ComplexThree/Cubic/Canonical.lean)
  and its independent [submission statement](CollisionIdeals/Palomar/PaperOne/Challenge.lean)
  / [proved solution](CollisionIdeals/Palomar/PaperOne/Solution.lean).
- **Paper II:** [quadratic collision theorem](CollisionIdeals/Planar/GenericDegreeTwo/Main.lean)
  and [explicit secant projector](CollisionIdeals/Planar/ExplicitSecant.lean),
  with an independent [submission statement](CollisionIdeals/Palomar/PaperTwo/Challenge.lean)
  / [proved solution](CollisionIdeals/Palomar/PaperTwo/Solution.lean).
- **Object tracing:** the [notation and proof-status dictionary](SEMANTIC-PARITY.md)
  identifies the shared objects; the [Palomar crosswalk](SEMANTIC-PARITY.md#palomar-submission-surface-crosswalk)
  explains their repeated submission definitions.

The Keller--Galois rigidity theorem is an **explicit literature input**:
`ComplexKellerGaloisRigidity n` is a proposition, not an installed axiom or a
theorem proved here. Results using it take its proof as a parameter. The
full planar Jacobian conjecture remains outside the completed degree-two result.

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

Since $I_R(F)\subseteq I_\Delta$, the quotient map
$q_F:S\twoheadrightarrow C_F:=S/I_R(F)$ carries $I_\Delta$ to

```math
\mathrm{Obs}(F)
=q_F(I_\Delta)
\cong I_\Delta/I_R(F)
=\ker(\bar\mu_F),
```

where $\bar\mu_F:C_F\to A$ is diagonal evaluation. Thus

```math
F\text{ is a polynomial automorphism}
\quad\Longleftrightarrow\quad
I_R(F)=I_\Delta
\quad\Longleftrightarrow\quad
\mathrm{Obs}(F)=0
```

over $\mathbb C$, with the reverse implication using Ax--Grothendieck.
Both manuscripts use this notation unchanged.

Writing

```math
B=\mathbb C[F_1,\ldots,F_n]\subseteq A,
\qquad K=\mathrm{Frac}(B),
\qquad L=\mathrm{Frac}(A),
```

finite generic degree gives a compatible identification

```math
K\otimes_BC_F\simeq_K L\otimes_KL,
```

under which the base-changed diagonal map is tensor multiplication.

## The two papers

### Paper I: generic degree three in $JC(3)$

For ambient dimension $3$ and generic degree $[L:K]=3$, nonautomorphy
is automatic, so the counterexample condition is equivalent to the Keller
condition. Keller--Galois rigidity excludes the normal cubic branch. In the
nonnormal branch the residual generic collision factor is the normal closure
$N$ of $L/K$, and

```math
K\otimes_BC_F\simeq_K L\times N,
\qquad
\mathrm{Gal}(N/K)\cong S_3.
```

The first factor is the diagonal. The second is the residual generic factor.

### Paper II: generic degree two in $JC(2)$

Paper II restates and cites the dimension-independent results from Paper I;
it does not reprove them. For a planar Keller map with
$\det JF=c\in\mathbb C^\times$, ordered divided differences give a secant
determinant $\delta_F$ and the canonical off-diagonal projector

```math
p_F=1-c^{-1}q_F(\delta_F)\in C_F,
\qquad
\mathrm{Obs}(F)=C_Fp_F.
```

Generic degree two yields

```math
K\otimes_BC_F\simeq_KL\times L,
```

so the residual factor forces $\mathrm{Obs}(F)\ne0$ and $p_F\ne0$.
But a separable quadratic extension is Galois; Keller--Galois rigidity makes
the map an automorphism, forcing $\mathrm{Obs}(F)=0$ and $p_F=0$.
Hence no planar Keller map has generic degree two.

This is the generic-degree-two case, not a proof of all of $JC(2)$.
Possible counterexamples of ambient dimension two must have nonnormal generic
degree at least three.

## Lean organization and status

The stable public modules follow the same ownership split as the manuscripts:

| Layer | Modules | Role |
|---|---|---|
| collision geometry | [General/Collision](CollisionIdeals/General/Collision/) | $I_R$, $I_\Delta$, $C_F$, $\mathrm{Obs}(F)$, and diagonal evaluation |
| generic fiber | [General/GenericFiber](CollisionIdeals/General/GenericFiber/) | $B\subseteq A$, $K\subseteq L$, generic base change, and marked-root decompositions |
| automorphism interfaces | [General/Automorphism](CollisionIdeals/General/Automorphism/) | automorphism criteria and the named Keller--Galois rigidity input |
| cubic specialization | [ComplexThree/Cubic](CollisionIdeals/ComplexThree/Cubic/) | nonnormal cubic residual factor, normal closure, and $S_3$ |
| planar secant | [Planar/ExplicitSecant](CollisionIdeals/Planar/ExplicitSecant.lean) | canonical divided differences, $\delta_F$, and $p_F$ |
| quadratic specialization | [Planar/GenericDegreeTwo](CollisionIdeals/Planar/GenericDegreeTwo/) | nonvanishing, rigidity vanishing, and the final contradiction |

The focused Paper II spine uses no normalization, boundary, inertia, purity, or
finite-étale assumptions.

The previous full-$JC(2)$ boundary/inertia manuscript is retained in
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
`comparator.json`, and `formalization.yaml`. Their repeated transparent
definitions are intentional: the independent statement must not import the
project implementation. See the [submission guide](CollisionIdeals/Palomar/README.md).

The main development pins Lean 4.28.0 and Mathlib v4.28.0. The separate
[submission release at `ccbba13`](https://github.com/what-social-construct/jacobian-collision-geometry/tree/ccbba1356d6e737e1e7dd336a7014360e2f52251)
pins Lean 4.35.0. **Both protected preflights passed** on November 4, 2026:
[verification run](https://github.com/what-social-construct/jacobian-collision-geometry/actions/runs/41967486280).
The reports contain no errors or warnings; Comparator, Lean, NanoDa, and
con-ron accepted both entries. This is verification evidence, not Palomar
registration.

## Build

From the repository root, check the Paper I proof and manuscript-facing endpoint:

```bash
lake build CollisionIdeals.Palomar.PaperOne.Solution CollisionIdeals.ComplexThree.Cubic.Canonical
```

Or build the full development:

```bash
lake build
```

From `paper/`:

```bash
latexmk -pdf paper1.tex
latexmk -pdf paper2.tex
```

## License

Lean source and other software are licensed under the [MIT License](LICENSE),
except for the credited AXIOM adaptation in
[`FiniteNormalClosure.lean`](CollisionIdeals/General/Galois/FiniteNormalClosure.lean),
which retains [Apache-2.0 terms](CollisionIdeals/General/Galois/AXIOM-STACKS-LICENSE).
The active manuscripts in [`paper/`](paper/) are licensed under
[CC BY 4.0](paper/LICENSE).
