# Collision Geometry and the Jacobian Conjecture

**[Read the paper (PDF)](Collision%20Geometry%20and%20the%20Jacobian%20Conjecture.pdf)** · [LaTeX source](paper/)

Let

```math
F=(F_1,\ldots,F_n):\mathbb A^n_{\mathbb C}\longrightarrow
\mathbb A^n_{\mathbb C}
```

be a polynomial map.  In the coordinate ring of two copies of the source,

```math
S=\mathbb C[x_1,\ldots,x_n,y_1,\ldots,y_n],
```

there are two canonical ideals:

```math
I_R(F)=\bigl(F_i(x)-F_i(y)\bigr)_{i=1}^n,
\qquad
I_\Delta=\bigl(x_i-y_i\bigr)_{i=1}^n.
```

Every polynomial difference vanishes on the diagonal, so there is a
canonical inclusion

```math
I_R(F)\subseteq I_\Delta
```

and therefore a canonical $S/I_R(F)$-module

```math
\mathrm{Obs}(F):=I_\Delta/I_R(F).
```

Thus $\mathrm{Obs}(F)$ is not an additional independent object: it
is the canonical defect module in the exact sequence

```math
0\longrightarrow I_R(F)\longrightarrow I_\Delta
\longrightarrow\mathrm{Obs}(F)\longrightarrow0.
```

Equivalently, let

```math
\bar\mu_F:S/I_R(F)\longrightarrow
\mathbb C[x_1,\ldots,x_n],
\qquad
[f]_{I_R}\longmapsto f(x,x),
```

be diagonal evaluation on the collision ring.  Since the kernel of
diagonal evaluation on $S$ is $I_\Delta$, we have

```math
\boxed{
\ker(\bar\mu_F)=\mathrm{Obs}(F)=I_\Delta/I_R(F),
}
```

so there is a second canonical exact sequence

```math
0\longrightarrow\mathrm{Obs}(F)
\longrightarrow S/I_R(F)
\xrightarrow{\bar\mu_F}\mathbb C[x_1,\ldots,x_n]
\longrightarrow0.
```

The purpose of this project is to study the vanishing of
$\mathrm{Obs}(F)$.
Since $I_R(F)\subseteq I_\Delta$, the elementary module criterion gives

```math
\mathrm{Obs}(F)=0
\quad\Longleftrightarrow\quad
I_R(F)=I_\Delta.
```

## Automorphism criterion

Over $\mathbb C$, the quotient has a direct interpretation:

```math
\boxed{
F\text{ is a polynomial automorphism}
\quad\Longleftrightarrow\quad
\mathrm{Obs}(F)=0.
}
```

If $F$ has a polynomial inverse, applying the inverse to the two output
tuples gives $I_\Delta\subseteq I_R(F)$.  Conversely, vanishing gives
$I_R(F)=I_\Delta$, hence injectivity on complex points; Ax–Grothendieck
then gives a polynomial automorphism.

The Lean proposition `PlanarJacobianConjecture` records the usual
automorphism formulation.  The proposition `PlanarAxGrothendieck` records
the injective-polynomial-map automorphism principle as an explicit
interface.  Lean proves the canonical formulation directly:

```text
PlanarAxGrothendieck →
  (PlanarJacobianConjecture ↔ PlanarVanishing)
```

in `planarJacobianConjecture_iff_planarVanishing`.  For each individual
map, `collisionDiagonal_ker` identifies the kernel of $\bar\mu_F$ with
the obstruction ideal.

The dimension-independent automorphism and Jacobian-conjecture interfaces
live under `General.Automorphism`: `Statements` names the propositions,
`Equivalences` compares them with collision vanishing, and `Criteria`
contains the underlying mapwise automorphism tests.  The planar files are
their $n=2,\ k=\mathbb C$ specializations.

All literature interfaces, including the standard Ax–Grothendieck
instance, are listed together in the canonical planar spine below.

Geometrically, if $C_F=S/I_R(F)$, then

```math
\mathrm{Spec}(C_F)
=
\mathbb A^n\times_{\mathbb A^n}\mathbb A^n
```

represents the functor of ordered pairs of points over a test scheme with
the same image under $F$; in particular, its complex points are the usual
ordered pairs with equal image.  The closed
subscheme cut out by $\mathrm{Obs}(F)$, regarded as an ideal of
$C_F$, is the diagonal.  Thus $\mathrm{Obs}(F)=0$ says that the
self-fiber product is scheme-theoretically only the diagonal.
Write
$C_F^\circ:=S/(I_R:I_\Delta)$ and
$R_F^\circ:=\operatorname{Spec}(C_F^\circ)$ for the affine first-colon
residual scheme.  It is the complementary off-diagonal factor when the
diagonal is clopen; no such product decomposition is implicit in the
definition.

## Universal property

The construction is dimension-generic.  Put

```math
A=R[x_i]_{i\in\iota},\qquad B=R[t_j]_{j\in\kappa},
\qquad t_j\longmapsto F_j.
```

For every commutative $R$-algebra $T$, the collision quotient satisfies

```math
\mathrm{Hom}_{R\text{-alg}}(S/I_R(F),T)
\cong
\left\{
(f,g):A\rightrightarrows T:
f(F_j)=g(F_j)\text{ for every }j
\right\}.
```

Consequently there is a canonical equivalence

```math
S/I_R(F)\cong A\otimes_BA.
```

This universal construction does not assert vanishing.  The planar question
asks whether the off-diagonal factor vanishes.  Under the explicit separable
cubic normal-closure conditions formalized here, the generic collision
algebra decomposes as $L\otimes_KL\simeq L\times N$, and the same residual
field satisfies $\mathrm{Gal}(N/K)\simeq S_3$.  No concrete
three-dimensional Keller counterexample is asserted.

## Formalization status

The Lean development separates the proved algebraic constructions from
the geometric inputs supplied explicitly at the current library boundary.
At a glance, it includes:

- the dimension-generic collision quotient, obstruction ideal, fiber-product
  interpretation, and automorphism criterion;
- the dimension-independent Galois collision map pair attached to an ordered
  pair of conjugate sheets \((g,\sigma g)\), together with the planar
  off-diagonal specialization for a group-theoretically moved pair;
- the planar secant and normalization constructions;
- the canonical conjugate affine opens on the Galois normalization, their
  pulled-back boundary ideals and moving-boundary sums, and the
  valuation-theoretic containment of every inertia-moving boundary ideal in
  the ramified height-one prime;
- the formal implications from supplied moving-sheet coverage, boundary
  separation, no hidden inertia, or `PlanarRamificationRigidity` together
  with its explicit support bridge, to obstruction vanishing;
- the off-diagonal decomposition and obstruction in the separable cubic
  $S_3$ case in dimension three.

The source tree follows mathematical ownership.  `CollisionIdeals.General`
exports the collision, fiber-product, generic-fiber, Galois, normalization,
Keller, and automorphism infrastructure shared by both applications.
`CollisionIdeals.ComplexThree` owns the cubic $S_3$ specialization, while
`CollisionIdeals.Planar` owns the secant, boundary, and rigidity development.
Within each dimension-specific layer, `Statements` names conjectural
propositions, `Equivalences` contains proved iff characterizations,
`Interfaces` records explicit comparison obligations, and `Consequences`
contains proved one-way endgames.

Universal `PlanarBoundaryCoherence` and `PlanarRamificationRigidity` are not
proved.  Their current Lean routes use the explicit
`BoundaryCoherenceBridge` and `RamificationRigidityBridge`; moving-sheet
coverage, boundary separation, and the older no-hidden-inertia interface are
likewise explicit inputs to their formal theorems.  The formal cubic theorem
does not instantiate its hypotheses with a concrete three-dimensional Keller
map.

<details>
<summary>Detailed theorem inventory</summary>

The current development is dimension-generic and proves:

- every polynomial difference lies in the diagonal ideal;
- the canonical containment $I_R(F)\subseteq I_\Delta$;
- the universal property of the collision quotient;
- the canonical equivalence $S/I_R(F)\simeq A\otimes_BA$;
- the obstruction ideal is the kernel of the diagonal map
  $S/I_R(F)\to A$;
- $\mathrm{Obs}(F)=0$ if and only if $I_R(F)=I_\Delta$;
- equality of the two ideals implies injectivity on points;
- a polynomial left inverse forces $I_R(F)=I_\Delta$;
- the abstract secant-determinant identities and resulting idempotent
  decomposition;
- a concrete planar secant decomposition whose chosen determinant restricts
  to the planar Jacobian determinant;
- for planar Keller maps,
  $I_R:I_\Delta=I_R+(\delta_F)$ and
  $I_R=I_\Delta\iff I_R+(\delta_F)=S$;
- the concrete secant projector witnessing that the planar collision
  diagonal is a clopen factor;
- saturation stabilizes at $I_R:I_\Delta$ when the diagonal is clopen;
- the complementary-ideal identities and Chinese-remainder sheet
  decomposition;
- the affine off-diagonal collision scheme
  $R_F^\circ=\mathrm{Spec}(S/(I_R:I_\Delta))$;
- the canonical identification of $\mathrm{Spec}(S/I_R)$ with
  the categorical affine self-fiber product $X\times_YX$;
- the concrete planar function fields
  $K=\mathbb C(P,Q)\subset L=\mathbb C(x,y)$, a finite normal-closure
  interface $L\hookrightarrow N$, and the fixing subgroup
  $H=\mathrm{Gal}(N/L)$;
- the normalized affine models
  ```math
  Z=\mathrm{Norm}_N(Y)\longrightarrow
  \overline X=\mathrm{Norm}_L(Y)\longrightarrow Y
  ```
  and the commuting normalization triangle;
- the dimension-independent double-coset index on
  $D_E\backslash G/H$, with its planar type specialization;
- a supplied height-one normalization diagram recording divisorial
  valuations and their conjugate centers;
- a separate supplied realization identifying its group-theoretic index
  with the geometric ramification index
  $[I_E:I_E\cap gHg^{-1}]$;
- the canonical pulled-back conjugate affine opens, closed boundaries,
  vanishing ideals, and moving-boundary ideals on the common Galois
  normalization, with right-$H$ invariance;
- the valuation-theoretic containment of every inertia-moving pulled-back
  boundary ideal in the ramified center prime, and direct implications from
  `PlanarMovingSheetCoverage` or `PlanarBoundarySeparation` to no
  codimension-one ramification;
- from the supplied Keller-to-étale bridge and ramification realization,
  the theorem placing every positive-index conjugate center in the deleted
  boundary, kept separate from `PlanarNoHiddenInertia`;
- the hypothesis-parametrized compositions from no codimension-one ramification---
  including the explicit `PlanarRamificationRigidity`/
  `RamificationRigidityBridge` route---through branch purity and
  finite-étale rigidity to `PlanarVanishing`;
- the dimension-generic function-field bridge
  $K\otimes_B(S/I_R)\simeq L\otimes_KL$, under the explicit
  generic-source surjectivity condition;
- for a separable cubic power-basis extension, the proved CRT decomposition
  $L\otimes_KL\simeq L\times\mathrm{AdjoinRoot}(\mathrm{minpolyDiv})$, with first
  projection equal to diagonal multiplication;
- a compatible nontrivial second factor in the generic collision algebra
  descends, by flatness of $K=\mathrm{Frac}(B)$, to
  $\mathrm{Obs}(F)\ne0$ and $I_R(F)\subsetneq I_\Delta$;
- cubic nonnormality implies irreducibility of the quadratic residual
  polynomial, identifies its residual algebra with the marked normal
  closure, and proves nontriviality of the subgroup fixing the marked
  cubic field;
- the lower-level generic witness builder takes explicit residual-field,
  degree-three, marked-normal-closure, marked-embedding compatibility, and
  nontrivial-fixing-subgroup data and concludes
  $\mathrm{Gal}(N/K)\simeq S_3$;
- classical Keller--Galois rigidity is represented by the explicit
  theorem-target proposition `ComplexKellerGaloisRigidity`; it is neither
  installed as an axiom nor proved in Lean;
- for $F:\mathbb A^3_{\mathbb C}\to\mathbb A^3_{\mathbb C}$, the theorem
  `complexThreeCubicS3Collision` takes the Keller condition and the
  nonnormal cubic branch as explicit hypotheses, constructs the residual
  normal-closure identification, and packages the generic decomposition
  $K\otimes_BC_F\simeq L\times N$, the identification
  $\operatorname{Gal}(N/K)\simeq S_3$,
  `IsComplexThreeJacobianCounterexample F`, nonemptiness of
  the off-diagonal collision scheme, and strict containment
  $I_R(F)\subsetneq I_\Delta$;
- from the clopen-projector datum, the scheme coproduct decomposition
  $\mathrm{Spec}(S/I_R)\cong\mathrm{Spec}(S/I_\Delta)\sqcup R_F^\circ$;
- emptiness of $R_F^\circ$, vanishing of the obstruction ideal, and
  equality $I_R=I_\Delta$ are equivalent;
- assuming the explicit Ax–Grothendieck interface, the standard planar
  Jacobian conjecture is equivalent to `PlanarVanishing`.

The definitions are generic in the coefficient ring, source variables, and
output coordinates.  The planar specialization uses
`R := ℂ` and `Fin 2`.

</details>

Build the project with:

```bash
lake build
```

## Planar dependency spine

The paper has one divisorial endgame with several exact formulations.
`PlanarRamificationRigidity`, moving-sheet coverage, and boundary separation
are respectively differential, valuation-theoretic, and ideal-theoretic
descriptions of its codimension-one premise.  After that premise is supplied,
purity and finite-étale rigidity give $N=K$, followed by $L=K$, $q_F=0$,
and $I_R(F)=I_\Delta$.  `PlanarBoundaryCoherence` is the equivalent global
boundary/properness formulation.  In Lean, `RamificationRigidityBridge` and
`BoundaryCoherenceBridge` still expose the corresponding unformalized
geometric implications.  These additional finiteness conditions do not
follow from the fact that the normalization rings are already finite over
the polynomial image ring.

The canonical modules are:

| Stage | Main module | Role |
|---|---|---|
| automorphism criterion | `General.Automorphism.Criteria`, `.Statements`, `.Equivalences` | dimension-independent obstruction detection, conjectural statements, and their equivalences |
| planar map | `Planar.Basic` | polynomials, Jacobian determinant, Keller condition |
| vanishing target | `Planar.Statements.Vanishing`, `Planar.Equivalences.Vanishing` | planar obstruction vanishing and its collision-ideal formulation |
| finite models | `General.Galois.NormalClosure`, `General.Normalization.Polynomial` | dimension-independent $K\subseteq L\subseteq N$ and $Z\to\overline X\to Y$ |
| planar notation | `Planar.Normalization` | thin $n=2,\ k=\mathbb C$ specialization |
| inertia | `General.Galois.ValuationInertia` | dimension-independent divisorial valuations and inertia kernels |
| conjugate sheets | `General.Galois.DecompositionSheets` | dimension-independent $D_E\backslash G/H$ classes and sheet index |
| Galois collision map pairs | `General.Galois.PolynomialCollisionPair`, `Planar.GaloisCollisionPair` | dimension-independent conjugate polynomial-source pairs and their planar off-diagonal specialization |
| geometric centers | `General.Normalization.Diagram`, `Planar.NormalizationDiagram` | shared centers and the legacy no-hidden-inertia interface |
| ramification realization | `General.Normalization.VisibleRamification` | dimension-independent identification of sheet and geometric ramification indices |
| rigidity statements | `Planar.Rigidity.Statements`, `.Interfaces` | global boundary coherence, divisorial ramification rigidity, and their explicit bridge interfaces |
| canonical boundary API | `Planar.Boundary.Separation` | pulled-back conjugate boundaries and ideals, valuation containment, moving-sheet coverage, and boundary separation |
| Keller local geometry | `General.Keller.Interfaces` | dimension-generic Keller-to-étale and Keller-to-flat interfaces |
| Keller collision model | `General.Keller.CollisionModel` | dimension-generic package of the supplied normalization and local-geometry data |
| generic degree one | `General.Automorphism.GenericDegreeOne` | dimension-generic descent from $L=K$ and flatness to obstruction vanishing |
| literature interfaces | `Planar.External.Interfaces`, `.Assumptions` | branch purity, finite-étale rigidity, Ax–Grothendieck, and their explicit witnesses |
| composition | `Planar.Rigidity.Consequences` | the hypothesis-parametrized divisorial endgame and automorphism theorems |
| secant projector | `Planar.Secant` | planar construction of $q_F$ from the secant determinant |
| explicit planar input | `Planar.ExplicitSecant`, `Planar.KellerFrame` | canonical telescoping divided differences and the polynomial inverse-Jacobian frame |
| landing candidate | `Planar.Research.SecantFrameDenominator` | nonzero finite-coefficient denominator ideals; uniform trace landing remains open |
| monogenic trace order | `Planar.Research.MonogenicOrder` | thin reuse of Mathlib's monogenic order, power basis, hypersurface presentation, Jacobian element, and conductor |
| finite Tate reconstruction | `Planar.Research.TateReconstruction` | explicit power-basis trace reduction and the monogenic trace-dual membership criterion |
| trace-dual/conductor comparison | `Planar.Research.MonogenicTraceDual` | generic monogenic and overorder identities; concrete normalization specialization remains separate |
| conductor landing API | `Planar.Research.MonogenicLanding` | bounded conductor stage, landing ideal, generic finite-overring collapse, and the conditional pointwise-pole passage to the planar endgame |
| endpoint API | `Planar.Conclusion` | packaged consequences |

`Planar.Secant` is an independent algebraic entry point into the same
off-diagonal factor.  It constructs the secant projector and proves the
colon-ideal criterion described below.

The prospective principal-parts and trace-landing objects are preserved
behind the separate `CollisionIdeals.Planar.Research` umbrella; they are not
imported by the stable API.  The manuscript now isolates two geometric
statements and a proved finite Tate--conductor reduction: a hidden
fixed--moving divisor localizes
`FixedMovingBoundaryPrincipalParts` to the unbounded DVR pole tower, while
the trace dual gives a finite bounded quotient.  The explicit divided-
difference secant and polynomial inverse-Jacobian frame are now formalized,
as is the generic nonzero denominator theorem for a finite coefficient
family.  The research layer proves the finite power-basis Tate
reconstruction formula, identifies the generic trace-integral carrier with
Mathlib's `Submodule.traceDual`, and proves the generic monogenic and
overorder conductor--trace-dual identities.  It also defines the associated
bounded conductor stage and landing ideal, and proves a generic normal
Noetherian finite-overring collapse lemma.  The single new mathematical
theorem still missing from the selected route is uniform trace landing: the
prescribed
secant--frame denominator ideal must be contained in the trace transporter,
equivalently its Jacobian multiple must land in the normalization conductor.
A merely nonzero intersection would only restate boundary separation; the
coefficientwise inclusion is the Keller-specific research target.
The first-jet ideal is the designated current candidate; it is enough more
generally to prove the same inclusion for some finite jet order.  Full ideal
inclusion is choice-free and stronger than the minimum needed conclusion:
one explicitly prescribed nonzero scalar in the candidate ideal with uniform
landing would also finish the endgame.  An unqualified existential scalar,
however, is just the already-equivalent boundary-separation assertion.
The corresponding local-cohomology localization and pointwise DVR pole
test, concrete normalization specialization, common ambient quotient maps,
actual \((g,\sigma g)\) overlap coefficient family, and uniform candidate
containment are not yet formalized.

The manuscript/Lean semantic-parity work is tracked in
[`SEMANTIC-PARITY.md`](SEMANTIC-PARITY.md).  In particular, no older
research or compatibility object is removed until its replacement is proved,
all consumers have migrated, both presentations have matching semantics, and
the Lean and manuscript builds pass.

### The map-specific model

`PlanarKellerCollisionModel F` is the $n=2,\ k=\mathbb C$
abbreviation of the dimension-independent
`PolynomialKellerCollisionModel F`.  It contains:

- the explicit Keller certificate;
- a finite normal-closure field $N/K$;
- the normalization diagram;
- the Keller-to-étale and Keller-to-flat bridges;
- the valuation formula realizing double-coset indices as ramification
  indices.

The generic-degree-one descent from $L=K$, together with the model's
Keller-to-flat bridge, to $\mathrm{Obs}(F)=0$ is proved in
`General.Automorphism.GenericDegreeOne`; it is not stored as opaque data
in the model.

It does **not** contain planar no-hidden-inertia rigidity.  That assertion
is a separate condition, so the local consequence of Keller étaleness and
the global planar rigidity input cannot be conflated.

### From Keller étaleness to the boundary

For a ramified height-one point $E$ of the normal cover and a conjugate
sheet $q\in D_E\backslash G/H$, let

```math
\iota_E(q)
=
[I_E:I_E\cap gHg^{-1}]
```

be the relative inertia index.  The normalization diagram records the
corresponding center $\overline q$ on the intermediate finite model.
The predicate

```text
RamifiedConjugateCentersInBoundaryAt E
```

means

```math
\forall q,\qquad
\iota_E(q)\ne1
\Longrightarrow
\overline q\in\overline X\setminus X.
```

Its family version is

```text
RamifiedConjugateCentersInBoundary.
```

The theorem

```text
ramifiedConjugateCentersInBoundary_of_keller
```

is the exact Keller contribution.  It combines the double-coset visibility
calculation, the valuation realization, and étaleness of the conjugate
affine sheet to place every positive-index center in the deleted boundary.

### The separate planar rigidity assertion

The existence of one complete hidden orbit is

```text
HasHiddenInertiaOrbit :=
  ∃ E,
    (∃ q, 1 < inertiaIndex E q) ∧
    RamifiedConjugateCentersInBoundaryAt E.
```

The planar assertion is its negation:

```text
PlanarNoHiddenInertia := ¬ HasHiddenInertiaOrbit.
```

Thus the logical step is short and explicit:

```math
\begin{aligned}
&\texttt{RamifiedConjugateCentersInBoundary},\\
&\texttt{core}(H)=1
  \Longrightarrow \text{a positive-index conjugate sheet exists},\\
&\texttt{PlanarNoHiddenInertia}
\end{aligned}
\quad\Longrightarrow\quad
\text{there are no ramified height-one points.}
```

In Lean this is

```text
M.diagram.noCodimensionOneRamification.
```

The canonical boundary API also exposes the sharper
`PlanarMovingSheetCoverage` and
`PlanarBoundarySeparation` conditions; either eliminates
ramified height-one points directly.  `PlanarNoHiddenInertia` remains as the
older compatible interface.

### Divisorial endgame

The single divisorial endgame and its downstream arrows are:

```math
\begin{array}{c}
\operatorname{PlanarRamificationRigidity}
+\operatorname{RamificationRigidityBridge}\\
\downarrow\\
\text{no codimension-one ramification}\\
\downarrow\quad\text{branch purity}\\
Z\to Y\text{ is finite étale}\\
\downarrow\quad\text{finite-étale rigidity of }\mathbb A^2_{\mathbb C}\\
N=K\\
\downarrow\\
L=K\\
\downarrow\quad\text{generic collision descent using }A/B\text{ flat}\\
R_F^\circ=\varnothing\\
\downarrow\\
\mathrm{Obs}(F)=0\\
\downarrow\\
I_R(F)=I_\Delta.
\end{array}
```

Ax–Grothendieck is used only after this chain, to pass from injectivity to
a polynomial automorphism.

The three standard literature results not presently supplied by mathlib are
isolated once, in `Planar.External.Assumptions`:

```text
branchPurityA2
affinePlaneFiniteEtaleRigidity
axGrothendieckA2
```

They are the only project axioms here.  `BoundaryCoherenceBridge`,
`RamificationRigidityBridge`, and the alternative coverage, separation, and
no-hidden-inertia conditions remain explicit route-specific parameters, not
project axioms.

The principal exported statements are schematically:

```text
planarVanishing_of_boundaryCoherence ...
planarVanishing_of_noCodimensionOneRamification ...
planarVanishing_of_ramificationRigidity ...
planarVanishing_of_movingSheetCoverage ...
planarVanishing_of_boundarySeparation ...

planarVanishing_of
  branchPurity
  finiteEtaleRigidity
  model
  noHiddenInertia :
  obstructionIdeal F = ⊥

planarVanishing_assuming_standardGeometry
  model
  noHiddenInertia :
  obstructionIdeal F = ⊥

planarAutomorphism_assuming_externalLiterature
  model
  noHiddenInertia :
  IsPolynomialAutomorphism F

planarAutomorphism_of_boundaryCoherence ...
```

This is the complete dependency statement.  The fully
parameterized theorem `planarVanishing_of` displays the geometric
interfaces in its signature.  The convenience wrappers use the named
literature axioms internally; those dependencies are visible with
`#print axioms`.

### Secant and off-diagonal formulations

Choose a secant matrix $M_F(x,y)$ satisfying

```math
F(x)-F(y)=M_F(x,y)(x-y)
```

and let $\delta_F=\det M_F$.  For a planar Keller map with
$\det JF=c\in\mathbb C^\times$,

```math
\delta_F I_\Delta\subseteq I_R(F),
\qquad
\delta_F\equiv c\pmod {I_\Delta}.
```

In the collision ring $C_F=S/I_R(F)$, this produces the idempotent

```math
q_F=1-\frac{\overline\delta_F}{c}
```

with

```math
\mathrm{Obs}(F)=C_Fq_F.
```

The complementary ideal in the polynomial ring is canonical:

```math
I_{\mathrm{off}}
=I_R:I_\Delta
=I_R+(\delta_F).
```

Consequently,

```math
\boxed{
\mathrm{Obs}(F)=0
\Longleftrightarrow
I_R(F)=I_\Delta
\Longleftrightarrow
I_R+(\delta_F)=S
\Longleftrightarrow
R_F^\circ=\varnothing.
}
```

The secant construction identifies the endpoint $q_F=0$ with disappearance
of the off-diagonal factor.  The single divisorial endgame reaches that
endpoint after codimension-one unramifiedness; boundary coherence is the
equivalent global-boundary formulation.

The manuscript also proves the classical normal/Galois marked-extension
case by boundary-divisor rigidity.  It follows that generic degree two is
impossible for a nonautomorphic planar Keller map; any unresolved planar
case has nonnormal function-field extension of degree at least three.  This
divisor argument is not yet formalized in Lean.

### Public planar modules

`CollisionIdeals.Planar` exports the local `Statements`, `Equivalences`,
`Rigidity`, and `Boundary` umbrellas alongside the legacy
no-hidden-inertia API.

Import `CollisionIdeals.Planar.Research` explicitly for the prospective
principal-parts, conjugate-secant, and completed tame-ramification modules.

## Cubic $S_3$ contrast

The intended comparison is:

```math
\begin{array}{c|c}
\text{planar ramification-elimination criterion} &
\mathrm{Keller}(F)+\text{normalization model}
+\text{an explicit ramification-elimination hypothesis}
\Longrightarrow\mathrm{Obs}(F)=0
\\[2mm]
\text{separable non-Galois cubic class} &
\mathrm{Obs}(F)\neq0
\quad\text{under the cubic residual/Galois conditions.}
\end{array}
```

The cubic class is the intended dimension-three case study, but the
$S_3$ mechanism comes from the degree-three field extension, not from
ambient dimension alone.

For such a map, strict containment

```math
I_R\subsetneq I_\Delta
```

is equivalent to

```math
\ker(\bar\mu_F)\neq0,
\qquad
C_F^\circ\neq0.
```

Generically, suppose the associated function-field extension $L/K$ is
separable, cubic, and non-Galois, with normal closure $N/K$.  Then, as
$L$-algebras,

```math
L\otimes_KL\cong L\times N,
```

where the first factor is the diagonal and
$\mathrm{Gal}(N/K)\cong S_3$.  Under the chosen power-basis presentation,
the canonical diagonal factor corresponds to the chosen primitive root;
the residual generic factor supplies a second distinct root, and those two
roots determine the third.  Thus the residual factor is
the normal closure $N/K$, whose Galois group is $S_3$.  The formal theorem
requires that the marked
embedding in `NormalClosureData` agree with the $L$-algebra structure
used for this residual factor.  It identifies $N$ as the second factor at
generic base change; together with the generic product--annihilator lemma,
this identifies $N$ with the intrinsic residual quotient.  It does not
identify $K\otimes_B C_F^\circ$ with $N$; that would require the missing
localization--colon comparison.
The nonzero generic kernel nevertheless descends to the affine
obstruction and records the failure of

```math
F(u)=F(v)\Longrightarrow u=v.
```

The dimension-three specialization is organized under `ComplexThree.Cubic`:
`FunctionField`, `GaloisGroup`, `Branch`, `S3Collision`, and `Main`.

This is a conditional cubic-extension statement.  It is neither a
universal assertion that every three-dimensional off-diagonal collision locus has
$S_3$-monodromy nor, without a separately verified Keller condition, a
counterexample to the three-dimensional Jacobian conjecture.

## License

The Lean source and other software in this repository are available under
the [MIT License](LICENSE).  The manuscript PDF
[`Collision Geometry and the Jacobian Conjecture.pdf`](Collision%20Geometry%20and%20the%20Jacobian%20Conjecture.pdf) and other non-code material
in [`paper/`](paper/) are available under [CC BY 4.0](paper/LICENSE).
