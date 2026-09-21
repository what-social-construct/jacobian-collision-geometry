# Primary proof spine: planar vanishing

## Endpoint and notation

For a planar Keller map \(F=(P,Q)\), the endpoint is
\(\operatorname{Obs}(F)=0\), not vanishing of the diagonal ideal itself.
Use the existing declarations:

- `PlanarVanishing` in [Statements/Vanishing.lean](../../Statements/Vanishing.lean).
- `planarVanishing_iff_forall_collisionIdeal_eq_diagonalIdeal` in
  [Equivalences/Vanishing.lean](../../Equivalences/Vanishing.lean): the same goal
  is \(I_R(F)=I_\Delta\).
- `planarJacobianConjecture_iff_planarVanishing` in
  [Equivalences/JacobianConjecture.lean](../../Equivalences/JacobianConjecture.lean):
  the equivalence with polynomial invertibility takes Ax--Grothendieck explicitly.

Write \(A=\mathbb C[x,y]\), \(B=\mathbb C[P,Q]\),
\(K=\operatorname{Frac}(B)\), \(L=\operatorname{Frac}(A)\),
\(N\) for the marked normal closure of \(L/K\), and \(T\) for the integral
closure of \(B\) in \(N\). These are the shared objects, not new planar copies.

## Current finding: exact characterizations

Identify the rings with their images in the marked normal closure. The
internally proved source-intersection theorem gives

\[
A\cap K=B,\qquad E^G\cap A=B.
\]

[ConjugateInvariantCriterion.lean](../../../General/Keller/ConjugateInvariantCriterion.lean)
packages the resulting boundary characterization:

\[
E^G\subseteq A\quad\Longleftrightarrow\quad E^G=B
\quad\Longleftrightarrow\quad\mathfrak b_F=B
\quad\Longleftrightarrow\quad U_F=\operatorname{Spec}B.
\]

Lean uses source-image membership and surjectivity of the existing base
map rather than literal equality of differently presented rings. This
criterion uses Keller and the existing separable normal-closure data,
not characteristic zero, purity, or Keller--Galois rigidity. It asserts
no universal source regularity or empty boundary. The conormal test
below is an equivalent alternative in characteristic zero.

The separate coordinate-descent characterization identifies normality
of \(L/K\), after which the explicit Keller--Galois input gives
automorphy and \(\operatorname{Obs}(F)=0\). The empty-boundary endpoint
instead uses source finiteness and its explicit geometric inputs.
The boundary ideal \(\mathfrak b_F\subset B\) is not the obstruction
ideal \(\operatorname{Obs}(F)\subset C_F\).

[BoundaryCriterion.lean](BoundaryCriterion.lean) packages the exact planar
equivalence \(\operatorname{Obs}(F)=0\iff\mathfrak b_F=B\), and its
source-regularity and conormal corollaries. Only `BranchPurityA2` and
`AffinePlaneFiniteEtaleRigidity` are passed as geometric inputs, in the
boundary-to-obstruction direction. The shared reverse bridge in
[ConjugateInvariantObstruction.lean](../../../General/Keller/ConjugateInvariantObstruction.lean)
evaluates \(I_R=I_\Delta\) at every Galois collision pair. The resulting
coordinate equalities put the all-conjugate algebra inside the marked
source, so the existing source-regularity criterion gives empty boundary.
This uses no Ax--Grothendieck or Keller--Galois rigidity. The first,
source-regularity step needs neither Keller nor separability; those
hypotheses enter only when applying the actual boundary criterion.

These are the findings to present. The historical attempts and their
negative controls below remain available, while the finite derivative
lattice is a [bench proposal](OBJECT-BENCH.md#finite-derivative-lattice-proposal-2026-09-20),
not a claimed next step proving full \(JC(2)\).

## Precise Galois-descent characterization

The complementary marked-closure criterion is now explicit:

\[
\operatorname{Obs}(F)=0\quad\Longleftrightarrow\quad L/K\text{ normal}
\quad\Longleftrightarrow\quad N=\iota(L)
\quad\Longleftrightarrow\quad H=1.
\]

`planarObstructionIdeal_eq_bot_iff_normal` and
`planarObstructionIdeal_eq_bot_iff_normalClosureEmbedding_surjective`
package the planar equivalences with only Keller--Galois rigidity passed
explicitly, from normality to vanishing. The other direction reuses the
direct coordinate equalities in
[CollisionVanishing.lean](../../../General/Galois/CollisionVanishing.lean),
with no Ax--Grothendieck input. The shared
`NormalClosureData.normal_iff_embedding_surjective` and
`normal_iff_intermediateFixingSubgroup_eq_bot` compare the actual marked
closure and its fixing subgroup (the subgroup theorem uses a perfect base).
The reverse planar characterization does not add an input to the focused
degree-two exclusion. It does not assert that the marked field fills its
normal closure for every Keller map.

Let \(\iota:L\hookrightarrow N\) be the existing marked embedding. The
coordinate-descent condition is

\[
\forall g\in\operatorname{Gal}(N/K),\qquad
g(\iota(x)),\ g(\iota(y))\in\iota(L).
\]

[GaloisDescent.lean](GaloisDescent.lean) names the universal complex-planar
statement `CollisionIdeals.Planar.PlanarGaloisDescent`, using the canonical
normal closure constructed from the Keller condition. No choice of a
separate model, generic-degree restriction, or normality of \(L/K\) is
assumed in its definition.

The shared bridges in
[General/Galois/Descent.lean](../../../General/Galois/Descent.lean) and
[General/Galois/PolynomialDescent.lean](../../../General/Galois/PolynomialDescent.lean)
give the chain

```text
conjugate coordinates descend to the marked L     [condition]
    <-> L/K is normal                            [coordinate-generation bridge]
    -> F is a polynomial automorphism            [Keller--Galois rigidity input]
    -> Obs(F) = 0                                [existing collision API]
```

The normality equivalence and the two conditional endpoints are formalized
as `planarGaloisDescent_iff_forall_normal`,
`planarJacobianConjecture_of_galoisDescent`, and
`planarVanishing_of_galoisDescent`. This route needs neither an
Ax--Grothendieck input nor the ramification route's purity input.

The universal assertion of descent remains open. Constructing the normal closure
proves normality of \(N/K\), not of \(L/K\). The target concerns rational
membership in the original field, not polynomial or valuation-ring
regularity. With the accepted rigidity input, proving it for every complex
planar Keller map would settle full \(JC(2)\); this is not a proved weaker
compatibility lemma. The earlier ramification and pole routes remain
separate approaches to the same vanishing endpoint.

The first attempt at a contradiction now has a concrete field-theoretic
witness. If descent fails, a conjugate coordinate \(z=g(\iota(X_i))\)
lies outside \(\iota(L)\). The fixed-field theorem supplies
\(h\in H=\operatorname{Gal}(N/\iota(L))\) with \(h(z)\ne z\).
This is packaged in `NormalClosureData.exists_fixingSubgroup_move_of_not_mem`
and `polynomialSource_exists_moved_conjugate_coordinate_of_not_normal`.
The existing Galois collision pair \((g,hg)\) is therefore off diagonal,
and its planar secant determinant evaluates to zero.

That zero is not a contradiction: \(h\in H\) fixes the original field,
not the conjugate sheet, and it gives no residue agreement or inertia
condition. The local rigidity theorem would exclude the pair if both
tuples could be realized in a local ring with identical residues, compatibly
with their distinct generic values. The common-center test is now sharper:
the two coordinate differences generate the unit ideal in any domain
containing both tuples as a collision pair. No prime in that simultaneous
regularity domain can supply the required center. This follows from the
existing diagonal/off-diagonal comaximality, not a new vanishing theorem.
Nor does preservation of each sheet by the extended Keller frame imply
descent. The precise tests are recorded in the
[descent audit](OBJECT-BENCH.md#descent-witness-and-frame-audit-2026-09-19).

Adjoining all conjugate source rings does not repair the problem. The
[common-center audit](OBJECT-BENCH.md#common-center-and-all-conjugate-ring-test-2026-09-19)
identifies a possible deleted base divisor: the resulting ring's
\(H\)-invariants have the form \(A[1/d]\), with \(0\ne d\in B\).
The underlying algebra \(E\) is now constructed in
[ConjugateAlgebra.lean](../../../General/Galois/ConjugateAlgebra.lean),
with conjugate-polynomial membership, Galois stability, and finite type.
The \(G\)-invariant target open is now constructed in
[ConjugateInvariantOpen.lean](../../../General/Keller/ConjugateInvariantOpen.lean).
The principal localization presentation and the \(H\)-invariant comparison
above are not yet packaged in Lean. Equality with \(A\), or a uniform
denominator bound forcing that equality, remains unproved. Thus the proposed
shortcut returns to the global boundary gap;
it does not bypass it through Galois symmetry or prime selection.

### Reduced-boundary invariant

For the all-conjugate open \(U=D(d)\) in that mathematical audit, retain
the canonical ideal \(\mathfrak b=I(\operatorname{Spec}B\setminus U)
=\sqrt{(d)}=(s)\), with \(s\ne0\) squarefree. It is independent of
the equation chosen for the same open. The shared
[simple-pole criterion](../../../General/Normalization/SimplePole.lean)
and base transversality give

\[
\partial_P(s^{-1}B),\partial_Q(s^{-1}B)\subseteq s^{-1}B
\quad\Longleftrightarrow\quad
\partial_Ps,\partial_Qs\in(s)
\quad\Longleftrightarrow\quad s\in B^\times.
\]

Keep this target explicitly finite: \(s^{-1}B\) is a free rank-one
\(B\)-module, and Leibniz reduces its preservation to the two tests on
\(1/s\). Equivalently, compare it with the module generated by
\(1/s,D_P(1/s),D_Q(1/s)\); no higher-jet sequence or whole pole tower
is part of this target. Finite means finitely generated over \(B\), not
finite-dimensional over \(\mathbb C\). The finite defect is
\((\partial_Ps\bmod s,\partial_Qs\bmod s)\).
The actual all-conjugate open and its canonical reduced boundary ideal are
now constructed. The characteristic-zero conormal criterion is applied to
that same ideal: all target-coordinate components vanish iff the open is
the whole target. This intrinsic criterion does not need a principal
presentation. The latter remains unformalized for the one-generator
simple-pole formulation. The Keller-specific claim that the components
vanish remains open. In particular,
neither preservation of \(B[1/s]\) nor adjoining first jets to the
secant coefficient lattice supplies simple-pole preservation. The
[bench test](OBJECT-BENCH.md#reduced-boundary-and-simple-pole-test-2026-09-19)
records an explicit proper-open example where those jets increase the
required denominator. No new universal theorem-target predicate is added.

The conditional finite-boundary endpoint is now packaged in
[FiniteBoundary.lean](FiniteBoundary.lean):

```text
target derivatives of finite boundary generators lie in the boundary ideal [open]
    -> all actual conormal components vanish
    -> U_F = Spec B, hence the base-to-fixed-algebra map is bijective
    -> E is finite over B, hence the embedded polynomial source A is finite
    -> the source fills its intermediate normalization
    -> no hidden inertia, hence no height-one ramification
    -> Obs(F) = 0                         [purity + finite-etale rigidity inputs]
```

The finite tests use a generating set for the same \(\mathfrak b_F\),
not a new denominator ideal or a chosen principal equation. The target
boundary and intermediate-normalization boundary are not identified;
source finiteness connects their emptiness by a proved implication.
`BranchPurityA2` and `AffinePlaneFiniteEtaleRigidity` remain explicit theorem
arguments. The new endpoint imports no custom literature axioms. These
are the existing full-planar research inputs, not the single
Keller--Galois rigidity input of the separate degree-two theorem.

The source-specific characterization also uses
[SourceIntersection.lean](../../../General/Keller/SourceIntersection.lean), which
proves \(A\cap K=B\) from visible source divisors and factorization.
[ConjugateInvariantSource.lean](../../../General/Keller/ConjugateInvariantSource.lean)
applies it to the existing fixed algebra: a fixed element regular on the
marked source already belongs to \(B\). The comparison does not show
that every fixed element is source-regular. Source unit reflection or a
visible center on each separate sheet cannot supply that assertion for
their joint algebra. The new criterion packages that assertion as
equivalent to boundary emptiness, rather than presuming a proof of it.

## Ramification reduction

For the canonical finite normalized cover constructed from the Keller
condition, the conditional endgame is:

```text
Keller condition + missing planar argument
    -> no height-one ramification in Spec(T) -> Spec(B)
    -> finite étale normalization                 [purity input]
    -> N = K, hence L = K                         [finite-étale rigidity input]
    -> Obs(F) = 0                                [Keller flatness + collision API]
```

The direct endpoint is now in [Ramification.lean](Ramification.lean):

- `planarVanishing_of_normalizedCover_noCodimensionOneRamification` takes the
  finite normalized cover, Keller hypothesis, and no-ramification premise.
- `planarVanishing_of_canonicalNoCodimensionOneRamification` constructs that
  cover internally and reduces the existing universal `PlanarVanishing`
  target to no height-one ramification for every planar Keller map.

Both take `BranchPurityA2` and `AffinePlaneFiniteEtaleRigidity` explicitly.
Neither imports the custom literature axioms nor requires the larger
collision model's conjugate centers or inertia-index realization. The older
model-based endpoint in
[Rigidity/Consequences.lean](../../Rigidity/Consequences.lean) remains available
to the boundary/conjugate-sheet route; it is not a dependency of this smaller
spine.

The missing mathematical step is deriving no height-one ramification from the
planar Keller hypothesis. Constructing the model or proving local comparison
lemmas does not establish that step.

## Local formulation of the missing step

For every height-one prime \(\mathfrak q\) of \(T\), with
\(\mathfrak p=\mathfrak q\cap B\), aim to prove

\[
e(\mathfrak q/\mathfrak p)=1.
\]

The existing target is `NoCodimensionOneRamification` in
[NormalizationDiagram.lean](../../NormalizationDiagram.lean), defined using
`Algebra.IsUnramifiedAt`, not a newly introduced index-one predicate.
The characteristic-zero residue-field criterion in
[General/Galois/RamificationIndex.lean](../../../General/Galois/RamificationIndex.lean)
relates unramifiedness, index one, and trivial inertia after the appropriate
Dedekind localization. Use the actual localized rings and the existing
`localRamificationIndex` comparisons; do not use global ideal powers in the
two-dimensional normalization.

Here the index is for the **full normal closure over the base**. Index one at
a visible center on one intermediate conjugate sheet is not the same result:
the sheet index is \([I:I\cap gHg^{-1}]\), which can be one while \(I\ne1\).
The primes in question lie over the affine base, not over a chosen
compactification's divisors at infinity.

Equivalently, the local differential target is
\((\Omega_{T/B})_{\mathfrak q}=0\) at every height-one prime. The existing
`PlanarRamificationRigidity` asks for finite length of \(\Omega_{T/B}\), a
sufficient criterion rather than a replacement goal. Its
`RamificationRigidityBridge` remains an explicit input in
[Rigidity/Interfaces.lean](../../Rigidity/Interfaces.lean).

## Original-extension pole route

One can instead work in \(L\), before forming its normal closure. Put
\(S=\operatorname{IntCl}_B(L)\). The constructed source open immersion
comes from \(S\subseteq A\); \(S\) is finite over \(B\). It would suffice
to prove

\[
x,y\in S_{\mathfrak p}\quad
\text{for every height-one prime }\mathfrak p\subset S.
\]

The normal-Noetherian height-one intersection theorem then gives
\(A=S\), so the original map is finite. Keller étaleness and the stated
finite-étale rigidity input finish. This is a mathematical reduction using
[Stacks, Tag 031T](https://stacks.math.columbia.edu/tag/031T), not a new
Lean endpoint with the regularity hypothesis discharged.

The global source-divisor theorem gives one visible prime over each base
divisor, not regularity at every prime of \(S\) above it. The
[original-extension test](OBJECT-BENCH.md#original-extension-pole-test-2026-09-19)
excludes genuinely monomial pole valuations in polynomial source
coordinates. General divisorial valuations can have cancellation between
terms of negative value; no reduction of all boundary valuations to the
monomial case has been proved.

## Direct local collision exclusion

[LocalCollision.lean](LocalCollision.lean) proves that two planar Keller
collision maps into any commutative local \(\mathbb C\)-algebra which agree
on residue coordinates are equal. The evaluated secant determinant reduces
to the nonzero constant Jacobian, hence is a unit; it annihilates every
coordinate difference. No domain hypothesis or ramification index is used.

[InertiaCoordinates.lean](InertiaCoordinates.lean) applies this directly to
the actual valuation inertia group of the marked normal closure. With the
ground-field constants included compatibly in a valuation ring \(V\),

\[
\sigma\in I_V,\quad \sigma gH\ne gH
\quad\Longrightarrow\quad
\exists i\in\{1,2\}:\ g(x_i)\notin V.
\]

Indeed, if both coordinates belonged to \(V\), inertia would provide a
second local collision map with the same residues, contradicting movement
of the sheet. This argument needs no `ConjugateRamificationRealization`.
At a divisorial valuation, nonmembership means a coordinate pole.

The missing step on this route is to rule out that pole: it would suffice
to produce, at each nontrivial-inertia divisor, a moved sheet whose two
coordinates are regular. The existing visible sheet is inertia-fixed and
does not supply such a witness. Taking closure does not supply it either:
\(\operatorname{IntCl}_B(gL)\subseteq gA\), not the reverse inclusion.
Extending the residual projector alone is insufficient; the collision
evaluation must extend on the source-coordinate generators. See the
[closure and pole-order audit](OBJECT-BENCH.md#local-collision-and-closure-audit-2026-09-19).

## First local step: a regular transverse derivation

[General/Normalization/DerivationCriterion.lean](../../../General/Normalization/DerivationCriterion.lean)
now proves a concrete sufficient condition for local index one. In
\(T_{\mathfrak q}\), it takes

\[
d:T_{\mathfrak q}\longrightarrow T_{\mathfrak q},\qquad
b\in\mathfrak q\cap B,\qquad d(b)\in T_{\mathfrak q}^{\times},
\]

where \(d\) is a derivation, and concludes
`localRamificationIndex (R := B) q = 1`. Its proof uses
\(d(\mathfrak m^2)\subseteq\mathfrak m\): the extended base ideal cannot lie
in \(\mathfrak m^2\) if it contains an element with unit derivative. No
uniformizer choice or principal-generator hypothesis is needed.

The generic criterion, local specialization, and composed unramifiedness
criterion passed targeted Lean builds. The index-one/unramifiedness comparison
is in [General/Normalization/LocalUnramified.lean](../../../General/Normalization/LocalUnramified.lean).
They do **not** assert that an extended Keller frame preserves
\(T_{\mathfrak q}\). That is the next hypothesis to investigate at missing
boundary points; regularity on the visible polynomial sheets is not enough.
The base transversality part is now proved in
[General/Normalization/BaseTransversality.lean](../../../General/Normalization/BaseTransversality.lean):
every nonzero proper ideal in a characteristic-zero polynomial ring contains
an element whose derivative in some coordinate lies outside the ideal. The
proof chooses a nonzero element of minimal total degree; it requires neither
a principal generator nor a height-one hypothesis. For a base divisor, use
the polynomial presentation of \(B=\mathbb C[P,Q]\). The coordinate selected
by this result can depend on the divisor: regularity of an arbitrary tangent
frame would not suffice.

[BaseFrame.lean](BaseFrame.lean) connects the target partials to the existing
Keller frames, both on the source and on each conjugate sheet in \(N\):
\(D_P(b(P,Q))=(\partial_u b)(P,Q)\), and similarly for \(D_Q\) and
\(\partial_v\). In Lean these use `coordinateAlgHom F`.
The partial is taken **before** target evaluation; it is not the ordinary
source partial of \(b(P,Q)\). Transporting the base-prime witness and the
derivative to the actual localization remains specialization work, separate
from the missing regularity proof.

This is an alternative local route, not an assumption that the trace-landing
route has already closed. The remaining mathematical input is regularity of
the selected transverse frame in the actual boundary localization. See the
[denominator test on the bench](OBJECT-BENCH.md#concrete-boundary-regularity-test):
the denominator must avoid \(\mathfrak q\), not just be nonzero.

## Testing the secant comparison

The finite generator criterion is in [FrameDenominator.lean](FrameDenominator.lean):
if \(D(B)\subseteq T\), a multiplier clears the derivatives of a finite
\(B\)-module generating family of \(T\) if and only if it clears all of
\(D(T)\). This uses Leibniz, not \(B\)-linearity. It gives a nonzero
denominator, not one outside a specified prime.

The existing secant family is a different family.
[SecantReduction.lean](SecantReduction.lean) removes its redundant adjugate
entries and jets without changing the lattice or denominator. The matrix
entries and both first-derivative families are retained; the adjugate may
still be useful for other determinant/kernel identities.

The [quadratic diagnostic on the bench](OBJECT-BENCH.md#secant-comparison-audit-2026-09-18)
shows that secant coefficients can all be regular while a transverse
normalization derivative has a pole. It is not a Keller counterexample,
but rules out the proposed comparison based on generic secant identities
and étaleness on retained sheets alone.

[ConductorComparison.lean](ConductorComparison.lean) supplies a precise
alternative comparison with the existing order \(U=B[\alpha]\):
\(D(U)\subseteq\Lambda\) implies \((U:T)D(T)\subseteq\Lambda\).
Control of the base derivatives and \(D(\alpha)\) suffices for its premise.
The local refinement in [ConductorLocalization.lean](ConductorLocalization.lean)
proves that a conductor element outside \(\mathfrak q\) makes control of
\(D(\alpha)\) equivalent to control of all \(D(T)\) in a
\(T_{\mathfrak q}\)-submodule. This does not construct the adapted generator.
Conductor avoidance can be arranged by a local monogenic construction in
this characteristic-zero finite-normalization setting; it should not be
listed as an independent Keller-specific conjecture. The construction is
outlined on the bench and is not yet packaged in Lean.

[GeneratorDerivative.lean](GeneratorDerivative.lean) isolates the remaining
test using the existing monogenic Jacobian. Write
\(f(X)=\sum_i a_iX^i=\operatorname{minpoly}_B(\alpha)\),
\(J=f'(\alpha)\), and \(\nu_D=\sum_i D(a_i)\alpha^i\). It proves

\[
J D(\alpha)=-\nu_D,\qquad
D(\alpha)\in\Lambda\ \Longleftrightarrow\ \nu_D\in J\Lambda
\quad(J\ne0).
\]

Base derivative control gives \(\nu_D\in\Lambda\), not membership in
\(J\Lambda\). In the local ring the missing test is
\(\nu_D\in JT_{\mathfrak q}\). For an adapted generator and a transverse
frame this is an exact reformulation of the ramification issue, not an
independent proof of its vanishing. Both comparisons remain bench tests;
neither is a new mandatory hypothesis of `PlanarVanishing`.

## Global polynomial input: one visible divisor over every base divisor

[General/Keller/DivisorVisibility.lean](../../../General/Keller/DivisorVisibility.lean)
uses the actual polynomial source, not merely a smooth affine open. Its
unit-reflection lemma applies to any subalgebra of a polynomial ring over a
reduced coefficient ring. For a Keller map, it proves

\[
\forall\mathfrak p\in\operatorname{Spec}^{(1)}B,\quad
\exists\mathfrak r\in\operatorname{Spec}^{(1)}A:\quad
\mathfrak r\cap B=\mathfrak p,
\qquad B\longrightarrow A\text{ is unramified at }\mathfrak r.
\]

The proof transfers unique factorization to the coordinate-image base,
chooses a prime generator of \(\mathfrak p\), and factors its nonunit image
in \(A\). Flat going-down identifies the contraction of a source factor;
Keller étaleness gives its unramifiedness. This dimension-independent result
requires no extra visibility hypothesis and no generic-degree restriction.

This is **one visible source divisor**, not every normal-closure divisor.
The source theorem concludes with a prime of `SourceRing`.
[VisibleConjugateCenter.lean](../../../General/Normalization/VisibleConjugateCenter.lean)
now transports that prime into the marked normalization: lying-over and
Galois transitivity prove that the intermediate prime is an actual
conjugate center of any chosen full-normalization prime over the base
prime. This requires no supplied visibility or center-surjectivity premise.

For a supplied normalization diagram and its existing
`ConjugateRamificationRealization`, the checked corollary gives an
inertia-fixed sheet at every ramified divisor. The realization remains
explicit; this check does not verify the older unconditional model/index
assembly. In group terms the conclusion is \(I\le gHg^{-1}\) for some
sheet, not \(I=1\). In the nonnormal case, inertia can fix one sheet while
moving others. The missing step must control those other sheets; unit
reflection alone does not establish \(\nu_D\in JT_{\mathfrak q}\).

[LocalizedJacobianDiagnostic.lean](LocalizedJacobianDiagnostic.lean)
checks a sharper negative test than the nonconstant-Jacobian quadratic
example: the rational map \((t,u)\mapsto(t^2,u/(2t))\) has determinant one
on \(t\ne0\), but its target derivative of \(t\) is not polynomial in
the normalization coordinates \((t,z)\). The diagnostic is not a global
polynomial Keller map; it misses the whole base divisor \(s=0\). Thus it
fails exactly the new visibility conclusion. The bench distinguishes the
Lean-checked identities/non-polynomiality from the local geometric
interpretation.

The cubic variant in the same file checks determinant one and a surviving
preimage for **every complex target point**, while its target derivative
still fails to preserve the polynomial normalization ring. Thus the new
visibility conclusion by itself does not repair the inference. The
[mixed-secant audit](OBJECT-BENCH.md#visible--hidden-secant-test-2026-09-19)
tests the actual polynomial identities separately: their singular matrix
relation does not bound hidden derivatives. No enlarged finite coefficient
family or new landing assumption is promoted into the spine from this test.

## Boundary/trace route into the spine

This is a candidate proof of the missing planar step, not an additional
condition on the final `PlanarVanishing` statement:

```text
uniform secant-frame trace landing                [OPEN]
    -> PlanarBoundarySeparation                   [proved conditional implication]
    -> NoCodimensionOneRamification               [for the supplied model]
    -> Obs(F) = 0                                [endgame above]
```

The actual boundary-section ring \(R_C\), secant-frame denominator ideal,
and pole witness are constructed. In
[SecantFrameTraceLanding.lean](../SecantFrameTraceLanding.lean),
`boundarySeparation_of_secantFrameTraceLanding` requires landing for every
nontrivial prime-order subgroup. `boundarySectionSubalgebra_eq_bot_of_secantFrameTraceLanding`
also shows that landing already forces \(R_C=T\): here `⊥` denotes the base
\(T\)-subalgebra, not the zero ring.

What is not proved is a uniform trace bound for **all** sections of \(R_C\).
Clearing finitely many secant coefficients is not that bound. The
[object bench](OBJECT-BENCH.md) records the constructions and negative tests.
This trace endgame needs a nonzero multiplier, not one outside the boundary
prime. The pole witness already defeats every nonzero multiplier. Its
outside-prime numerator is constructed in `HeightOneBoundaryPole`; that
choice must not be confused with a regularity denominator for the frame.

## Earlier work order for the local-ramification route

This is retained as a research plan, not the current manuscript proof
spine. The established findings are the characterizations above; the
following steps would pursue the stronger universal vanishing target.

1. Test whether the global polynomial Keller condition supplies
   \(\nu_D\in JT_{\mathfrak q}\) for the adapted integral generator and
   the transverse frame, or rules out the coordinate pole forced by the
   direct inertia argument. The local collision contradiction is proved
   without an index realization; source-coordinate regularity is not.
   The [polynomial pole-order test](OBJECT-BENCH.md#global-polynomial-pole-order-test-2026-09-19-not-formalized)
   yields \(e\le(d-2)M\), which allows poles when total polynomial degree
   \(d\ge3\); iterating the same derivative does not strengthen it.
   The coefficientwise derivative identity is proved;
   the divisibility is not. The source-visibility theorem now supplies an
   unramified source divisor over every base divisor, but does not control
   the remaining normal-closure sheets. The weaker generic secant comparison fails the
   quadratic diagnostic even with unit conductor. Keep the local adapted
   generator construction and transport to the actual localization separate
   from this substantive premise. More equivalent criteria alone do not
   discharge it.
2. Keep the larger conjugate-sheet model/index assembly on the bench for the
   boundary route. Its ramification-to-nontrivial-inertia leaves, local-index
   wrappers, and complete characteristic-zero model assembly are verified.
   They are not prerequisites of the smaller direct conditional endgame.
   Boundary separation/trace landing remains an
   alternative route to the same no-ramification premise.
3. Once one route closes, assemble `PlanarVanishing`, run the complete build
   and axiom audit, and align Paper 2 with the verified argument. Do not require
   every bench route to succeed or import them all into the final proof.

Keller--Galois rigidity remains a separate possible finish if one proves
\(L/K\) normal. The normality of \(N/K\) does not supply that premise.

## Checked first step (2026-09-18)

Targeted builds passed for `General.Normalization.LocalUnramified`,
`General.Normalization.DerivationCriterion`, and
`Planar.Research.Vanishing.Ramification`. The nine new lemmas were audited:
their only axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Purity, finite-etale rigidity, and no ramification are explicit hypotheses in
the planar reduction, not hidden axioms or discharged conclusions.

This is not a full-repository build or a proof of `PlanarVanishing`. The
normalization-specific index wrapper and older conjugate-index/model assembly
remain separate verification work; the direct endpoint above builds without
them.

## Checked base/frame step (2026-09-18)

Targeted builds passed for `General.Normalization.BaseTransversality` and
`Planar.Research.Vanishing.BaseFrame`. All ten new lemmas were audited and use
only `propext`, `Classical.choice`, and `Quot.sound`. No new predicates,
literature assumptions, or `sorry` proofs were introduced.

This discharges the generic base-transversality argument and identifies the
actual Keller-frame action on target polynomials. It does not prove boundary
regularity, prime avoidance for the frame denominator, or `PlanarVanishing`.
No full-repository build is claimed.

## Checked comparison/pruning step (2026-09-18)

Targeted builds passed for `Vanishing.FrameDenominator`,
`Vanishing.SecantReduction`, and `Vanishing.ConductorComparison`, all under
`CollisionIdeals.Planar.Research`. All ten public lemmas were audited and use
only `propext`, `Classical.choice`, and `Quot.sound`; there are no new axioms,
`sorry` proofs, or object definitions. The original secant definitions were
preserved; matrix-only equality is available without breaking their users.

The quadratic secant/conductor diagnostic and the conjugate-source overring
comparison are mathematical audits recorded on the bench, not Lean results.
They explain which weaker inferences fail and which hypotheses a successful
Keller-specific argument must genuinely use. Boundary regularity and planar
vanishing remain open in this development. No full-repository build or
manuscript change was made in this step.

## Checked local-generator test (2026-09-18)

The targeted build for `Vanishing.GeneratorDerivative` also built
`Vanishing.ConductorLocalization` successfully (1842 jobs). All seven new
lemmas were audited and use only `propext`, `Classical.choice`, and
`Quot.sound`. No new definitions, axioms, or `sorry` proofs were added.

This verifies the local conductor cancellation, the differentiated
minimal-polynomial identity, and the exact lattice-membership criterion.
It does not construct the locally adapted generator in Lean or establish
the required Keller-specific numerator divisibility. No full-repository
build, manuscript change, commit, or submission is claimed.

## Checked global visibility step (2026-09-19)

Targeted builds passed for `General.Keller.DivisorVisibility` (2914 jobs)
and `Planar.Research.Vanishing.LocalizedJacobianDiagnostic` (2626 jobs),
under `CollisionIdeals`. All five new public results were audited; their
only axioms are `propext`, `Classical.choice`, and `Quot.sound`. No new
object definitions, axioms, or `sorry` proofs were added. The diagnostic
build reports only simplifier/tactic-style warnings.

The visibility theorem derives a source prime from `IsKeller` rather than
requiring a visibility witness. The diagnostic verifies identities on the
actual rational function field and a failure of polynomial derivative
regularity, not a counterexample to planar vanishing. The local generator
constructor, the marked-normalization transport of source visibility, and
the Keller-specific derivative divisibility are not proved by this step.
No full-repository build or manuscript change is claimed.

## Checked direct local collision step (2026-09-19)

Targeted builds passed cleanly for `Vanishing.LocalCollision` (1576 jobs)
and `Vanishing.InertiaCoordinates` (2600 jobs), under
`CollisionIdeals.Planar.Research`. All three new lemmas passed a joint
axiom audit and use only `propext`, `Classical.choice`, and `Quot.sound`.
No new object definitions, axioms, or `sorry` proofs were introduced.

This proves local collision rigidity and the coordinate-pole consequence
of actual inertia movement without an index realization. It does not
establish boundary regularity or `PlanarVanishing`. The completion and
pole-order calculations remain mathematical audits on the bench. No
full-repository build, manuscript change, commit, or submission was made.

## Checked monomial-support exclusion (2026-09-19)

The targeted build for `General.Keller.MonomialWeights` passed cleanly
(1543 jobs). Both new lemmas passed a joint axiom audit using only
`propext`, `Classical.choice`, and `Quot.sound`. They use the existing
`IsKeller` and `Finsupp.weight`; no new predicates or axioms were added.

The result concerns integer weights on polynomial supports in arbitrary
dimension over any field. The monomial-valuation consequence and the
nonmonomial cancellation diagnostics are mathematical applications recorded
on the bench, not a formal valuation construction. No general height-one
coordinate-regularity theorem or proof of `PlanarVanishing` was obtained.
The research import graph is acyclic; this is not a full-repository build.
No manuscript change, commit, push, or submission was made.

## Checked Galois-descent target (2026-09-19)

Targeted builds passed cleanly for `General.Galois.Descent` (1890 jobs),
`General.Galois.PolynomialDescent` (2520 jobs), and
`Planar.Research.Vanishing.GaloisDescent` (2629 jobs). All eight new
theorems and the `PlanarGaloisDescent` target definition passed a joint
axiom audit using only `propext`, `Classical.choice`, and `Quot.sound`.
No new axioms or `sorry` proofs were introduced.

The shared normality criterion is dimension-independent and does not
require separability. The open universal target is specifically over
the complex plane, using the existing canonical marked closure. Its
vanishing endpoint takes both descent and Keller--Galois rigidity as
explicit hypotheses; neither is proved by defining the target.

The research entry point imports the new route; its local import graph is
acyclic, and all 99 local documentation links checked exist. This is not
a full-repository build. No manuscript change, commit, push, or submission
was made.

## Checked non-descent witness (2026-09-19)

Targeted builds passed cleanly for the updated `General.Galois.Descent`
(1890 jobs) and `General.Galois.PolynomialDescent` (2520 jobs). Both new
witness lemmas passed the axiom audit using only `propext`,
`Classical.choice`, and `Quot.sound`. A temporary integration theorem also
passed: the witness gives a genuinely moved planar collision coordinate
and a zero value of its secant determinant, using the existing collision
pair and secant APIs. It has the same three standard axioms.

No new object definitions, axioms, or `sorry` proofs were introduced. The
frame/nonnormal-cubic diagnostic remains a mathematical audit, not a new
formalized counterexample. Neither a common local realization of the
moving pair nor the universal descent target was proved. This is not a
full-repository build; no manuscript change, commit, push, or submission
was made.

## Checked common-center test (2026-09-19)

A temporary `lake env lean` audit verified that zero secant evaluation
forces the coordinate-difference ideal to be the unit ideal, and that
distinct Keller collision maps into a domain satisfy this premise. Both
lemmas use only `propext`, `Classical.choice`, and `Quot.sound`; the check
passed without warnings or errors. The result is already encoded by the
existing comaximality API, so no repository Lean module or new target was
added or changed in this step.

The all-conjugate-ring quotient calculation and proper-open cubic test
are recorded separately as mathematical audits. They identify a possible
deleted divisor, not a proof that it is empty. The common-center shortcut
does not establish descent or planar vanishing. All 109 local documentation
links checked exist; there was no full-repository build, manuscript edit,
commit, push, or submission.

## Checked finite simple-pole test (2026-09-19)

Targeted builds passed for `General.Normalization.SimplePole` (1386 jobs)
and the updated `Planar.Research.Vanishing.LocalizedJacobianDiagnostic`
(3318 jobs). The five shared criterion lemmas and two new diagnostic
lemmas passed axiom audits using only the standard `propext`,
`Classical.choice`, and `Quot.sound` axioms (the ideal-only lemma does not
need choice). No new definitions, axioms, or `sorry` proofs were added.
The diagnostic build has tactic-style warnings, including a redundant
`ring` following a closing `field_simp`; the shared criterion builds cleanly.

The polynomial criterion requires neither squarefreeness nor a fixed
number of variables. The diagnostic verifies that a target derivative
raises a simple pole and leaves its cyclic module on a proper open source;
it is not a full-plane polynomial Keller example. Exact secant denominator
ideals and the conormal interpretation remain mathematical audits, not
additional Lean claims.

The active boundary target is now explicitly finite: two generator tests
or two remainders modulo the reduced boundary equation, without an entire
pole tower. Actual Keller-specific preservation and the Lean construction
of the all-conjugate base boundary remain open. All 116 local documentation
links checked exist, and the 118-module local import graph checked is
acyclic. This is not a full-repository build; no manuscript change, commit,
push, or submission was made.

## Checked conormal realization and manuscript synchronization (2026-09-19)

The targeted build of `General.Normalization.ConormalDerivation` passed
(2886 jobs). Its adapter definition and four lemmas passed axiom audits
using only `propext`, `Classical.choice`, and `Quot.sound`. Temporary
examples also verified the existing finite-generation instances for
`Ideal.Cotangent` over both the Noetherian base and its quotient. No
duplicate quotient, universal theorem-target predicate, axiom, or `sorry`
was introduced.

Paper II now records the all-conjugate target open, reduced boundary,
finite simple-pole/conormal criterion, and the Galois origin of the secant
relation in a separate research section. Its degree-two theorem is
unchanged. The actual boundary remains uninstantiated in Lean, and no
Keller-specific vanishing or comparison from secants to its conormal
classes is claimed. The semantic-parity table records these distinctions.
No research object was pruned, archived, committed, or pushed in this step.

## All-conjugate algebra and dependency audit (2026-09-19)

`General.Galois.ConjugateAlgebra` now defines the actual
\(E=B[g(\iota(A)):g\in G]\subset N\) as the adjoin of the finite
set of conjugate source coordinates. Conjugate-polynomial membership,
Galois stability in both directions, finite generation, and finite type
are proved. This construction is dimension-independent and needs no
Keller condition beyond the supplied marked finite normal-closure data.
It does not assert that \(E\) is module-finite over \(B\).

The geometric audit of Paper II confirms the selected regular component,
free scheme-theoretic action, invariant affine open, and reduced principal
boundary argument under its stated Keller hypotheses. The finite-submodule
step uses Noetherianity of \(B\); empty boundary then uses classical
finite-etale rigidity of affine space. The actual target open is now
instantiated by the shorter route below, followed by its actual reduced
boundary. The stronger etale/free-action identifications remain separate work.

The construction reuses \(E\) rather than introducing a new boundary-model
hypothesis bundle. The 2026-09-20 checkpoint below shortens the route to the
target open:

1. Construct \(E\), identify its fraction field with \(N\), and construct
   its fixed algebra, over which \(E\) is module-finite (proved).
2. Realize \(E^G\) inside \(K\) with fraction field \(K\) under separability,
   and prove \(E/B\) unramified under Keller (proved).
3. Descend finite type and quasi-finiteness to \(E^G/B\). Use birationality
   and normality of \(B\) to identify its spectrum with an affine target
   open (proved). The selected-etale-component and free-action comparisons are not
   prerequisites for this shorter open-immersion route.
4. Form the radical ideal of the actual complement and specialize the
   existing conormal criterion (proved). Its principal reduced presentation
   remains separate work for the one-generator simple-pole formulation;
   it is not needed for the intrinsic conormal criterion.

These are construction tasks. None proves that the resulting conormal
components vanish; that remains the distinct Keller-specific comparison.

The new [comparison diagnostic](OBJECT-BENCH.md#galois--secant-boundary-comparison-audit-2026-09-19)
shows exactly why Galois descent and secants alone are insufficient on a
proper open source. Even a finite invariant secant expression for \(1/s\)
does not bound its first derivatives. No Keller-specific vanishing is
claimed, and the full polynomial-plane hypothesis must enter any successful
comparison explicitly.

The dependency audit separates this active finite test from the alternative
conductor, trace, and ramification routes. The unchanged elementary lemma
`derivation_mem_ideal_of_mem_sq` was moved to
[DerivationIdeal.lean](../../../General/Normalization/DerivationIdeal.lean),
preserving its name and existing clients. As a result the conormal criterion
has only four local modules in its import closure, down from 24, and no
ramification dependency. No mathematical object, alternative route, or
negative control was deleted. The public planar spine remains isolated.

The accumulated research umbrella requires all of the previously untracked
Lean research modules. Its import changes must be committed together with
those dependencies, not as an incomplete umbrella-only snapshot.

## Integrated research checkpoint (2026-09-19)

The all-conjugate algebra's seven declarations passed their targeted build
and axiom audit. The extracted derivation lemma, simple-pole criterion, and
conormal realization passed targeted builds and a combined nine-declaration
audit; finite-generation instances for the conormal module were checked as
well. These audits use only `propext`, `Classical.choice`, and `Quot.sound`.

Integration exposed elaboration issues in the older divisorial-index route.
The repairs reuse the existing local-base-change algebra instances, scope
the normal-closure base algebra to the actual field rather than a polymorphic
instance that also matches the source field, and remove redundant type
reconstructions. The polynomial wrapper has a local heartbeat allowance;
the theorem statements and mathematical hypotheses are unchanged. The
characteristic-zero diagram and `PolynomialKellerCollisionModel.ofIsKeller`
now compile with the inertia and local-index inputs derived internally.

The combined integration build passed all 3818 jobs:

```sh
lake build CollisionIdeals CollisionIdeals.Planar.Research CollisionIdeals.Palomar.PaperOne.Solution CollisionIdeals.Palomar.PaperTwo.Solution
```

Only the existing local-base-change and diagnostic tactic-style linter
warnings remain. This verifies the public library, the separate research
umbrella, and both solution entry points together; it does not discharge
the open research hypotheses.

A final axiom audit of `integralClosure_localRamificationIndex_eq`,
`polynomialConjugateCenter_localRamificationIndex_eq`, and
`PolynomialKellerCollisionModel.ofIsKeller` passed. Each depends only on
`propext`, `Classical.choice`, and `Quot.sound`; the integration repairs
introduce no new mathematical input.

Paper II was rebuilt and all thirteen rendered pages checked, with no final
LaTeX warnings or layout defects. Paper I and the manuscript archive are
unchanged. The parity queue now distinguishes the verified full
collision-normalization model from the still-uninstantiated invariant-open
boundary. Neither that model nor the finite conormal criterion proves the
Keller-specific vanishing comparison. No submission is made.

## Fraction-field and invariant-ring checkpoint (2026-09-19)

[ConjugateFractionField.lean](../../../General/Galois/ConjugateFractionField.lean)
proves that the existing inclusion \(E\subset N\) makes \(N\) a fraction
field of \(E\). Every conjugate source rational function is a quotient of
conjugate polynomials in \(E\), and these generate the supplied normal
closure. The shared lemma `NormalClosureData.eq_top_of_conjugate_mem` now
serves both this proof and the existing descent theorem. No normality of
\(L/K\), coordinate descent, Keller condition, or separability premise is
introduced.

[ConjugateInvariants.lean](../../../General/Galois/ConjugateInvariants.lean)
restricts the action via Mathlib's `IsInvariantSubring` and reuses
`FixedPoints.subalgebra` for \(E^G\). The fraction-field result makes this
action faithful. Finite-group invariants give integrality over \(E^G\),
and the already-proved finite type over \(B\) gives module-finiteness over
\(E^G\). Neither finiteness over \(B\) nor scheme-theoretic freeness is
inferred. Under the explicit additional assumption that \(N/K\) is
separable, membership in \(E^G\) is equivalent to membership in the embedded
base field \(K\).

At this checkpoint the comparison was elementwise. The 2026-09-20
checkpoint below packages the corresponding \(B\)-subalgebra of \(K\) and
its fraction field, using `Subalgebra.comap` along the marked base-field
embedding, not a new abstract quotient or supplied birationality hypothesis.

The geometric route considered at this checkpoint was to identify \(E\) with the
selected component of the tensor product of conjugate source algebras and
obtain etaleness from the Keller condition. Scheme-theoretic freeness and
the invariant affine-open realization would then follow; the ordinary
fixed-ring construction alone is not the quotient theorem. The relevant
free-action comparison is [Stacks, Tag 07S7](https://stacks.math.columbia.edu/tag/07S7),
with the affine invariant-ring formulation in
[Tag 03BM](https://stacks.math.columbia.edu/tag/03BM).
Only after identifying this actual open should its reduced complement be
fed into the existing finite conormal criterion. Keller-specific conormal
vanishing remains open. The next checkpoint separates the shorter route
to the target open from these stronger etale/free-action identifications.

The targeted fraction-field build passed all 2521 jobs, and the invariant
module build passed all 2585 jobs. A combined audit of fifteen declarations
uses only `propext`, `Classical.choice`, and `Quot.sound`. Five generic
external-client checks passed: faithful action, module-finiteness,
inference of the fixed algebra's ring structure, integrality, and the
separable fixed-field membership equivalence. The canonical fixed-algebra
ring instance is exported as a specialization of `Subalgebra.toCommRing`;
no parallel ring structure or quotient is introduced.

The combined build of `CollisionIdeals`, `CollisionIdeals.Planar.Research`,
`CollisionIdeals.Palomar.PaperOne.Solution`, and
`CollisionIdeals.Palomar.PaperTwo.Solution` passed all 3820 jobs. Only the
previously known local-base-change and diagnostic linter warnings replayed;
the two new modules have no warnings. No axiom or `sorry` declaration was
added.

The 170-module local import graph is acyclic with no missing imports. The
focused planar closure remains 35 modules, and the separate research closure
is 122; all 134 local documentation-link targets checked exist. No manuscript,
PDF, archive, push, or submission is changed in this step.

## Target-field and unramifiedness checkpoint (2026-09-20)

[ConjugateInvariantField.lean](../../../General/Galois/ConjugateInvariantField.lean)
realizes the existing fixed algebra in the target function field. Pull back
\(E\subset N\) along \(K\hookrightarrow N\); the resulting
\(B\)-subalgebra of \(K\) has fraction field \(K\). Under separability
of \(N/K\), the fixed-field theorem gives a canonical \(B\)-algebra
equivalence with the same \(E^G\) already constructed. This gives its
embedding in \(K\); fractions from \(B\) already suffice to prove
\(\operatorname{Frac}(E^G)=K\). The compatibility lemmas preserve both
the original map from \(B\) and the inclusion in \(N\). No additional
quotient, global competing algebra instance, or birationality hypothesis
is introduced.

[ConjugateUnramified.lean](../../../General/Keller/ConjugateUnramified.lean)
uses the Keller condition on the actual generating source sheets. Two
infinitesimal lifts from \(E\) agree on each conjugate source algebra by
Keller etaleness, hence agree on their generated algebra. This proves
formal unramifiedness, and existing finite type gives unramifiedness of
\(E/B\). This argument does not first identify a tensor-product component
and does not infer flatness or etaleness of \(E/B\).

### Geometric construction planned at this checkpoint

The following was the audited next route. It is implemented in the
target-open checkpoint below:

1. Unramifiedness and finite type make \(E/B\) quasi-finite.
2. Since \(B\) is Noetherian and \(E\) is finite over its fixed subalgebra,
   [Artin–Tate (Stacks, Tag 00IS)](https://stacks.math.columbia.edu/tag/00IS)
   makes \(E^G/B\) finite type.
3. The integral inclusion \(E^G\hookrightarrow E\) gives a surjection on
   spectra. Thus quasi-finiteness descends to \(E^G/B\), as in
   [Stacks, Tag 0GWS](https://stacks.math.columbia.edu/tag/0GWS).
4. Apply the existing
   `isOpenImmersion_integralClosure_of_quasiFinite` from
   [OpenImmersion.lean](../../../General/Normalization/OpenImmersion.lean).
   The fraction-field comparison and normality of \(B\) identify the
   relative integral closure with \(B\), yielding the desired open
   immersion \(\operatorname{Spec}(E^G)\hookrightarrow\operatorname{Spec}B\).

This route needs neither scheme-theoretic freeness nor the stronger
selected-etale-component identification merely to construct the target
open. Those comparisons remain available for the stronger torsor picture.
It also does not require assuming that \(E^G\) is normal: normality of
the target \(B\), already available from the finite function-field data,
is sufficient here.

The remaining construction after the open immersion is its actual reduced
boundary and principal presentation. Proving the two Keller-specific
conormal components vanish is still a separate open theorem. None of the
new algebraic results identifies \(E^G\) with \(B\) or proves planar
obstruction vanishing.

The target-field module passed its targeted build (2586 jobs), and the
unramifiedness module passed its targeted build (2809 jobs), both without
warnings. The fraction-field proof uses a theorem-local elaboration budget
and explicit scalar action; this changes no mathematical hypothesis.

The combined axiom audit of thirteen declarations uses only `propext`,
`Classical.choice`, and `Quot.sound`. All ten external-client checks passed,
covering the pullback's canonical structures, the equivalence, the original
fixed algebra's fraction field, both scalar towers, embedding compatibility,
and the two unramifiedness statements. Four examples require a scoped
typeclass-synthesis budget of 80000; the two tower examples also bind the
canonical scalar actions explicitly. These are inference controls, not new
algebra structures or mathematical premises.

The combined build of `CollisionIdeals`, `CollisionIdeals.Planar.Research`,
`CollisionIdeals.Palomar.PaperOne.Solution`, and
`CollisionIdeals.Palomar.PaperTwo.Solution` passed all 3822 jobs. Only the
pre-existing local-base-change and diagnostic linter warnings replayed.
The 172-module local import graph is acyclic with no missing imports; the
focused planar closure remains 35 modules and the separate research closure
is 124. All 141 local documentation-link targets checked exist, and
`git diff --check` passes. No manuscript, PDF, archive, commit, push, or
submission is changed in this checkpoint.

## Invariant target-open checkpoint (2026-09-20)

The preceding fraction-field/unramifiedness checkpoint was committed as
`121fb56`. Those two results now enter the actual open-immersion proof:

1. [ConjugateInvariantFiniteType.lean](../../../General/Galois/ConjugateInvariantFiniteType.lean)
   applies Artin–Tate to the existing \(B\subset E^G\subset E\), proving
   finite type of \(E^G/B\). Neither Keller nor separability is needed
   for this step.
2. [QuasiFiniteDescent.lean](../../../General/Normalization/QuasiFiniteDescent.lean)
   proves the reusable finite-fiber descent along an integral injective
   extension. Applying it to \(E^G\subset E\), Keller unramifiedness of
   \(E/B\) gives quasi-finiteness of \(E^G/B\).
3. [BirationalOpen.lean](../../../General/Normalization/BirationalOpen.lean)
   identifies the relative integral closure with the normal base for an
   intermediate algebra in its fraction field. The existing affine
   Zariski-main theorem then gives an open immersion. This generic lemma
   assumes neither Noetherianity of the base nor normality of the
   intermediate algebra.
4. [ConjugateInvariantOpen.lean](../../../General/Keller/ConjugateInvariantOpen.lean)
   applies these lemmas to the actual fixed algebra and its proved
   target-field embedding. Under Keller and separability of \(N/K\), it
   proves
   \[
   \operatorname{Spec}(E^G)\hookrightarrow\operatorname{Spec}B.
   \]
   `polynomialConjugateInvariantTargetOpen` is the standard
   `Scheme.Hom.opensRange` of this map, and
   `polynomialConjugateInvariantTargetOpen_isAffineOpen` proves that this
   actual \(U_F\) is affine.

The fixed algebra has not been replaced by a second quotient, and no
open-model hypothesis was introduced. Neither flatness of \(E/B\) nor
scheme-theoretic freeness is needed for this construction. Its next step
is the actual radical ideal
\(\mathfrak b_F=I(\operatorname{Spec}B\setminus U_F)\) and its principal
reduced presentation. The stronger etale/torsor and \(H\)-invariant
localization comparisons remain separate. Proving the Keller-specific
conormal classes vanish remains the substantive open theorem; the open
immersion does not assert \(U_F=\operatorname{Spec}B\).

The generic descent leaf passed 2001 jobs and its default-setting external
client; the birational leaf passed 2678 jobs and two independent clients.
The actual finite-type and target-open build passed all 2923 jobs. These
builds have no warnings. A private generic adapter reuses Mathlib's
unramified-to-quasi-finite instance to avoid inference through the nested
conjugate subalgebra; it adds no mathematical premise.

The combined build of `CollisionIdeals`, `CollisionIdeals.Planar.Research`,
`CollisionIdeals.Palomar.PaperOne.Solution`, and
`CollisionIdeals.Palomar.PaperTwo.Solution` passed all 3826 jobs. The eight
public declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
All seven external-client checks passed: the two generic clients use default
settings, while the five actual-object clients use scoped elaboration and
typeclass-synthesis budgets of 800000 and 80000. These budgets add no
mathematical premises. Only pre-existing local-base-change and diagnostic
linter warnings replayed.

The 176-module local import graph is acyclic with no missing imports. The
focused planar closure remains 35 modules; the research closure is 128.
All 152 local documentation-link targets checked exist, and
`git diff --check` passes. Paper II's Lean-status paragraph now records the
proved invariant open and the still-open reduced-boundary and conormal
steps. Its rebuilt 13-page PDF passed visual review, with no warnings in
the final LaTeX log. Paper I and the manuscript archive are unchanged.
The earlier checkpoint is committed as `121fb56`; this target-open
checkpoint remains uncommitted, with no push or submission.

## Actual reduced-boundary and intrinsic-conormal checkpoint (2026-09-20)

The next construction uses the same target open, without selecting an
equation or supplying a new boundary model:

\[
\mathfrak b_F=I(\operatorname{Spec}B\setminus U_F)\subset B.
\]

[AffineOpenBoundary.lean](../../../General/Normalization/AffineOpenBoundary.lean)
reuses Mathlib's `PrimeSpectrum.vanishingIdeal`. It proves radicality, the
exact complement as zero locus, and the unit-ideal/full-open equivalence.
Its nonzero-ideal lemma needs only a nonempty open, not a domain assumption.
[ConjugateInvariantBoundary.lean](../../../General/Keller/ConjugateInvariantBoundary.lean)
applies this API to the actual target open, proves that open nonempty, and
proves \(\mathfrak b_F\) nonzero and finitely generated. A nonzero ideal
does not assert a nonempty boundary: the empty boundary has the unit ideal.

[PolynomialConormal.lean](../../../General/Normalization/PolynomialConormal.lean)
transports polynomial-coordinate derivations through an algebra equivalence
and transfers the existing characteristic-zero conormal criterion to any
algebra with that polynomial presentation.
[ConjugateInvariantConormal.lean](../../../General/Keller/ConjugateInvariantConormal.lean)
uses the existing injective target-polynomial presentation of \(B\).
`polynomialImageCoordinatePartial_rangeRestrict` verifies that the partial
is taken before target evaluation; it is not the ordinary source partial
of the evaluated polynomial. No new frame, quotient, or obstruction is
introduced.

The actual conormal module \(\mathfrak b_F/\mathfrak b_F^2\) is finitely
generated over \(B\). In characteristic zero the actual criterion is

\[
\left(\forall i,\ [d_i]:\mathfrak b_F/\mathfrak b_F^2\to B/\mathfrak b_F
\text{ is zero}\right)
\quad\Longleftrightarrow\quad U_F=\operatorname{Spec}B.
\]

There are two component maps in the planar specialization. This criterion
does not require the principal presentation \(\mathfrak b_F=(s)\), so
that separate formalization no longer blocks stating the actual finite
conormal target. Without selecting a generator, these are two maps on a
finitely generated module, not two chosen element classes or a claim of
cyclicity. The principal reduced presentation remains useful for the
rank-one simple-pole formulation.

The substantive gap is unchanged: prove the actual Keller-specific
component maps vanish (equivalently, preserve \(\mathfrak b_F\)).
The new equivalence establishes neither side for every Keller map. No
principal-equation assumption, flatness/freeness assertion, or boundary
vanishing hypothesis is introduced into the construction.

The generic boundary leaf passed 1920 build jobs, four theorem-axiom
checks, and five external scheme-open clients. The generic polynomial
conormal leaf passed 1731 jobs, five declaration-axiom checks, and four
external clients at default elaboration settings. The actual boundary and
conormal modules passed the combined 2931-job targeted build without
warnings. A private generic finite-quotient helper avoids an inference
timeout through the nested actual ideal; it changes no premise and needs
no increased elaboration budget. The nonempty-open theorem alone uses a
scoped typeclass-synthesis budget of 80000 for the inherited fixed-ring
structures.

The final combined build of `CollisionIdeals`,
`CollisionIdeals.Planar.Research`,
`CollisionIdeals.Palomar.PaperOne.Solution`, and
`CollisionIdeals.Palomar.PaperTwo.Solution` passed all 3830 jobs. Only the
pre-existing local-base-change and diagnostic linter warnings replayed.
All 21 public declarations use only `propext`, `Classical.choice`, and
`Quot.sound`. All ten final external-client checks passed at default
elaboration settings, including the planar two-component specialization
and a proper-nonzero-ideal negative control. The final audit was rerun
directly after the delegated temporary session became unavailable.

The 180-module local import graph has no missing imports or cycles. The
focused planar closure remains 35 modules; the research closure is 132.
All 162 local documentation-link targets checked exist, and
`git diff --check` passes. The semantic parity queue and Paper II's status
paragraph now distinguish the actual boundary and intrinsic conormal
criterion from the still-unformalized principal presentation and open
Keller-specific vanishing statement. The rebuilt 13-page PDF passed
complete visual review, with no warnings in the final LaTeX log. Paper I
and the manuscript archive are unchanged. This work and the preceding
target-open checkpoint remain uncommitted; no push or submission was made.

## Finite-generator-to-vanishing checkpoint (2026-09-20)

The actual finite test is now connected to the existing planar endpoint:

1. [FiniteConormalTest.lean](../../../General/Normalization/FiniteConormalTest.lean)
   reduces a conormal component to derivatives of any finite ideal
   generating set, by Leibniz and span induction. The actual-boundary
   wrappers supply such a set and identify the successful test with
   \(U_F=\operatorname{Spec}B\). No principal equation is required.
2. [FullOpenAlgebra.lean](../../../General/Normalization/FullOpenAlgebra.lean)
   converts a full affine open immersion into a bijective algebra map.
   [ConjugateInvariantFiniteness.lean](../../../General/Keller/ConjugateInvariantFiniteness.lean)
   applies this to \(B\to E^G\), then uses finiteness of \(E/E^G\)
   and the embedded source \(A\subset E\) to prove finiteness of
   \(E/B\) and \(A/B\). Noetherianity of \(B\) supplies submodule
   finiteness; source finiteness is derived, not assumed in this bridge.
3. [FiniteSource.lean](../../../General/Normalization/FiniteSource.lean)
   proves that a finite source fills its intermediate normalization.
   [FiniteBoundary.lean](FiniteBoundary.lean) then excludes hidden inertia
   and uses the existing no-ramification endpoint to conclude
   \(\operatorname{Obs}(F)=0\). `BranchPurityA2` and
   `AffinePlaneFiniteEtaleRigidity` are explicit inputs. The model is
   constructed from the Keller map; no model-existence premise or custom
   literature-axiom import is added.

The target boundary and intermediate-normalization boundary remain
distinct. Their emptiness is connected through actual source finiteness,
not an identification of their defining objects. The generic leaves and
dimension-independent wrappers stay in `General`; only the final planar
endpoint is in the research tree. The focused degree-two theorem is
unchanged.

The remaining theorem is the generator membership itself:
\(\partial_Pf_j,\partial_Qf_j\in\mathfrak b_F\) for generators of
the actual reduced boundary. Neither finite generation nor preservation
after localization proves it. The
[proper-open negative control](OBJECT-BENCH.md#finite-generator-endpoint-audit-2026-09-20)
records this distinction. This checkpoint completes a conditional
connection, not a proof of full planar vanishing.

The targeted actual-boundary endpoint build passed all 3020 jobs. Only
the pre-existing local-base-change linter warning replayed. The shared
source-finiteness proofs use scoped elaboration budgets for the nested
subalgebra structures; no mathematical hypothesis is added by those
settings.

The full build of `CollisionIdeals`, `CollisionIdeals.Planar.Research`,
`CollisionIdeals.Palomar.PaperOne.Solution`, and
`CollisionIdeals.Palomar.PaperTwo.Solution` passed all 3835 jobs. Only the
pre-existing local-base-change and diagnostic linter warnings replayed.
All 20 new public declarations use only `propext`, `Classical.choice`, and
`Quot.sound`. All 14 downstream clients passed at default elaboration
settings, including the universal canonical-conormal premise implying
the existing `PlanarVanishing` target. That client constructs the normal
closure internally and takes only the remaining conormal premise and
the two geometric theorem inputs; no separate model-existence premise
is needed.

The 185-module local import graph has no missing imports or cycles. The
focused planar closure is unchanged at 35 modules; the research closure
is 137. The new endpoint's 82-module closure contains no custom-axiom
module. All 178 local documentation-link targets checked exist, and
`git diff --check` passes. The object bench and semantic parity queue now
record the finite-generator and source-finiteness bridges. No manuscript
or PDF was edited in this checkpoint. This and the preceding two
checkpoints remain uncommitted; no push or submission was made.

## Polynomial-source intersection checkpoint (2026-09-20)

The next source-specific comparison is the classical intersection
property, proved internally rather than added as a literature input:
\[
A\cap K=B\qquad\text{inside }L.
\]

[SourceIntersection.lean](../../../General/Keller/SourceIntersection.lean)
first reflects divisibility by a prime \(p\in B\), using an existing
visible source divisor contracting to \((p)\). UFD factorization and
cancellation handle arbitrary divisors, including zero and units. A
fraction in \(K\) that is polynomial on the source then has its
denominator dividing its numerator already in \(B\). Neither
characteristic zero nor separability is required for these three
theorems. The targeted build passed all 2915 jobs without warnings or
increased elaboration budgets.

[ConjugateInvariantSource.lean](../../../General/Keller/ConjugateInvariantSource.lean)
applies this comparison to the existing separable marked normal closure.
For each element of the actual fixed algebra, membership in the marked
polynomial source is equivalent to membership in the image of the base
map. No new intersection ring, source copy, or theorem-target predicate
is defined.

This is useful source information, not a vanishing argument:
\(E^G\cap\iota(A)=\iota(B)\) does not imply
\(E^G\subseteq\iota(A)\). The generator derivative memberships remain
open. The [object-bench audit](OBJECT-BENCH.md#what-the-full-polynomial-source-does-supply-2026-09-20)
records the classical attribution and explains why unit reflection and
separate visible sheets do not furnish the missing regularity assertion.

The actual fixed-algebra application passed its 2928-job targeted build
without warnings or increased elaboration budgets. The combined build of
`CollisionIdeals`, `CollisionIdeals.Planar.Research`,
`CollisionIdeals.Palomar.PaperOne.Solution`, and
`CollisionIdeals.Palomar.PaperTwo.Solution` passed all 3837 jobs; only the
pre-existing local-base-change and diagnostic linter warnings replayed.
All four new public declarations use only `propext`, `Classical.choice`,
and `Quot.sound`. All twelve external clients passed at default budgets
without warnings. The two canonical-closure clients construct the
separability and base-algebra structures internally and express the
conclusion in the ambient normal closure, coercing the public theorem's
fixed-algebra membership result. This avoids redundant instance search
through the concrete nested fixed ring; no mathematical premise or
source theorem was changed.
The 187-module import
graph has no missing imports or cycles. The focused planar closure
remains 35 modules; the research closure is 139. The new leaf's 29-module
closure contains no custom-axiom module. All 187 local documentation-link
targets checked exist, and `git diff --check` passes.

The shared semantic parity table, object bench, and active proof spine
use the existing rings and embeddings throughout. No manuscript, PDF,
archive, focused degree-two theorem, commit, push, or submission was
changed in this checkpoint. Earlier uncommitted changes are preserved.

## Source-regularity characterization checkpoint (2026-09-20)

[ConjugateInvariantCriterion.lean](../../../General/Keller/ConjugateInvariantCriterion.lean)
combines the pointwise source-intersection theorem with the existing
actual target open and boundary. Its three declarations identify:

1. Regularity on the marked source of every element of \(E^G\) with
   surjectivity of the canonical map \(B\to E^G\).
2. That surjectivity with \(\mathfrak b_F=B\).
3. Source regularity directly with empty target boundary.

The reverse boundary implication uses the same injective base map and
the affine spectrum isomorphism; no equality between incompatible Lean
subtypes is asserted. Together with the earlier intersection theorem,
this formalizes \(E^G\subseteq A\iff E^G=B\iff\mathfrak b_F=B\)
under the established embeddings.

This checkpoint consolidates exact criteria and their existing
consequences. The Galois-descent consequence still takes classical
Keller--Galois rigidity; the conditional finite-boundary vanishing
endpoint still takes `BranchPurityA2` and `AffinePlaneFiniteEtaleRigidity`.
Neither universal descent nor boundary emptiness is proved. The
finite-lattice proposal remains on the bench, and no historical
research objects have been deleted or duplicated.

The same checkpoint adds the complementary marked-closure criterion in
`General.Galois.Descent` and the map-by-map obstruction characterization
in `Planar.Research.Vanishing.GaloisDescent`. For complex planar Keller
maps, at this checkpoint the latter took Ax--Grothendieck and
Keller--Galois rigidity explicitly; the Ax--Grothendieck input is removed
in the later direct-closure checkpoint below. It characterizes vanishing
by normality of the original
extension, or equivalently by surjectivity of the marked embedding into
its normal closure. The field-theoretic fixing-subgroup criterion reuses
the same \(H\) as Paper I; it is not an inertia-group assertion.

Verification: the fixed-algebra criterion passed its 2946-job targeted
build; the closure/vanishing additions passed their 2637-job targeted
build. All seven new declarations use only `propext`, `Classical.choice`,
and `Quot.sound`; all 22 external clients passed at default budgets,
including canonical-closure and complementary nonvanishing examples.
The combined build of `CollisionIdeals`, `CollisionIdeals.Planar.Research`,
and both Palomar solution targets passed all 3838 jobs. Only pre-existing
linter warnings replayed.

The 188-module project import graph has no missing imports or cycles;
the focused planar closure remains 35 modules and the research closure
is 141. All 193 checked local documentation paths and 21 anchors resolve.
Paper II now presents these criteria and their distinct classical inputs;
its 14-page PDF rebuilt without TeX warnings and all rendered pages were
visually reviewed. Wang's intersection theorem is cited while its Lean
proof remains internal. Paper I and the manuscript archive are untouched.
`git diff --check` passes. Changes remain uncommitted; no push or submission
was made.

## Direct collision-to-boundary characterization (2026-09-20)

The reverse implication is now intrinsic to the collision construction,
not an application of Ax--Grothendieck. In
[ConjugateInvariantObstruction.lean](../../../General/Keller/ConjugateInvariantObstruction.lean),
vanishing gives \(I_R=I_\Delta\). Every Galois collision pair therefore
annihilates the diagonal generators, so all conjugate source coordinates
equal the marked coordinates. Adjoin generation places \(E\), and hence
\(E^G\), in the marked polynomial source. This first implication needs
neither Keller nor separability. The second applies the existing actual
boundary criterion, with Keller and separability, to give \(\mathfrak b_F=B\).

[BoundaryCriterion.lean](BoundaryCriterion.lean) combines this direct
reverse with the existing finite-boundary endpoint. Its central theorem
and two corollaries package

\[
\operatorname{Obs}(F)=0\iff\mathfrak b_F=B
\iff E^G\subseteq\iota(A)
\iff\text{both target-coordinate conormal components vanish}.
\]

Only `BranchPurityA2` and `AffinePlaneFiniteEtaleRigidity` are theorem
inputs, and only from boundary emptiness to obstruction vanishing.
There is no Ax--Grothendieck or Keller--Galois rigidity input on this
route. At this checkpoint the separate normal-closure characterization
retained its two-input signature, subsequently simplified below.
No new rings, quotients, or universal-vanishing assumptions
were added. The unused automorphism-based draft created during this
checkpoint was removed; earlier research files were preserved.

Verification: the shared leaf passed its 2947-job targeted build on the
first attempt, with no warnings or increased elaboration budgets. The
combined repository, research, and two Palomar solution build passed all
3840 jobs; only pre-existing linter warnings replayed. All five new
declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
All 14 external clients passed at default settings, including both
directions, the nonvanishing complements, the hypothesis-free shared
source implication, and canonical-closure instantiations.

The 190-module project graph has no missing imports or cycles. The focused
Planar closure remains 35 modules; the research closure is 143. Neither
new leaf reaches a custom-axiom module. All 202 local documentation paths
checked exist, and `git diff --check` passes. Paper II's direct reverse
proof and Lean-status paragraph are synchronized; its 14-page PDF rebuild
has no TeX warnings, and all rendered pages were visually reviewed.
Paper I and the archive remain untouched. No commit, push, or submission
was made; earlier uncommitted changes are preserved.

## Direct normal-closure criterion and exposition checkpoint (2026-09-20)

`General.Galois.CollisionVanishing` now owns the dimension-independent
conjugate-coordinate equality obtained by evaluating the diagonal
generators at a Galois collision pair. It also proves
`polynomialSource_normal_of_obstructionIdeal_eq_bot`, using the existing
marked normal closure and coordinate-descent criterion. Neither Keller,
separability, nor a literature theorem is needed for this shared step.
`General.Keller.ConjugateInvariantObstruction` reuses the coordinate
equality instead of duplicating that proof.

The two per-map planar normal-closure equivalences consequently drop
their former Ax--Grothendieck parameter. Their only literature input is
`ComplexKellerGaloisRigidity 2`, used from normality to vanishing.
The general vanishing-to-automorphism theorem remains unchanged.
The boundary equivalences likewise retain their distinct purity and
finite-etale inputs only in the boundary-to-obstruction direction.
No universal vanishing assertion or replacement object is introduced.

Paper II follows the direct collision proof, reuses its coordinate
equalities in the boundary argument, and shortens the Lean-status
inventory and conclusion. The current semantic table and research
overview record the reduced inputs; earlier checkpoint records above
remain explicitly historical. Paper I and the archive are untouched.

Verification: the three targeted modules passed their 2957-job build
without new warnings. The full repository, research, and both Palomar
solution targets passed all 3841 jobs, replaying only pre-existing linter
warnings. All 33 refreshed external clients passed at default budgets;
all 11 axiom checks report only `propext`, `Classical.choice`, and
`Quot.sound`.

The 191-module local import graph has 474 edges, no missing imports, and
no cycles. The focused Planar closure remains 35 modules; Research is
143. Neither direct-collision nor boundary-criterion leaf reaches a
custom-axiom module; the broad research umbrella retains its pre-existing
assumptions import. All 205 checked local documentation links resolve.
Paper II rebuilt to 13 pages without TeX warnings, and all pages were
visually reviewed. The complete checkpoint is prepared for the authorized
local commit; no push or submission is included.
