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

## Precise Galois-descent target

The current finite comparison is the
[reduced-boundary invariant](#reduced-boundary-invariant) below. The
Galois-descent route supplies collision witnesses; it is not assumed in
order to derive their secant identities. No object pruning has been made
while the comparison from those witnesses to the boundary remains open.

Let \(\iota:L\hookrightarrow N\) be the existing marked embedding. The
proposed target is

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
conjugate coordinates descend to the marked L     [open target]
    <-> L/K is normal                            [coordinate-generation bridge]
    -> F is a polynomial automorphism            [Keller--Galois rigidity input]
    -> Obs(F) = 0                                [existing collision API]
```

The normality equivalence and the two conditional endpoints are formalized
as `planarGaloisDescent_iff_forall_normal`,
`planarJacobianConjecture_of_galoisDescent`, and
`planarVanishing_of_galoisDescent`. This route needs neither an
Ax--Grothendieck input nor the ramification route's purity input.

The missing theorem is descent itself. Constructing the normal closure
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
The invariant-open identification is still a mathematical calculation,
not a Lean theorem. Equality with \(A\), or a uniform denominator bound
forcing that equality, remains
unproved. Thus the proposed shortcut returns to the global boundary gap;
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
The algebraic equivalence is proved; constructing this particular
all-conjugate open and its boundary ideal in Lean is separate work. The
Keller-specific claim that the defect vanishes remains open. In particular,
neither preservation of \(B[1/s]\) nor adjoining first jets to the
secant coefficient lattice supplies simple-pole preservation. The
[bench test](OBJECT-BENCH.md#reduced-boundary-and-simple-pole-test-2026-09-19)
records an explicit proper-open example where those jets increase the
required denominator. No new universal theorem-target predicate is added.

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

## Work order and verification

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
finite-etale rigidity of affine space. Those geometric identifications and
the actual boundary ideal remain to be instantiated in Lean.

The remaining construction should be formalized in this order, reusing
\(E\) rather than introducing a new boundary-model hypothesis bundle:

1. Identify its fraction field with the supplied \(N\).
2. Identify \(E\) with the selected component of the finite tensor product
   of conjugate source algebras; obtain etaleness from the Keller condition.
3. Restrict the Galois action, prove scheme-theoretic freeness, and identify
   the invariant quotient with an affine open of \(\operatorname{Spec}B\).
4. Form the radical ideal of the actual complement and prove its principal,
   reduced presentation. Only then specialize the existing conormal criterion.

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
