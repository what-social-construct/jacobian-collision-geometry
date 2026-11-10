# Planar vanishing

The [preserved Paper II boundary excerpt](BOUNDARY-CRITERIA.tex) retains the
target-boundary, source-regularity, and conormal discussion removed from the
limited-scope manuscript. It uses the complex characteristic-zero setup;
it is not a characteristic-two statement or a standalone paper.

The research goal is the original obstruction-vanishing statement:

```math
F\text{ planar Keller}\quad\Longrightarrow\quad
\mathrm{Obs}(F)=I_\Delta/I_R(F)=0.
```

The existing Lean name is `CollisionIdeals.PlanarVanishing`, in
[Statements/Vanishing.lean](../../Statements/Vanishing.lean). It is a theorem
target, not an axiom or a proved theorem. There is no generic-degree restriction
in this target. Generic degree two is a settled special case conditional on
the stated Keller--Galois rigidity input, not the scope of the full program.

The current findings are exact characterizations. Identifying the shared
rings with their images in the marked normal closure gives

```math
E^G\cap A=B,\qquad
E^G\subseteq A\ \Longleftrightarrow\ E^G=B
\ \Longleftrightarrow\ \mathfrak b_F=B.
```

The last condition means empty target boundary. It is not the assertion
that the collision obstruction ideal is the unit ideal: that separate
ideal is $\mathrm{Obs}(F)\subseteq C_F$, whose desired value is
zero. Conjugate-coordinate descent is separately equivalent to normality
of $L/K$; the stated Keller--Galois rigidity input then gives
invertibility and obstruction vanishing. The source-regularity and
conormal criteria characterize boundary emptiness without proving it
for every Keller map.

The complementary normal-closure condition is also packaged map by map:
$\mathrm{Obs}(F)=0\iff L/K\text{ normal}\iff N=\iota(L)\iff H=1$.
The planar obstruction equivalence takes only Keller--Galois rigidity,
in the normality-to-vanishing direction. The other direction follows
directly from collision-coordinate equality, without Ax--Grothendieck;
the shared closure/subgroup equivalences are field-theoretic.
Constructing $N$ alone proves none of these conditions.

The separate [boundary criterion](BoundaryCriterion.lean) now connects
the actual boundary tests directly to $\mathrm{Obs}(F)=0$.
Vanishing collision equations identify all conjugate source coordinates,
so the implication to source regularity and empty boundary needs neither
Ax--Grothendieck nor Galois rigidity. The converse retains exactly
`BranchPurityA2` and `AffinePlaneFiniteEtaleRigidity` from the existing
finite-boundary endpoint. No universal vanishing assertion is added.

Maintain three working documents:

- [Primary proof spine](PROOF-SPINE.md): established characterizations and
  conditional routes to obstruction vanishing, with each input visible.
- [Object bench](OBJECT-BENCH.md): constructions, alternative routes, and
  negative controls; what each contributes and what would justify promoting
  it into the primary argument.
- [Source ledger](../SOURCE-LEDGER.md): exact source passages, hypotheses,
  applicability checks, and the distinction between reading, independent
  verification, formalization, and explicit theorem inputs.

The first coherent-analogy checkpoint is formalized in
[DerivationAnnihilator.lean](../../../General/Normalization/DerivationAnnihilator.lean):
a supplied target-partial Leibniz action and a nonzero module annihilator
force vanishing over a characteristic-zero polynomial algebra. The
[source ledger](../SOURCE-LEDGER.md#coherent-derivation-analogy) distinguishes
this generic mechanism from the actual quotient action below and the
still missing finite control.

The [actual target-section comparison](../../../General/Keller/ConjugateInvariantSections.lean)
now identifies $E^G/B$ with the sections on $U_F$ modulo the original base.
This is a torsion $B$-module, and its vanishing is equivalent to
$\mathfrak b_F=B$. It is not asserted finite or uniformly annihilated.
The [Keller-frame quotient action](../InvariantQuotientAction.lean)
constructs both additive operators and proves their target-coordinate
Leibniz rules. Preservation of the fixed algebra is derived from the
existing field frames, not supplied. The next task is preserved finite-stage
control; the separate filtered-Ext cohomology comparison is not assumed
as a premise.

The first [concrete finite-stage tests](PROOF-SPINE.md#concrete-finite-stage-tests)
rule out two shortcuts. A nonzero class has a coordinate derivative
outside its finite cyclic span $Bq$. The fixed-field part of the old
trace-integral stage already maps to zero modulo $B$ in characteristic
zero. These tests do not provide the missing preserved stage; the original
normalization-based trace objects are retained for their separate role.

The [differential-orbit test](PROOF-SPINE.md#differential-orbit-and-finite-jet-denominator-test)
makes the coherent-stage target quantitative. A fixed nonzero
target-polynomial denominator clearing all frame words through its own
total degree already forces the class to vanish. Torsion automatically
provides $a^{r+1}$ at order $r$, but those growing denominators do not
meet that degree threshold. A Keller-specific improvement remains open;
no coherent preserved stage or all-orders bound is inferred.

There is now a [constructed finite-stage benchmark](PROOF-SPINE.md#constructed-finite-stages-in-low-total-degree):
if both coordinate polynomials have total degree at most two, the actual
Keller frames preserve finite ground-polynomial stages of the original
all-conjugate algebra. Invariant pullback and the quotient projection
give finite preserved $B$-stages, proving $E^G/B=0$. This is total
polynomial degree, not generic degree. The higher-degree stage problem
remains open.

The [fractional-normalization test](PROOF-SPINE.md#fractional-normalization-and-local-pole-growth)
constructs finite candidates $s^{-m}T$ from the original normalization
and proves their valuation bounds, also modulo $B$. A separate local
transverse-derivative calculation constructs successive unit numerators,
giving exact pole growth at a supplied target DVR. The quotient rule
rules out obtaining preservation merely by enlarging a power shift.
Containment of the actual Keller orbit in one finite candidate remains
the required polynomial-geometric step; preserving the entire candidate
is stronger than needed.

The [scheme comparison](PROOF-SPINE.md#source-restriction-and-normalization-comparison)
proves that the original polynomial source is finite étale over the
existing invariant open. It also places the all-conjugate scheme as an
open in the original finite normalization, by the ring inclusion
$T\hookrightarrow E$. This is not the requested containment of an entire
Keller orbit in one fractional $T$-stage; that boundary-extension step
remains open.

The [actual boundary setup](PROOF-SPINE.md#constructed-target-divisor-and-common-regularity)
now derives a target height-one prime, its DVR, and a polar invariant
representative from a hypothetical nonzero quotient class. It also
identifies $\mathrm{Spec}E$ with the finite normalization restricted to
$U_F$, and tests point membership by regularity of every conjugate
coordinate in the same local ring. No boundary divisor is supplied as
an extra input. The resulting coordinate pole is not automatically a
ramification or inertia witness; the uniform orbit bound remains open.

The [original multiplier comparison](PROOF-SPINE.md#original-multiplier-comparison-in-the-common-ambient-quotient)
now places $R_C/T$, $T^\dagger/T$, and $E^G/B$ in the same ambient $N/T$.
For a supplied landing multiplier it recovers
$[r]\mapsto[sr]$ from $R_C/T$ to $T^\dagger/T$, without asserting
injectivity. The original embeddings give $E^G/B\hookrightarrow N/T$
by $K\cap T=B$; they do not identify the section domains.
The collision ring already gives local rigidity once the moved sheet
is regular at the selected divisor. Establishing that regularity or
uniform landing remains the geometric task, not construction of a
second collision ring.

Ramification vanishing, trivial inertia, and trace landing are possible
intermediate results. They do not replace the central goal or receive the
name `PlanarVanishing`.

The [finite polynomial cancellation checkpoint](PROOF-SPINE.md#finite-polynomial-cancellation-at-a-pole)
now identifies what a moved coordinate pole forces: repeated dominance
among the actual monomials of one Keller component. Target regularity
comes from the same normalization center, not a premise about the source
sheet. This makes cancellation explicit; excluding it with the full
constant-Jacobian identity remains open.

The [full leading-Jacobian test](PROOF-SPINE.md#full-jacobian-constraint-on-weighted-components)
now separates balanced and strict weighted degrees. Signed Euler excludes
common leading zeros with nonzero weighted radial vector in the balanced
case. An actual polynomial automorphism shows that the strict case admits
such zeros: lower polar terms survive. Successive cancellation, rather
than a contradiction from the leading face alone, remains the target.

The [one-step cancellation budget](PROOF-SPINE.md#weighted-cancellation-budget-and-target-shears)
reuses the existing frame identity to bound a genuine degree drop:
$0<rn-k\le D$. The leading-polynomial relation is an input, while
nonvanishing of the residual and its sharp degree are derived.
Exponent-one subtraction in either target coordinate preserves Keller
and the same image algebra and strictly decreases the nonnegative defect.

The [actual boundary comparison](PROOF-SPINE.md#actual-boundary-weights-and-initial-residues)
now supplies signed weights and nonzero initial coordinates in the
residue field of the same DVR. Positive-degree target initial forms
vanish there. Both shear directions preserve regular target values at
that fixed divisor. What remains is [availability of the next legal
reduction](PROOF-SPINE.md#availability-of-the-next-legal-reduction): derive
the required polynomial relation, not merely its evaluated residue, or
exclude the remaining state by the full Keller identity.

## Evaluated-projector and fixed-locus checkpoint

[`EvaluatedProjector.lean`](../EvaluatedProjector.lean) evaluates the existing
canonical `Planar.ExplicitSecant.collisionProjector`; it does not choose a
second secant presentation. The off-diagonal projector is zero on identical
collision sheets and one on distinct sheets in a domain. For a Keller map,
its membership in the evaluated coordinate-difference ideal makes that
ideal the unit ideal for a distinct pair.

[`ConjugateFixedLocus.lean`](../ConjugateFixedLocus.lean) applies this in the
actual all-conjugate algebra $E$, not merely in $N$. For a planar Keller map,
marked normal-closure data, and $1\ne\sigma\in G$, it proves

```math
(\sigma(z)-z:z\in E)=E.
```

Consequently the affine fixed-locus quotient is the zero ring, its zero
locus is empty, and Mathlib's `Ideal.inertia` is trivial at every proper
ideal of $E$. No generic-degree, Galois-rigidity, purity, or boundary
emptiness input is used. These statements do not exclude setwise-stable
primes or eliminate inertia on the normalization boundary outside this
model. The affine cover comparison is the next checkpoint below;
identifying its target open with the maximal finite locus is still
separate. This certificate does not prove `PlanarVanishing`.

Verification (2026-11-07, Lean 4.28.0): both modules pass their targeted
builds, and the research umbrella passes its import check. A separate
importing client checks the actual-algebra projector
values, unit difference ideal, fixed quotient, and inertia statements
without local instance workarounds. All seven audited endpoint theorems
depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Finite étale cover and tensor comparison

[`ConjugateCover.lean`](../ConjugateCover.lean) applies the fixed-locus
certificate to the same extension $E/E^G$. It proves projectivity,
étaleness, and faithful flatness; module-finiteness was already proved in
the shared invariant-ring module. It also constructs the canonical
equivalence

```math
E\otimes_{E^G}E\simeq_{E^G}\prod_{g\in G}E,
\qquad a\otimes b\longmapsto(g\longmapsto a\,g(b)).
```

The generic algebraic leaves are [GaloisTensor.lean](../GaloisTensor.lean),
[GaloisTrace.lean](../GaloisTrace.lean), and
[GaloisTensorEquiv.lean](../GaloisTensorEquiv.lean): comaximal graph kernels
give surjectivity by Chinese remainders; a preimage of the identity delta
function gives a finite trace-dual frame; that frame proves projectivity
and reconstructs every tensor. Keller unramifiedness then gives étaleness.
Flatness and the delta frame are conclusions, not additional inputs.
This frame belongs to the finite extension $E/E^G$; it is not a uniform
trace-landing theorem for the separate boundary-section ring $R_C$.

This is the affine algebraic Galois-torsor certificate, not a new bundled
scheme-level torsor object. Its base is $E^G$, not $B$. It does not prove
$E^G=B$, finiteness over $B$, or obstruction vanishing. Neither manuscript
nor the submission release is changed.

Verification (2026-11-07, Lean 4.28.0): all four new cover modules build,
and the research umbrella passes its import check. Bare importing clients
check projectivity, étaleness, faithful flatness, and the tensor equivalence
with its pure-tensor formula. All nine audited endpoints use only
`propext`, `Classical.choice`, and `Quot.sound`.

## Planar Keller--Galois rigidity from geometry

[`GaloisRigidity.lean`](GaloisRigidity.lean) derives
`ComplexKellerGaloisRigidity 2` from the two existing theorem inputs
`BranchPurityA2` and `AffinePlaneFiniteEtaleRigidity`. They remain explicit;
neither is proved or installed as an axiom by this module.

[`NormalRamification.lean`](NormalRamification.lean) makes normality of the
original $L/K$ imply $H=1$. The existing visible-center theorem supplies an
inertia-fixed sheet at any hypothetical ramified divisor; when $H=1$, this
forces inertia trivial. The canonical endpoint constructs its normalization
diagram and local-index realization internally, with no boundary-emptiness
premise. Purity and finite-etale rigidity then give $N=K$, hence $L=K$.

[`BirationalAutomorphism.lean`](BirationalAutomorphism.lean) uses the existing
$A\cap K=B$ to deduce $A=B$ and polynomial invertibility from $L=K$.
Thus neither Ax--Grothendieck nor an independent Keller--Galois rigidity
input is needed for this specialization. Obstruction vanishing is packaged
alongside it. Existing degree-two results can receive this derived rigidity
value without changing their statements.

For general nonnormal $L/K$, the no-ramification step remains open. The
new implication is planar only: Paper I's dimension-three rigidity input
and both frozen submissions are unchanged. The $E/E^G$ cover comparison is
independent of this proof; it is not forced into the rigidity dependency.

Verification (2026-11-07, Lean 4.28.0): all three modules build, and the
research umbrella passes its import check. Bare clients check field
triviality, vanishing, automorphy, and reuse of the derived rigidity in the
existing degree-two exclusion. All seven audited endpoints use only
`propext`, `Classical.choice`, and `Quot.sound`; the two geometric results
remain explicit parameters. The rebuild also reports an existing unused
section-variable warning in the unchanged `General/Normalization/LocalBaseChange.lean`.

This folder reuses the existing Lean objects, notation, and namespaces rather
than making parallel definitions for a proof sketch or manuscript.

## Active dependency map

| Piece | Role and current boundary |
| --- | --- |
| [ConjugateAlgebra.lean](../../../General/Galois/ConjugateAlgebra.lean) | Constructs the actual $B$-subalgebra $E\subset N$ from finitely many conjugate source coordinates; proves conjugate-polynomial membership, Galois stability, and finite type. Not module-finiteness over $B$. |
| [ConjugateFractionField.lean](../../../General/Galois/ConjugateFractionField.lean) | Identifies the supplied normal closure $N$ as the fraction field of this same $E$, without Keller or descent hypotheses. |
| [ConjugateInvariants.lean](../../../General/Galois/ConjugateInvariants.lean) | Restricts the faithful Galois action, reuses Mathlib's fixed subalgebra for $E^G$, and proves $E$ module-finite over $E^G$. Under separability, membership in $E^G$ means membership in the embedded $K$. Faithfulness is not scheme-theoretic freeness; $E^G=B$ is not claimed. |
| [ConjugateInvariantField.lean](../../../General/Galois/ConjugateInvariantField.lean) | Realizes the same fixed algebra inside $K$ by subalgebra pullback, with a canonical $B$-algebra equivalence under separability. Proves $\mathrm{Frac}(E^G)=K$ with compatible embeddings. |
| [ConjugateInvariantFiniteType.lean](../../../General/Galois/ConjugateInvariantFiniteType.lean) | Artin–Tate proves finite type of the same $E^G/B$, without Keller or separability assumptions. This is not module-finiteness over $B$. |
| [ConjugateUnramified.lean](../../../General/Keller/ConjugateUnramified.lean) | Keller étaleness on every generating source sheet gives unramifiedness of the actual $E/B$. No flatness, selected-component identification, or boundary vanishing is inferred. |
| [ConjugateInvariantOpen.lean](../../../General/Keller/ConjugateInvariantOpen.lean) | Under Keller, quasi-finiteness descends to $E^G/B$. Under separability, birational Zariski main gives the actual open immersion and affine target open $U_F$. No supplied open-model hypothesis or free-action comparison is used. |
| [GaloisDescent.lean](GaloisDescent.lean) and the existing Galois collision/secant API | Descent is equivalent to normality of $L/K$; its failure gives a moved-coordinate witness. Secant identities do not require descent. |
| [CollisionVanishing.lean](../../../General/Galois/CollisionVanishing.lean) | Vanishing identifies every conjugate source coordinate with its marked coordinate, hence gives normality of $L/K$. The shared proof needs neither Keller nor separability and has no literature input. |
| [SimplePole.lean](../../../General/Normalization/SimplePole.lean) and [ConormalDerivation.lean](../../../General/Normalization/ConormalDerivation.lean) | Prove the finite boundary-ideal criterion, without ramification dependencies or an assumed Keller vanishing statement. |
| [ConjugateInvariantBoundary.lean](../../../General/Keller/ConjugateInvariantBoundary.lean) | Constructs the actual radical complement ideal $\mathfrak b_F\subset B$, proves it nonzero and finitely generated, and identifies $\mathfrak b_F=B$ with $U_F=\mathrm{Spec}B$. Nonzero does not mean a nonempty boundary. |
| [ConjugateInvariantConormal.lean](../../../General/Keller/ConjugateInvariantConormal.lean) | Transports the target coordinate partials to $B$ and applies the existing conormal construction to $\mathfrak b_F$, with a finitely generated conormal module. In characteristic zero, all components vanish iff $U_F=\mathrm{Spec}B$. No principal equation is needed for this criterion; its actual vanishing remains open. |
| [FiniteConormalTest.lean](../../../General/Normalization/FiniteConormalTest.lean) and the actual generator test in `ConjugateInvariantConormal` | A finite ideal generating set tests the two planar component maps by its first derivatives modulo $\mathfrak b_F$. Finite generation supplies such a set internally; this does not prove the tests succeed. |
| [ConjugateInvariantFiniteness.lean](../../../General/Keller/ConjugateInvariantFiniteness.lean) | Empty actual target boundary makes the base-to-fixed-algebra map bijective. The all-conjugate algebra, and then its embedded polynomial source, are module-finite over $B$. Boundary emptiness is an explicit premise. |
| [FiniteBoundary.lean](FiniteBoundary.lean) | Source finiteness fills the intermediate normalization by [FiniteSource.lean](../../../General/Normalization/FiniteSource.lean). The existing no-hidden-inertia endpoint then gives $\mathrm{Obs}(F)=0$, with `BranchPurityA2` and `AffinePlaneFiniteEtaleRigidity` explicit. This module imports no custom literature axioms. |
| [BoundaryCriterion.lean](BoundaryCriterion.lean) | Packages $\mathrm{Obs}(F)=0\iff\mathfrak b_F=B$, with equivalent fixed-source regularity and conormal formulations. The reverse bridge in [ConjugateInvariantObstruction.lean](../../../General/Keller/ConjugateInvariantObstruction.lean) comes directly from collision equations, not automorphism detection. Only the converse geometric inputs above remain. |
| [SourceIntersection.lean](../../../General/Keller/SourceIntersection.lean) and [ConjugateInvariantSource.lean](../../../General/Keller/ConjugateInvariantSource.lean) | Visible source divisors give divisibility reflection and $A\cap K=B$. Consequently a fixed-algebra element regular on the marked source belongs to $B$. This does not prove that all of $E^G$ is source-regular. |
| [ConjugateInvariantCriterion.lean](../../../General/Keller/ConjugateInvariantCriterion.lean) | Characterizes source regularity of every fixed element by surjectivity of $B\to E^G$, equivalently $\mathfrak b_F=B$. This packages the displayed equivalence using the actual embeddings; no characteristic-zero, purity, or Galois-rigidity input is used for the criterion itself. |
| Keller--secant comparison | Research alternative: derive the conormal memberships using the full polynomial source. Neither Galois symmetry nor localization stability supplies them. |

The [comparison audit](OBJECT-BENCH.md#galois--secant-boundary-comparison-audit-2026-09-19)
tests the proposed comparison against a proper-open Galois example. The
finite-lattice, conductor, trace, and ramification routes remain research
alternatives, not additional established consequences of the criteria.
Their negative controls are retained.

## Targets and alternative routes

The Galois-descent characterization is stated in
[GaloisDescent.lean](GaloisDescent.lean): membership of every normal-closure
conjugate of each source coordinate in the marked original field $L$
is equivalent to normality of $L/K$. Keller--Galois rigidity then gives
invertibility and obstruction vanishing; the planar value can now be
constructed from the two geometric inputs above. The descent target
itself remains unproved. Normality of the
already-constructed closure $N/K$ does not supply it.
Failure of descent now supplies an explicit conjugate coordinate moved by
an element fixing the original field. For the resulting off-diagonal
collision, the coordinate differences already generate the unit ideal:
no prime on the simultaneous regularity domain supplies a common center.
The [common-center test](OBJECT-BENCH.md#common-center-and-all-conjugate-ring-test-2026-09-19)
records this verified consequence and why adjoining all conjugate rings
can remove a base divisor rather than preserve the entire source. The
[descent audit](OBJECT-BENCH.md#descent-witness-and-frame-audit-2026-09-19)
also records why extended-frame compatibility alone does not prove descent.
The alternative [simple-pole test](OBJECT-BENCH.md#reduced-boundary-and-simple-pole-test-2026-09-19)
uses the reduced deleted-boundary ideal rather than a chosen finite
coefficient denominator. The shared algebra in
[SimplePole.lean](../../../General/Normalization/SimplePole.lean) identifies
preservation of its simple-pole module with preservation of the principal
ideal. Actual secant-frame preservation of that module remains unproved;
the proper-open diagnostic exhibits pole growth even with determinant one.
This test stays finite: one module generator and its two first
target derivatives, equivalently two remainders modulo the boundary
equation. It does not ask for a bound on an entire pole tower.
The corresponding conormal components are now constructed in
[ConormalDerivation.lean](../../../General/Normalization/ConormalDerivation.lean)
using Mathlib's existing `Ideal.Cotangent`; their vanishing is equivalent
to preservation of the ideal. The actual Keller boundary and its
componentwise criterion are now instantiated. Its principal presentation
remains unformalized, but is not needed for this intrinsic criterion.
The finite-generator tests and their conditional route to obstruction
vanishing now use those same actual objects. The missing mathematical
step, if pursuing this route further, is preservation of the actual
boundary ideal, not the existence of a generating set or another choice
of normalization model. The current characterization is complete without
claiming that these tests succeed universally. The proposed
[finite derivative lattice](OBJECT-BENCH.md#finite-derivative-lattice-proposal-2026-09-20)
remains on the object bench.

The ramification proof-spine entry point is
[`CollisionIdeals.Planar.Research.Vanishing.Ramification`](Ramification.lean).
It uses the finite normalized cover constructed from the Keller condition,
without the larger collision model's conjugate-sheet index realization.
The local approach uses the shared base-transversality theorem and
[BaseFrame.lean](BaseFrame.lean) to select the corresponding target derivative;
preservation of the boundary local ring remains an open input.
The comparison tests are [FrameDenominator.lean](FrameDenominator.lean),
[ConductorComparison.lean](ConductorComparison.lean), and the matrix-only
reduction [SecantReduction.lean](SecantReduction.lean). The bench distinguishes
these algebraic results from the still-missing Keller-specific comparison.
[ConductorLocalization.lean](ConductorLocalization.lean) removes a supplied
outside-prime conductor from the comparison. The exact generator derivative
test is in [GeneratorDerivative.lean](GeneratorDerivative.lean): its
coefficientwise numerator must lie in the monogenic-Jacobian multiple of
the local lattice. This is a proved algebraic criterion, not a proof that
the actual Keller frame satisfies it.
The global polynomial input isolated next is
[General/Keller/DivisorVisibility.lean](../../../General/Keller/DivisorVisibility.lean):
every height-one base prime has a visible unramified source divisor.
[VisibleConjugateCenter.lean](../../../General/Normalization/VisibleConjugateCenter.lean)
transports it to an actual conjugate center by lying-over and Galois
transitivity. With the existing local-index realization supplied, it gives
an inertia-fixed sheet, not triviality of inertia. The
[localized Jacobian diagnostic](LocalizedJacobianDiagnostic.lean) tests why
constant Jacobian identities on a proper open cannot replace that global
input. Its cubic variant reaches every complex target point and still has
a non-polynomial target derivative. The
[visible--hidden secant test](OBJECT-BENCH.md#visible--hidden-secant-test-2026-09-19)
records why the mixed identities do not yet supply the missing bound.
Existence of one visible sheet still does not control all sheets.
The direct local exclusion is in [LocalCollision.lean](LocalCollision.lean)
and [InertiaCoordinates.lean](InertiaCoordinates.lean): residue agreement
forces a local Keller collision pair to coincide, so an inertia-moved sheet
has a source coordinate outside the valuation ring. This uses no supplied
ramification-index realization. Proving that the required coordinates are
regular remains open; closure and extension of the projector do not imply
it. The [closure audit](OBJECT-BENCH.md#local-collision-and-closure-audit-2026-09-19)
also records a polynomial pole-order estimate, explicitly separate from
the Lean results and from generic degree two.
The [original-extension pole test](OBJECT-BENCH.md#original-extension-pole-test-2026-09-19)
works before taking the normal closure: regularity at all height-one
primes of $S=\mathrm{IntCl}_B(L)$ would give $A=S$ and finiteness.
Monomial valuations in polynomial source coordinates are excluded by the
nonsingular linear part. Cancellation for nonmonomial valuations remains
uncontrolled; a local Jacobian unit or a regular two-form is insufficient.
The broader object bench remains accessible through
`CollisionIdeals.Planar.Research`; the public `CollisionIdeals.Planar` import
remains separate.

When updating the spine or bench, distinguish a proved conditional implication
from a proof of its hypotheses. Record theorem inputs and build status; do not
promote a candidate merely because it is constructed or has a nonzero finite
denominator. The broader research endpoints remain separate from the frozen
submission snapshots; no resubmission follows merely from a new construction.
