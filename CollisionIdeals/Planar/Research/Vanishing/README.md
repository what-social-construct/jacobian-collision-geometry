# Planar vanishing

The research goal is the original obstruction-vanishing statement:

\[
F\text{ planar Keller}\quad\Longrightarrow\quad
\operatorname{Obs}(F)=I_\Delta/I_R(F)=0.
\]

The existing Lean name is `CollisionIdeals.PlanarVanishing`, in
[Statements/Vanishing.lean](../../Statements/Vanishing.lean). It is a theorem
target, not an axiom or a proved theorem. There is no generic-degree restriction
in this target. Generic degree two is a settled special case conditional on
the stated Keller--Galois rigidity input, not the scope of the full program.

The current findings are exact characterizations. Identifying the shared
rings with their images in the marked normal closure gives

\[
E^G\cap A=B,\qquad
E^G\subseteq A\ \Longleftrightarrow\ E^G=B
\ \Longleftrightarrow\ \mathfrak b_F=B.
\]

The last condition means empty target boundary. It is not the assertion
that the collision obstruction ideal is the unit ideal: that separate
ideal is \(\operatorname{Obs}(F)\subseteq C_F\), whose desired value is
zero. Conjugate-coordinate descent is separately equivalent to normality
of \(L/K\); the stated Keller--Galois rigidity input then gives
invertibility and obstruction vanishing. The source-regularity and
conormal criteria characterize boundary emptiness without proving it
for every Keller map.

The complementary normal-closure condition is also packaged map by map:
\(\operatorname{Obs}(F)=0\iff L/K\text{ normal}\iff N=\iota(L)\iff H=1\).
The planar obstruction equivalence takes only Keller--Galois rigidity,
in the normality-to-vanishing direction. The other direction follows
directly from collision-coordinate equality, without Ax--Grothendieck;
the shared closure/subgroup equivalences are field-theoretic.
Constructing \(N\) alone proves none of these conditions.

The separate [boundary criterion](BoundaryCriterion.lean) now connects
the actual boundary tests directly to \(\operatorname{Obs}(F)=0\).
Vanishing collision equations identify all conjugate source coordinates,
so the implication to source regularity and empty boundary needs neither
Ax--Grothendieck nor Galois rigidity. The converse retains exactly
`BranchPurityA2` and `AffinePlaneFiniteEtaleRigidity` from the existing
finite-boundary endpoint. No universal vanishing assertion is added.

Maintain two working documents:

- [Primary proof spine](PROOF-SPINE.md): established characterizations and
  conditional routes to obstruction vanishing, with each input visible.
- [Object bench](OBJECT-BENCH.md): constructions, alternative routes, and
  negative controls; what each contributes and what would justify promoting
  it into the primary argument.

Ramification vanishing, trivial inertia, and trace landing are possible
intermediate results. They do not replace the central goal or receive the
name `PlanarVanishing`.

This folder reuses the existing Lean objects, notation, and namespaces rather
than making parallel definitions for a proof sketch or manuscript.

## Active dependency map

| Piece | Role and current boundary |
| --- | --- |
| [ConjugateAlgebra.lean](../../../General/Galois/ConjugateAlgebra.lean) | Constructs the actual \(B\)-subalgebra \(E\subset N\) from finitely many conjugate source coordinates; proves conjugate-polynomial membership, Galois stability, and finite type. Not module-finiteness over \(B\). |
| [ConjugateFractionField.lean](../../../General/Galois/ConjugateFractionField.lean) | Identifies the supplied normal closure \(N\) as the fraction field of this same \(E\), without Keller or descent hypotheses. |
| [ConjugateInvariants.lean](../../../General/Galois/ConjugateInvariants.lean) | Restricts the faithful Galois action, reuses Mathlib's fixed subalgebra for \(E^G\), and proves \(E\) module-finite over \(E^G\). Under separability, membership in \(E^G\) means membership in the embedded \(K\). Faithfulness is not scheme-theoretic freeness; \(E^G=B\) is not claimed. |
| [ConjugateInvariantField.lean](../../../General/Galois/ConjugateInvariantField.lean) | Realizes the same fixed algebra inside \(K\) by subalgebra pullback, with a canonical \(B\)-algebra equivalence under separability. Proves \(\operatorname{Frac}(E^G)=K\) with compatible embeddings. |
| [ConjugateInvariantFiniteType.lean](../../../General/Galois/ConjugateInvariantFiniteType.lean) | Artin–Tate proves finite type of the same \(E^G/B\), without Keller or separability assumptions. This is not module-finiteness over \(B\). |
| [ConjugateUnramified.lean](../../../General/Keller/ConjugateUnramified.lean) | Keller étaleness on every generating source sheet gives unramifiedness of the actual \(E/B\). No flatness, selected-component identification, or boundary vanishing is inferred. |
| [ConjugateInvariantOpen.lean](../../../General/Keller/ConjugateInvariantOpen.lean) | Under Keller, quasi-finiteness descends to \(E^G/B\). Under separability, birational Zariski main gives the actual open immersion and affine target open \(U_F\). No supplied open-model hypothesis or free-action comparison is used. |
| [GaloisDescent.lean](GaloisDescent.lean) and the existing Galois collision/secant API | Descent is equivalent to normality of \(L/K\); its failure gives a moved-coordinate witness. Secant identities do not require descent. |
| [CollisionVanishing.lean](../../../General/Galois/CollisionVanishing.lean) | Vanishing identifies every conjugate source coordinate with its marked coordinate, hence gives normality of \(L/K\). The shared proof needs neither Keller nor separability and has no literature input. |
| [SimplePole.lean](../../../General/Normalization/SimplePole.lean) and [ConormalDerivation.lean](../../../General/Normalization/ConormalDerivation.lean) | Prove the finite boundary-ideal criterion, without ramification dependencies or an assumed Keller vanishing statement. |
| [ConjugateInvariantBoundary.lean](../../../General/Keller/ConjugateInvariantBoundary.lean) | Constructs the actual radical complement ideal \(\mathfrak b_F\subset B\), proves it nonzero and finitely generated, and identifies \(\mathfrak b_F=B\) with \(U_F=\operatorname{Spec}B\). Nonzero does not mean a nonempty boundary. |
| [ConjugateInvariantConormal.lean](../../../General/Keller/ConjugateInvariantConormal.lean) | Transports the target coordinate partials to \(B\) and applies the existing conormal construction to \(\mathfrak b_F\), with a finitely generated conormal module. In characteristic zero, all components vanish iff \(U_F=\operatorname{Spec}B\). No principal equation is needed for this criterion; its actual vanishing remains open. |
| [FiniteConormalTest.lean](../../../General/Normalization/FiniteConormalTest.lean) and the actual generator test in `ConjugateInvariantConormal` | A finite ideal generating set tests the two planar component maps by its first derivatives modulo \(\mathfrak b_F\). Finite generation supplies such a set internally; this does not prove the tests succeed. |
| [ConjugateInvariantFiniteness.lean](../../../General/Keller/ConjugateInvariantFiniteness.lean) | Empty actual target boundary makes the base-to-fixed-algebra map bijective. The all-conjugate algebra, and then its embedded polynomial source, are module-finite over \(B\). Boundary emptiness is an explicit premise. |
| [FiniteBoundary.lean](FiniteBoundary.lean) | Source finiteness fills the intermediate normalization by [FiniteSource.lean](../../../General/Normalization/FiniteSource.lean). The existing no-hidden-inertia endpoint then gives \(\operatorname{Obs}(F)=0\), with `BranchPurityA2` and `AffinePlaneFiniteEtaleRigidity` explicit. This module imports no custom literature axioms. |
| [BoundaryCriterion.lean](BoundaryCriterion.lean) | Packages \(\operatorname{Obs}(F)=0\iff\mathfrak b_F=B\), with equivalent fixed-source regularity and conormal formulations. The reverse bridge in [ConjugateInvariantObstruction.lean](../../../General/Keller/ConjugateInvariantObstruction.lean) comes directly from collision equations, not automorphism detection. Only the converse geometric inputs above remain. |
| [SourceIntersection.lean](../../../General/Keller/SourceIntersection.lean) and [ConjugateInvariantSource.lean](../../../General/Keller/ConjugateInvariantSource.lean) | Visible source divisors give divisibility reflection and \(A\cap K=B\). Consequently a fixed-algebra element regular on the marked source belongs to \(B\). This does not prove that all of \(E^G\) is source-regular. |
| [ConjugateInvariantCriterion.lean](../../../General/Keller/ConjugateInvariantCriterion.lean) | Characterizes source regularity of every fixed element by surjectivity of \(B\to E^G\), equivalently \(\mathfrak b_F=B\). This packages the displayed equivalence using the actual embeddings; no characteristic-zero, purity, or Galois-rigidity input is used for the criterion itself. |
| Keller--secant comparison | Research alternative: derive the conormal memberships using the full polynomial source. Neither Galois symmetry nor localization stability supplies them. |

The [comparison audit](OBJECT-BENCH.md#galois--secant-boundary-comparison-audit-2026-09-19)
tests the proposed comparison against a proper-open Galois example. The
finite-lattice, conductor, trace, and ramification routes remain research
alternatives, not additional established consequences of the criteria.
Their negative controls are retained.

## Targets and alternative routes

The Galois-descent characterization is stated in
[GaloisDescent.lean](GaloisDescent.lean): membership of every normal-closure
conjugate of each source coordinate in the marked original field \(L\)
is equivalent to normality of \(L/K\). The explicit
Keller--Galois rigidity input then gives invertibility and obstruction
vanishing. The descent target itself remains unproved. Normality of the
already-constructed closure \(N/K\) does not supply it.
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
primes of \(S=\operatorname{IntCl}_B(L)\) would give \(A=S\) and finiteness.
Monomial valuations in polynomial source coordinates are excluded by the
nonsingular linear part. Cancellation for nonmonomial valuations remains
uncontrolled; a local Jacobian unit or a regular two-form is insufficient.
The broader object bench remains accessible through
`CollisionIdeals.Planar.Research`; the public `CollisionIdeals.Planar` import
remains separate.

When updating the spine or bench, distinguish a proved conditional implication
from a proof of its hypotheses. Record theorem inputs and build status; do not
promote a candidate merely because it is constructed or has a nonzero finite
denominator. Both submissions remain on hold pending the remaining theorem.
