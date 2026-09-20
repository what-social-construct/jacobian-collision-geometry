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

Maintain two working documents:

- [Primary proof spine](PROOF-SPINE.md): the shortest currently identified
  route to obstruction vanishing, with each missing premise visible.
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
| [ConjugateAlgebra.lean](../../../General/Galois/ConjugateAlgebra.lean) | Constructs the actual \(B\)-subalgebra \(E\subset N\) from finitely many conjugate source coordinates; proves conjugate-polynomial membership, Galois stability, and finite type. Not module-finiteness. |
| [GaloisDescent.lean](GaloisDescent.lean) and the existing Galois collision/secant API | Descent is equivalent to normality of \(L/K\); its failure gives a moved-coordinate witness. Secant identities do not require descent. |
| [SimplePole.lean](../../../General/Normalization/SimplePole.lean) and [ConormalDerivation.lean](../../../General/Normalization/ConormalDerivation.lean) | Prove the finite boundary-ideal criterion, without ramification dependencies or an assumed Keller vanishing statement. |
| Actual invariant open and its reduced boundary | Paper II gives the mathematical construction; its quotient/open identification and boundary ideal are not yet instantiated in Lean. |
| Keller--secant comparison | Still open: prove the two conormal classes vanish using the full polynomial source, not just Galois symmetry or localization stability. |

The [comparison audit](OBJECT-BENCH.md#galois--secant-boundary-comparison-audit-2026-09-19)
tests the last step against a proper-open Galois example. The conductor,
trace, and ramification routes below are alternatives, not extra premises
of this active finite test. Their negative controls are retained.

## Targets and alternative routes

The proposed Galois route is stated in
[GaloisDescent.lean](GaloisDescent.lean): every normal-closure conjugate of
each source coordinate should belong to the marked original field \(L\).
The shared algebra identifies this with normality of \(L/K\); the explicit
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
The next [simple-pole test](OBJECT-BENCH.md#reduced-boundary-and-simple-pole-test-2026-09-19)
uses the reduced deleted-boundary ideal rather than a chosen finite
coefficient denominator. The shared algebra in
[SimplePole.lean](../../../General/Normalization/SimplePole.lean) identifies
preservation of its simple-pole module with preservation of the principal
ideal. Actual secant-frame preservation of that module remains unproved;
the proper-open diagnostic exhibits pole growth even with determinant one.
The active test stays finite: one module generator and its two first
target derivatives, equivalently two remainders modulo the boundary
equation. It does not ask for a bound on an entire pole tower.
The corresponding conormal components are now constructed in
[ConormalDerivation.lean](../../../General/Normalization/ConormalDerivation.lean)
using Mathlib's existing `Ideal.Cotangent`; their vanishing is equivalent
to preservation of the ideal. The actual Keller boundary is still not
instantiated by this general construction.

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
