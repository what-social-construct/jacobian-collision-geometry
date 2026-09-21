import CollisionIdeals.General.Keller.ConjugateInvariantOpen
import CollisionIdeals.General.Normalization.AffineOpenBoundary

/-!
# The reduced boundary of the actual invariant target open

The boundary ideal is the vanishing ideal of the complement of the existing
target open. It is radical, nonzero, and finitely generated. It is the unit
ideal exactly when that open is the whole target. Nonzero here does not
mean a nonempty boundary: the empty boundary has the unit ideal.

This construction chooses no equation and assumes neither a principal
presentation nor boundary vanishing. The target-base boundary ideal is
distinct from the collision obstruction in the collision coordinate ring.
-/

set_option autoImplicit false

namespace CollisionIdeals

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ}
variable {F : PolynomialSelfMap k n}
variable {N : Type u} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]
variable [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]

/-- The canonical reduced target boundary, using Mathlib's vanishing ideal
of the complement rather than a chosen denominator equation. -/
def polynomialConjugateInvariantBoundaryIdeal
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    Ideal (PolynomialImageAlgebra F) :=
  affineOpenBoundaryIdeal (polynomialConjugateInvariantTargetOpen D hKeller)

/-- The constructed boundary ideal defines the reduced closed complement. -/
theorem polynomialConjugateInvariantBoundaryIdeal_isRadical
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    (polynomialConjugateInvariantBoundaryIdeal D hKeller).IsRadical :=
  affineOpenBoundaryIdeal_isRadical _

/-- Its zero locus is exactly the complement of the already constructed open. -/
theorem polynomialConjugateInvariantBoundaryIdeal_zeroLocus
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    PrimeSpectrum.zeroLocus (polynomialConjugateInvariantBoundaryIdeal D hKeller :
      Set (PolynomialImageAlgebra F)) =
      (polynomialConjugateInvariantTargetOpen D hKeller :
        Set (Spec (.of (PolynomialImageAlgebra F))))ᶜ :=
  affineOpenBoundaryIdeal_zeroLocus _

/-- Empty boundary means the unit ideal, not the zero ideal. -/
theorem polynomialConjugateInvariantBoundaryIdeal_eq_top_iff
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    polynomialConjugateInvariantBoundaryIdeal D hKeller = ⊤ ↔
      polynomialConjugateInvariantTargetOpen D hKeller = ⊤ :=
  affineOpenBoundaryIdeal_eq_top_iff _

set_option synthInstance.maxHeartbeats 80000 in
/-- The actual target open is nonempty, since the fixed algebra is a
subring of a field and hence has a nonempty spectrum. -/
theorem polynomialConjugateInvariantTargetOpen_nonempty
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    (polynomialConjugateInvariantTargetOpen D hKeller :
      Set (Spec (.of (PolynomialImageAlgebra F)))).Nonempty := by
  letI := polynomialConjugateInvariantAlgebra_isOpenImmersion_of_isKeller D hKeller
  change (Set.range (Spec.map (CommRingCat.ofHom
    (algebraMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D))))).Nonempty
  exact Set.range_nonempty _

/-- A proper closed complement has a nonzero vanishing ideal; this does
not assert that the complement is empty. -/
theorem polynomialConjugateInvariantBoundaryIdeal_ne_bot
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    polynomialConjugateInvariantBoundaryIdeal D hKeller ≠ ⊥ :=
  affineOpenBoundaryIdeal_ne_bot_of_nonempty _
    (polynomialConjugateInvariantTargetOpen_nonempty D hKeller)

/-- The actual boundary ideal is finitely generated over the target base. -/
theorem polynomialConjugateInvariantBoundaryIdeal_fg
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    (polynomialConjugateInvariantBoundaryIdeal D hKeller).FG := by
  letI := polynomialImageAlgebra_isNoetherianRing F
  exact IsNoetherian.noetherian _

end

end CollisionIdeals
