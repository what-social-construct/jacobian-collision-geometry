import CollisionIdeals.General.Galois.ConjugateInvariants
import CollisionIdeals.General.Normalization.Finiteness
import Mathlib.RingTheory.Adjoin.Tower

/-!
# Finite type of the all-conjugate fixed algebra

The actual all-conjugate algebra is of finite type over the Noetherian
coordinate-image algebra and finite as a module over its fixed algebra.
Artin--Tate therefore makes that same fixed algebra of finite type over
the coordinate-image algebra. No Keller or separability hypothesis is
needed, and no module-finiteness over the coordinate-image algebra is asserted.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ}
variable {F : PolynomialSelfMap k n}
variable {N : Type u} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 80000 in
/-- Artin--Tate applied to the actual fixed subalgebra. This is finite
type over the coordinate-image algebra, not module-finiteness over it. -/
theorem polynomialConjugateInvariantAlgebra_finiteType
    (D : PolynomialNormalClosureData F N) :
    Algebra.FiniteType (PolynomialImageAlgebra F)
      (polynomialConjugateInvariantAlgebra D) := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI := polynomialImageAlgebra_isNoetherianRing F
  letI := polynomialConjugateAlgebra_finiteType D
  letI := polynomialConjugateAlgebra_finite_over_invariants D
  letI : IsScalarTower (PolynomialImageAlgebra F)
      (polynomialConjugateInvariantAlgebra D) (polynomialConjugateAlgebra D) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨fg_of_fg_of_fg (PolynomialImageAlgebra F)
    (polynomialConjugateInvariantAlgebra D) (polynomialConjugateAlgebra D)
    Algebra.FiniteType.out Module.Finite.fg_top
    (fun _ _ h => Subtype.ext h)⟩

end

end CollisionIdeals
