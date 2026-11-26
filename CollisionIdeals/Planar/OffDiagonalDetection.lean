import CollisionIdeals.General.ResidualCollision.GenericBaseChange
import CollisionIdeals.Planar.OffDiagonalFlat
import Mathlib.RingTheory.Flat.Stability

/-!
# Generic detection of the planar off-diagonal factor

The actual planar Keller residual quotient is flat over the coordinate-image
algebra. Consequently its map to the target-generic residual algebra is
injective: passing to the target generic point does not discard any portion
of the residual ring when testing for vanishing.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

open scoped TensorProduct

noncomputable section

attribute [local instance high] Algebra.toModule

/-- Flatness over the left source and then over the coordinate image gives
flatness of the actual residual algebra over the original target algebra. -/
theorem planarOffDiagonalRing_flat_over_image
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F) :
    letI : Algebra (polynomialMapImageAlgebra F) (OffDiagonalRing F) :=
      polynomialImageOffDiagonalAlgebra F
    Module.Flat (polynomialMapImageAlgebra F) (OffDiagonalRing F) := by
  let B := polynomialMapImageAlgebra F
  let A := SourceRing ℂ (Fin 2)
  let O := OffDiagonalRing F
  letI : Algebra A O :=
    ((collisionToOffDiagonal F).comp (collisionLeft F)).toRingHom.toAlgebra
  letI : Algebra B O := polynomialImageOffDiagonalAlgebra F
  letI : IsScalarTower B A O := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra.Etale B A := polynomialSource_etale_of_isKeller F hKeller
  letI : Module.Flat A O := planarOffDiagonalRing_flat_left F hKeller
  exact Module.Flat.trans B A O

/-- The affine residual ring embeds canonically into its target generic
fiber. This is an injection, not an assertion of affine finiteness. -/
theorem planarOffDiagonalRing_injective_genericBaseChange
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F) :
    let B := polynomialMapImageAlgebra F
    let K := PolynomialBaseFunctionField F
    letI : Algebra B (OffDiagonalRing F) := polynomialImageOffDiagonalAlgebra F
    Function.Injective (fun z : OffDiagonalRing F => (1 : K) ⊗ₜ[B] z) := by
  let B := polynomialMapImageAlgebra F
  let K := PolynomialBaseFunctionField F
  let O := OffDiagonalRing F
  letI : Algebra B O := polynomialImageOffDiagonalAlgebra F
  letI : Module.Flat B O := planarOffDiagonalRing_flat_over_image F hKeller
  have hi := Module.Flat.rTensor_preserves_injective_linearMap
    (M := O) (Algebra.linearMap B K) (IsFractionRing.injective B K)
  change Function.Injective (fun z : O => (1 : K) ⊗ₜ[B] z)
  intro x y hxy
  apply (_root_.TensorProduct.lid B O).symm.injective
  apply hi
  simpa only [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul,
    Algebra.linearMap_apply, map_one] using hxy

/-- The collision obstruction vanishes precisely when the target-generic
fiber of the actual off-diagonal quotient is the zero ring. -/
theorem planarObstructionIdeal_eq_bot_iff_genericOffDiagonalRing_subsingleton
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F) :
    let B := polynomialMapImageAlgebra F
    let K := PolynomialBaseFunctionField F
    letI : Algebra B (OffDiagonalRing F) := polynomialImageOffDiagonalAlgebra F
    obstructionIdeal F = ⊥ ↔ Subsingleton (K ⊗[B] OffDiagonalRing F) := by
  let B := polynomialMapImageAlgebra F
  let K := PolynomialBaseFunctionField F
  let O := OffDiagonalRing F
  letI : Algebra B O := polynomialImageOffDiagonalAlgebra F
  rw [obstructionIdeal_eq_bot_iff_offDiagonalRing_subsingleton F]
  constructor
  · intro h
    letI : Subsingleton O := h
    have hz : (1 : O) = 0 := Subsingleton.elim _ _
    exact subsingleton_of_zero_eq_one (by
      rw [Algebra.TensorProduct.one_def, hz, TensorProduct.tmul_zero])
  · intro h
    letI : Subsingleton (K ⊗[B] O) := h
    exact (planarOffDiagonalRing_injective_genericBaseChange F hKeller).subsingleton

end

end CollisionIdeals
