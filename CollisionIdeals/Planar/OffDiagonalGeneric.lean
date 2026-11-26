import CollisionIdeals.General.Keller.GenericFiniteness
import CollisionIdeals.General.ResidualCollision.GenericComparison
import CollisionIdeals.Planar.GenericDegreeTwo.FunctionField
import CollisionIdeals.Planar.OffDiagonalDetection
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# The generic fiber of the actual planar off-diagonal ring

For a planar Keller map, the secant projector identifies the base change of
the affine first-colon quotient with the marked-root residual algebra. This
compares the actual affine residual with Paper I's generic construction,
without invoking a normalization or ramification hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

noncomputable section

open MvPolynomial Polynomial
open scoped TensorProduct

attribute [local instance high] Algebra.toModule

/-- The actual first-colon quotient, after target-generic base change, is the
algebra of the remaining roots of any marked primitive element. -/
def planarGenericOffDiagonalEquivMarkedRoot
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F)
    (pb : PowerBasis (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := ℂ) (ι := Fin 2))) :
    let B := polynomialMapImageAlgebra F
    let K := PolynomialBaseFunctionField F
    letI : Algebra B (OffDiagonalRing F) := polynomialImageOffDiagonalAlgebra F
    K ⊗[B] OffDiagonalRing F ≃ₐ[K] AdjoinRoot (minpolyDiv K pb.gen) := by
  let B := polynomialMapImageAlgebra F
  let K := PolynomialBaseFunctionField F
  let L := PolynomialSourceFunctionField (R := ℂ) (ι := Fin 2)
  let T := AdjoinRoot (minpolyDiv K pb.gen)
  letI : Algebra B (CollisionRing F) := polynomialImageCollisionAlgebra F
  letI : Algebra B (OffDiagonalRing F) := polynomialImageOffDiagonalAlgebra F
  letI : FiniteDimensional K L :=
    polynomialSourceFunctionField_finiteDimensional_of_isKeller F hKeller
  letI : Algebra.IsSeparable K L :=
    polynomialSourceFunctionField_isSeparable_of_isKeller F hKeller
  have hsurj : Function.Surjective (polynomialGenericSourceTensorMap F) :=
    polynomialGenericSourceTensorMap_surjective_of_finrank_pos F
      (Module.finrank_pos (R := K) (M := L))
  let e : K ⊗[B] CollisionRing F ≃ₐ[K] L × T :=
    (polynomialGenericCollisionEquiv F hsurj).trans
      ((primitiveTensorDecomposition K L pb).restrictScalars K)
  have hdiag : (AlgHom.fst K L T).comp e.toAlgHom =
      polynomialGenericCollisionDiagonal F hsurj := by
    apply AlgHom.ext
    intro x
    change (primitiveTensorDecomposition K L pb
      (polynomialGenericCollisionEquiv F hsurj x)).1 =
      polynomialGenericCollisionDiagonal F hsurj x
    rw [fst_primitiveTensorDecomposition_apply]
    exact AlgHom.congr_fun
      (polynomialGenericCollisionEquiv_intertwines_diagonal F hsurj) x
  let hq := exists_collisionOffDiagonalProjector_of_isPlanarKeller F hKeller
  exact polynomialGenericOffDiagonalEquivOfProduct F hq.choose hq.choose_spec hsurj e hdiag

/-- If the generic degree is `d`, the actual generic residual has dimension
`d * (d - 1)` over the target function field. This is not affine finiteness. -/
theorem planarGenericOffDiagonal_finrank
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F) :
    let B := polynomialMapImageAlgebra F
    let K := PolynomialBaseFunctionField F
    letI : Algebra B (OffDiagonalRing F) := polynomialImageOffDiagonalAlgebra F
    Module.finrank K (K ⊗[B] OffDiagonalRing F) =
      planarGenericDegree F * (planarGenericDegree F - 1) := by
  let B := polynomialMapImageAlgebra F
  let K := PolynomialBaseFunctionField F
  let L := PolynomialSourceFunctionField (R := ℂ) (ι := Fin 2)
  letI : Algebra B (OffDiagonalRing F) := polynomialImageOffDiagonalAlgebra F
  letI : FiniteDimensional K L :=
    polynomialSourceFunctionField_finiteDimensional_of_isKeller F hKeller
  letI : Algebra.IsSeparable K L :=
    polynomialSourceFunctionField_isSeparable_of_isKeller F hKeller
  let pb := Field.powerBasisOfFiniteOfSeparable K L
  let p := minpolyDiv K pb.gen
  have hdim : Module.finrank L (AdjoinRoot p) = Module.finrank K L - 1 := by
    change Module.finrank L (L[X] ⧸ Ideal.span {p}) = Module.finrank K L - 1
    rw [finrank_quotient_span_eq_natDegree, PowerBasis.finrank pb]
    have hp := natDegree_minpolyDiv_succ pb.isIntegral_gen
    rw [pb.natDegree_minpoly] at hp
    change p.natDegree + 1 = pb.dim at hp
    omega
  calc
    Module.finrank K (K ⊗[B] OffDiagonalRing F) =
        Module.finrank K (AdjoinRoot p) :=
      (planarGenericOffDiagonalEquivMarkedRoot F hKeller pb).toLinearEquiv.finrank_eq
    _ = Module.finrank K L * Module.finrank L (AdjoinRoot p) :=
      (Module.finrank_mul_finrank K L (AdjoinRoot p)).symm
    _ = planarGenericDegree F * (planarGenericDegree F - 1) := by
      change Module.finrank K L * Module.finrank L (AdjoinRoot p) =
        Module.finrank K L * (Module.finrank K L - 1)
      rw [hdim]

/-- The actual affine residual is reduced. No nilpotents are lost by
passing to its generic fiber, because the base-change map is injective. -/
theorem planarOffDiagonalRing_isReduced
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F) :
    IsReduced (OffDiagonalRing F) := by
  let B := polynomialMapImageAlgebra F
  let K := PolynomialBaseFunctionField F
  let L := PolynomialSourceFunctionField (R := ℂ) (ι := Fin 2)
  letI : Algebra B (OffDiagonalRing F) := polynomialImageOffDiagonalAlgebra F
  letI : FiniteDimensional K L :=
    polynomialSourceFunctionField_finiteDimensional_of_isKeller F hKeller
  letI : Algebra.IsSeparable K L :=
    polynomialSourceFunctionField_isSeparable_of_isKeller F hKeller
  let pb := Field.powerBasisOfFiniteOfSeparable K L
  let p := minpolyDiv K pb.gen
  have hp : p.Separable := by
    apply ((Polynomial.separable_map (algebraMap K L)).mpr
      (Algebra.IsSeparable.isSeparable K pb.gen)).of_dvd
    exact ⟨Polynomial.X - Polynomial.C pb.gen, (minpolyDiv_spec K pb.gen).symm⟩
  letI : IsReduced (AdjoinRoot p) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp
      (isRadical_iff_span_singleton.mp hp.squarefree.isRadical)
  let e := planarGenericOffDiagonalEquivMarkedRoot F hKeller pb
  letI : IsReduced (K ⊗[B] OffDiagonalRing F) :=
    isReduced_of_injective e.toRingEquiv e.injective
  refine ⟨fun z hz => ?_⟩
  apply planarOffDiagonalRing_injective_genericBaseChange F hKeller
  change (1 : K) ⊗ₜ[B] z = (1 : K) ⊗ₜ[B] (0 : OffDiagonalRing F)
  rw [TensorProduct.tmul_zero]
  obtain ⟨n, hn⟩ := hz
  exact IsNilpotent.eq_zero ⟨n, by
    rw [Algebra.TensorProduct.tmul_pow, one_pow, hn, TensorProduct.tmul_zero]⟩

/-- The planar first-colon residual is already radical over the affine
polynomial pair ring. This does not assert that it is the unit ideal. -/
theorem planarCollisionOffDiagonalIdeal_isRadical
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F) :
    (collisionOffDiagonalIdeal F).IsRadical :=
  (Ideal.isRadical_iff_quotient_reduced _).mpr (planarOffDiagonalRing_isReduced F hKeller)

end

end CollisionIdeals
