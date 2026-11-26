import CollisionIdeals.Planar.OffDiagonalGeneric
import CollisionIdeals.Planar.GenericCollisionFinite
import CollisionIdeals.Planar.ExplicitSecant
import CollisionIdeals.Planar.Statements.Vanishing

/-!
# The finite separable comparison square

The marked-root product carries the actual affine off-diagonal projector
to `(0, 1)`. Thus the comparison intertwines multiplication by the affine
projector and projection onto the generic residual factor. This proves
compatibility of the two decompositions, rather than vanishing of either
residual. For a planar Keller map, vanishing is equivalent to generic
degree one.

The comparison follows the distinction in the descendant
`galois-obstruction-theory`: extending a projector and making its image
zero are separate assertions. No declarations from that repository are
imported here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

noncomputable section

open scoped TensorProduct

attribute [local instance high] Algebra.toModule

/-- The generic collision product, with its first factor marked by the
original source inclusion. -/
def planarGenericCollisionEquivMarkedRoot
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F)
    (pb : PowerBasis (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := ℂ) (ι := Fin 2))) :
    let B := polynomialMapImageAlgebra F
    let K := PolynomialBaseFunctionField F
    let L := PolynomialSourceFunctionField (R := ℂ) (ι := Fin 2)
    letI : Algebra B (CollisionRing F) := polynomialImageCollisionAlgebra F
    K ⊗[B] CollisionRing F ≃ₐ[K] L × AdjoinRoot (minpolyDiv K pb.gen) := by
  let K := PolynomialBaseFunctionField F
  let L := PolynomialSourceFunctionField (R := ℂ) (ι := Fin 2)
  letI : FiniteDimensional K L :=
    polynomialSourceFunctionField_finiteDimensional_of_isKeller F hKeller
  letI : Algebra.IsSeparable K L :=
    polynomialSourceFunctionField_isSeparable_of_isKeller F hKeller
  exact (polynomialGenericCollisionEquiv F
    (polynomialGenericSourceTensorMap_surjective_of_finrank_pos F
      (Module.finrank_pos (R := K) (M := L)))).trans
    ((primitiveTensorDecomposition K L pb).restrictScalars K)

/-- The first-projection square is the original generic diagonal square. -/
theorem planarGenericCollisionEquivMarkedRoot_diagonal
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F)
    (pb : PowerBasis (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := ℂ) (ι := Fin 2)))
    (hsurj : Function.Surjective (polynomialGenericSourceTensorMap F)) :
    let K := PolynomialBaseFunctionField F
    let L := PolynomialSourceFunctionField (R := ℂ) (ι := Fin 2)
    (AlgHom.fst K L (AdjoinRoot (minpolyDiv K pb.gen))).comp
      (planarGenericCollisionEquivMarkedRoot F hKeller pb).toAlgHom =
        polynomialGenericCollisionDiagonal F hsurj := by
  let K := PolynomialBaseFunctionField F
  let L := PolynomialSourceFunctionField (R := ℂ) (ι := Fin 2)
  letI : Algebra.IsSeparable K L :=
    polynomialSourceFunctionField_isSeparable_of_isKeller F hKeller
  apply AlgHom.ext
  intro x
  change (primitiveTensorDecomposition K L pb
    (polynomialGenericCollisionEquiv F hsurj x)).1 =
      polynomialGenericCollisionDiagonal F hsurj x
  rw [fst_primitiveTensorDecomposition_apply]
  exact AlgHom.congr_fun
    (polynomialGenericCollisionEquiv_intertwines_diagonal F hsurj) x

/-- Every affine off-diagonal projector becomes the unit of the generic
residual factor. The residual ring is allowed to be the zero ring. -/
theorem planarGenericCollisionEquivMarkedRoot_projector
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F)
    (pb : PowerBasis (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := ℂ) (ι := Fin 2)))
    (q : CollisionRing F) (hq : IsCollisionOffDiagonalProjector F q) :
    let B := polynomialMapImageAlgebra F
    let K := PolynomialBaseFunctionField F
    letI : Algebra B (CollisionRing F) := polynomialImageCollisionAlgebra F
    planarGenericCollisionEquivMarkedRoot F hKeller pb ((1 : K) ⊗ₜ[B] q) = (0, 1) := by
  let B := polynomialMapImageAlgebra F
  let K := PolynomialBaseFunctionField F
  let L := PolynomialSourceFunctionField (R := ℂ) (ι := Fin 2)
  letI : Algebra B (CollisionRing F) := polynomialImageCollisionAlgebra F
  letI : Algebra B (OffDiagonalRing F) := polynomialImageOffDiagonalAlgebra F
  letI : FiniteDimensional K L :=
    polynomialSourceFunctionField_finiteDimensional_of_isKeller F hKeller
  have hsurj := polynomialGenericSourceTensorMap_surjective_of_finrank_pos F
    (Module.finrank_pos (R := K) (M := L))
  let e := planarGenericCollisionEquivMarkedRoot F hKeller pb
  have hdiag := planarGenericCollisionEquivMarkedRoot_diagonal F hKeller pb hsurj
  have hqzero : collisionDiagonal F q = 0 := by
    change q ∈ RingHom.ker (collisionDiagonal F).toRingHom
    rw [collisionDiagonal_ker, hq.2]
    exact Ideal.mem_span_singleton_self q
  have hqone : collisionToOffDiagonal F q = 1 := by
    have hm : 1 - q ∈ RingHom.ker (collisionToOffDiagonal F).toRingHom := by
      rw [collisionToOffDiagonal_ker_eq_span_complement F q hq]
      exact Ideal.mem_span_singleton_self _
    have hz : collisionToOffDiagonal F (1 - q) = 0 := hm
    exact (sub_eq_zero.mp (by simpa only [map_sub, map_one] using hz)).symm
  apply Prod.ext
  · have h := AlgHom.congr_fun hdiag ((1 : K) ⊗ₜ[B] q)
    change (e ((1 : K) ⊗ₜ[B] q)).1 =
      polynomialGenericCollisionDiagonal F hsurj ((1 : K) ⊗ₜ[B] q) at h
    change (e ((1 : K) ⊗ₜ[B] q)).1 = 0
    rw [h]
    change polynomialGenericSourceEquiv F hsurj
      ((1 : K) ⊗ₜ[B] collisionDiagonal F q) = 0
    rw [hqzero, TensorProduct.tmul_zero, map_zero]
  · have h := polynomialGenericOffDiagonalEquivOfProduct_apply
      F q hq hsurj e hdiag ((1 : K) ⊗ₜ[B] q)
    have hgeneric : polynomialGenericCollisionToOffDiagonal F
        ((1 : K) ⊗ₜ[B] q) = 1 := by
      change (1 : K) ⊗ₜ[B] collisionToOffDiagonal F q = 1
      rw [hqone, ← Algebra.TensorProduct.one_def]
    rw [hgeneric, map_one] at h
    exact h.symm

/-- The explicit secant projector is the generic residual selector. -/
theorem planarGenericCollisionEquivMarkedRoot_explicitProjector
    (F : PlanarPolynomialMap) (c : ℂ) (hc : c ≠ 0)
    (hJacobian : planarJacobianDet F = MvPolynomial.C c)
    (pb : PowerBasis (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := ℂ) (ι := Fin 2))) :
    let B := polynomialMapImageAlgebra F
    let K := PolynomialBaseFunctionField F
    letI : Algebra B (CollisionRing F) := polynomialImageCollisionAlgebra F
    planarGenericCollisionEquivMarkedRoot F ⟨c, hc, hJacobian⟩ pb
      ((1 : K) ⊗ₜ[B] Planar.ExplicitSecant.collisionProjector F c hc) = (0, 1) :=
  planarGenericCollisionEquivMarkedRoot_projector F ⟨c, hc, hJacobian⟩ pb _
    (Planar.ExplicitSecant.collisionProjector_isProjector F c hc hJacobian)

/-- The comparison square intertwines multiplication by the affine
projector with the generic residual projection. -/
theorem planarGenericCollision_projector_square
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F)
    (pb : PowerBasis (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := ℂ) (ι := Fin 2)))
    (q : CollisionRing F) (hq : IsCollisionOffDiagonalProjector F q) :
    let B := polynomialMapImageAlgebra F
    let K := PolynomialBaseFunctionField F
    letI : Algebra B (CollisionRing F) := polynomialImageCollisionAlgebra F
    let evaluation := (planarGenericCollisionEquivMarkedRoot F hKeller pb).toLinearMap
    evaluation.comp (LinearMap.mulLeft K ((1 : K) ⊗ₜ[B] q)) =
      (LinearMap.mulLeft K (0, 1)).comp evaluation := by
  let B := polynomialMapImageAlgebra F
  let K := PolynomialBaseFunctionField F
  letI : Algebra B (CollisionRing F) := polynomialImageCollisionAlgebra F
  apply LinearMap.ext
  intro z
  change planarGenericCollisionEquivMarkedRoot F hKeller pb
      (((1 : K) ⊗ₜ[B] q) * z) =
    (0, 1) * planarGenericCollisionEquivMarkedRoot F hKeller pb z
  rw [map_mul, planarGenericCollisionEquivMarkedRoot_projector F hKeller pb q hq]

/-- The generic residual is finite-dimensional; this asserts no affine
finiteness over the target. -/
theorem planarGenericOffDiagonal_finiteDimensional
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F) :
    let B := polynomialMapImageAlgebra F
    let K := PolynomialBaseFunctionField F
    letI : Algebra B (OffDiagonalRing F) := polynomialImageOffDiagonalAlgebra F
    FiniteDimensional K (K ⊗[B] OffDiagonalRing F) := by
  let B := polynomialMapImageAlgebra F
  let K := PolynomialBaseFunctionField F
  let L := PolynomialSourceFunctionField (R := ℂ) (ι := Fin 2)
  letI : Algebra B (CollisionRing F) := polynomialImageCollisionAlgebra F
  letI : Algebra B (OffDiagonalRing F) := polynomialImageOffDiagonalAlgebra F
  letI : FiniteDimensional K L :=
    polynomialSourceFunctionField_finiteDimensional_of_isKeller F hKeller
  letI := planarGenericCollision_finiteDimensional F (Module.finrank_pos (R := K) (M := L))
  exact Module.Finite.of_surjective (polynomialGenericCollisionToOffDiagonal F).toLinearMap
    (polynomialGenericCollisionToOffDiagonal_surjective F)

/-- Finite separability identifies the remaining vanishing target exactly:
the generic degree must be one. No rigidity theorem is used. -/
theorem planarObstructionIdeal_eq_bot_iff_genericDegree_eq_one
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F) :
    obstructionIdeal F = ⊥ ↔ planarGenericDegree F = 1 := by
  let B := polynomialMapImageAlgebra F
  let K := PolynomialBaseFunctionField F
  let L := PolynomialSourceFunctionField (R := ℂ) (ι := Fin 2)
  letI : Algebra B (OffDiagonalRing F) := polynomialImageOffDiagonalAlgebra F
  letI : FiniteDimensional K L :=
    polynomialSourceFunctionField_finiteDimensional_of_isKeller F hKeller
  letI := planarGenericOffDiagonal_finiteDimensional F hKeller
  have hpos : 0 < planarGenericDegree F := Module.finrank_pos (R := K) (M := L)
  have hdetect : obstructionIdeal F = ⊥ ↔ Subsingleton (K ⊗[B] OffDiagonalRing F) :=
    planarObstructionIdeal_eq_bot_iff_genericOffDiagonalRing_subsingleton F hKeller
  have hdim : Module.finrank K (K ⊗[B] OffDiagonalRing F) =
      planarGenericDegree F * (planarGenericDegree F - 1) :=
    planarGenericOffDiagonal_finrank F hKeller
  rw [hdetect, ← Module.finrank_zero_iff (R := K), hdim]
  constructor
  · intro hz
    rcases Nat.mul_eq_zero.mp hz with hz | hz <;> omega
  · intro h
    simp [h]

/-- The explicit projector vanishes exactly in generic degree one. -/
theorem planarExplicitProjector_eq_zero_iff_genericDegree_eq_one
    (F : PlanarPolynomialMap) (c : ℂ) (hc : c ≠ 0)
    (hJacobian : planarJacobianDet F = MvPolynomial.C c) :
    Planar.ExplicitSecant.collisionProjector F c hc = 0 ↔
      planarGenericDegree F = 1 :=
  (collisionOffDiagonalProjector_eq_zero_iff_obstructionIdeal_eq_bot F _
    (Planar.ExplicitSecant.collisionProjector_isProjector F c hc hJacobian)).trans
    (planarObstructionIdeal_eq_bot_iff_genericDegree_eq_one F ⟨c, hc, hJacobian⟩)

/-- The unrestricted planar target still requires degree one for every
Keller map; finite separability alone does not supply this assertion. -/
theorem planarVanishing_iff_forall_genericDegree_eq_one :
    PlanarVanishing ↔ ∀ F : PlanarPolynomialMap,
      IsPlanarKeller F → planarGenericDegree F = 1 := by
  constructor
  · intro h F hKeller
    exact (planarObstructionIdeal_eq_bot_iff_genericDegree_eq_one F hKeller).mp (h F hKeller)
  · intro h F hKeller
    exact (planarObstructionIdeal_eq_bot_iff_genericDegree_eq_one F hKeller).mpr (h F hKeller)

end

end CollisionIdeals
