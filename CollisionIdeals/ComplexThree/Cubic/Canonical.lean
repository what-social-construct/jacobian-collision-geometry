import CollisionIdeals.ComplexThree.Cubic.Criteria
import CollisionIdeals.ComplexThree.Cubic.Main
import CollisionIdeals.General.Galois.CanonicalNormalClosure
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Cubic collisions with the normal closure constructed internally

The manuscript-facing theorem takes only a complex three-dimensional Keller
map of generic degree three and the explicitly stated Keller--Galois rigidity
input. The normal closure, its marked embedding, the primitive power basis,
and generic-source surjectivity are constructed inside the proof.

The arbitrary-normal-closure theorem remains available in `Cubic.Main`.
This wrapper retains the diagonal compatibility and the Galois group of the
same residual field; it does not introduce a new collision or closure object.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

open scoped TensorProduct

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Every complex three-dimensional Keller map of generic degree three has
the diagonal-compatible collision decomposition with its canonical normal
closure and Galois group `S₃`, relative to the stated rigidity theorem.
No normal-closure realization, power basis, or nonnormality proof is an input. -/
theorem complexThreeGenericDegreeThreeS3Collision
    (hRigidity : ComplexKellerGaloisRigidity 3)
    (F : ComplexThreePolynomialMap)
    (hKeller : IsComplexThreeKeller F)
    (hDegree : Module.finrank (ComplexThreeBaseFunctionField F)
      ComplexThreeSourceFunctionField = 3) :
    let K := ComplexThreeBaseFunctionField F
    let L := ComplexThreeSourceFunctionField
    let N := CanonicalNormalClosure K L
    let hsurj := polynomialGenericSourceTensorMap_surjective_of_finrank_pos
      F (by rw [hDegree]; norm_num)
    letI : Algebra (polynomialMapImageAlgebra F) (CollisionRing F) :=
      polynomialImageCollisionAlgebra F
    IsComplexThreeJacobianCounterexample F ∧
      obstructionIdeal F ≠ ⊥ ∧
      collisionIdeal F < diagonalIdeal (R := ℂ) (ι := Fin 3) ∧
      ∃ e : (K ⊗[polynomialMapImageAlgebra F] CollisionRing F) ≃ₐ[K] L × N,
        (AlgHom.fst K L N).comp e.toAlgHom =
          polynomialGenericCollisionDiagonal F hsurj ∧
        Nonempty ((N ≃ₐ[K] N) ≃* Equiv.Perm (Fin 3)) := by
  let K := ComplexThreeBaseFunctionField F
  let L := ComplexThreeSourceFunctionField
  let N := CanonicalNormalClosure K L
  have hpos : 0 < Module.finrank K L := by
    rw [hDegree]
    norm_num
  letI : FiniteDimensional K L := FiniteDimensional.of_finrank_pos hpos
  letI : Algebra.IsSeparable K L :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  let D : NormalClosureData K L N := canonicalNormalClosureData K L
  letI : Algebra L N := D.embedding.toRingHom.toAlgebra
  letI : IsScalarTower K L N :=
    IsScalarTower.of_algebraMap_eq fun x => (D.embedding.commutes x).symm
  have hmarked : D.embedding = IsScalarTower.toAlgHom K L N := by
    ext x
    rfl
  let pb : PowerBasis K L := Field.powerBasisOfFiniteOfSeparable K L
  have hpbdim : pb.dim = 3 := (PowerBasis.finrank pb).symm.trans hDegree
  have hsurj := polynomialGenericSourceTensorMap_surjective_of_finrank_pos F hpos
  have hNotNormal :=
    complexThree_not_normal_of_finrank_eq_three hRigidity F hKeller hDegree
  letI : Algebra (polynomialMapImageAlgebra F) (CollisionRing F) :=
    polynomialImageCollisionAlgebra F
  obtain ⟨hCounterexample, hObstruction, hStrict, _, ⟨_, witness⟩⟩ :=
    complexThreeCubicS3Collision
      F hKeller N D hmarked hsurj pb hpbdim hNotNormal
  let e : (K ⊗[polynomialMapImageAlgebra F] CollisionRing F) ≃ₐ[K] L × N :=
    (polynomialGenericCollisionEquiv F hsurj).trans
      (witness.genericCollisionEquiv.restrictScalars K)
  refine ⟨hCounterexample, hObstruction, hStrict, e, ?_, ?_⟩
  · apply AlgHom.ext
    intro x
    change
      (witness.genericCollisionEquiv (polynomialGenericCollisionEquiv F hsurj x)).1 =
        polynomialGenericCollisionDiagonal F hsurj x
    calc
      _ = primitiveTensorDiagonal K L (polynomialGenericCollisionEquiv F hsurj x) :=
        AlgHom.congr_fun witness.fst_genericCollisionEquiv _
      _ = polynomialGenericCollisionDiagonal F hsurj x :=
        AlgHom.congr_fun
          (polynomialGenericCollisionEquiv_intertwines_diagonal F hsurj) x
  · exact ⟨witness.galoisGroupEquiv⟩

end

end CollisionIdeals
