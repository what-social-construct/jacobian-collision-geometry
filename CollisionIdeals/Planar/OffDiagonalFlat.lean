import CollisionIdeals.Planar.Secant
import CollisionIdeals.General.Keller.CollisionEtale
import Mathlib.RingTheory.Smooth.Flat

/-!
# Flatness of the planar off-diagonal collision factor

For a planar Keller map, the secant projector splits the collision ring
into its diagonal and off-diagonal factors.  The latter is a retract over
the left polynomial source, so it inherits flatness from the étale
collision ring.  This does not assert finiteness of the off-diagonal factor.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CollisionIdeals

noncomputable section

open MvPolynomial

/-- The off-diagonal collision quotient is flat over the left polynomial
source for a planar Keller map. -/
theorem planarOffDiagonalRing_flat_left
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F) :
    letI : Algebra (SourceRing ℂ (Fin 2)) (OffDiagonalRing F) :=
      ((collisionToOffDiagonal F).comp (collisionLeft F)).toRingHom.toAlgebra
    Module.Flat (SourceRing ℂ (Fin 2)) (OffDiagonalRing F) := by
  let A := SourceRing ℂ (Fin 2)
  let C := CollisionRing F
  let D := PairRing ℂ (Fin 2) ⧸ diagonalIdeal (R := ℂ) (ι := Fin 2)
  let O := OffDiagonalRing F
  letI : Algebra A C := (collisionLeft F).toRingHom.toAlgebra
  letI : Algebra A D :=
    ((Ideal.Quotient.mkₐ ℂ (diagonalIdeal (R := ℂ) (ι := Fin 2))).comp
      (leftRename (R := ℂ) (ι := Fin 2))).toRingHom.toAlgebra
  letI : Algebra A O :=
    ((collisionToOffDiagonal F).comp (collisionLeft F)).toRingHom.toAlgebra
  letI : Algebra.Etale A C :=
    polynomialCollisionRing_etale_left_of_isKeller F hKeller
  obtain ⟨q, hq⟩ := exists_collisionOffDiagonalProjector_of_isPlanarKeller F hKeller
  let eR : C ≃+* D × O := collisionRingEquivDiagonalProdOffDiagonal F q hq
  let e : C ≃ₐ[A] D × O :=
    { eR with
      commutes' := by
        intro a
        apply Prod.ext
        · change (eR (collisionLeft F a)).1 =
            (Ideal.Quotient.mkₐ ℂ (diagonalIdeal (R := ℂ) (ι := Fin 2)))
              (leftRename a)
          rw [collisionLeft_apply]
          rfl
        · change (eR (collisionLeft F a)).2 =
            collisionToOffDiagonal F (collisionLeft F a)
          rw [collisionLeft_apply]
          rfl }
  let i : O →ₗ[A] C := e.toLinearEquiv.symm.toLinearMap.comp (LinearMap.inr A D O)
  let r : C →ₗ[A] O := (LinearMap.snd A D O).comp e.toLinearEquiv.toLinearMap
  have hri : r.comp i = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change (e (e.symm (0, x))).2 = x
    simp
  exact Module.Flat.of_retract i r hri

end

end CollisionIdeals
