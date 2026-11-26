import CollisionIdeals.General.ResidualCollision.DividedDifferenceEvaluation
import CollisionIdeals.General.GenericFiber.FunctionField
import CollisionIdeals.Planar.ExplicitSecant

/-!
# Coordinate relations and the actual secant projector

The product of the two coordinate-relation divided differences is
supported on the diagonal. Its diagonal coefficient is the product of
the two evaluated formal derivatives. No primitive-coordinate theorem,
localization, or Galois invariance premise is used in this comparison.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CollisionIdeals.Planar

noncomputable section

open MvPolynomial

variable (F : PlanarPolynomialMap)

attribute [local instance] polynomialImageCollisionAlgebra

private def sourceLeft : PlanePolynomial →ₐ[polynomialMapImageAlgebra F] CollisionRing F :=
  { (collisionLeft F).toRingHom with commutes' := fun _ => rfl }

private def sourceRight : PlanePolynomial →ₐ[polynomialMapImageAlgebra F] CollisionRing F := by
  refine { (collisionRight F).toRingHom with commutes' := ?_ }
  intro b
  change collisionRight F (b : PlanePolynomial) = collisionLeft F (b : PlanePolynomial)
  apply (collisionImageTensorEquiv F).injective
  rw [collisionImageTensorEquiv_collisionRight, collisionImageTensorEquiv_collisionLeft]
  simpa using (Algebra.TensorProduct.tmul_one_eq_one_tmul
    (A := PlanePolynomial) (B := PlanePolynomial) b).symm

/-- The coefficientwise divided difference of a target-coefficient
relation, evaluated at the two actual copies of source coordinate `i`. -/
def coordinateRelationSecant (H : Polynomial (polynomialMapImageAlgebra F)) (i : Fin 2) :
    CollisionRing F :=
  dividedDifferenceValue H (collisionLeft F (X i)) (collisionRight F (X i))

theorem coordinateRelationSecant_mul_difference
    (H : Polynomial (polynomialMapImageAlgebra F)) (i : Fin 2)
    (hH : Polynomial.aeval (X i : PlanePolynomial) H = 0) :
    coordinateRelationSecant F H i *
      (collisionLeft F (X i) - collisionRight F (X i)) = 0 := by
  rw [coordinateRelationSecant, dividedDifferenceValue_mul_sub]
  have hleft := AlgHom.congr_fun (Polynomial.aeval_algHom (sourceLeft F) (X i)) H
  have hright := AlgHom.congr_fun (Polynomial.aeval_algHom (sourceRight F) (X i)) H
  change Polynomial.aeval (collisionLeft F (X i)) H =
    collisionLeft F (Polynomial.aeval (X i) H) at hleft
  change Polynomial.aeval (collisionRight F (X i)) H =
    collisionRight F (Polynomial.aeval (X i) H) at hright
  rw [hleft, hright, hH, map_zero, map_zero, sub_self]

theorem diagonal_coordinateRelationSecant
    (H : Polynomial (polynomialMapImageAlgebra F)) (i : Fin 2) :
    collisionDiagonal F (coordinateRelationSecant F H i) =
      Polynomial.aeval (X i : PlanePolynomial) H.derivative := by
  change polynomialImageCollisionDiagonal F
    (dividedDifferenceValue H (collisionLeft F (X i)) (collisionRight F (X i))) = _
  rw [map_dividedDifferenceValue]
  change dividedDifferenceValue H (collisionDiagonal F (collisionLeft F (X i)))
    (collisionDiagonal F (collisionRight F (X i))) = _
  rw [collisionDiagonal_collisionLeft,
    collisionDiagonal_collisionRight, dividedDifferenceValue_self]

private theorem mem_annihilator_of_mul_differences_eq_zero
    (w : CollisionRing F)
    (hw : ∀ i : Fin 2, w * (collisionLeft F (X i) - collisionRight F (X i)) = 0) :
    w ∈ (obstructionIdeal F).annihilator := by
  apply Submodule.mem_annihilator.mpr
  intro z hz
  obtain ⟨p, hp, rfl⟩ := (Ideal.mem_map_iff_of_surjective
    (Ideal.Quotient.mk (collisionIdeal F)) Ideal.Quotient.mk_surjective).mp hz
  clear hz
  change p ∈ Ideal.span (Set.range (diagonalGenerator (R := ℂ) (ι := Fin 2))) at hp
  change w * Ideal.Quotient.mk (collisionIdeal F) p = 0
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    simpa only [diagonalGenerator, map_sub, collisionLeft_apply, collisionRight_apply,
      leftRename, rightRename, MvPolynomial.rename_X] using hw i
  | zero => simp
  | add p r hp hr ihp ihr => simp only [map_add, mul_add, ihp, ihr, add_zero]
  | smul a p hp ih =>
    change w * Ideal.Quotient.mk (collisionIdeal F) (a * p) = 0
    rw [map_mul]
    calc
      _ = Ideal.Quotient.mk (collisionIdeal F) a *
        (w * Ideal.Quotient.mk (collisionIdeal F) p) := by ring
      _ = 0 := by rw [ih, mul_zero]

private theorem eq_left_diagonal_mul_complement
    (q : CollisionRing F) (hq : IsCollisionOffDiagonalProjector F q)
    (w : CollisionRing F) (hw : w ∈ (obstructionIdeal F).annihilator) :
    w = collisionLeft F (collisionDiagonal F w) * (1 - q) := by
  have hqmem : q ∈ obstructionIdeal F := by
    rw [hq.2]
    exact Ideal.mem_span_singleton_self q
  have hwq : w * q = 0 := Submodule.mem_annihilator.mp hw q hqmem
  have hdiff : w - collisionLeft F (collisionDiagonal F w) ∈ obstructionIdeal F := by
    rw [← collisionDiagonal_ker]
    change collisionDiagonal F (w - collisionLeft F (collisionDiagonal F w)) = 0
    rw [map_sub, collisionDiagonal_collisionLeft, sub_self]
  rw [hq.2] at hdiff
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hdiff
  calc
    w = w * (1 - q) := by rw [mul_sub, mul_one, hwq, sub_zero]
    _ = collisionLeft F (collisionDiagonal F w) * (1 - q) := by
      apply sub_eq_zero.mp
      rw [← sub_mul, ← ha, mul_assoc, mul_sub, mul_one, hq.1.eq, sub_self, mul_zero]

/-- The two actual coordinate relations give an affine comparison with
the existing explicit diagonal secant projector. The source coefficient
on the right is retained; this theorem does not descend it to the base. -/
theorem coordinateRelationSecant_product_eq_diagonal_projector
    (H : Fin 2 → Polynomial (polynomialMapImageAlgebra F))
    (hH : ∀ i, Polynomial.aeval (X i : PlanePolynomial) (H i) = 0)
    (c : ℂ) (hc : c ≠ 0) (hJacobian : planarJacobianDet F = C c) :
    coordinateRelationSecant F (H 0) 0 * coordinateRelationSecant F (H 1) 1 =
      collisionLeft F
        (Polynomial.aeval (X 0 : PlanePolynomial) (H 0).derivative *
          Polynomial.aeval (X 1 : PlanePolynomial) (H 1).derivative) *
        (1 - ExplicitSecant.collisionProjector F c hc) := by
  let w := coordinateRelationSecant F (H 0) 0 * coordinateRelationSecant F (H 1) 1
  have hw : w ∈ (obstructionIdeal F).annihilator := by
    apply mem_annihilator_of_mul_differences_eq_zero F w
    intro i
    fin_cases i
    · change (coordinateRelationSecant F (H 0) 0 * coordinateRelationSecant F (H 1) 1) *
        (collisionLeft F (X 0) - collisionRight F (X 0)) = 0
      rw [mul_right_comm, coordinateRelationSecant_mul_difference F (H 0) 0 (hH 0), zero_mul]
    · change (coordinateRelationSecant F (H 0) 0 * coordinateRelationSecant F (H 1) 1) *
        (collisionLeft F (X 1) - collisionRight F (X 1)) = 0
      rw [mul_assoc, coordinateRelationSecant_mul_difference F (H 1) 1 (hH 1), mul_zero]
  have hdiag : collisionDiagonal F w =
      Polynomial.aeval (X 0 : PlanePolynomial) (H 0).derivative *
        Polynomial.aeval (X 1 : PlanePolynomial) (H 1).derivative := by
    dsimp only [w]
    rw [map_mul, diagonal_coordinateRelationSecant, diagonal_coordinateRelationSecant]
  simpa only [hdiag] using eq_left_diagonal_mul_complement F
    (ExplicitSecant.collisionProjector F c hc)
    (ExplicitSecant.collisionProjector_isProjector F c hc hJacobian) w hw

/-- Cancelling the diagonal projector already requires the off-diagonal
projector to vanish. It cannot be used to prove that vanishing. -/
theorem injective_mul_diagonal_projector_iff
    (q : CollisionRing F) (hq : IsCollisionOffDiagonalProjector F q) :
    Function.Injective (fun z : CollisionRing F => (1 - q) * z) ↔ q = 0 := by
  constructor
  · intro h
    apply h
    change (1 - q) * q = (1 - q) * 0
    rw [sub_mul, one_mul, hq.1.eq, sub_self, mul_zero]
  · intro h
    simp only [h, sub_zero, one_mul]
    exact Function.injective_id

end

end CollisionIdeals.Planar
