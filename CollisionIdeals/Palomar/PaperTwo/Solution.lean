import CollisionIdeals.Planar.GenericDegreeTwo

/-!
# Solution for the explicit planar projector and quadratic rigidity

This module connects the Mathlib-only Palomar statement to the project proof.
-/

set_option autoImplicit false

namespace CollisionIdeals.Palomar.PaperTwo

noncomputable section

open MvPolynomial

namespace ExplicitSecant

def powDifferenceFactor
    (x y : PairRing ℂ (Fin 2)) (n : ℕ) :
    PairRing ℂ (Fin 2) :=
  (Polynomial.powSubPowFactor x y n).1

def firstCoefficient
    (v : Fin 2 →₀ ℕ) (r : ℂ) : PairRing ℂ (Fin 2) :=
  C r *
    powDifferenceFactor (X (Sum.inl 0)) (X (Sum.inr 0)) (v 0) *
    X (Sum.inl 1) ^ v 1

def secondCoefficient
    (v : Fin 2 →₀ ℕ) (r : ℂ) : PairRing ℂ (Fin 2) :=
  C r * X (Sum.inr 0) ^ v 0 *
    powDifferenceFactor (X (Sum.inl 1)) (X (Sum.inr 1)) (v 1)

def first (p : SourceRing ℂ (Fin 2)) : PairRing ℂ (Fin 2) :=
  p.sum firstCoefficient

def second (p : SourceRing ℂ (Fin 2)) : PairRing ℂ (Fin 2) :=
  p.sum secondCoefficient

def determinant (F : PlanarPolynomialMap) : PairRing ℂ (Fin 2) :=
  first (F 0) * second (F 1) -
    second (F 0) * first (F 1)

noncomputable def collisionConstantUnit
    (F : PlanarPolynomialMap) (c : ℂ) (hc : c ≠ 0) :
    (CollisionRing F)ˣ :=
  Units.map
    (Ideal.Quotient.mk (collisionIdeal F)).toMonoidHom
    (Units.map MvPolynomial.C.toMonoidHom (Units.mk0 c hc))

noncomputable def collisionProjector
    (F : PlanarPolynomialMap) (c : ℂ) (hc : c ≠ 0) :
    CollisionRing F :=
  1 -
    (↑((collisionConstantUnit F c hc)⁻¹) : CollisionRing F) *
      Ideal.Quotient.mk (collisionIdeal F) (determinant F)

end ExplicitSecant

private theorem collisionProjector_eq_project
    (F : PlanarPolynomialMap) (c : ℂ) (hc : c ≠ 0) :
    ExplicitSecant.collisionProjector F c hc =
      Planar.ExplicitSecant.collisionProjector F c hc := by
  rfl

theorem explicitPlanarSecantProjector
    (F : PlanarPolynomialMap)
    (c : ℂ) (hc : c ≠ 0)
    (hJacobian : jacobianDet F = C c) :
    IsIdempotentElem
        (ExplicitSecant.collisionProjector F c hc) ∧
      obstructionIdeal F =
        Ideal.span {ExplicitSecant.collisionProjector F c hc} ∧
      (obstructionIdeal F).annihilator =
        Ideal.span
          {1 - ExplicitSecant.collisionProjector F c hc} ∧
      ∀ u : CollisionRing F,
        IsIdempotentElem u →
        obstructionIdeal F = Ideal.span {u} →
        u = ExplicitSecant.collisionProjector F c hc := by
  rw [collisionProjector_eq_project]
  have hProjector :=
    Planar.ExplicitSecant.collisionProjector_isProjector
      F c hc hJacobian
  refine ⟨hProjector.1, hProjector.2, ?_, ?_⟩
  · rw [hProjector.2]
    exact annihilator_span_idempotent hProjector.1
  · intro u hu hObstruction
    exact collisionOffDiagonalProjector_unique F
      ⟨hu, hObstruction⟩ hProjector

theorem quadraticPlanarCollisionRigidity
    (hRigidity : CollisionIdeals.ComplexKellerGaloisRigidity 2)
    (F : CollisionIdeals.PlanarPolynomialMap)
    (hDegree : CollisionIdeals.planarGenericDegree F = 2) :
    CollisionIdeals.obstructionIdeal F ≠ ⊥ ∧
      ¬ CollisionIdeals.IsPlanarKeller F :=
  ⟨CollisionIdeals.planarGenericDegreeTwo_obstructionIdeal_ne_bot F hDegree,
    CollisionIdeals.planarGenericDegreeTwo_not_keller hRigidity F hDegree⟩

end

end CollisionIdeals.Palomar.PaperTwo
