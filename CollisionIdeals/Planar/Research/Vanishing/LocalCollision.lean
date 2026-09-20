import CollisionIdeals.Planar.ConjugateSecantEvaluation
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Local rigidity of planar Keller collision pairs

If two planar Keller collision maps take values in a local ring and agree
on the residue coordinates, their evaluated secant determinant is a unit.
Since this determinant annihilates every coordinate difference, the two
maps coincide. No domain hypothesis is needed.

This is a local algebra implication. It does not construct a local-ring
evaluation of conjugate source coordinates at a boundary divisor.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

open MvPolynomial

noncomputable section

variable {R : Type*} [CommRing R] [IsLocalRing R] [Algebra ℂ R]

/-- Residue agreement makes the evaluated Keller secant determinant a unit. -/
theorem isUnit_collisionLift_planarSecantClass_of_residue_agreement
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F)
    (c : CollisionMapPair F R)
    (hResidue : ∀ i : Fin 2,
      c.left (X i) - c.right (X i) ∈ IsLocalRing.maximalIdeal R) :
    IsUnit (collisionLift c (planarSecantClass F)) := by
  obtain ⟨a, ha, hJacobian⟩ := hKeller
  have hDiagonal : diagonalIdeal (R := ℂ) (ι := Fin 2) ≤
      Ideal.comap (collisionPairMap c).toRingHom
        (IsLocalRing.maximalIdeal R) := by
    rw [diagonalIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change collisionPairMap c (diagonalGenerator i) ∈
      IsLocalRing.maximalIdeal R
    simpa [collisionPairMap, diagonalGenerator] using hResidue i
  have hDifference : collisionLift c (planarSecantClass F) -
      algebraMap ℂ R a ∈ IsLocalRing.maximalIdeal R := by
    have h := hDiagonal
      (planarSecantDet_sub_constant_mem_diagonalIdeal F a hJacobian)
    change collisionPairMap c (planarSecantDet F - C a) ∈
      IsLocalRing.maximalIdeal R at h
    simpa [planarSecantClass, collisionLift] using h
  have haUnit : IsUnit (algebraMap ℂ R a) :=
    (isUnit_iff_ne_zero.mpr ha).map (algebraMap ℂ R)
  apply IsLocalRing.notMem_maximalIdeal.mp
  intro hSecant
  apply (IsLocalRing.notMem_maximalIdeal.mpr haUnit)
  have h := (IsLocalRing.maximalIdeal R).sub_mem hSecant hDifference
  simpa only [sub_sub_cancel] using h

/-- A planar Keller collision pair with identical residue coordinates is
already a diagonal pair over the local ring. -/
theorem collisionMapPair_left_eq_right_of_residue_agreement
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F)
    (c : CollisionMapPair F R)
    (hResidue : ∀ i : Fin 2,
      c.left (X i) - c.right (X i) ∈ IsLocalRing.maximalIdeal R) :
    c.left = c.right := by
  have hUnit := isUnit_collisionLift_planarSecantClass_of_residue_agreement
    F hKeller c hResidue
  apply MvPolynomial.algHom_ext
  intro i
  apply sub_eq_zero.mp
  apply hUnit.mul_left_cancel
  simpa only [mul_zero] using
    collisionLift_planarSecantClass_mul_coordinateDifference_eq_zero F c i

end

end CollisionIdeals.Planar
