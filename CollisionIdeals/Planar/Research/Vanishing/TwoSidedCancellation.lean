import CollisionIdeals.Planar.Research.Vanishing.CancellationBudget
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Legal weighted cancellation in either target coordinate

The earlier subtraction API changes only the second target coordinate.
Conjugating it by the actual target-coordinate swap gives the first-coordinate
operation `(P - ell Q^s, Q)`. The two swaps cancel their Jacobian signs, so
this operation preserves the original Jacobian constant, the Keller condition,
and the same coordinate-image subalgebra.

The weighted descent still requires an actual leading-polynomial relation.
Allowing both orientations does not assert that either relation is available
at an arbitrary boundary valuation.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

open MvPolynomial

/-- The polynomial automorphism interchanging the two target coordinates. -/
def targetCoordinateSwap : PlanarPolynomialMap := ![X 1, X 0]

/-- Compose a polynomial map with the actual target-coordinate swap. -/
def swapTargetCoordinates (F : PlanarPolynomialMap) : PlanarPolynomialMap :=
  ![F 1, F 0]

theorem coordinateAlgHom_targetCoordinateSwap_comp_self :
    (coordinateAlgHom targetCoordinateSwap).comp
      (coordinateAlgHom targetCoordinateSwap) = AlgHom.id ℂ PlanePolynomial := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [coordinateAlgHom, targetCoordinateSwap]

theorem coordinateAlgHom_swapTargetCoordinates (F : PlanarPolynomialMap) :
    coordinateAlgHom (swapTargetCoordinates F) =
      (coordinateAlgHom F).comp (coordinateAlgHom targetCoordinateSwap) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [coordinateAlgHom, swapTargetCoordinates, targetCoordinateSwap]

theorem swapTargetCoordinates_jacobian (F : PlanarPolynomialMap) :
    planarJacobianDet (swapTargetCoordinates F) = -planarJacobianDet F := by
  change jacobianDet (swapTargetCoordinates F) = -jacobianDet F
  simp only [jacobianDet_fin_two, swapTargetCoordinates,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The target-coordinate permutation preserves the original image range. -/
theorem coordinateAlgHom_swapTargetCoordinates_range (F : PlanarPolynomialMap) :
    (coordinateAlgHom (swapTargetCoordinates F)).range = (coordinateAlgHom F).range := by
  rw [coordinateAlgHom_swapTargetCoordinates]
  apply le_antisymm
  · exact AlgHom.range_comp_le_range _ _
  · intro z hz
    obtain ⟨p, hp⟩ := hz
    refine ⟨coordinateAlgHom targetCoordinateSwap p, ?_⟩
    change coordinateAlgHom F (coordinateAlgHom targetCoordinateSwap
      (coordinateAlgHom targetCoordinateSwap p)) = z
    have hInverse := AlgHom.congr_fun coordinateAlgHom_targetCoordinateSwap_comp_self p
    change coordinateAlgHom targetCoordinateSwap
      (coordinateAlgHom targetCoordinateSwap p) = p at hInverse
    rw [hInverse]
    exact hp

/-- The first-coordinate target shear, complementary to `targetSubtract`. -/
def targetSubtractFirst (F : PlanarPolynomialMap) (ell : ℂ) (s : ℕ) :
    PlanarPolynomialMap := ![F 0 - C ell * (F 1) ^ s, F 1]

theorem targetSubtractFirst_eq_swapTargetCoordinates
    (F : PlanarPolynomialMap) (ell : ℂ) (s : ℕ) :
    targetSubtractFirst F ell s =
      swapTargetCoordinates (targetSubtract (swapTargetCoordinates F) ell s) := by
  funext i
  fin_cases i <;> simp [targetSubtractFirst, swapTargetCoordinates, targetSubtract]

/-- The inverse first-coordinate operation is obtained by negating `ell`. -/
theorem targetSubtractFirst_neg
    (F : PlanarPolynomialMap) (ell : ℂ) (s : ℕ) :
    targetSubtractFirst (targetSubtractFirst F ell s) (-ell) s = F := by
  funext i
  fin_cases i <;> simp [targetSubtractFirst]

/-- Two target swaps cancel their signs: the original Jacobian constant
is retained, rather than its negative. -/
theorem targetSubtractFirst_jacobian
    (F : PlanarPolynomialMap) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = C c) (ell : ℂ) (s : ℕ) :
    planarJacobianDet (targetSubtractFirst F ell s) = C c := by
  have hSwap : planarJacobianDet (swapTargetCoordinates F) = C (-c) := by
    rw [swapTargetCoordinates_jacobian, hJ, map_neg]
  rw [targetSubtractFirst_eq_swapTargetCoordinates, swapTargetCoordinates_jacobian,
    targetSubtract_jacobian (swapTargetCoordinates F) (-c) (neg_ne_zero.mpr hc)
      hSwap ell s, map_neg, neg_neg]

theorem targetSubtractFirst_isKeller
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F) (ell : ℂ) (s : ℕ) :
    IsPlanarKeller (targetSubtractFirst F ell s) := by
  obtain ⟨c, hc, hJ⟩ := hKeller
  exact ⟨c, hc, targetSubtractFirst_jacobian F c hc hJ ell s⟩

/-- The first-coordinate shear preserves the same coordinate-image
subalgebra inside the original polynomial source. -/
theorem coordinateAlgHom_targetSubtractFirst_range
    (F : PlanarPolynomialMap) (ell : ℂ) (s : ℕ) :
    (coordinateAlgHom (targetSubtractFirst F ell s)).range =
      (coordinateAlgHom F).range := by
  rw [targetSubtractFirst_eq_swapTargetCoordinates,
    coordinateAlgHom_swapTargetCoordinates_range,
    coordinateAlgHom_targetSubtract_range,
    coordinateAlgHom_swapTargetCoordinates_range]

/-- Regularity of the target values at a fixed valuation ring survives
the second-coordinate shear. No source coordinate is assumed regular. -/
theorem targetSubtract_mem_valuationRing
    {N : Type*} [Field N] [Algebra ℂ N]
    (V : ValuationSubring N) (φ : PlanePolynomial →ₐ[ℂ] N)
    (F : PlanarPolynomialMap)
    (hGround : ∀ c : ℂ, algebraMap ℂ N c ∈ V)
    (hRegular : ∀ j : Fin 2, φ (F j) ∈ V) (ell : ℂ) (s : ℕ) :
    ∀ j : Fin 2, φ (targetSubtract F ell s j) ∈ V := by
  intro j
  fin_cases j
  · simpa only [targetSubtract, Matrix.cons_val_zero] using hRegular 0
  · change φ (F 1 - C ell * (F 0) ^ s) ∈ V
    rw [map_sub, map_mul, map_pow]
    apply V.sub_mem (hRegular 1)
    apply V.toSubring.mul_mem ?_ (V.pow_mem (hRegular 0) s)
    simpa only [← MvPolynomial.algebraMap_eq, φ.commutes] using hGround ell

/-- The opposite shear also keeps the same valuation ring and regular
target values. The underlying source-coordinate map is unchanged. -/
theorem targetSubtractFirst_mem_valuationRing
    {N : Type*} [Field N] [Algebra ℂ N]
    (V : ValuationSubring N) (φ : PlanePolynomial →ₐ[ℂ] N)
    (F : PlanarPolynomialMap)
    (hGround : ∀ c : ℂ, algebraMap ℂ N c ∈ V)
    (hRegular : ∀ j : Fin 2, φ (F j) ∈ V) (ell : ℂ) (s : ℕ) :
    ∀ j : Fin 2, φ (targetSubtractFirst F ell s j) ∈ V := by
  intro j
  fin_cases j
  · change φ (F 0 - C ell * (F 1) ^ s) ∈ V
    rw [map_sub, map_mul, map_pow]
    apply V.sub_mem (hRegular 0)
    apply V.toSubring.mul_mem ?_ (V.pow_mem (hRegular 1) s)
    simpa only [← MvPolynomial.algebraMap_eq, φ.commutes] using hGround ell
  · simpa only [targetSubtractFirst, Matrix.cons_val_one] using hRegular 1

/-- If the first leading component is a scalar power of the second,
subtracting in that orientation gives a legal weighted descent. No
existence of such a relation or subsequent reduction is asserted. -/
theorem exists_weighted_targetSubtractFirst_descent
    (F : PlanarPolynomialMap) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = C c)
    (w : Fin 2 → ℤ) (m n : ℤ)
    (hPdeg : weightedTotalDegree' w (F 0) = (m : WithBot ℤ))
    (hQdeg : weightedTotalDegree' w (F 1) = (n : WithBot ℤ))
    (ell : ℂ) (s : ℕ) (hBalance : m = (s : ℤ) * n)
    (hLeading : weightedHomogeneousComponent w m (F 0) =
      C ell * (weightedHomogeneousComponent w n (F 1)) ^ s) :
    IsPlanarKeller (targetSubtractFirst F ell s) ∧
      (coordinateAlgHom (targetSubtractFirst F ell s)).range = (coordinateAlgHom F).range ∧
      ∃ k : ℤ,
        weightedTotalDegree' w ((targetSubtractFirst F ell s) 0) = (k : WithBot ℤ) ∧
        0 ≤ k + n - w 0 - w 1 ∧
        k + n - w 0 - w 1 < m + n - w 0 - w 1 := by
  refine ⟨targetSubtractFirst_isKeller F ⟨c, hc, hJ⟩ ell s,
    coordinateAlgHom_targetSubtractFirst_range F ell s, ?_⟩
  have hSwap : planarJacobianDet (swapTargetCoordinates F) = C (-c) := by
    rw [swapTargetCoordinates_jacobian, hJ, map_neg]
  obtain ⟨_, _, k, hk, hNonneg, hDrop⟩ := exists_weighted_targetSubtract_descent
    (swapTargetCoordinates F) (-c) (neg_ne_zero.mpr hc) hSwap w n m
    (by simpa only [swapTargetCoordinates, Matrix.cons_val_zero] using hQdeg)
    (by simpa only [swapTargetCoordinates, Matrix.cons_val_one] using hPdeg)
    ell s hBalance
    (by simpa only [swapTargetCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one]
      using hLeading)
  refine ⟨k, ?_, by omega, by omega⟩
  simpa only [targetSubtractFirst, targetSubtract, swapTargetCoordinates,
    Matrix.cons_val_zero, Matrix.cons_val_one] using hk

end

end CollisionIdeals.Planar
