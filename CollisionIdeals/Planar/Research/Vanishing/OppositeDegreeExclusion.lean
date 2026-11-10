import CollisionIdeals.Planar.Research.Vanishing.WeightedJacobian
import CollisionIdeals.General.Normalization.WeightedDegreeBounds
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Tactic.LinearCombination

/-!
# Opposite signed degrees and the zero leading Jacobian

Two nonzero weighted-homogeneous plane polynomials of strictly opposite
signed degrees cannot have zero Jacobian in characteristic zero. Euler's
identity would make a positive-power product constant, forcing both
polynomials to be units.

For a constant-Jacobian pair this forces the balanced weighted degree,
not a general exclusion of opposite signs. The identity map with weights
`(1,-1)` is a balanced opposite-sign example. No next target reduction
or source-coordinate regularity is inferred here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CollisionIdeals.Planar

noncomputable section

open MvPolynomial

/-- Contracting a zero Jacobian with the weighted Euler vector gives
the cross-multiplied differential relation, without passing to a
rational function field. -/
theorem weightedHomogeneous_cross_pderiv_eq_of_jacobian_eq_zero
    (P Q : PlanePolynomial) (w : Fin 2 → ℤ) (m n : ℤ)
    (hP : P.IsWeightedHomogeneous w m) (hQ : Q.IsWeightedHomogeneous w n)
    (hJ : jacobianDet (![P, Q] : PlanarPolynomialMap) = 0) (i : Fin 2) :
    (m : PlanePolynomial) * P * pderiv i Q =
      (n : PlanePolynomial) * Q * pderiv i P := by
  have eP := sum_weight_X_mul_pderiv_int w P m hP
  have eQ := sum_weight_X_mul_pderiv_int w Q n hQ
  simp only [Fin.sum_univ_two, zsmul_eq_mul] at eP eQ
  have hJ' : pderiv 0 P * pderiv 1 Q - pderiv 1 P * pderiv 0 Q = 0 := by
    simpa only [jacobianDet_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one] using hJ
  fin_cases i
  · change (m : PlanePolynomial) * P * pderiv 0 Q =
      (n : PlanePolynomial) * Q * pderiv 0 P
    linear_combination -(pderiv 0 Q) * eP + pderiv 0 P * eQ -
      ((w 1 : PlanePolynomial) * X 1) * hJ'
  · change (m : PlanePolynomial) * P * pderiv 1 Q =
      (n : PlanePolynomial) * Q * pderiv 1 P
    linear_combination -(pderiv 1 Q) * eP + pderiv 1 P * eQ +
      ((w 0 : PlanePolynomial) * X 0) * hJ'

/-- Nonzero weighted-homogeneous polynomials with strictly opposite
signed degrees cannot have zero Jacobian. This uses characteristic
zero through the existing polynomial derivative-zero criterion. -/
theorem jacobian_ne_zero_of_weightedHomogeneous_opposite_degrees
    (P Q : PlanePolynomial) (w : Fin 2 → ℤ) (m n : ℤ)
    (hP : P.IsWeightedHomogeneous w m) (hQ : Q.IsWeightedHomogeneous w n)
    (hPne : P ≠ 0) (hQne : Q ≠ 0) (hm : 0 < m) (hn : n < 0) :
    jacobianDet (![P, Q] : PlanarPolynomialMap) ≠ 0 := by
  intro hJ
  let a : ℕ := (-n).toNat
  let b : ℕ := m.toNat
  have ha : (a : ℤ) = -n := by dsimp [a]; omega
  have hb : (b : ℤ) = m := by dsimp [b]; omega
  have haPos : 0 < a := by omega
  have hbPos : 0 < b := by omega
  have haCast : (a : PlanePolynomial) = -(n : PlanePolynomial) := by
    have h := congrArg (fun z : ℤ => (z : PlanePolynomial)) ha
    simpa only [Int.cast_natCast, Int.cast_neg] using h
  have hbCast : (b : PlanePolynomial) = (m : PlanePolynomial) := by
    have h := congrArg (fun z : ℤ => (z : PlanePolynomial)) hb
    simpa only [Int.cast_natCast] using h
  have haPow : P ^ a = P ^ (a - 1) * P := by
    have h : a = (a - 1) + 1 := by omega
    conv_lhs => rw [h, pow_succ]
  have hbPow : Q ^ b = Q ^ (b - 1) * Q := by
    have h : b = (b - 1) + 1 := by omega
    conv_lhs => rw [h, pow_succ]
  have hDerivative : ∀ i : Fin 2, pderiv i (P ^ a * Q ^ b) = 0 := by
    intro i
    have hCross := weightedHomogeneous_cross_pderiv_eq_of_jacobian_eq_zero
      P Q w m n hP hQ hJ i
    rw [pderiv_mul, pderiv_pow, pderiv_pow, haCast, hbCast, haPow, hbPow]
    calc
      _ = P ^ (a - 1) * Q ^ (b - 1) *
          ((m : PlanePolynomial) * P * pderiv i Q -
            (n : PlanePolynomial) * Q * pderiv i P) := by ring
      _ = 0 := by rw [sub_eq_zero.mpr hCross, mul_zero]
  have hConstant := eq_C_of_forall_pderiv_eq_zero (P ^ a * Q ^ b) hDerivative
  have hProductNe : P ^ a * Q ^ b ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hPne) (pow_ne_zero _ hQne)
  have hc : coeff 0 (P ^ a * Q ^ b) ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hConstant
    exact hProductNe hConstant
  have hUnitProduct : IsUnit (P ^ a * Q ^ b) := by
    rw [hConstant]
    exact (isUnit_iff_ne_zero.mpr hc).map C
  have hUnitP : IsUnit P :=
    (isUnit_pow_iff (by omega : a ≠ 0)).mp (isUnit_of_mul_isUnit_left hUnitProduct)
  obtain ⟨c, _, hPc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hUnitP
  have hPzeroDegree : P.IsWeightedHomogeneous w (0 : ℤ) := by
    rw [hPc]
    exact isWeightedHomogeneous_C w c
  have hmZero := IsWeightedHomogeneous.inj_right hPne hP hPzeroDegree
  omega

/-- For a constant-Jacobian pair with positive first and negative second
sharp weighted degree, the leading Jacobian must be in the balanced
degree. Opposite signs are therefore excluded from the strict-defect
branch, but not from the balanced branch. -/
theorem weighted_degrees_balance_of_opposite_signs
    (F : PlanarPolynomialMap) (c : ℂ) (hJ : jacobianDet F = C c)
    (w : Fin 2 → ℤ) (m n : ℤ)
    (hPdeg : weightedTotalDegree' w (F 0) = (m : WithBot ℤ))
    (hQdeg : weightedTotalDegree' w (F 1) = (n : WithBot ℤ))
    (hm : 0 < m) (hn : n < 0) :
    m + n = w 0 + w 1 := by
  by_contra hBalance
  have hTop := jacobianDet_weightedComponents_eq_of_constant F c hJ w m n
    (fun a ha => weight_le_of_weightedTotalDegree'_eq_int w (F 0) hPdeg ha)
    (fun a ha => weight_le_of_weightedTotalDegree'_eq_int w (F 1) hQdeg ha)
  rw [if_neg hBalance] at hTop
  exact jacobian_ne_zero_of_weightedHomogeneous_opposite_degrees
    (weightedHomogeneousComponent w m (F 0))
    (weightedHomogeneousComponent w n (F 1)) w m n
    (weightedHomogeneousComponent_isWeightedHomogeneous m (F 0))
    (weightedHomogeneousComponent_isWeightedHomogeneous n (F 1))
    (weightedHomogeneousComponent_ne_zero_of_degree'_eq_int w (F 0) hPdeg)
    (weightedHomogeneousComponent_ne_zero_of_degree'_eq_int w (F 1) hQdeg)
    hm hn hTop

end

end CollisionIdeals.Planar
