import CollisionIdeals.General.Normalization.WeightedComponents
import CollisionIdeals.General.Normalization.WeightedEuler
import CollisionIdeals.Planar.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The weighted leading Jacobian and the balanced common-zero exclusion

The highest possible weighted component of the full planar Jacobian is
the Jacobian of the corresponding component pair. For a constant
Jacobian it is zero off the balanced degree, and retains the same
constant in the balanced degree.

Signed Euler identity then excludes a common zero with a nonzero
weighted radial vector in that balanced case, over any field extension
of the complex coefficient field. The strict-degree case is different:
its leading Jacobian may vanish and have common zeros even for genuine
polynomial automorphisms.

Weights may be negative. No valuation is asserted to be monomial and
no source-coordinate regularity or universal pole exclusion is supplied.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals.Planar

noncomputable section

open MvPolynomial

/-- The highest possible weighted component of the full Jacobian is
computed from the actual polynomial component pair. The support bounds
allow signed coordinate weights. -/
theorem weightedComponent_jacobianDet_fin_two
    (F : PlanarPolynomialMap) (w : Fin 2 → ℤ) (m n : ℤ)
    (hP : ∀ a ∈ (F 0).support, Finsupp.weight w a ≤ m)
    (hQ : ∀ a ∈ (F 1).support, Finsupp.weight w a ≤ n) :
    weightedHomogeneousComponent w (m + n - w 0 - w 1) (jacobianDet F) =
      jacobianDet ![weightedHomogeneousComponent w m (F 0),
        weightedHomogeneousComponent w n (F 1)] := by
  have h01 := weightedHomogeneousComponent_mul_top_int w
    (pderiv 0 (F 0)) (pderiv 1 (F 1)) (m - w 0) (n - w 1)
    (fun a ha => weight_le_of_mem_support_pderiv_int w (F 0) 0 hP ha)
    (fun a ha => weight_le_of_mem_support_pderiv_int w (F 1) 1 hQ ha)
  have h10 := weightedHomogeneousComponent_mul_top_int w
    (pderiv 1 (F 0)) (pderiv 0 (F 1)) (m - w 1) (n - w 0)
    (fun a ha => weight_le_of_mem_support_pderiv_int w (F 0) 1 hP ha)
    (fun a ha => weight_le_of_mem_support_pderiv_int w (F 1) 0 hQ ha)
  have hd01 : m + n - w 0 - w 1 = (m - w 0) + (n - w 1) := by omega
  have hd10 : m + n - w 0 - w 1 = (m - w 1) + (n - w 0) := by omega
  have h01' :
      weightedHomogeneousComponent w (m + n - w 0 - w 1)
        (pderiv 0 (F 0) * pderiv 1 (F 1)) =
      weightedHomogeneousComponent w (m - w 0) (pderiv 0 (F 0)) *
        weightedHomogeneousComponent w (n - w 1) (pderiv 1 (F 1)) := by
    rwa [hd01]
  have h10' :
      weightedHomogeneousComponent w (m + n - w 0 - w 1)
        (pderiv 1 (F 0) * pderiv 0 (F 1)) =
      weightedHomogeneousComponent w (m - w 1) (pderiv 1 (F 0)) *
        weightedHomogeneousComponent w (n - w 0) (pderiv 0 (F 1)) := by
    rwa [hd10]
  rw [jacobianDet_fin_two, map_sub, h01', h10']
  simp only [weightedHomogeneousComponent_pderiv_int, sub_add_cancel]
  rw [jacobianDet_fin_two]
  rfl

/-- The full constant-Jacobian equation gives an exact two-case formula
for the Jacobian of the leading weighted component pair. -/
theorem jacobianDet_weightedComponents_eq_of_constant
    (F : PlanarPolynomialMap) (c : ℂ) (hJ : jacobianDet F = C c)
    (w : Fin 2 → ℤ) (m n : ℤ)
    (hP : ∀ a ∈ (F 0).support, Finsupp.weight w a ≤ m)
    (hQ : ∀ a ∈ (F 1).support, Finsupp.weight w a ≤ n) :
    jacobianDet ![weightedHomogeneousComponent w m (F 0),
        weightedHomogeneousComponent w n (F 1)] =
      if m + n = w 0 + w 1 then C c else 0 := by
  rw [← weightedComponent_jacobianDet_fin_two F w m n hP hQ, hJ]
  have hC : C c ∈ weightedHomogeneousSubmodule ℂ w (0 : ℤ) :=
    isWeightedHomogeneous_C w c
  rw [weightedHomogeneousComponent_of_mem hC]
  have hBalance : (m + n - w 0 - w 1 = 0) ↔ m + n = w 0 + w 1 := by omega
  simp only [hBalance]

private theorem weight_mul_point_eq_zero_of_common_zero
    {S : Type*} [Field S] [Algebra ℂ S]
    (P Q : PlanePolynomial) (w : Fin 2 → ℤ) (m n : ℤ)
    (hP : P.IsWeightedHomogeneous w m) (hQ : Q.IsWeightedHomogeneous w n)
    (c : ℂ) (hc : c ≠ 0) (hJ : jacobianDet ![P, Q] = C c)
    (z : Fin 2 → S) (hzP : aeval z P = 0) (hzQ : aeval z Q = 0) :
    ∀ i : Fin 2, (w i : S) * z i = 0 := by
  let e : PlanePolynomial →ₐ[ℂ] S := aeval z
  have eP := congrArg e (sum_weight_X_mul_pderiv_int w P m hP)
  have eQ := congrArg e (sum_weight_X_mul_pderiv_int w Q n hQ)
  have hPz : e P = 0 := hzP
  have hQz : e Q = 0 := hzQ
  have eX (i : Fin 2) : e (X i) = z i := by simp [e]
  simp only [Fin.sum_univ_two, map_add, map_zsmul, map_mul, eX, hPz, hQz,
    smul_zero] at eP eQ
  simp only [zsmul_eq_mul] at eP eQ
  have eJ : e (pderiv 0 P) * e (pderiv 1 Q) -
      e (pderiv 1 P) * e (pderiv 0 Q) = algebraMap ℂ S c := by
    have h := congrArg e hJ
    simpa only [jacobianDet_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      map_sub, map_mul, e, aeval_C] using h
  have hcS : algebraMap ℂ S c ≠ 0 := by
    intro h
    apply hc
    apply (algebraMap ℂ S).injective
    simpa only [map_zero] using h
  have h0 : algebraMap ℂ S c * ((w 0 : S) * z 0) = 0 := by
    calc
      _ = e (pderiv 1 Q) *
          ((w 0 : S) * (z 0 * e (pderiv 0 P)) +
            (w 1 : S) * (z 1 * e (pderiv 1 P))) -
          e (pderiv 1 P) *
          ((w 0 : S) * (z 0 * e (pderiv 0 Q)) +
            (w 1 : S) * (z 1 * e (pderiv 1 Q))) := by rw [← eJ]; ring
      _ = 0 := by rw [eP, eQ]; ring
  have h1 : algebraMap ℂ S c * ((w 1 : S) * z 1) = 0 := by
    calc
      _ = e (pderiv 0 P) *
          ((w 0 : S) * (z 0 * e (pderiv 0 Q)) +
            (w 1 : S) * (z 1 * e (pderiv 1 Q))) -
          e (pderiv 0 Q) *
          ((w 0 : S) * (z 0 * e (pderiv 0 P)) +
            (w 1 : S) * (z 1 * e (pderiv 1 P))) := by rw [← eJ]; ring
      _ = 0 := by rw [eP, eQ]; ring
  intro i
  fin_cases i
  · exact (mul_eq_zero.mp h0).resolve_left hcS
  · exact (mul_eq_zero.mp h1).resolve_left hcS

/-- In the balanced degree, the full Keller identity excludes a common
zero of the leading components with nonzero weighted radial vector.
The evaluation field may be a residue-field extension of the coefficients. -/
theorem not_common_zero_weightedComponents_of_balance
    {S : Type*} [Field S] [Algebra ℂ S]
    (F : PlanarPolynomialMap) (c : ℂ) (hc : c ≠ 0) (hJ : jacobianDet F = C c)
    (w : Fin 2 → ℤ) (m n : ℤ)
    (hP : ∀ a ∈ (F 0).support, Finsupp.weight w a ≤ m)
    (hQ : ∀ a ∈ (F 1).support, Finsupp.weight w a ≤ n)
    (hBalance : m + n = w 0 + w 1)
    (z : Fin 2 → S) (hRadial : ∃ i : Fin 2, w i ≠ 0 ∧ z i ≠ 0) :
    ¬ (aeval z (weightedHomogeneousComponent w m (F 0)) = 0 ∧
      aeval z (weightedHomogeneousComponent w n (F 1)) = 0) := by
  letI : CharZero S := charZero_of_injective_algebraMap (algebraMap ℂ S).injective
  rintro ⟨hzP, hzQ⟩
  have hTop := jacobianDet_weightedComponents_eq_of_constant F c hJ w m n hP hQ
  rw [if_pos hBalance] at hTop
  have hZero := weight_mul_point_eq_zero_of_common_zero
    (weightedHomogeneousComponent w m (F 0))
    (weightedHomogeneousComponent w n (F 1)) w m n
    (weightedHomogeneousComponent_isWeightedHomogeneous m (F 0))
    (weightedHomogeneousComponent_isWeightedHomogeneous n (F 1))
    c hc hTop z hzP hzQ
  obtain ⟨i, hi, hzi⟩ := hRadial
  exact mul_ne_zero (Int.cast_ne_zero.mpr hi) hzi (hZero i)

end

end CollisionIdeals.Planar
