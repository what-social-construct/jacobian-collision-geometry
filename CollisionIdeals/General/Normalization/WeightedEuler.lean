import CollisionIdeals.General.Normalization.BaseTransversality
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Euler's identity for signed polynomial weights

The standard weighted-homogeneity predicate permits integer weights.
Euler's identity holds for these weights as well, without a positivity
or characteristic-zero hypothesis.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

open MvPolynomial

variable {σ k : Type*} [Fintype σ] [Field k]

/-- Euler's identity for an integer-weighted homogeneous polynomial. -/
theorem sum_weight_X_mul_pderiv_int
    (w : σ → ℤ) (P : MvPolynomial σ k) (m : ℤ)
    (hP : P.IsWeightedHomogeneous w m) :
    ∑ i : σ, w i • (X i * pderiv i P) = m • P := by
  classical
  ext d
  simp only [coeff_sum, coeff_smul, coeff_X_mul_pderiv]
  by_cases hd : coeff d P = 0
  · simp [hd]
  · have hWeight : (∑ i : σ, (d i : ℤ) * w i) = m := by
      have h := hP hd
      rw [Finsupp.weight_apply] at h
      rw [Finsupp.sum_fintype d (fun i a => a • w i) (fun i => zero_smul ℕ (w i))] at h
      simpa only [nsmul_eq_mul] using h
    have hCast := congrArg (fun t : ℤ => (t : k)) hWeight
    push_cast at hCast
    have hWeightCast : (∑ i : σ, (w i : k) * (d i : k)) = (m : k) := by
      simpa only [mul_comm] using hCast
    simp only [zsmul_eq_mul, ← mul_assoc, ← Finset.sum_mul, hWeightCast]

end

end CollisionIdeals
