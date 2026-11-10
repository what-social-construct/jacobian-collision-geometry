import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Lean.Elab.Tactic.Omega

/-!
# Signed weighted components and partial derivatives

These lemmas use Mathlib's existing weighted homogeneous components with
integer weights. Partial differentiation shifts the weight by the
corresponding variable weight, and the highest permitted component of a
product is the product of the corresponding components. The bounds are
on the original polynomial supports; no new initial-form object is used.
-/

set_option autoImplicit false

namespace CollisionIdeals

open MvPolynomial Finsupp

variable {R σ : Type*} [CommRing R]

private theorem weightedHomogeneousComponent_monomial_int
    (w : σ → ℤ) (d : ℤ) (a : σ →₀ ℕ) (r : R) :
    weightedHomogeneousComponent w d (monomial a r) =
      if weight w a = d then monomial a r else 0 := by
  classical
  simpa only [eq_comm] using
    (weightedHomogeneousComponent_of_mem (m := d)
      (show monomial a r ∈ weightedHomogeneousSubmodule R w (weight w a) from
        isWeightedHomogeneous_monomial w a r rfl))

/-- With signed weights, taking a partial derivative shifts a weighted
component by exactly the weight of that variable. -/
theorem weightedHomogeneousComponent_pderiv_int
    (w : σ → ℤ) (d : ℤ) (i : σ) (P : MvPolynomial σ R) :
    weightedHomogeneousComponent w d (pderiv i P) =
      pderiv i (weightedHomogeneousComponent w (d + w i) P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial a r =>
      by_cases hai : a i = 0
      · by_cases hd : weight w a = d + w i <;>
          simp [pderiv_monomial, hai, weightedHomogeneousComponent_monomial_int, hd]
      · have hweight := weight_sub_single_add (w := w) hai
        have hiff : weight w (a - single i 1) = d ↔ weight w a = d + w i := by
          omega
        rw [pderiv_monomial, weightedHomogeneousComponent_monomial_int,
          weightedHomogeneousComponent_monomial_int]
        by_cases h : weight w a = d + w i
        · rw [if_pos (hiff.mpr h), if_pos h, pderiv_monomial]
        · rw [if_neg (not_congr hiff |>.mpr h), if_neg h, map_zero]
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ]

/-- A support weight bound drops by the variable weight after partial
differentiation. This permits negative or zero variable weights. -/
theorem weight_le_of_mem_support_pderiv_int
    (w : σ → ℤ) (P : MvPolynomial σ R) (i : σ) {m : ℤ}
    (hP : ∀ a ∈ P.support, weight w a ≤ m) {a : σ →₀ ℕ}
    (ha : a ∈ (pderiv i P).support) :
    weight w a ≤ m - w i := by
  classical
  have hsum :
      pderiv i P = ∑ b ∈ P.support, pderiv i (monomial b (coeff b P)) := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
  have hcoeffsum :
      (∑ b ∈ P.support, coeff a (pderiv i (monomial b (coeff b P)))) ≠ 0 := by
    rw [← coeff_sum, ← hsum]
    exact MvPolynomial.mem_support_iff.mp ha
  obtain ⟨b, hb, hcoeff⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcoeffsum
  have hbi : b i ≠ 0 := by
    intro hzero
    simp only [pderiv_monomial, hzero, Nat.cast_zero, mul_zero, monomial_zero,
      coeff_zero, ne_eq, not_true_eq_false] at hcoeff
  have hba : b - single i 1 = a := by
    rw [pderiv_monomial, coeff_monomial] at hcoeff
    split_ifs at hcoeff with h
    · exact h
    · exact False.elim (hcoeff rfl)
  have hweight : weight w a + w i = weight w b := by
    rw [← hba]
    exact weight_sub_single_add hbi
  have hbound := hP b hb
  omega

/-- The component at the sum of two support weight bounds is the product
of the components at those bounds. No positivity assumption is needed. -/
theorem weightedHomogeneousComponent_mul_top_int
    (w : σ → ℤ) (P Q : MvPolynomial σ R) (m n : ℤ)
    (hP : ∀ a ∈ P.support, weight w a ≤ m)
    (hQ : ∀ a ∈ Q.support, weight w a ≤ n) :
    weightedHomogeneousComponent w (m + n) (P * Q) =
      weightedHomogeneousComponent w m P * weightedHomogeneousComponent w n Q := by
  classical
  ext a
  simp only [coeff_weightedHomogeneousComponent, coeff_mul]
  by_cases ha : weight w a = m + n
  · simp only [ha, if_true]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hbp : coeff b.1 P = 0
    · simp only [hbp, ite_self, zero_mul]
    by_cases hbq : coeff b.2 Q = 0
    · simp only [hbq, ite_self, mul_zero]
    have hp := hP b.1 (MvPolynomial.mem_support_iff.mpr hbp)
    have hq := hQ b.2 (MvPolynomial.mem_support_iff.mpr hbq)
    have hba := Finset.mem_antidiagonal.mp hb
    have hweight : weight w b.1 + weight w b.2 = m + n := by
      rw [← map_add, hba, ha]
    have hm : weight w b.1 = m := by omega
    have hn : weight w b.2 = n := by omega
    rw [if_pos hm, if_pos hn]
  · simp only [ha, if_false]
    symm
    apply Finset.sum_eq_zero
    intro b hb
    by_cases hm : weight w b.1 = m
    · by_cases hn : weight w b.2 = n
      · exfalso
        apply ha
        rw [← Finset.mem_antidiagonal.mp hb, map_add, hm, hn]
      · rw [if_neg hn, mul_zero]
    · rw [if_neg hm, zero_mul]

end CollisionIdeals
