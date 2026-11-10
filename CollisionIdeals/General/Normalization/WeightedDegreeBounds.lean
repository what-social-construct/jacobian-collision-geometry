import CollisionIdeals.General.Normalization.WeightedComponents
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Bounds and sharp degrees for signed weighted components

The degree is Mathlib's existing `weightedTotalDegree'`, with values in
`WithBot ℤ`. A finite integer degree is characterized by a support bound
and a nonzero component at the bound. Products and powers preserve sharp
degrees over a domain. The support and component formulas themselves do
not require a domain or positive weights.
-/

set_option autoImplicit false

namespace CollisionIdeals

open MvPolynomial

variable {R σ : Type*} [CommRing R]

/-- A finite upper bound on signed weighted degree is precisely the
corresponding bound on every exponent in the polynomial support. -/
theorem weightedTotalDegree'_le_coe_int_iff
    (w : σ → ℤ) (P : MvPolynomial σ R) (m : ℤ) :
    weightedTotalDegree' w P ≤ (m : WithBot ℤ) ↔
      ∀ a ∈ P.support, Finsupp.weight w a ≤ m := by
  classical
  simp only [weightedTotalDegree', Finset.sup_le_iff, WithBot.coe_le_coe]

/-- Every support exponent is bounded by a supplied sharp weighted degree. -/
theorem weight_le_of_weightedTotalDegree'_eq_int
    (w : σ → ℤ) (P : MvPolynomial σ R) {m : ℤ}
    (hdeg : weightedTotalDegree' w P = (m : WithBot ℤ))
    {a : σ →₀ ℕ} (ha : a ∈ P.support) :
    Finsupp.weight w a ≤ m :=
  (weightedTotalDegree'_le_coe_int_iff w P m).mp hdeg.le a ha

/-- A finite sharp weighted degree implies that the polynomial is nonzero. -/
theorem ne_zero_of_weightedTotalDegree'_eq_int
    (w : σ → ℤ) (P : MvPolynomial σ R) {m : ℤ}
    (hdeg : weightedTotalDegree' w P = (m : WithBot ℤ)) : P ≠ 0 := by
  intro hP
  rw [hP, weightedTotalDegree'_zero] at hdeg
  exact WithBot.bot_ne_coe hdeg

/-- The component at a supplied finite weighted degree cannot vanish. -/
theorem weightedHomogeneousComponent_ne_zero_of_degree'_eq_int
    (w : σ → ℤ) (P : MvPolynomial σ R) {m : ℤ}
    (hdeg : weightedTotalDegree' w P = (m : WithBot ℤ)) :
    weightedHomogeneousComponent w m P ≠ 0 := by
  classical
  have hP : P.support.Nonempty :=
    MvPolynomial.support_nonempty.mpr (ne_zero_of_weightedTotalDegree'_eq_int w P hdeg)
  obtain ⟨a, ha, hmax⟩ := Finset.exists_mem_eq_sup P.support hP
    (fun a => (Finsupp.weight w a : WithBot ℤ))
  have hweight : Finsupp.weight w a = m :=
    WithBot.coe_injective (hmax.symm.trans hdeg)
  intro hzero
  have hcoeff : coeff a (weightedHomogeneousComponent w m P) ≠ 0 := by
    rw [coeff_weightedHomogeneousComponent, if_pos hweight]
    exact MvPolynomial.mem_support_iff.mp ha
  rw [hzero, coeff_zero] at hcoeff
  exact hcoeff rfl

/-- Sharp finite weighted degree is equivalent to a support bound whose
component is nonzero. The bound need not be positive. -/
theorem weightedTotalDegree'_eq_coe_int_iff
    (w : σ → ℤ) (P : MvPolynomial σ R) (m : ℤ) :
    weightedTotalDegree' w P = (m : WithBot ℤ) ↔
      (∀ a ∈ P.support, Finsupp.weight w a ≤ m) ∧
        weightedHomogeneousComponent w m P ≠ 0 := by
  classical
  constructor
  · intro hdeg
    exact ⟨fun a ha => weight_le_of_weightedTotalDegree'_eq_int w P hdeg ha,
      weightedHomogeneousComponent_ne_zero_of_degree'_eq_int w P hdeg⟩
  · rintro ⟨hbound, htop⟩
    apply le_antisymm ((weightedTotalDegree'_le_coe_int_iff w P m).mpr hbound)
    obtain ⟨a, ha⟩ := MvPolynomial.exists_coeff_ne_zero htop
    have hweight : Finsupp.weight w a = m := by
      by_contra h
      rw [coeff_weightedHomogeneousComponent, if_neg h] at ha
      exact ha rfl
    have hPa : a ∈ P.support := by
      apply MvPolynomial.mem_support_iff.mpr
      simpa only [coeff_weightedHomogeneousComponent, if_pos hweight] using ha
    have hle : (Finsupp.weight w a : WithBot ℤ) ≤ weightedTotalDegree' w P :=
      Finset.le_sup (f := fun b => (Finsupp.weight w b : WithBot ℤ)) hPa
    simpa only [hweight] using hle

/-- Vanishing of the component at a support bound strictly improves that
bound, including when the polynomial itself is zero. -/
theorem weightedTotalDegree'_lt_coe_int_of_component_eq_zero
    (w : σ → ℤ) (P : MvPolynomial σ R) (m : ℤ)
    (hbound : ∀ a ∈ P.support, Finsupp.weight w a ≤ m)
    (hzero : weightedHomogeneousComponent w m P = 0) :
    weightedTotalDegree' w P < (m : WithBot ℤ) := by
  apply lt_of_le_of_ne ((weightedTotalDegree'_le_coe_int_iff w P m).mpr hbound)
  intro hdeg
  exact weightedHomogeneousComponent_ne_zero_of_degree'_eq_int w P hdeg hzero

/-- Support bounds add under multiplication, even if some product terms
cancel or the coefficient ring has zero divisors. -/
theorem weight_le_of_mem_support_mul_int
    (w : σ → ℤ) (P Q : MvPolynomial σ R) (m n : ℤ)
    (hP : ∀ a ∈ P.support, Finsupp.weight w a ≤ m)
    (hQ : ∀ a ∈ Q.support, Finsupp.weight w a ≤ n)
    {a : σ →₀ ℕ} (ha : a ∈ (P * Q).support) :
    Finsupp.weight w a ≤ m + n := by
  classical
  have hcoeff := MvPolynomial.mem_support_iff.mp ha
  rw [coeff_mul] at hcoeff
  obtain ⟨b, hb, hproduct⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcoeff
  have hp := hP b.1 (MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hproduct))
  have hq := hQ b.2 (MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hproduct))
  rw [← Finset.mem_antidiagonal.mp hb, map_add]
  exact add_le_add hp hq

/-- Subtraction preserves a common support weight bound. -/
theorem weight_le_of_mem_support_sub_int
    (w : σ → ℤ) (P Q : MvPolynomial σ R) (m : ℤ)
    (hP : ∀ a ∈ P.support, Finsupp.weight w a ≤ m)
    (hQ : ∀ a ∈ Q.support, Finsupp.weight w a ≤ m)
    {a : σ →₀ ℕ} (ha : a ∈ (P - Q).support) :
    Finsupp.weight w a ≤ m := by
  classical
  have hcoeff := MvPolynomial.mem_support_iff.mp ha
  by_cases hp : coeff a P = 0
  · have hq : coeff a Q ≠ 0 := by
      intro hzero
      simp only [coeff_sub, hp, hzero, sub_zero, ne_eq, not_true_eq_false] at hcoeff
    exact hQ a (MvPolynomial.mem_support_iff.mpr hq)
  · exact hP a (MvPolynomial.mem_support_iff.mpr hp)

/-- A constant scalar cannot raise a support weight bound. -/
theorem weight_le_of_mem_support_C_mul_int
    (w : σ → ℤ) (c : R) (P : MvPolynomial σ R) (m : ℤ)
    (hP : ∀ a ∈ P.support, Finsupp.weight w a ≤ m)
    {a : σ →₀ ℕ} (ha : a ∈ (C c * P).support) :
    Finsupp.weight w a ≤ m := by
  have hcoeff := MvPolynomial.mem_support_iff.mp ha
  rw [coeff_C_mul] at hcoeff
  exact hP a (MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hcoeff))

/-- Raising a polynomial to a natural power multiplies a support bound
by that power, with the product taken in the signed integers. -/
theorem weight_le_of_mem_support_pow_int
    (w : σ → ℤ) (P : MvPolynomial σ R) (m : ℤ) (r : ℕ)
    (hP : ∀ a ∈ P.support, Finsupp.weight w a ≤ m)
    {a : σ →₀ ℕ} (ha : a ∈ (P ^ r).support) :
    Finsupp.weight w a ≤ (r : ℤ) * m := by
  induction r generalizing a with
  | zero =>
      simp only [pow_zero] at ha
      have hweight := (isWeightedHomogeneous_one R w) (MvPolynomial.mem_support_iff.mp ha)
      simpa only [Nat.cast_zero, zero_mul] using hweight.le
  | succ r ih =>
      rw [pow_succ] at ha
      have hbound := weight_le_of_mem_support_mul_int w (P ^ r) P ((r : ℤ) * m) m
        (fun a ha => ih ha) hP ha
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hbound

/-- The component at a power's multiplied support bound is the power of
the original component, without a nonvanishing or domain hypothesis. -/
theorem weightedHomogeneousComponent_pow_top_int
    (w : σ → ℤ) (P : MvPolynomial σ R) (m : ℤ) (r : ℕ)
    (hP : ∀ a ∈ P.support, Finsupp.weight w a ≤ m) :
    weightedHomogeneousComponent w ((r : ℤ) * m) (P ^ r) =
      (weightedHomogeneousComponent w m P) ^ r := by
  induction r with
  | zero =>
      simp only [pow_zero, Nat.cast_zero, zero_mul]
      exact (isWeightedHomogeneous_one R w).weightedHomogeneousComponent_same
  | succ r ih =>
      have hmul := weightedHomogeneousComponent_mul_top_int w (P ^ r) P ((r : ℤ) * m) m
        (fun a ha => weight_le_of_mem_support_pow_int w P m r hP ha) hP
      rw [ih] at hmul
      simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hmul

/-- Every nonzero constant has signed weighted degree zero. -/
theorem weightedTotalDegree'_C_int
    (w : σ → ℤ) (c : R) (hc : c ≠ 0) :
    weightedTotalDegree' w (C c : MvPolynomial σ R) = ((0 : ℤ) : WithBot ℤ) := by
  apply (weightedTotalDegree'_eq_coe_int_iff w (C c) 0).mpr
  refine ⟨fun a ha => ((isWeightedHomogeneous_C w c)
    (MvPolynomial.mem_support_iff.mp ha)).le, ?_⟩
  rw [(isWeightedHomogeneous_C w c).weightedHomogeneousComponent_same]
  exact C_ne_zero.mpr hc

section Domain

variable [IsDomain R]

/-- Sharp finite signed weighted degrees add under multiplication over a
domain. -/
theorem weightedTotalDegree'_mul_int
    (w : σ → ℤ) (P Q : MvPolynomial σ R) (m n : ℤ)
    (hP : weightedTotalDegree' w P = (m : WithBot ℤ))
    (hQ : weightedTotalDegree' w Q = (n : WithBot ℤ)) :
    weightedTotalDegree' w (P * Q) = ((m + n : ℤ) : WithBot ℤ) := by
  have hPb : ∀ a ∈ P.support, Finsupp.weight w a ≤ m :=
    fun a ha => weight_le_of_weightedTotalDegree'_eq_int w P hP ha
  have hQb : ∀ a ∈ Q.support, Finsupp.weight w a ≤ n :=
    fun a ha => weight_le_of_weightedTotalDegree'_eq_int w Q hQ ha
  apply (weightedTotalDegree'_eq_coe_int_iff w (P * Q) (m + n)).mpr
  refine ⟨fun a ha => weight_le_of_mem_support_mul_int w P Q m n hPb hQb ha, ?_⟩
  rw [weightedHomogeneousComponent_mul_top_int w P Q m n hPb hQb]
  exact mul_ne_zero
    (weightedHomogeneousComponent_ne_zero_of_degree'_eq_int w P hP)
    (weightedHomogeneousComponent_ne_zero_of_degree'_eq_int w Q hQ)

/-- Sharp finite signed weighted degree is multiplied by natural powers. -/
theorem weightedTotalDegree'_pow_int
    (w : σ → ℤ) (P : MvPolynomial σ R) (m : ℤ) (r : ℕ)
    (hP : weightedTotalDegree' w P = (m : WithBot ℤ)) :
    weightedTotalDegree' w (P ^ r) = (((r : ℤ) * m : ℤ) : WithBot ℤ) := by
  induction r with
  | zero =>
      simpa only [pow_zero, Nat.cast_zero, zero_mul, map_one] using
        weightedTotalDegree'_C_int w (1 : R) one_ne_zero
  | succ r ih =>
      have hmul := weightedTotalDegree'_mul_int w (P ^ r) P ((r : ℤ) * m) m ih hP
      simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hmul

/-- Multiplication by a nonzero constant preserves sharp weighted degree. -/
theorem weightedTotalDegree'_C_mul_int
    (w : σ → ℤ) (c : R) (hc : c ≠ 0) (P : MvPolynomial σ R) (m : ℤ)
    (hP : weightedTotalDegree' w P = (m : WithBot ℤ)) :
    weightedTotalDegree' w (C c * P) = (m : WithBot ℤ) := by
  simpa only [zero_add] using
    weightedTotalDegree'_mul_int w (C c) P 0 m (weightedTotalDegree'_C_int w c hc) hP

end Domain

end CollisionIdeals
