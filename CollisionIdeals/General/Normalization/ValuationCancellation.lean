import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.Finset.Max

/-!
# Cancellation among maximal valuation terms

If a finite sum has value at most `a`, but one summand has value greater
than `a`, its maximal summand value is attained at least twice. This is
the finite-sum ultrametric cancellation statement; no geometric or
Keller-specific regularity conclusion is included.
-/

set_option autoImplicit false

namespace CollisionIdeals

variable {R Γ₀ ι : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]

/-- A term above the value bound on the sum forces two distinct terms
with the same maximal value, also above that bound. -/
theorem exists_distinct_valuation_max_of_sum_le_of_lt
    (v : Valuation R Γ₀) (s : Finset ι) (f : ι → R) {j : ι} {a : Γ₀}
    (hj : j ∈ s) (hsum : v (∑ i ∈ s, f i) ≤ a) (hja : a < v (f j)) :
    ∃ i ∈ s, ∃ k ∈ s, i ≠ k ∧ v (f i) = v (f k) ∧ a < v (f i) ∧
      ∀ l ∈ s, v (f l) ≤ v (f i) := by
  classical
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image (fun l => v (f l)) ⟨j, hj⟩
  have hai : a < v (f i) := lt_of_lt_of_le hja (hmax j hj)
  have hsecond : ∃ k ∈ s, k ≠ i ∧ v (f k) = v (f i) := by
    by_contra h
    have hstrict : ∀ k ∈ s \ {i}, v (f k) < v (f i) := by
      intro k hk
      obtain ⟨hks, hkn⟩ := Finset.mem_sdiff.mp hk
      have hki : k ≠ i := by simpa only [Finset.mem_singleton] using hkn
      apply lt_of_le_of_ne (hmax k hks)
      intro hvalue
      exact h ⟨k, hks, hki, hvalue⟩
    have heq := v.map_sum_eq_of_lt hi hstrict
    exact (not_le_of_gt hai) (heq ▸ hsum)
  obtain ⟨k, hk, hki, hvalue⟩ := hsecond
  exact ⟨i, hi, k, hk, hki.symm, hvalue.symm, hai, hmax⟩

end CollisionIdeals
