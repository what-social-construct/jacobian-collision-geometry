import CollisionIdeals.General.Keller.MonomialWeights
import CollisionIdeals.General.Normalization.ValuationCancellation

/-!
# Polar cancellation in a polynomial Keller component

If a source coordinate has a pole while all output coordinates are regular,
some component has two distinct dominant polar monomials of equal value.
The component and monomials come from the actual finite polynomial supports.

This is a necessary cancellation certificate, not an exclusion of all poles.
The Keller input used here is the nonsingular linear part at the origin.
No no-cancellation hypothesis, degree restriction, or regularity of the
source-coordinate tuple is assumed.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

open MvPolynomial

variable {k N Γ₀ : Type*} [Field k] [Field N] [Algebra k N]
variable [LinearOrderedCommGroupWithZero Γ₀] {n : ℕ}

/-- A source-coordinate pole forces a repeated dominant polar value in
the support of an actual Keller component. Constants are measured with
their usual trivial valuation. -/
theorem exists_dominant_monomial_pair_of_isKeller_of_coordinate_pole
    (F : PolynomialSelfMap k n) (hKeller : IsKeller F)
    (φ : MvPolynomial (Fin n) k →ₐ[k] N) (v : Valuation N Γ₀)
    (hScalar : ∀ c : k, c ≠ 0 → v (algebraMap k N c) = 1)
    (hRegular : ∀ j : Fin n, v (φ (F j)) ≤ 1)
    (i : Fin n) (hPole : 1 < v (φ (X i))) :
    ∃ j : Fin n, ∃ a ∈ (F j).support, ∃ b ∈ (F j).support,
      a ≠ b ∧
      v (φ (monomial a (coeff a (F j)))) =
        v (φ (monomial b (coeff b (F j)))) ∧
      1 < v (φ (monomial a (coeff a (F j)))) ∧
      ∀ m ∈ (F j).support,
        v (φ (monomial m (coeff m (F j)))) ≤
          v (φ (monomial a (coeff a (F j)))) := by
  classical
  obtain ⟨j, hj⟩ := exists_linearCoeff_ne_zero_of_isKeller F hKeller i
  have hLinear :
      φ (monomial (Finsupp.single i 1) (coeff (Finsupp.single i 1) (F j))) =
        algebraMap k N (coeff (Finsupp.single i 1) (F j)) * φ (X i) := by
    rw [← C_mul_X_eq_monomial, map_mul]
    rw [← MvPolynomial.algebraMap_eq, φ.commutes]
  have hLinearPole :
      1 < v (φ (monomial (Finsupp.single i 1) (coeff (Finsupp.single i 1) (F j)))) := by
    rw [hLinear, map_mul, hScalar _ hj, one_mul]
    exact hPole
  have hSum :
      v (∑ m ∈ (F j).support, φ (monomial m (coeff m (F j)))) ≤ 1 := by
    rw [← map_sum, support_sum_monomial_coeff]
    exact hRegular j
  obtain ⟨a, ha, b, hb, hab, hval, hpolar, hmax⟩ :=
    exists_distinct_valuation_max_of_sum_le_of_lt v (F j).support
      (fun m => φ (monomial m (coeff m (F j))))
      (MvPolynomial.mem_support_iff.mpr hj) hSum hLinearPole
  exact ⟨j, a, ha, b, hb, hab, hval, hpolar, hmax⟩

end

end CollisionIdeals
