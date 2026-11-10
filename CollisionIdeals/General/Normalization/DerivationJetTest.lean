import CollisionIdeals.General.Normalization.DerivationOrbit

/-!
# A finite derivative-jet test for a proposed annihilator

A single nonzero polynomial annihilating every derivative word through
its own total degree forces the original module class to vanish. Strong
induction on degree uses the Leibniz rule to transfer the same finite
test to a nonzero coordinate derivative of that polynomial.

This gives a quantitative failure test for any proposed uniform
denominator. It does not construct such a denominator from elementwise
torsion, nor identify a growing finite-order bound with a uniform one.
No commutation of the module operators is required.
-/

set_option autoImplicit false

namespace CollisionIdeals

open MvPolynomial

variable {σ k B M : Type*} [Field k] [CharZero k] [CommRing B] [Algebra k B]
  [AddCommMonoid M] [Module B M]

/-- A fixed nonzero polynomial killing all derivative words through an
order at least its total degree forces the original class to vanish.
The scalar polynomial is unchanged as the tested word varies. -/
theorem eq_zero_of_polynomial_annihilates_derivationJet
    (e : MvPolynomial σ k ≃ₐ[k] B) (nabla : σ → M →+ M)
    (hLeibniz : ∀ (i : σ) (b : B) (m : M),
      nabla i (b • m) = polynomialEquivPartial e i b • m + b • nabla i m)
    (q : M) (r : ℕ) (f : MvPolynomial σ k) (hf : f ≠ 0)
    (hDegree : f.totalDegree ≤ r)
    (hJet : ∀ word : List σ, word.length ≤ r →
      e f • derivationWordAction nabla word q = 0) : q = 0 := by
  classical
  induction r using Nat.strong_induction_on generalizing f with
  | h r ih =>
      by_cases hConstant : f = C (coeff 0 f)
      · have hc : coeff 0 f ≠ 0 := by
          intro hc
          apply hf
          rw [hConstant, hc, map_zero]
        have hInverse : e (C ((coeff 0 f)⁻¹)) * e f = 1 := by
          rw [show e f = e (C (coeff 0 f)) from congrArg e hConstant,
            ← map_mul, ← map_mul, inv_mul_cancel₀ hc, map_one, map_one]
        have hq := hJet [] (Nat.zero_le r)
        simp only [derivationWordAction_nil] at hq
        have h := congrArg (fun m : M => e (C ((coeff 0 f)⁻¹)) • m) hq
        simpa only [smul_smul, hInverse, one_smul, smul_zero] using h
      · obtain ⟨i, hi⟩ := exists_pderiv_ne_zero_of_ne_C f hConstant
        have hLower : (pderiv i f).totalDegree < r :=
          lt_of_lt_of_le (totalDegree_pderiv_lt i f hi) hDegree
        apply ih (pderiv i f).totalDegree hLower (pderiv i f) hi le_rfl
        intro word hWord
        have hWordr : word.length ≤ r := le_trans hWord hLower.le
        have hConsr : (i :: word).length ≤ r := by
          simp only [List.length_cons]
          omega
        have hNext : e f • nabla i (derivationWordAction nabla word q) = 0 := by
          simpa only [derivationWordAction_cons] using hJet (i :: word) hConsr
        have h := congrArg (nabla i) (hJet word hWordr)
        rw [hLeibniz, polynomialEquivPartial_apply_equiv, map_zero,
          hNext, add_zero] at h
        exact h

/-- It suffices to test through the proposed annihilator's own degree. -/
theorem eq_zero_of_polynomial_annihilates_degree_jet
    (e : MvPolynomial σ k ≃ₐ[k] B) (nabla : σ → M →+ M)
    (hLeibniz : ∀ (i : σ) (b : B) (m : M),
      nabla i (b • m) = polynomialEquivPartial e i b • m + b • nabla i m)
    (q : M) (f : MvPolynomial σ k) (hf : f ≠ 0)
    (hJet : ∀ word : List σ, word.length ≤ f.totalDegree →
      e f • derivationWordAction nabla word q = 0) : q = 0 :=
  eq_zero_of_polynomial_annihilates_derivationJet
    e nabla hLeibniz q f.totalDegree f hf le_rfl hJet

/-- Every nonzero class defeats a proposed nonzero annihilator by a
derivative word whose length is at most that polynomial's total degree. -/
theorem exists_derivationWord_not_annihilated_length_le_degree
    (e : MvPolynomial σ k ≃ₐ[k] B) (nabla : σ → M →+ M)
    (hLeibniz : ∀ (i : σ) (b : B) (m : M),
      nabla i (b • m) = polynomialEquivPartial e i b • m + b • nabla i m)
    (q : M) (hq : q ≠ 0) (f : MvPolynomial σ k) (hf : f ≠ 0) :
    ∃ word : List σ, word.length ≤ f.totalDegree ∧
      e f • derivationWordAction nabla word q ≠ 0 := by
  by_contra! hJet
  exact hq (eq_zero_of_polynomial_annihilates_degree_jet e nabla hLeibniz q f hf hJet)

end CollisionIdeals
