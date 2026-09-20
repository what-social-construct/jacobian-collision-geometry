import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.Data.Nat.Find

/-!
# Transversality in a polynomial base

Over a field of characteristic zero, a nonzero proper polynomial ideal is
not preserved by every coordinate partial derivative. In particular, a
nonzero prime of the polynomial base contains an element transverse to a
coordinate derivation. No height or principality hypothesis is needed.

This statement concerns only the polynomial base. It does not establish
that a field extension of the chosen derivation preserves a normalization
local ring at a boundary prime.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

open MvPolynomial

variable {σ k : Type*} [Field k] [CharZero k]

omit [CharZero k] in
/-- Multiplying a coordinate derivative by its coordinate restores each
monomial exponent, multiplying its coefficient by that exponent. -/
theorem coeff_X_mul_pderiv (i : σ) (m : σ →₀ ℕ) (f : MvPolynomial σ k) :
    coeff m (X i * pderiv i f) = (m i : k) * coeff m f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial s a =>
      rw [X_mul_pderiv_monomial, coeff_smul]
      by_cases h : s = m
      · subst s
        simp [nsmul_eq_mul]
      · simp [coeff_monomial, h]
  | add p q hp hq =>
      simp only [map_add, mul_add, coeff_add, hp, hq]

/-- In characteristic zero, a polynomial killed by all coordinate partials
is constant. -/
theorem eq_C_of_forall_pderiv_eq_zero (f : MvPolynomial σ k)
    (hf : ∀ i, pderiv i f = 0) : f = C (coeff 0 f) := by
  classical
  ext m
  by_cases hm : m = 0
  · subst m
    simp
  · have hex : ∃ i, m i ≠ 0 := by
      by_contra! h
      exact hm (Finsupp.ext h)
    obtain ⟨i, hi⟩ := hex
    have hcoeff := coeff_X_mul_pderiv i m f
    rw [hf i, mul_zero, coeff_zero] at hcoeff
    have hz : coeff m f = 0 :=
      (mul_eq_zero.mp hcoeff.symm).resolve_left (Nat.cast_ne_zero.mpr hi)
    simp [coeff_C, Ne.symm hm, hz]

/-- Every nonconstant polynomial in characteristic zero has a nonzero
coordinate partial derivative. -/
theorem exists_pderiv_ne_zero_of_ne_C (f : MvPolynomial σ k)
    (hf : f ≠ C (coeff 0 f)) : ∃ i, pderiv i f ≠ 0 := by
  by_contra! h
  exact hf (eq_C_of_forall_pderiv_eq_zero f h)

omit [CharZero k] in
/-- A nonzero coordinate partial has strictly smaller total degree. -/
theorem totalDegree_pderiv_lt (i : σ) (f : MvPolynomial σ k)
    (hf : pderiv i f ≠ 0) : (pderiv i f).totalDegree < f.totalDegree := by
  classical
  obtain ⟨m, hm, hdegree⟩ := (pderiv i f).support.exists_mem_eq_sup
    (Finsupp.support_nonempty_iff.mpr hf) (fun m : σ →₀ ℕ => m.sum fun _ n => n)
  have hcoeff : coeff (Finsupp.single i 1 + m) f ≠ 0 := by
    intro hzero
    have heq := coeff_X_mul_pderiv i (Finsupp.single i 1 + m) f
    rw [coeff_X_mul, hzero, mul_zero] at heq
    exact (mem_support_iff.mp hm) heq
  have hle := le_totalDegree (mem_support_iff.mpr hcoeff)
  have hsum : (Finsupp.single i 1 + m).sum (fun _ n => n) =
      1 + m.sum (fun _ n => n) := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    simp
  rw [hsum] at hle
  change (pderiv i f).support.sup (fun m : σ →₀ ℕ => m.sum fun _ n => n) < _
  rw [hdegree]
  omega

/-- Every nonzero proper polynomial ideal over a characteristic-zero field
contains an element transverse to some coordinate partial derivative. -/
theorem exists_mem_pderiv_not_mem (I : Ideal (MvPolynomial σ k))
    (hzero : I ≠ ⊥) (htop : I ≠ ⊤) :
    ∃ b ∈ I, ∃ i, pderiv i b ∉ I := by
  classical
  obtain ⟨f, hf, hfzero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hzero
  have hex : ∃ n : ℕ, ∃ b : MvPolynomial σ k,
      b ∈ I ∧ b ≠ 0 ∧ b.totalDegree = n :=
    ⟨f.totalDegree, f, hf, hfzero, rfl⟩
  obtain ⟨b, hb, hbzero, hdegree⟩ := Nat.find_spec hex
  have hbconstant : b ≠ C (coeff 0 b) := by
    intro hconstant
    have hc : coeff 0 b ≠ 0 := by
      intro hc
      apply hbzero
      rw [hconstant, hc, map_zero]
    exact htop (I.eq_top_of_isUnit_mem hb
      (hconstant ▸ (isUnit_iff_ne_zero.mpr hc).map C))
  obtain ⟨i, hi⟩ := exists_pderiv_ne_zero_of_ne_C b hbconstant
  refine ⟨b, hb, i, ?_⟩
  intro hmem
  have hminimal := Nat.find_min' hex
    (show ∃ c : MvPolynomial σ k,
      c ∈ I ∧ c ≠ 0 ∧ c.totalDegree = (pderiv i b).totalDegree from
      ⟨pderiv i b, hmem, hi, rfl⟩)
  have hlt := totalDegree_pderiv_lt i b hi
  omega

/-- The prime-ideal specialization used for a polynomial base divisor. -/
theorem exists_mem_pderiv_not_mem_prime (p : Ideal (MvPolynomial σ k))
    [p.IsPrime] (hp : p ≠ ⊥) : ∃ b ∈ p, ∃ i, pderiv i b ∉ p :=
  exists_mem_pderiv_not_mem p hp (Ideal.IsPrime.ne_top inferInstance)

end

end CollisionIdeals
