import CollisionIdeals.General.Normalization.DerivationOrbit
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Finite-order annihilators for an iterated Leibniz orbit

If `a` kills a class, the power `a^(r+1)` kills every frame derivative
of word length at most `r`. The proof uses only Leibniz and permits
noncommuting operators. It supplies an order-dependent denominator,
not a fixed exponent or a common annihilator for the entire orbit.
-/

set_option autoImplicit false

namespace CollisionIdeals

section General

variable {σ k B M : Type*} [CommRing k] [CommRing B] [Algebra k B]
  [AddCommMonoid M] [Module B M]

private theorem mul_derivation_pow
    (d : Derivation k B B) (a : B) (r : ℕ) :
    a * d (a ^ r) = (r : B) * d a * a ^ r := by
  cases r with
  | zero => simp
  | succ r =>
      rw [d.leibniz_pow]
      simp only [Nat.succ_sub_one, nsmul_eq_mul, smul_eq_mul, pow_succ]
      ring

/-- Differentiating a class killed by a power of `a` needs at most one
further power. No characteristic or commuting-operator premise is used. -/
theorem pow_succ_smul_leibniz_eq_zero_of_pow_smul_eq_zero
    (d : Derivation k B B) (nabla : M →+ M)
    (hLeibniz : ∀ (b : B) (m : M),
      nabla (b • m) = d b • m + b • nabla m)
    (a : B) (q : M) (r : ℕ) (hkill : a ^ r • q = 0) :
    a ^ (r + 1) • nabla q = 0 := by
  have h := congrArg (fun m : M => a • m) (hLeibniz (a ^ r) q)
  have hFirst : a • (d (a ^ r) • q) = 0 := by
    rw [smul_smul, mul_derivation_pow]
    rw [mul_smul, hkill, smul_zero]
  dsimp only at h
  rw [hkill, map_zero, smul_zero, smul_add, hFirst, zero_add] at h
  simpa only [smul_smul, pow_succ, mul_comm] using h.symm

/-- One annihilator for the initial class yields a denominator bound
linear in the derivative word length. It does not make that bound uniform
over all lengths. -/
theorem pow_length_succ_smul_derivationWordAction_eq_zero
    (d : σ → Derivation k B B) (nabla : σ → M →+ M)
    (hLeibniz : ∀ (i : σ) (b : B) (m : M),
      nabla i (b • m) = d i b • m + b • nabla i m)
    (a : B) (q : M) (haq : a • q = 0) (word : List σ) :
    a ^ (word.length + 1) • derivationWordAction nabla word q = 0 := by
  induction word with
  | nil => simpa [derivationWordAction] using haq
  | cons i word ih =>
      simpa [derivationWordAction] using
        pow_succ_smul_leibniz_eq_zero_of_pow_smul_eq_zero
          (d i) (nabla i) (hLeibniz i) a
          (derivationWordAction nabla word q) (word.length + 1) ih

/-- At any fixed derivative order there is a common power denominator
for all words up to that order, even when the indexing type is infinite. -/
theorem pow_order_succ_smul_derivationWordAction_eq_zero
    (d : σ → Derivation k B B) (nabla : σ → M →+ M)
    (hLeibniz : ∀ (i : σ) (b : B) (m : M),
      nabla i (b • m) = d i b • m + b • nabla i m)
    (a : B) (q : M) (haq : a • q = 0) (r : ℕ)
    (word : List σ) (hword : word.length ≤ r) :
    a ^ (r + 1) • derivationWordAction nabla word q = 0 := by
  have hkill := pow_length_succ_smul_derivationWordAction_eq_zero
    d nabla hLeibniz a q haq word
  have hExp : r + 1 = (r - word.length) + (word.length + 1) := by omega
  rw [hExp, pow_add, mul_smul, hkill, smul_zero]

end General

section Domain

variable {σ k B M : Type*} [CommRing k] [CommRing B] [IsDomain B] [Algebra k B]
  [AddCommMonoid M] [Module B M]

/-- Torsion of one class supplies a nonzero denominator at each finite
order. The chosen denominator is allowed to depend on that order. -/
theorem exists_nonzero_finite_order_derivation_annihilator
    (d : σ → Derivation k B B) (nabla : σ → M →+ M)
    (hLeibniz : ∀ (i : σ) (b : B) (m : M),
      nabla i (b • m) = d i b • m + b • nabla i m)
    (q : M) (hTorsion : ∃ a : B, a ≠ 0 ∧ a • q = 0) (r : ℕ) :
    ∃ a : B, a ≠ 0 ∧ ∀ word : List σ, word.length ≤ r →
      a • derivationWordAction nabla word q = 0 := by
  obtain ⟨a, ha, haq⟩ := hTorsion
  exact ⟨a ^ (r + 1), pow_ne_zero _ ha,
    fun word hword => pow_order_succ_smul_derivationWordAction_eq_zero
      d nabla hLeibniz a q haq r word hword⟩

end Domain

end CollisionIdeals
