import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Derivative defects of fixed fractional stages

The quotient rule separates the derivative of the numerator from the
derivative of the denominator. A one-step denominator for a finite order
therefore puts the derivative of a pole-order stage in the next stage,
not necessarily in the same stage.

These identities do not construct a fixed fractional lattice containing
an entire differential orbit. They impose no normalization or Keller
regularity premise.
-/

set_option autoImplicit false

namespace CollisionIdeals

section Ring

variable {k N : Type*} [CommRing k] [CommRing N] [Algebra k N]

/-- An exact numerator identity for one derivative. It remains valid at
`s = 0`, before interpreting powers of `s` as denominators. -/
theorem pow_succ_mul_derivation_eq_fractional_numerator
    (delta : Derivation k N N) (s : N) (m : ℕ) (z : N) :
    s ^ (m + 1) * delta z =
      s * delta (s ^ m * z) - (m : N) * delta s * (s ^ m * z) := by
  have hpow : s * delta (s ^ m) = (m : N) * delta s * s ^ m := by
    cases m with
    | zero => simp
    | succ m =>
        rw [delta.leibniz_pow]
        simp only [Nat.succ_sub_one, nsmul_eq_mul, smul_eq_mul, pow_succ]
        ring
  rw [delta.leibniz]
  simp only [smul_eq_mul, mul_add]
  rw [← mul_assoc s z (delta (s ^ m)), mul_comm s z,
    mul_assoc z s (delta (s ^ m)), hpow]
  simp only [pow_succ]
  ring

/-- Clearing derivatives of all order elements and differentiating the
denominator keeps the resulting numerator in the same order. -/
theorem fractional_derivation_numerator_mem
    (delta : Derivation k N N) (T : Subalgebra k N) (s : N)
    (hDeltaS : delta s ∈ T)
    (hClear : ∀ t ∈ T, s * delta t ∈ T)
    (m : ℕ) {t : N} (ht : t ∈ T) :
    s * delta t - (m : N) * delta s * t ∈ T := by
  exact T.sub_mem (hClear t ht)
    (T.mul_mem (T.mul_mem (T.natCast_mem m) hDeltaS) ht)

/-- The same one-step clearing estimate raises the denominator exponent
by at most one. It supplies no exponent uniform in derivative order. -/
theorem pow_succ_mul_derivation_mem_of_pow_mul_mem
    (delta : Derivation k N N) (T : Subalgebra k N) (s : N)
    (hDeltaS : delta s ∈ T)
    (hClear : ∀ t ∈ T, s * delta t ∈ T)
    (m : ℕ) {z : N} (hz : s ^ m * z ∈ T) :
    s ^ (m + 1) * delta z ∈ T := by
  rw [pow_succ_mul_derivation_eq_fractional_numerator]
  exact fractional_derivation_numerator_mem delta T s hDeltaS hClear m hz

end Ring

section Field

variable {k N : Type*} [CommRing k] [Field N] [Algebra k N]

/-- Exact defect of preserving a fixed fractional stage. Dividing by a
larger power changes the numerator by the logarithmic denominator term. -/
theorem pow_succ_mul_derivation_inv_pow_mul
    (delta : Derivation k N N) (s : N) (hs : s ≠ 0) (m : ℕ) (t : N) :
    s ^ (m + 1) * delta ((s ^ m)⁻¹ * t) =
      s * delta t - (m : N) * delta s * t := by
  have hcancel : s ^ m * ((s ^ m)⁻¹ * t) = t := by
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hs), one_mul]
  rw [pow_succ_mul_derivation_eq_fractional_numerator, hcancel]

/-- Whole-stage preservation already forces the logarithmic denominator
derivative to be integral after multiplication by the stage exponent.
This follows just by testing the numerator `1`; it does not assert that
the orbit of a particular element fills the whole fractional stage. -/
theorem natCast_mul_logarithmic_derivation_mem_of_fractional_preservation
    (delta : Derivation k N N) (T : Subalgebra k N)
    (s : N) (hs : s ≠ 0) (m : ℕ)
    (hPreserved : ∀ t ∈ T, s ^ m * delta ((s ^ m)⁻¹ * t) ∈ T) :
    (m : N) * (delta s / s) ∈ T := by
  have hvalue : s ^ m * delta ((s ^ m)⁻¹) =
      -((m : N) * (delta s / s)) := by
    apply mul_left_cancel₀ hs
    calc
      s * (s ^ m * delta ((s ^ m)⁻¹)) =
          s ^ (m + 1) * delta ((s ^ m)⁻¹) := by
        rw [pow_succ]
        ring
      _ = -((m : N) * delta s) := by
        simpa using pow_succ_mul_derivation_inv_pow_mul delta s hs m 1
      _ = s * -((m : N) * (delta s / s)) := by
        field_simp
  have h := hPreserved 1 T.one_mem
  simp only [mul_one] at h
  rw [hvalue] at h
  simpa only [neg_neg] using T.neg_mem h

end Field

end CollisionIdeals
