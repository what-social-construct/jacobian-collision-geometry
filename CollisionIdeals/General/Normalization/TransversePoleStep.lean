import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# A transverse derivative produces the next unit numerator

In a local algebra over a characteristic-zero field, let `f` lie in the
maximal ideal and have unit derivative. Differentiating a fraction `u / f^m`
with unit numerator and positive exponent produces a unit numerator over
`f^(m+1)`. The numerator cannot cancel against the same boundary parameter.

This is an actual algebraic next step, not a premise that a differential
orbit lies in a finite lattice. It supplies neither a Keller-specific lattice
nor regularity of a field derivation on a normalization boundary local ring.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

section Local

variable {k R : Type*} [Field k] [CharZero k] [CommRing R]
  [Algebra k R] [IsLocalRing R]

/-- The derivative numerator is a unit at the same local boundary: its
first term lies in the maximal ideal and its second term is a unit.
The coefficient-field hypothesis ensures every positive natural number
is a unit, unlike characteristic zero of the local ring alone. -/
theorem isUnit_transverse_pole_numerator
    (d : Derivation k R R) {f u : R}
    (hf : f ∈ IsLocalRing.maximalIdeal R)
    (hdf : IsUnit (d f)) (hu : IsUnit u)
    (m : ℕ) (hm : 0 < m) :
    IsUnit (f * d u - (m : R) * u * d f) := by
  have hmUnit : IsUnit (m : R) := by
    have hmField : IsUnit (m : k) :=
      isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm))
    simpa only [map_natCast] using hmField.map (algebraMap k R)
  have hSecond : IsUnit ((m : R) * u * d f) := (hmUnit.mul hu).mul hdf
  apply IsLocalRing.notMem_maximalIdeal.mp
  intro hNumerator
  have hFirst : f * d u ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.maximalIdeal R).mul_mem_right (d u) hf
  have hSecondMem : (m : R) * u * d f ∈ IsLocalRing.maximalIdeal R := by
    have h := (IsLocalRing.maximalIdeal R).sub_mem hFirst hNumerator
    simpa only [sub_sub_cancel] using h
  exact (IsLocalRing.notMem_maximalIdeal.mpr hSecond) hSecondMem

end Local

section Field

variable {k R K : Type*} [CommRing k] [CommRing R] [Field K]
  [Algebra k R] [Algebra k K] [Algebra R K]

/-- The exact derivative formula for a positive power denominator, for
any compatible field extension of the local derivation. -/
theorem transverse_pole_derivative_eq
    (d : Derivation k R R) (dK : Derivation k K K)
    (hExtend : ∀ a : R, dK (algebraMap R K a) = algebraMap R K (d a))
    (f u : R) (hf : algebraMap R K f ≠ 0)
    (m : ℕ) (hm : 0 < m) :
    dK (algebraMap R K u / algebraMap R K f ^ m) =
      algebraMap R K (f * d u - (m : R) * u * d f) /
        algebraMap R K f ^ (m + 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  rw [dK.leibniz_div, dK.leibniz_pow, hExtend, hExtend]
  simp only [Nat.succ_sub_one, smul_eq_mul, nsmul_eq_mul,
    map_sub, map_mul, map_natCast]
  field_simp
  simp only [pow_succ]
  ring

end Field

section LocalField

variable {k R K : Type*} [Field k] [CharZero k] [CommRing R]
  [Algebra k R] [IsLocalRing R] [Field K] [Algebra k K] [Algebra R K]

/-- A concrete next numerator with the same parameter and exponent
increased by one. No complete discrete valuation field is required. -/
theorem exists_unit_transverse_pole_derivative_numerator
    (d : Derivation k R R) (dK : Derivation k K K)
    (hExtend : ∀ a : R, dK (algebraMap R K a) = algebraMap R K (d a))
    {f u : R} (hf : f ∈ IsLocalRing.maximalIdeal R)
    (hfK : algebraMap R K f ≠ 0)
    (hdf : IsUnit (d f)) (hu : IsUnit u)
    (m : ℕ) (hm : 0 < m) :
    ∃ u' : R, IsUnit u' ∧
      dK (algebraMap R K u / algebraMap R K f ^ m) =
        algebraMap R K u' / algebraMap R K f ^ (m + 1) :=
  ⟨f * d u - (m : R) * u * d f,
    isUnit_transverse_pole_numerator d hf hdf hu m hm,
    transverse_pole_derivative_eq d dK hExtend f u hfK m hm⟩

/-- Iterating the actual derivative constructs a unit numerator at every
order, with the same boundary parameter and exponent `m + n`. The unit
condition is derived recursively; no pole-tower or sequence-existence
hypothesis is supplied. -/
theorem exists_unit_iterated_transverse_pole_numerator
    (d : Derivation k R R) (dK : Derivation k K K)
    (hExtend : ∀ a : R, dK (algebraMap R K a) = algebraMap R K (d a))
    {f u : R} (hf : f ∈ IsLocalRing.maximalIdeal R)
    (hfK : algebraMap R K f ≠ 0)
    (hdf : IsUnit (d f)) (hu : IsUnit u)
    (m : ℕ) (hm : 0 < m) (n : ℕ) :
    ∃ u_n : R, IsUnit u_n ∧
      ((dK : K → K)^[n]) (algebraMap R K u / algebraMap R K f ^ m) =
        algebraMap R K u_n / algebraMap R K f ^ (m + n) := by
  induction n with
  | zero => exact ⟨u, hu, by simp⟩
  | succ n ih =>
      obtain ⟨v, hv, hOrbit⟩ := ih
      have hmAdd : 0 < m + n := lt_of_lt_of_le hm (Nat.le_add_right m n)
      obtain ⟨w, hw, hNext⟩ := exists_unit_transverse_pole_derivative_numerator
        d dK hExtend hf hfK hdf hv (m + n) hmAdd
      refine ⟨w, hw, ?_⟩
      rw [Function.iterate_succ_apply', hOrbit, hNext]
      simp only [Nat.add_assoc]

end LocalField

end

end CollisionIdeals
