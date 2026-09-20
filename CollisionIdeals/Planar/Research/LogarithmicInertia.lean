import Mathlib.RingTheory.Derivation.Basic

/-!
# Logarithmic inertia at a tame divisor

This file isolates the formal local calculation behind the proposed planar
logarithmic-inertia argument.  It proves the logarithmic weights of a
uniformizer and its principal parts, together with the corresponding inertia
characters.  It intentionally does not assert the missing global rigidity
statement connecting these local identities to planar conjugate coverage.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]

namespace LogarithmicInertia

/--
A derivation is logarithmic at an element with a supplied weight when it
sends the element to the weight times that element.
-/
def IsLogarithmicAt
    (D : Derivation ℚ K K) (t weight : K) : Prop :=
  D t = weight * t

omit [CharZero K] in
/-- A logarithmic derivation acts diagonally on every integral power. -/
theorem apply_zpow_of_isLogarithmicAt
    (D : Derivation ℚ K K) {t weight : K} (ht : t ≠ 0)
    (hlog : IsLogarithmicAt D t weight) (n : ℤ) :
    D (t ^ n) = (n : K) * weight * t ^ n := by
  rw [D.leibniz_zpow, hlog]
  have hpow : t ^ (n - 1) * t = t ^ n := by
    calc
      t ^ (n - 1) * t = t ^ (n - 1) * t ^ (1 : ℤ) := by rw [zpow_one]
      _ = t ^ ((n - 1) + 1) := (zpow_add₀ ht (n - 1) 1).symm
      _ = t ^ n := by congr 1; omega
  rw [← Int.cast_smul_eq_zsmul K]
  simp only [smul_eq_mul]
  calc
    (n : K) * (t ^ (n - 1) * (weight * t))
        = (n : K) * weight * (t ^ (n - 1) * t) := by ring
    _ = (n : K) * weight * t ^ n := by rw [hpow]

/--
For a branch parameter s = u t^e with D(s) = s, the logarithmic weight of
t is e⁻¹(1 - u⁻¹D(u)).  In particular, the weight is e⁻¹ when the unit is
horizontal.
-/
theorem isLogarithmicAt_of_eq_unit_mul_pow_general
    (D : Derivation ℚ K K) {s u t : K} {e : ℕ}
    (he : 0 < e) (hu : u ≠ 0) (ht : t ≠ 0)
    (hst : s = u * t ^ e) (hDs : D s = s) :
    IsLogarithmicAt D t ((e : K)⁻¹ * (1 - u⁻¹ * D u)) := by
  have h :
      u * ((e : K) * t ^ (e - 1) * D t) + t ^ e * D u =
        u * t ^ e := by
    calc
      u * ((e : K) * t ^ (e - 1) * D t) + t ^ e * D u
          = u * (e • t ^ (e - 1) • D t) + t ^ e * D u := by
              rw [← Nat.cast_smul_eq_nsmul K]
              simp only [smul_eq_mul]
              ring
      _ = u * D (t ^ e) + t ^ e * D u := by rw [D.leibniz_pow]
      _ = D (u * t ^ e) := by simp [D.leibniz, smul_eq_mul]
      _ = D s := by rw [← hst]
      _ = s := hDs
      _ = u * t ^ e := hst
  have h₁ :
      u * ((e : K) * t ^ (e - 1) * D t) =
        t ^ e * (u - D u) := by
    calc
      u * ((e : K) * t ^ (e - 1) * D t)
          = u * t ^ e - t ^ e * D u := eq_sub_of_add_eq h
      _ = t ^ e * (u - D u) := by ring
  have hpow : t ^ e = t ^ (e - 1) * t := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
    simp [pow_succ]
  have h₂ : u * (e : K) * D t = t * (u - D u) := by
    apply mul_left_cancel₀ (pow_ne_zero (e - 1) ht)
    calc
      t ^ (e - 1) * (u * (e : K) * D t)
          = u * ((e : K) * t ^ (e - 1) * D t) := by ring
      _ = t ^ e * (u - D u) := h₁
      _ = t ^ (e - 1) * (t * (u - D u)) := by rw [hpow]; ring
  have heK : (e : K) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt he
  have hden : u * (e : K) ≠ 0 := mul_ne_zero hu heK
  have hdiv : D t = (t * (u - D u)) / (u * (e : K)) := by
    apply (eq_div_iff hden).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using h₂
  unfold IsLogarithmicAt
  rw [hdiv]
  apply (div_eq_iff hden).2
  symm
  calc
    (e : K)⁻¹ * (1 - u⁻¹ * D u) * t * (u * (e : K))
        = ((e : K)⁻¹ * (e : K)) * t *
            ((1 - u⁻¹ * D u) * u) := by ring
    _ = t * ((1 - u⁻¹ * D u) * u) := by
      rw [inv_mul_cancel₀ heK, one_mul]
    _ = t * (u - D u) := by
      congr 1
      calc
        (1 - u⁻¹ * D u) * u = u - (u⁻¹ * u) * D u := by ring
        _ = u - D u := by rw [inv_mul_cancel₀ hu, one_mul]

/--
If the unit in s = u t^e is horizontal, then the logarithmic weight of t is
exactly e⁻¹.
-/
theorem isLogarithmicAt_of_eq_unit_mul_pow
    (D : Derivation ℚ K K) {s u t : K} {e : ℕ}
    (he : 0 < e) (hu : u ≠ 0) (ht : t ≠ 0)
    (hst : s = u * t ^ e) (hDu : D u = 0) (hDs : D s = s) :
    IsLogarithmicAt D t (e : K)⁻¹ := by
  simpa [hDu] using
    isLogarithmicAt_of_eq_unit_mul_pow_general D he hu ht hst hDs

/--
Combining the preceding two lemmas gives the expected weight n/e on every
integral power, including negative powers representing principal parts.
-/
theorem apply_zpow_of_eq_unit_mul_pow
    (D : Derivation ℚ K K) {s u t : K} {e : ℕ}
    (he : 0 < e) (hu : u ≠ 0) (ht : t ≠ 0)
    (hst : s = u * t ^ e) (hDu : D u = 0) (hDs : D s = s)
    (n : ℤ) :
    D (t ^ n) = (n : K) * (e : K)⁻¹ * t ^ n :=
  apply_zpow_of_isLogarithmicAt D ht
    (isLogarithmicAt_of_eq_unit_mul_pow D he hu ht hst hDu hDs) n

omit [CharZero K] [Algebra ℚ K] in
/-- An inertia action that scales a uniformizer acts by the expected character. -/
theorem inertia_apply_pow
    (σ : K ≃+* K) {t ζ : K} (hσ : σ t = ζ * t) (n : ℕ) :
    σ (t ^ n) = ζ ^ n * t ^ n := by
  rw [map_pow, hσ, mul_pow]

omit [CharZero K] [Algebra ℚ K] in
/--
The same character formula on a negative-power principal part, written as
the inverse of a positive power.
-/
theorem inertia_apply_inv_pow
    (σ : K ≃+* K) {t ζ : K} (hσ : σ t = ζ * t) (n : ℕ) :
    σ ((t ^ n)⁻¹) = (ζ ^ n)⁻¹ * (t ^ n)⁻¹ := by
  rw [map_inv₀, inertia_apply_pow σ hσ]
  simp [mul_comm]

/--
Supplied tame local data at one ramified divisor.  Constructing this package
from a completed height-one point of the polynomial normalization remains a
separate geometric step.
-/
structure TameParameterData
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K] where
  derivation : Derivation ℚ K K
  inertiaAction : K ≃+* K
  branchParameter : K
  unit : K
  uniformizer : K
  inertiaScalar : K
  ramificationIndex : ℕ
  ramificationIndex_pos : 0 < ramificationIndex
  unit_ne_zero : unit ≠ 0
  uniformizer_ne_zero : uniformizer ≠ 0
  branch_eq :
    branchParameter = unit * uniformizer ^ ramificationIndex
  derivation_branch :
    derivation branchParameter = branchParameter
  inertia_uniformizer :
    inertiaAction uniformizer = inertiaScalar * uniformizer
  inertiaScalar_pow :
    inertiaScalar ^ ramificationIndex = 1

namespace TameParameterData

variable (T : TameParameterData K)

/-- The actual logarithmic weight, including the derivative of the unit. -/
def logarithmicWeight : K :=
  (T.ramificationIndex : K)⁻¹ *
    (1 - T.unit⁻¹ * T.derivation T.unit)

/-- The supplied derivation is logarithmic at the local uniformizer. -/
theorem derivation_isLogarithmicAt :
    IsLogarithmicAt T.derivation T.uniformizer T.logarithmicWeight :=
  isLogarithmicAt_of_eq_unit_mul_pow_general
    T.derivation T.ramificationIndex_pos T.unit_ne_zero
    T.uniformizer_ne_zero T.branch_eq T.derivation_branch

/-- Every integral power of the uniformizer has its predicted logarithmic weight. -/
theorem derivation_apply_zpow (n : ℤ) :
    T.derivation (T.uniformizer ^ n) =
      (n : K) * T.logarithmicWeight * T.uniformizer ^ n :=
  apply_zpow_of_isLogarithmicAt T.derivation T.uniformizer_ne_zero
    T.derivation_isLogarithmicAt n

/-- The chosen inertia action has the expected character on positive powers. -/
theorem inertia_apply_pow' (n : ℕ) :
    T.inertiaAction (T.uniformizer ^ n) =
      T.inertiaScalar ^ n * T.uniformizer ^ n :=
  inertia_apply_pow T.inertiaAction T.inertia_uniformizer n

/-- The chosen inertia action has the expected character on principal parts. -/
theorem inertia_apply_inv_pow' (n : ℕ) :
    T.inertiaAction ((T.uniformizer ^ n)⁻¹) =
      (T.inertiaScalar ^ n)⁻¹ * (T.uniformizer ^ n)⁻¹ :=
  inertia_apply_inv_pow T.inertiaAction T.inertia_uniformizer n

/-- Every pole whose order is a multiple of the ramification index is
inertia-invariant. Thus killing the nontrivial inertia characters does not
itself bound the orders of the surviving principal parts. -/
theorem inertia_apply_inv_pow_mul_ramificationIndex (n : ℕ) :
    T.inertiaAction ((T.uniformizer ^ (T.ramificationIndex * n))⁻¹) =
      (T.uniformizer ^ (T.ramificationIndex * n))⁻¹ := by
  rw [T.inertia_apply_inv_pow', pow_mul, T.inertiaScalar_pow]
  simp

/-- Even when the tame unit is horizontal, the logarithmic derivation
acts on every surviving invariant pole: its weight is `-n`, not a
vanishing statement. This calculation supplies no uniform pole bound. -/
theorem derivation_apply_inv_pow_mul_ramificationIndex
    (hunit : T.derivation T.unit = 0) (n : ℕ) :
    T.derivation ((T.uniformizer ^ (T.ramificationIndex * n))⁻¹) =
      -(n : K) * (T.uniformizer ^ (T.ramificationIndex * n))⁻¹ := by
  have h := apply_zpow_of_eq_unit_mul_pow T.derivation
    T.ramificationIndex_pos T.unit_ne_zero T.uniformizer_ne_zero
    T.branch_eq hunit T.derivation_branch
    (-((T.ramificationIndex * n : ℕ) : ℤ))
  simp only [zpow_neg, zpow_natCast] at h
  simp only [Int.cast_neg, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at h
  have he : (T.ramificationIndex : K) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt T.ramificationIndex_pos
  rw [h]
  calc
    _ = -(n : K) * ((T.ramificationIndex : K) *
        (T.ramificationIndex : K)⁻¹) *
        (T.uniformizer ^ (T.ramificationIndex * n))⁻¹ := by ring
    _ = _ := by rw [mul_inv_cancel₀ he, mul_one]

end TameParameterData

end LogarithmicInertia

end

end CollisionIdeals.Planar
