import CollisionIdeals.Planar.Research.KellerFrameExtension
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# A unit-Jacobian diagnostic on a proper open set

In the actual rational function field `ℂ(t,z)`, put `u = 2*t*z`.
The source-coordinate derivations dual to `(t,u)` give the target pair
`(t^2,z)` determinant one. Its first target-dual derivation nevertheless
takes `t` to `1/(2*t)`, which is not in the polynomial ring `ℂ[t,z]`.

In source coordinates this is `(t,u) ↦ (t^2,u/(2*t))` on `t ≠ 0`.
It is not a polynomial map on the full affine plane and is not a
counterexample to the Jacobian conjecture. It records why a unit Jacobian
on an open source does not imply derivative regularity on its boundary.

The cubic variant `(t,u) ↦ (t^3-3*t,u/(3*t^2-3))` also has determinant
one on its domain, and every complex target point has a preimage in that
domain. Its target derivative still fails to preserve `ℂ[t,z]`. Thus
missing an entire base divisor is not essential to the diagnostic.
The statements below verify point-surjectivity and field identities, not
a construction of the cubic normal closure or its inertia action.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals.Planar

noncomputable section

local notation "N₀" => FractionRing PlanePolynomial
local notation "t₀" =>
  (algebraMap PlanePolynomial N₀ (MvPolynomial.X 0))
local notation "z₀" =>
  (algebraMap PlanePolynomial N₀ (MvPolynomial.X 1))
local notation "u₀" => (2 * t₀ * z₀)
local notation "dx₀" => planarDerivationFraction (MvPolynomial.pderiv 0)
local notation "dz₀" => planarDerivationFraction (MvPolynomial.pderiv 1)
local notation "σ₀" => (dx₀ - (z₀ / t₀) • dz₀)
local notation "τ₀" => ((2 * t₀)⁻¹ • dz₀)
local notation "D₀" => ((2 * t₀)⁻¹ • dx₀)

private theorem diagnostic_coordinate_derivatives :
    dx₀ t₀ = 1 ∧ dx₀ z₀ = 0 ∧ dz₀ t₀ = 0 ∧ dz₀ z₀ = 1 := by
  simp [planarDerivationFraction_algebraMap, MvPolynomial.pderiv_X]

private theorem diagnostic_t_ne_zero : t₀ ≠ 0 := by
  simpa only [map_zero] using
    (IsFractionRing.injective PlanePolynomial N₀).ne (MvPolynomial.X_ne_zero 0)

/-- Actual source duality and determinant one on the proper open source,
together with the corresponding first target-dual identities. -/
theorem localized_unitJacobian_diagnostic :
    σ₀ t₀ = 1 ∧ σ₀ u₀ = 0 ∧ τ₀ t₀ = 0 ∧ τ₀ u₀ = 1 ∧
      σ₀ (t₀ ^ 2) * τ₀ z₀ - σ₀ z₀ * τ₀ (t₀ ^ 2) = 1 ∧
      D₀ (t₀ ^ 2) = 1 ∧ D₀ z₀ = 0 := by
  obtain ⟨hxt, hxz, hzt, hzz⟩ := diagnostic_coordinate_derivatives
  have hx2 : dx₀ (2 : N₀) = 0 := by
    rw [show (2 : N₀) = 1 + 1 by norm_num]
    simp only [map_add, Derivation.map_one_eq_zero, add_zero]
  have hz2 : dz₀ (2 : N₀) = 0 := by
    rw [show (2 : N₀) = 1 + 1 by norm_num]
    simp only [map_add, Derivation.map_one_eq_zero, add_zero]
  have hxu : dx₀ u₀ = 2 * z₀ := by
    simp only [Derivation.leibniz, hxt, hxz, hx2, smul_eq_mul]
    ring
  have hzu : dz₀ u₀ = 2 * t₀ := by
    simp only [Derivation.leibniz, hzt, hzz, hz2, smul_eq_mul]
    ring
  have hxtwo : dx₀ (t₀ ^ 2) = 2 * t₀ := by
    simp only [pow_two, Derivation.leibniz, hxt, smul_eq_mul]
    ring
  have hztwo : dz₀ (t₀ ^ 2) = 0 := by
    simp only [pow_two, Derivation.leibniz, hzt, smul_eq_mul]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul,
      hxt, hxz, hzt, hzz, hxu, hzu, hxtwo, hztwo,
      sub_zero, mul_zero, mul_one] <;>
    field_simp [diagnostic_t_ne_zero] <;> ring

/-- The actual target-dual derivation does not preserve the polynomial
normalization ring: its value on `t` has a pole along `t = 0`. -/
theorem localized_target_derivation_not_polynomial :
    D₀ t₀ ∉ (1 : Submodule PlanePolynomial N₀) := by
  obtain ⟨hxt, _, _, _⟩ := diagnostic_coordinate_derivatives
  have hcancel : (2 * t₀) * D₀ t₀ = 1 := by
    simp only [Derivation.smul_apply, smul_eq_mul, hxt, mul_one]
    exact mul_inv_cancel₀ (mul_ne_zero (by norm_num) diagnostic_t_ne_zero)
  intro hmem
  obtain ⟨p, hp⟩ := Submodule.mem_one.mp hmem
  have hpoly : (2 : PlanePolynomial) * MvPolynomial.X 0 * p = 1 := by
    apply IsFractionRing.injective PlanePolynomial N₀
    simpa only [map_mul, map_ofNat, map_one, hp] using hcancel
  have hzero := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (0 : ℂ))) hpoly
  simp at hzero

/-- A first target derivative raises a simple source-boundary pole to
order three in the proper-open diagnostic. -/
theorem localized_target_derivation_inv :
    D₀ (t₀⁻¹) = -((2 * t₀ ^ 3)⁻¹) := by
  obtain ⟨hxt, _, _, _⟩ := diagnostic_coordinate_derivatives
  simp only [Derivation.smul_apply, Derivation.leibniz_inv, hxt,
    smul_eq_mul, mul_one]
  field_simp [diagnostic_t_ne_zero]

/-- Even the simple-pole module is not preserved by the actual target
frame on this proper open set. This does not specialize the polynomial
secant construction to the rational diagnostic map. -/
theorem localized_target_derivation_inv_not_simplePole :
    D₀ (t₀⁻¹) ∉ Submodule.span PlanePolynomial ({t₀⁻¹} : Set N₀) := by
  intro hmem
  obtain ⟨p, hp⟩ := Submodule.mem_span_singleton.mp hmem
  rw [Algebra.smul_def (R := PlanePolynomial) (A := N₀) p (t₀⁻¹)] at hp
  have hp' : algebraMap PlanePolynomial N₀ p * t₀⁻¹ = -((2 * t₀ ^ 3)⁻¹) := by
    simpa only [localized_target_derivation_inv] using hp
  have hfrac : (2 * t₀ ^ 2) * algebraMap PlanePolynomial N₀ p = -1 := by
    calc
      (2 * t₀ ^ 2) * algebraMap PlanePolynomial N₀ p =
          (2 * t₀ ^ 3) * (algebraMap PlanePolynomial N₀ p * t₀⁻¹) := by
        field_simp [diagnostic_t_ne_zero] <;> ring
      _ = (2 * t₀ ^ 3) * (-((2 * t₀ ^ 3)⁻¹)) := by rw [hp']
      _ = -1 := by
        field_simp [diagnostic_t_ne_zero]
  have hpoly : (2 : PlanePolynomial) * MvPolynomial.X 0 ^ 2 * p = -1 := by
    apply IsFractionRing.injective PlanePolynomial N₀
    simpa only [map_mul, map_pow, map_ofNat, map_neg, map_one] using hfrac
  have hzero := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (0 : ℂ))) hpoly
  norm_num at hzero

section Cubic

local notation "q₃" => (3 * t₀ ^ 2 - 3)
local notation "s₃" => (t₀ ^ 3 - 3 * t₀)
local notation "u₃" => (q₃ * z₀)
local notation "σ₃" =>
  (dx₀ - (6 * t₀ * z₀ / q₃) • dz₀ : Derivation ℂ N₀ N₀)
local notation "τ₃" => (q₃⁻¹ • dz₀ : Derivation ℂ N₀ N₀)
local notation "D₃" => (q₃⁻¹ • dx₀ : Derivation ℂ N₀ N₀)

private theorem cubic_diagnostic_q_ne_zero : q₃ ≠ 0 := by
  intro h
  have hpoly : (3 : PlanePolynomial) * MvPolynomial.X 0 ^ 2 - 3 = 0 := by
    apply IsFractionRing.injective PlanePolynomial N₀
    simpa only [map_sub, map_mul, map_pow, map_ofNat, map_zero] using h
  have hzero := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (0 : ℂ))) hpoly
  norm_num only [map_sub, map_mul, map_pow, map_ofNat, map_zero,
    MvPolynomial.eval_X] at hzero

/-- The cubic rational map on `3*t^2-3 ≠ 0` hits every complex target
point. At either branch value its simple root survives in this open set. -/
theorem cubic_localized_source_surjective (s z : ℂ) :
    ∃ t u : ℂ, 3 * t ^ 2 - 3 ≠ 0 ∧
      t ^ 3 - 3 * t = s ∧ u / (3 * t ^ 2 - 3) = z := by
  let p : Polynomial ℂ := Polynomial.X ^ 3 - 3 * Polynomial.X - Polynomial.C s
  have hcoeff : p.coeff 3 = 1 := by simp [p, Polynomial.coeff_X]
  have hdegree : p.degree ≠ 0 := by
    intro h
    have hz := Polynomial.coeff_eq_zero_of_degree_lt
      (show p.degree < (3 : WithBot ℕ) by rw [h]; norm_num)
    rw [hcoeff] at hz
    exact one_ne_zero hz
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root p hdegree
  have hroot : t ^ 3 - 3 * t = s := by
    simpa [Polynomial.IsRoot, p, sub_eq_zero] using ht
  by_cases hq : 3 * t ^ 2 - 3 = 0
  · have hfactor : (t - 1) * (t + 1) = 0 := by
      linear_combination (1 / 3 : ℂ) * hq
    rcases mul_eq_zero.mp hfactor with htone | htneg
    · have ht' : t = 1 := sub_eq_zero.mp htone
      have hs : s = -2 := by norm_num [ht'] at hroot; exact hroot.symm
      rw [hs]
      refine ⟨-2, 9 * z, by norm_num, by norm_num, ?_⟩
      norm_num
    · have ht' : t = -1 := by linear_combination htneg
      have hs : s = 2 := by norm_num [ht'] at hroot; exact hroot.symm
      rw [hs]
      refine ⟨2, 9 * z, by norm_num, by norm_num, ?_⟩
      norm_num
  · exact ⟨t, (3 * t ^ 2 - 3) * z, hq, hroot, mul_div_cancel_left₀ z hq⟩

/-- Source duality, determinant one, and target duality for the cubic
proper-open diagnostic. This is not a full-plane polynomial Keller map. -/
theorem cubic_localized_unitJacobian_diagnostic :
    σ₃ t₀ = 1 ∧ σ₃ u₃ = 0 ∧ τ₃ t₀ = 0 ∧ τ₃ u₃ = 1 ∧
      σ₃ s₃ * τ₃ z₀ - σ₃ z₀ * τ₃ s₃ = 1 ∧
      D₃ s₃ = 1 ∧ D₃ z₀ = 0 := by
  obtain ⟨hxt, hxz, hzt, hzz⟩ := diagnostic_coordinate_derivatives
  have hx3 : dx₀ (3 : N₀) = 0 := Derivation.map_natCast dx₀ 3
  have hz3 : dz₀ (3 : N₀) = 0 := Derivation.map_natCast dz₀ 3
  have hxq : dx₀ q₃ = 6 * t₀ := by
    simp only [map_sub, Derivation.leibniz, Derivation.leibniz_pow,
      hx3, hxt, smul_eq_mul, Nat.reduceSub, pow_one, nsmul_eq_mul]
    ring
  have hzq : dz₀ q₃ = 0 := by
    simp only [map_sub, Derivation.leibniz, Derivation.leibniz_pow,
      hz3, hzt, smul_eq_mul, Nat.reduceSub, pow_one, nsmul_eq_mul]
    ring
  have hxu : dx₀ u₃ = 6 * t₀ * z₀ := by
    simp only [Derivation.leibniz, hxq, hxz, smul_eq_mul]
    ring
  have hzu : dz₀ u₃ = q₃ := by
    simp only [Derivation.leibniz, hzq, hzz, smul_eq_mul]
    ring
  have hxs : dx₀ s₃ = q₃ := by
    simp only [map_sub, Derivation.leibniz, Derivation.leibniz_pow,
      hx3, hxt, smul_eq_mul, Nat.reduceSub, nsmul_eq_mul]
    ring
  have hzs : dz₀ s₃ = 0 := by
    simp only [map_sub, Derivation.leibniz, Derivation.leibniz_pow,
      hz3, hzt, smul_eq_mul, Nat.reduceSub, nsmul_eq_mul]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul,
      hxt, hxz, hzt, hzz, hxu, hzu, hxs, hzs,
      sub_zero, mul_zero, zero_mul, mul_one,
      div_mul_cancel₀ _ cubic_diagnostic_q_ne_zero,
      inv_mul_cancel₀ cubic_diagnostic_q_ne_zero,
      mul_inv_cancel₀ cubic_diagnostic_q_ne_zero, sub_self]

/-- The cubic diagnostic retains a pole in the first target derivative
despite having a preimage for every complex target point. -/
theorem cubic_localized_target_derivation_not_polynomial :
    D₃ t₀ ∉ (1 : Submodule PlanePolynomial N₀) := by
  obtain ⟨hxt, _, _, _⟩ := diagnostic_coordinate_derivatives
  have hcancel : q₃ * D₃ t₀ = 1 := by
    simp only [Derivation.smul_apply, smul_eq_mul, hxt, mul_one]
    exact mul_inv_cancel₀ cubic_diagnostic_q_ne_zero
  intro hmem
  obtain ⟨p, hp⟩ := Submodule.mem_one.mp hmem
  have hpoly : ((3 : PlanePolynomial) * MvPolynomial.X 0 ^ 2 - 3) * p = 1 := by
    apply IsFractionRing.injective PlanePolynomial N₀
    simpa only [map_sub, map_mul, map_pow, map_ofNat, map_one, hp] using hcancel
  have hzero := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (1 : ℂ))) hpoly
  norm_num at hzero

end Cubic

end

end CollisionIdeals.Planar
