import CollisionIdeals.Planar.Research.MonogenicLanding
import CollisionIdeals.Planar.Research.SecantFrameDenominator
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Finite denominator clearing is not uniform landing

This negative control concerns arbitrary overrings of a normal Noetherian
domain, not Keller maps. A finite coefficient family always has a nonzero
denominator ideal, whereas a proper overring in the fraction field has no
nonzero multiplier into the base ring. In particular, clearing the singleton
`X⁻¹` in `k(X)` does not clear the whole algebra `k[X, X⁻¹]`.

The concrete secant--frame landing theorem therefore needs additional
Keller-specific input; finite denominator clearing alone cannot supply it.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

universe u v

variable (T : Type u) [CommRing T] [IsDomain T]
variable (N : Type v) [Field N] [Algebra T N] [IsFractionRing T N]

section ProperOverring

variable [IsNoetherianRing T] [IsIntegrallyClosed T]

omit [IsDomain T] in
/-- A proper overring of a normal Noetherian domain has zero transporter
into the base ring, even though each finite family has a denominator. -/
theorem baseTransporter_eq_bot_of_proper_subalgebra
    (R : Subalgebra T N) (hR : R ≠ ⊥) :
    (1 : Submodule T N).colon R.toSubmodule = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro a ha
  change a = 0
  by_contra ha0
  apply hR
  apply subalgebra_eq_bot_of_nonzero_mul_mem_base T N R a ha0
  intro r
  have h := (Submodule.mem_colon.mp ha) (r : N) r.property
  rw [Algebra.smul_def] at h
  exact Submodule.mem_one.mp h

/-- No finite coefficient denominator ideal can land a proper overring
uniformly in the base ring. The denominator ideal itself is nonzero. -/
theorem finiteCoefficientDenominator_not_le_overringTransporter
    (R : Subalgebra T N) (hR : R ≠ ⊥)
    {n : ℕ} (coefficients : Fin n → N) :
    ¬ finiteCoefficientDenominatorIdeal T N coefficients ≤
      (1 : Submodule T N).colon R.toSubmodule := by
  rw [baseTransporter_eq_bot_of_proper_subalgebra T N R hR]
  intro h
  exact finiteCoefficientDenominatorIdeal_ne_bot T N coefficients
    (le_bot_iff.mp h)

end ProperOverring

/-- Inverting a nonzero nonunit gives a genuinely larger subalgebra of
the fraction field. -/
theorem adjoin_inverse_ne_bot_of_nonunit
    (a : T) (ha : a ≠ 0) (hunit : ¬ IsUnit a) :
    Algebra.adjoin T {(algebraMap T N a)⁻¹} ≠ ⊥ := by
  intro h
  have hinv : (algebraMap T N a)⁻¹ ∈
      Algebra.adjoin T {(algebraMap T N a)⁻¹} :=
    Algebra.subset_adjoin (Set.mem_singleton _)
  rw [h, Algebra.mem_bot] at hinv
  obtain ⟨b, hb⟩ := hinv
  have haN : algebraMap T N a ≠ 0 := by
    intro hz
    apply ha
    apply IsFractionRing.injective T N
    simpa using hz
  apply hunit
  apply IsUnit.of_mul_eq_one (b := b)
  apply IsFractionRing.injective T N
  simp only [map_mul, hb, mul_inv_cancel₀ haN, map_one]

/-- The inverse generator is cleared by its own denominator. This is the
finite calculation that must not be confused with uniform landing. -/
theorem self_mem_inverseCoefficientDenominator
    (a : T) (ha : a ≠ 0) :
    a ∈ finiteCoefficientDenominatorIdeal T N
      (fun _ : Fin 1 => (algebraMap T N a)⁻¹) := by
  rw [mem_finiteCoefficientDenominatorIdeal_iff]
  intro i
  have haN : algebraMap T N a ≠ 0 := by
    intro hz
    apply ha
    apply IsFractionRing.injective T N
    simpa using hz
  simp only [Algebra.smul_def, mul_inv_cancel₀ haN]
  exact Submodule.mem_one.mpr ⟨1, map_one _⟩

/-- Explicit polynomial negative control: `X` clears the coefficient
`X⁻¹`, but its finite denominator ideal cannot carry every element of
`k[X, X⁻¹]` into `k[X]`. This is not a Keller counterexample. -/
theorem polynomial_finiteClearing_not_uniformLanding
    (k : Type u) [Field k] :
    let T := Polynomial k
    let N := FractionRing T
    let coefficients := fun _ : Fin 1 =>
      (algebraMap T N Polynomial.X)⁻¹
    let R := Algebra.adjoin T {(algebraMap T N Polynomial.X)⁻¹}
    Polynomial.X ∈ finiteCoefficientDenominatorIdeal T N coefficients ∧
      finiteCoefficientDenominatorIdeal T N coefficients ≠ ⊥ ∧
      (1 : Submodule T N).colon R.toSubmodule = ⊥ ∧
      ¬ finiteCoefficientDenominatorIdeal T N coefficients ≤
        (1 : Submodule T N).colon R.toSubmodule := by
  dsimp only
  have hR := adjoin_inverse_ne_bot_of_nonunit
    (Polynomial k) (FractionRing (Polynomial k)) Polynomial.X
    Polynomial.X_ne_zero Polynomial.not_isUnit_X
  exact ⟨self_mem_inverseCoefficientDenominator _ _ _ Polynomial.X_ne_zero,
    finiteCoefficientDenominatorIdeal_ne_bot _ _ _,
    baseTransporter_eq_bot_of_proper_subalgebra _ _ _ hR,
    finiteCoefficientDenominator_not_le_overringTransporter _ _ _ hR _⟩

end

end CollisionIdeals.Planar
