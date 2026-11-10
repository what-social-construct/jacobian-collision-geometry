import CollisionIdeals.General.Normalization.Finiteness
import CollisionIdeals.General.Normalization.ValuationFiniteStage

/-!
# Finite fractional images of the actual normalization

Multiplication by a fixed field element maps the existing finite integral
closure to a finite base submodule. No new normalization ring or lattice
structure is introduced: the candidate is a standard linear-map range.

For a nonzero denominator, membership is exactly integrality after
clearing that denominator. Every such candidate has a common valuation
bound at any valuation nonpositive on base pole orders, also modulo the
base image. No Keller derivative orbit is asserted to lie in a candidate.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ} {F : PolynomialSelfMap k n}
variable {N : Type u} [Field N] [Algebra (PolynomialMapBaseFunctionField F) N]

@[reducible] local instance fractionalNormalizationBaseAlgebra :
    Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

local notation "B₀" => PolynomialImageAlgebra F
local notation "T₀" => PolynomialNormalizationInExtensionRing (F := F) (N := N)

/-- This is the original normalization image multiplied by a fixed scalar,
not a supplied finite-stage hypothesis. -/
theorem polynomialFractionalNormalization_image_finite
    [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]
    (D : PolynomialNormalClosureData F N) (a : N) :
    Module.Finite B₀ (LinearMap.range
      ((LinearMap.mulLeft B₀ a).comp (integralClosure B₀ N).val.toLinearMap)) := by
  letI : Module.Finite B₀ T₀ := polynomialNormalClosureNormalization_finite D
  infer_instance

/-- A fixed fractional normalization image consists exactly of those
elements made integral by its fixed denominator power. -/
theorem mem_fractionalNormalization_image_iff
    (s : N) (hs : s ≠ 0) (m : ℕ) (z : N) :
    z ∈ LinearMap.range
      ((LinearMap.mulLeft B₀ (s ^ m)⁻¹).comp
        (integralClosure B₀ N).val.toLinearMap) ↔
      IsIntegral B₀ (s ^ m * z) := by
  have hsm : s ^ m ≠ 0 := pow_ne_zero _ hs
  constructor
  · rintro ⟨t, rfl⟩
    change IsIntegral B₀ (s ^ m * ((s ^ m)⁻¹ * (t : N)))
    simpa only [← mul_assoc, mul_inv_cancel₀ hsm, one_mul] using t.property
  · intro hz
    refine ⟨⟨s ^ m * z, hz⟩, ?_⟩
    change (s ^ m)⁻¹ * (s ^ m * z) = z
    rw [← mul_assoc, inv_mul_cancel₀ hsm, one_mul]

/-- Finiteness of the actual normalization gives a bound on each fixed
fractional image, including representatives differing by base elements.
It does not put a derivative orbit in one such image. -/
theorem polynomialFractionalNormalization_image_valuation_bound
    [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]
    (D : PolynomialNormalClosureData F N) (a : N)
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation N Γ₀)
    (hBase : ∀ b : B₀, v (algebraMap B₀ N b) ≤ 1) :
    ∃ C : Γ₀, 1 ≤ C ∧ ∀ z : N,
      z ∈ LinearMap.range
        ((LinearMap.mulLeft B₀ a).comp (integralClosure B₀ N).val.toLinearMap) →
      ∀ b : B₀, v (z + algebraMap B₀ N b) ≤ C := by
  let Λ : Submodule B₀ N := LinearMap.range
    ((LinearMap.mulLeft B₀ a).comp (integralClosure B₀ N).val.toLinearMap)
  letI : Module.Finite B₀ Λ := polynomialFractionalNormalization_image_finite D a
  exact exists_valuation_bound_of_finite_submodule_mod_base v hBase Λ

end

end CollisionIdeals
