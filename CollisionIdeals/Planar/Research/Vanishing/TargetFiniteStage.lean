import CollisionIdeals.Planar.Research.Vanishing.TargetPoleTower
import CollisionIdeals.General.Normalization.DVRPoleEscape
import CollisionIdeals.General.Normalization.FractionalNormalization
import Mathlib.RingTheory.Noetherian.Basic

/-!
# The constructed target pole ray escapes finite base stages

The original invariant quotient, target divisor, and selected Keller
frame are unchanged. Exact pole growth in the target function field
excludes the entire tail of this ray from each fixed finite base stage
in the marked normal closure, even after adding base elements.

Pullback along the original field inclusion makes the finite-stage test
in the target field. No valuation extension, ramified divisor, or new
normalization model is needed. The fixed fractional normalization images
are instances of the same finite-stage conclusion.

This is an obstruction to a proposed bound, conditional on a nonzero
class. It does not construct the missing Keller-specific bound or prove
planar vanishing.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 20000

namespace CollisionIdeals

open AlgebraicGeometry

noncomputable section

variable {F : PlanarPolynomialMap} {N : Type} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]
variable [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]

@[reducible] local instance finiteStageBaseAlgebra :
    Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

local instance finiteStageBaseSMul : SMul (PolynomialImageAlgebra F) N := Algebra.toSMul
local instance finiteStageBaseModule : Module (PolynomialImageAlgebra F) N := Algebra.toModule

@[reducible] local instance finiteStageBaseFieldAlgebra :
    Algebra (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) :=
  OreLocalization.instAlgebra

local instance finiteStageBaseFieldSMul :
    SMul (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) := Algebra.toSMul

local instance finiteStageBaseFieldModule :
    Module (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) := Algebra.toModule

local instance finiteStageBaseFieldTower :
    IsScalarTower (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) N :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

@[reducible] local instance finiteStageImageAlgebra (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateAlgebra D)

local instance finiteStageImageSMul (D : PolynomialNormalClosureData F N) :
    SMul (PolynomialImageAlgebra F) (polynomialConjugateAlgebra D) := Algebra.toSMul

local instance finiteStageImageModule (D : PolynomialNormalClosureData F N) :
    Module (PolynomialImageAlgebra F) (polynomialConjugateAlgebra D) := Algebra.toModule

@[reducible] local instance finiteStageInvariantAlgebra (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateInvariantAlgebra D)

local instance finiteStageInvariantSMul (D : PolynomialNormalClosureData F N) :
    SMul (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) := Algebra.toSMul

local instance finiteStageInvariantModule (D : PolynomialNormalClosureData F N) :
    Module (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) := Algebra.toModule

@[reducible] local instance finiteStagePullbackAlgebra (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateInvariantBaseAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateInvariantBaseAlgebra D)

local instance finiteStagePullbackSMul (D : PolynomialNormalClosureData F N) :
    SMul (PolynomialImageAlgebra F) (polynomialConjugateInvariantBaseAlgebra D) := Algebra.toSMul

local instance finiteStagePullbackModule (D : PolynomialNormalClosureData F N) :
    Module (PolynomialImageAlgebra F) (polynomialConjugateInvariantBaseAlgebra D) := Algebra.toModule

local notation "B₀" => PolynomialImageAlgebra F
local notation "K₀" => PolynomialMapBaseFunctionField F
local notation "T₀" => PolynomialNormalizationInExtensionRing (F := F) (N := N)

/-- One constructed divisor and one invariant-frame direction work for
every proposed finite base stage in the original normal closure. The
cutoff may depend on the stage; arbitrary base additions are allowed. -/
theorem planarKellerInvariantQuotient_eventually_escapes_finite_stages
    (D : PolynomialNormalClosureData F N) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = MvPolynomial.C c)
    (q : polynomialConjugateInvariantAlgebra D ⧸ LinearMap.range
      (Algebra.linearMap B₀ (polynomialConjugateInvariantAlgebra D))) (hq : q ≠ 0) :
    ∃ (z : polynomialConjugateInvariantAlgebra D) (p : PrimeSpectrum B₀) (i : Fin 2),
      Submodule.Quotient.mk z = q ∧ p.asIdeal.primeHeight = 1 ∧
      p ∉ polynomialConjugateInvariantTargetOpen D ⟨c, hc, hJ⟩ ∧
      ∀ (Λ : Submodule B₀ N), Module.Finite B₀ Λ →
        ∃ cutoff : ℕ, ∀ order ≥ cutoff,
          ¬ ∃ a ∈ Λ, ∃ b : B₀,
            ((((planarKellerInvariantFrame D c hc hJ i :
              polynomialConjugateInvariantAlgebra D →
                polynomialConjugateInvariantAlgebra D)^[order]) z).val : N) =
              a + algebraMap B₀ N b := by
  letI := D.finiteIntermediate
  letI : IsNoetherianRing B₀ := polynomialImageAlgebra_isNoetherianRing F
  letI : IsIntegrallyClosed B₀ :=
    polynomialImageAlgebra_isIntegrallyClosed_of_finiteDimensional F
  obtain ⟨z, p, i, b, _m, hRep, hHeight, hOutside, hb, hdb, _hm, hTower⟩ :=
    planarKellerInvariantQuotient_exists_transverse_target_pole_tower D ⟨c, hc, hJ⟩ q hq
  let e := polynomialConjugateInvariantBaseEquiv D
  let r : K₀ := (e.symm z : K₀)
  let ray (order : ℕ) : K₀ :=
    ((localizationDerivation (nonZeroDivisors B₀) K₀
      (polynomialImageCoordinatePartial F i) : K₀ → K₀)^[order]) r
  have hPole : r ∉ Localization.subalgebra.ofField K₀ p.asIdeal.primeCompl
      p.asIdeal.primeCompl_le_nonZeroDivisors := by
    obtain ⟨_u, _hu, _hCalc, hNonregular⟩ := hTower 0
    simpa only [Function.iterate_zero_apply] using hNonregular
  have hDVR : IsDiscreteValuationRing (Localization.AtPrime p.asIdeal) :=
    heightOne_isDiscreteValuationRing p hHeight
  let j : K₀ →ₗ[B₀] N := (IsScalarTower.toAlgHom B₀ K₀ N).toLinearMap
  have hj : Function.Injective j := (algebraMap K₀ N).injective
  have hjBase (a : B₀) : j (algebraMap B₀ K₀ a) = algebraMap B₀ N a :=
    (IsScalarTower.toAlgHom B₀ K₀ N).commutes a
  have hLift (order : ℕ) : j (ray order) =
      ((((planarKellerInvariantFrame D c hc hJ i :
        polynomialConjugateInvariantAlgebra D →
          polynomialConjugateInvariantAlgebra D)^[order]) z).val : N) := by
    change algebraMap K₀ N (ray order) = _
    rw [show ray order = ((polynomialConjugateInvariantBaseEquiv D).symm
      (((planarKellerInvariantFrame D c hc hJ i :
        polynomialConjugateInvariantAlgebra D → polynomialConjugateInvariantAlgebra D)^[order]) z)
        : K₀) from planarKellerInvariantFrame_targetPartial_iterate D c hc hJ i z order]
    exact congrArg (fun w : polynomialConjugateInvariantAlgebra D => (w.val : N))
      (e.apply_symm_apply _)
  refine ⟨z, p, i, hRep, hHeight, hOutside, ?_⟩
  intro Λ hΛ
  letI : Module.Finite B₀ Λ := hΛ
  let Γ : Submodule B₀ K₀ := Λ.comap j
  letI : Module B₀ Γ := Submodule.module Γ
  have hΓ : Γ.FG := Submodule.fg_of_fg_map_injective j hj
    ((Module.Finite.iff_fg.mp hΛ : Λ.FG).of_le (Submodule.map_comap_le j Λ))
  letI : Module.Finite B₀ Γ := Module.Finite.of_fg hΓ
  obtain ⟨cutoff, hCutoff⟩ :=
    eventually_not_mem_finite_submodule_mod_base_of_localized_pole
      (polynomialImageCoordinatePartial F i) p hDVR b hb hdb r hPole Γ
  refine ⟨cutoff, ?_⟩
  intro order hOrder
  rintro ⟨a, ha, t, hEq⟩
  apply hCutoff order hOrder
  refine ⟨ray order - algebraMap B₀ K₀ t, ?_, t, (sub_add_cancel _ _).symm⟩
  change j (ray order - algebraMap B₀ K₀ t) ∈ Λ
  rw [map_sub, hLift, hjBase, sub_eq_iff_eq_add.mpr hEq]
  exact ha

/-- Every fixed scalar image of the original finite normalization is
eventually missed by the same invariant-frame ray, even modulo the base.
Taking the scalar `(s^m)⁻¹` recovers every fixed fractional stage. -/
theorem planarKellerInvariantQuotient_eventually_escapes_fractional_normalization
    (D : PolynomialNormalClosureData F N) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = MvPolynomial.C c)
    (q : polynomialConjugateInvariantAlgebra D ⧸ LinearMap.range
      (Algebra.linearMap B₀ (polynomialConjugateInvariantAlgebra D))) (hq : q ≠ 0) :
    ∃ (z : polynomialConjugateInvariantAlgebra D) (p : PrimeSpectrum B₀) (i : Fin 2),
      Submodule.Quotient.mk z = q ∧ p.asIdeal.primeHeight = 1 ∧
      p ∉ polynomialConjugateInvariantTargetOpen D ⟨c, hc, hJ⟩ ∧
      ∀ scalar : N, ∃ cutoff : ℕ, ∀ order ≥ cutoff,
        ¬ ∃ t : T₀, ∃ b : B₀,
          ((((planarKellerInvariantFrame D c hc hJ i :
            polynomialConjugateInvariantAlgebra D →
              polynomialConjugateInvariantAlgebra D)^[order]) z).val : N) =
            scalar * (t : N) + algebraMap B₀ N b := by
  obtain ⟨z, p, i, hRep, hHeight, hOutside, hEscape⟩ :=
    planarKellerInvariantQuotient_eventually_escapes_finite_stages D c hc hJ q hq
  refine ⟨z, p, i, hRep, hHeight, hOutside, ?_⟩
  intro scalar
  let Λ : Submodule B₀ N := LinearMap.range
    ((LinearMap.mulLeft B₀ scalar).comp (integralClosure B₀ N).val.toLinearMap)
  have hΛ : Module.Finite B₀ Λ := polynomialFractionalNormalization_image_finite D scalar
  obtain ⟨cutoff, hCutoff⟩ := hEscape Λ hΛ
  refine ⟨cutoff, ?_⟩
  intro order hOrder
  rintro ⟨t, b, hEq⟩
  exact hCutoff order hOrder ⟨scalar * (t : N), ⟨t, rfl⟩, b, hEq⟩

end

end CollisionIdeals
