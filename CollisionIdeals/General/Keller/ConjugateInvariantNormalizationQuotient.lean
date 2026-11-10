import CollisionIdeals.General.Galois.ConjugateInvariantField
import CollisionIdeals.General.Normalization.Finiteness
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The invariant target quotient in the normalization quotient

The original inclusion of the fixed algebra in the marked normal closure
descends from the standard module quotient by the target-base image to
the standard quotient by the normalization-ring image. The descended
map is injective: a fixed element is in the target function field, and
an element of that field integral over the normal target base lies in
the base.

No inclusion in a fixed--moving boundary-section ring, multiplier landing,
or boundary vanishing is asserted. In particular, this comparison does
not identify the two ambient rings or replace the earlier landing input.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace CollisionIdeals

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ}
variable {F : PolynomialSelfMap k n} {N : Type u} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

@[reducible] local instance normalizationQuotientBaseAlgebra :
    Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

@[reducible] local instance normalizationQuotientBaseFieldAlgebra :
    Algebra (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) :=
  OreLocalization.instAlgebra

local instance normalizationQuotientBaseFieldSMul :
    SMul (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) := Algebra.toSMul

local instance normalizationQuotientBaseFieldTower :
    IsScalarTower (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) N :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

local instance normalizationQuotientNormalizationTower :
    IsScalarTower (PolynomialImageAlgebra F)
      (PolynomialNormalizationInExtensionRing (F := F) (N := N)) N :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

@[reducible] local instance normalizationQuotientConjugateAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateAlgebra D)

@[reducible] local instance normalizationQuotientInvariantAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateInvariantAlgebra D)

private def invariantToNormalLinear
    (D : PolynomialNormalClosureData F N) :
    polynomialConjugateInvariantAlgebra D →ₗ[PolynomialImageAlgebra F] N :=
  ((polynomialConjugateAlgebra D).val.comp
    (polynomialConjugateInvariantAlgebra D).val).toLinearMap

/-- The canonical base-linear map from the existing target-section quotient
to the ambient quotient by the actual normalization-ring image. -/
def polynomialConjugateInvariantNormalizationQuotientMap
    (D : PolynomialNormalClosureData F N) :
    (polynomialConjugateInvariantAlgebra D ⧸ LinearMap.range
      (Algebra.linearMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D)))
      →ₗ[PolynomialImageAlgebra F]
    N ⧸ (LinearMap.range (Algebra.linearMap
      (PolynomialNormalizationInExtensionRing (F := F) (N := N)) N)).restrictScalars
        (PolynomialImageAlgebra F) :=
  (LinearMap.range (Algebra.linearMap (PolynomialImageAlgebra F)
    (polynomialConjugateInvariantAlgebra D))).mapQ _
      (invariantToNormalLinear D) (by
        intro z hz
        obtain ⟨b, rfl⟩ := hz
        change ∃ t : PolynomialNormalizationInExtensionRing (F := F) (N := N),
          algebraMap _ N t = invariantToNormalLinear D
            ((Algebra.linearMap (PolynomialImageAlgebra F)
              (polynomialConjugateInvariantAlgebra D)) b)
        exact ⟨algebraMap (PolynomialImageAlgebra F) _ b, rfl⟩)

@[simp]
theorem polynomialConjugateInvariantNormalizationQuotientMap_mk
    (D : PolynomialNormalClosureData F N) (z : polynomialConjugateInvariantAlgebra D) :
    polynomialConjugateInvariantNormalizationQuotientMap D (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (z.val : N) := rfl

variable [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]

private theorem invariant_mem_base_of_mem_normalization
    (D : PolynomialNormalClosureData F N) (z : polynomialConjugateInvariantAlgebra D)
    (hz : (z.val : N) ∈
      (LinearMap.range (Algebra.linearMap
        (PolynomialNormalizationInExtensionRing (F := F) (N := N)) N)).restrictScalars
          (PolynomialImageAlgebra F)) :
    z ∈ LinearMap.range
      (Algebra.linearMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D)) := by
  letI := D.finiteIntermediate
  letI := polynomialImageAlgebra_isIntegrallyClosed_of_finiteDimensional F
  change ∃ t : PolynomialNormalizationInExtensionRing (F := F) (N := N),
    algebraMap _ N t = (z.val : N) at hz
  obtain ⟨t, ht⟩ := hz
  have hIntegralN : IsIntegral (PolynomialImageAlgebra F) (z.val : N) := by
    rw [← ht]
    exact t.property
  obtain ⟨r, hr⟩ :=
    (polynomialConjugateInvariantAlgebra_mem_iff_baseField D z.val).mp z.property
  have hIntegralK : IsIntegral (PolynomialImageAlgebra F) r := by
    apply (isIntegral_algebraMap_iff (R := PolynomialImageAlgebra F)
      (A := PolynomialMapBaseFunctionField F) (B := N)
      (algebraMap (PolynomialMapBaseFunctionField F) N).injective).mp
    rwa [hr]
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hIntegralK
  refine ⟨b, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change algebraMap (PolynomialImageAlgebra F) N b = (z.val : N)
  change algebraMap (PolynomialMapBaseFunctionField F) N
    (algebraMap (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) b) = _
  rw [hb, hr]

/-- Injectivity is the normal-base intersection property `K ∩ T = B`,
not a boundary-section containment or a uniform landing assertion. -/
theorem polynomialConjugateInvariantNormalizationQuotientMap_injective
    (D : PolynomialNormalClosureData F N) :
    Function.Injective (polynomialConjugateInvariantNormalizationQuotientMap D) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro q
  refine Submodule.Quotient.induction_on _ q ?_
  intro z hz
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply invariant_mem_base_of_mem_normalization D z
  exact (Submodule.Quotient.mk_eq_zero _).mp hz

end

end CollisionIdeals
