import CollisionIdeals.Planar.Research.BoundarySections
import CollisionIdeals.Planar.Research.TraceLanding
import CollisionIdeals.General.Normalization.MultiplierQuotient

/-!
# The earlier boundary-section multiplier comparison

For the existing boundary-section module and normalization trace dual,
a supplied landing multiplier induces the map `[r] ↦ [s r]` between
their standard quotients by the normalization-ring image. Both quotient
inclusions into `N / T` are instances of the generic ambient comparison.

The normalization image is proved to lie in both modules, so these are
the actual `R_C / T` and `T† / T` quotients, not a new principal-parts
model. The landing condition is not proved here, and the multiplier map
is not asserted injective. No identification with filtered-Ext local
cohomology or with the target quotient `E^G / B` is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals.Planar

noncomputable section

variable {F : PlanarPolynomialMap} {N : Type} [Field N]
variable [Algebra (PlanarBaseFunctionField F) N]

local notation "B₀" => PolynomialImageAlgebra F
local notation "K₀" => PlanarBaseFunctionField F
local notation "T₀" => GaloisNormalizationRing (F := F) (N := N)

@[reducible] local instance multiplierComparisonBaseAlgebra : Algebra B₀ N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

@[reducible] local instance multiplierComparisonNormalizationCommRing : CommRing T₀ :=
  Subalgebra.toCommRing (integralClosure B₀ N)

@[reducible] local instance multiplierComparisonBaseFieldAlgebra : Algebra B₀ K₀ :=
  OreLocalization.instAlgebra

local instance multiplierComparisonBaseFieldSMul : SMul B₀ K₀ := Algebra.toSMul

local instance multiplierComparisonBaseFieldTower : IsScalarTower B₀ K₀ N :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Every normalization-ring element belongs to the existing trace dual.
This follows from normality of the target base and integrality, not a
finite-local-freeness or landing hypothesis. -/
theorem normalizationImage_le_traceIntegralSubmodule
    (D : NormalizationDiagram (F := F) (N := N)) :
    LinearMap.range (Algebra.linearMap T₀ N) ≤ normalizationTraceIntegralSubmodule D := by
  letI := D.cover.normalClosure.finiteIntermediate
  letI : IsIntegrallyClosed B₀ :=
    polynomialImageAlgebra_isIntegrallyClosed_of_finiteDimensional F
  letI : FiniteDimensional K₀ N := D.cover.normalClosure.finiteNormal
  change LinearMap.range (Algebra.linearMap T₀ N) ≤ TraceIntegralSubmodule B₀ K₀ T₀ N
  rw [traceIntegralSubmodule_eq_traceDual, ← Submodule.one_eq_range]
  exact Submodule.one_le_traceDual_one (A := B₀) (K := K₀)

/-- The actual section module already contains the normalization image. -/
theorem normalizationImage_le_boundarySectionSubmodule
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) (hC : C ≠ ⊥) :
    LinearMap.range (Algebra.linearMap T₀ N) ≤ boundarySectionSubmodule D C hC := by
  rintro _ ⟨t, rfl⟩
  exact normalization_mem_boundarySectionSubalgebra D C hC t

/-- Recover the earlier conditional comparison from actual boundary
sections modulo `T` to the trace dual modulo `T`. The substantive landing
condition remains the existing trace-transporter membership. -/
def boundarySectionMultiplierQuotientMap
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) (hC : C ≠ ⊥) (s : T₀)
    (hLanding : s ∈ normalizationTraceTransporterIdeal D
      (boundarySectionSubmodule D C hC)) :
    (boundarySectionSubmodule D C hC ⧸
      (LinearMap.range (Algebra.linearMap T₀ N)).comap
        (boundarySectionSubmodule D C hC).subtype) →ₗ[T₀]
    normalizationTraceIntegralSubmodule D ⧸
      (LinearMap.range (Algebra.linearMap T₀ N)).comap
        (normalizationTraceIntegralSubmodule D).subtype :=
  multiplierSubmoduleQuotientMap (LinearMap.range (Algebra.linearMap T₀ N))
    (boundarySectionSubmodule D C hC) (normalizationTraceIntegralSubmodule D) s (by
      intro z hz
      simpa only [Algebra.smul_def] using
        (mem_normalizationTraceTransporterIdeal_iff
          D (boundarySectionSubmodule D C hC) s).mp hLanding z hz)

/-- The recovered comparison is multiplication by the prescribed scalar
in the same ambient normalization quotient. -/
theorem boundarySectionMultiplierQuotientMap_ambient
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) (hC : C ≠ ⊥) (s : T₀)
    (hLanding : s ∈ normalizationTraceTransporterIdeal D
      (boundarySectionSubmodule D C hC)) :
    (submoduleQuotientToAmbient (LinearMap.range (Algebra.linearMap T₀ N))
      (normalizationTraceIntegralSubmodule D)).comp
        (boundarySectionMultiplierQuotientMap D C hC s hLanding) =
      s • submoduleQuotientToAmbient (LinearMap.range (Algebra.linearMap T₀ N))
        (boundarySectionSubmodule D C hC) := by
  unfold boundarySectionMultiplierQuotientMap
  exact multiplierSubmoduleQuotientMap_ambient _ _ _ _ _

/-- Representative evaluation of the earlier map in `N / T`. -/
@[simp]
theorem boundarySectionMultiplierQuotientMap_ambient_mk
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) (hC : C ≠ ⊥) (s : T₀)
    (hLanding : s ∈ normalizationTraceTransporterIdeal D
      (boundarySectionSubmodule D C hC))
    (r : boundarySectionSubmodule D C hC) :
    submoduleQuotientToAmbient (LinearMap.range (Algebra.linearMap T₀ N))
        (normalizationTraceIntegralSubmodule D)
        (boundarySectionMultiplierQuotientMap D C hC s hLanding
          (Submodule.Quotient.mk r)) =
      Submodule.Quotient.mk ((s : N) * (r : N)) := rfl

end

end CollisionIdeals.Planar
