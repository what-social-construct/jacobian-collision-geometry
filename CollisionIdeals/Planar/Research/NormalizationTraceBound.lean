import CollisionIdeals.Planar.Research.BoundarySections
import CollisionIdeals.Planar.Research.MonogenicLanding
import CollisionIdeals.Planar.Research.TraceLanding
import CollisionIdeals.General.Normalization.Finiteness
import Mathlib.RingTheory.Localization.Integer

/-!
# A bounded denominator for the normalization trace dual

The trace-integral dual lies in the span of a finite trace-dual basis.
Consequently one nonzero normalization element clears every element of the
trace dual.  This does not require finite freeness of the normalization or
assume the desired boundedness as a geometric input.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals.Planar

noncomputable section

section TraceBound

variable (B K T N : Type*)
variable [CommRing B] [IsDomain B] [Field K] [CommRing T] [IsDomain T] [Field N]
variable [Algebra B K] [Algebra B T] [Algebra B N] [Algebra K N] [Algebra T N]
variable [IsScalarTower B K N] [IsScalarTower B T N]
variable [IsFractionRing B K] [IsFractionRing T N] [IsIntegralClosure T B N]
variable [FiniteDimensional K N] [Algebra.IsSeparable K N]

omit [IsDomain B] [IsDomain T] [IsFractionRing B K] [IsFractionRing T N] in
/-- An integral generic basis bounds the trace-integral dual by its finite
trace-dual span. -/
theorem traceIntegralSubmodule_le_span_traceDual
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K N) (hb : ∀ i, IsIntegral B (b i)) :
    TraceIntegralSubmodule B K T N ≤
      Submodule.span T (Set.range b.traceDual) := by
  intro z hz
  rw [← b.traceDual.sum_repr z]
  apply Submodule.sum_mem
  intro i _
  obtain ⟨t, ht⟩ := (IsIntegralClosure.isIntegral_iff (A := T)).mp (hb i)
  obtain ⟨r, hr⟩ := hz t
  have hrepr : b.traceDual.repr z i = algebraMap B K r := by
    rw [Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply, ← ht]
    exact hr.symm
  rw [hrepr, IsScalarTower.algebraMap_smul]
  exact ((Submodule.span T (Set.range b.traceDual)).restrictScalars B).smul_mem r
    (Submodule.subset_span (Set.mem_range_self i))

/-- One nonzero element of the integral closure clears the entire
trace-integral dual, not merely a prescribed finite coefficient family. -/
theorem exists_nonzero_traceIntegralSubmodule_denominator :
    ∃ d : T, d ≠ 0 ∧ ∀ z ∈ TraceIntegralSubmodule B K T N,
      d • z ∈ (1 : Submodule T N) := by
  classical
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral B K N
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors T) b.traceDual
  refine ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp d.property, ?_⟩
  intro z hz
  have hzspan := traceIntegralSubmodule_le_span_traceDual B K T N b hb hz
  refine Submodule.span_induction
    (p := fun z _ => (d : T) • z ∈ (1 : Submodule T N)) ?_ ?_ ?_ ?_ hzspan
  · rintro _ ⟨i, rfl⟩
    exact Submodule.mem_one.mpr (hd i)
  · simp
  · intro x y hx hy ihx ihy
    simpa only [smul_add] using (1 : Submodule T N).add_mem ihx ihy
  · intro a x hx ih
    rw [smul_smul, mul_comm, ← smul_smul]
    exact (1 : Submodule T N).smul_mem a ih

end TraceBound

variable {F : PlanarPolynomialMap}
variable {N : Type} [Field N]
variable [Algebra (PlanarBaseFunctionField F) N]

local notation "B₀" => PolynomialImageAlgebra F
local notation "K₀" => PlanarBaseFunctionField F
local notation "T₀" => GaloisNormalizationRing (F := F) (N := N)

/-- Finiteness of the normalization model over the polynomial image makes
its ring Noetherian. -/
theorem normalization_isNoetherianRing
    (D : NormalizationDiagram (F := F) (N := N)) :
    IsNoetherianRing T₀ := by
  letI : IsNoetherianRing B₀ := polynomialImageAlgebra_isNoetherianRing F
  letI : Module.Finite B₀ T₀ := D.cover.finiteNormalClosureModel
  exact IsNoetherianRing.of_finite B₀ T₀

/-- The normalization ring is integrally closed in its fraction field. -/
theorem normalization_isIntegrallyClosed
    (D : NormalizationDiagram (F := F) (N := N)) :
    IsIntegrallyClosed T₀ := by
  letI algebraBK : Algebra B₀ K₀ := OreLocalization.instAlgebra
  letI : SMul B₀ K₀ := algebraBK.toSMul
  letI : Algebra B₀ N := polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI : IsScalarTower B₀ K₀ N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : FiniteDimensional K₀ N := D.cover.normalClosure.finiteNormal
  exact integralClosure.isIntegrallyClosedOfFiniteExtension K₀

/-- The concrete normalization trace dual has a nonzero uniform denominator.
All extension and fraction-field hypotheses come from the given diagram. -/
theorem exists_nonzero_normalizationTraceIntegralSubmodule_denominator
    (D : NormalizationDiagram (F := F) (N := N)) :
    ∃ d : T₀, d ≠ 0 ∧ ∀ z ∈ normalizationTraceIntegralSubmodule D,
      (d : N) * z ∈ (1 : Submodule T₀ N) := by
  letI algebraBK : Algebra B₀ K₀ := OreLocalization.instAlgebra
  letI : SMul B₀ K₀ := algebraBK.toSMul
  letI : Algebra B₀ N := polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI : IsScalarTower B₀ K₀ N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : FiniteDimensional K₀ N := D.cover.normalClosure.finiteNormal
  letI : IsFractionRing T₀ N := normalization_isFractionRing D
  obtain ⟨d, hd, hdz⟩ := exists_nonzero_traceIntegralSubmodule_denominator B₀ K₀ T₀ N
  refine ⟨d, hd, ?_⟩
  intro z hz
  exact hdz z hz

/-- A uniform nonzero trace-dual multiplier forces the actual boundary
section algebra to be the normalization ring itself.  The additional
geometric claim that a deleted divisor gives a proper overring is separate. -/
theorem boundarySectionSubalgebra_eq_bot_of_trace_bound
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) (hC : C ≠ ⊥)
    (s : T₀) (hs : s ≠ 0)
    (hBound : ∀ z ∈ boundarySectionSubmodule D C hC,
      (s : N) * z ∈ normalizationTraceIntegralSubmodule D) :
    boundarySectionSubalgebra D C hC = ⊥ := by
  letI : IsNoetherianRing T₀ := normalization_isNoetherianRing D
  letI : IsIntegrallyClosed T₀ := normalization_isIntegrallyClosed D
  letI : IsFractionRing T₀ N := normalization_isFractionRing D
  obtain ⟨d, hd, hdz⟩ :=
    exists_nonzero_normalizationTraceIntegralSubmodule_denominator D
  apply subalgebra_eq_bot_of_nonzero_mul_mem_base T₀ N
    (boundarySectionSubalgebra D C hC) (d * s) (mul_ne_zero hd hs)
  intro z
  have hz : (z : N) ∈ boundarySectionSubmodule D C hC := z.property
  have h := Submodule.mem_one.mp (hdz _ (hBound _ hz))
  simpa only [map_mul, mul_assoc] using h

end

end CollisionIdeals.Planar
