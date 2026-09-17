import CollisionIdeals.Planar.Rigidity.Consequences
import CollisionIdeals.Planar.Research.PrincipalPartsStrategy

/-!
# Trace-transporter landing

This file wires a supplied nonzero landing ideal directly into the
trace-integral dual and the established planar boundary-separation endgame.
It does not assert the secant--frame landing theorem, construct its concrete
coefficient ideal, or supply the local pole witness.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals.Planar

noncomputable section

variable {F : PlanarPolynomialMap}
variable {E : Type} [Field E]
variable [Algebra (PlanarBaseFunctionField F) E]

local notation "B₀" => PolynomialImageAlgebra F
local notation "K₀" => PlanarBaseFunctionField F
local notation "T₀" => GaloisNormalizationRing (F := F) (N := E)

/-- The trace-integral dual on the normalization ring, with finiteness of the
generic normal extension supplied by the normalization diagram. -/
def normalizationTraceIntegralSubmodule
    (D : NormalizationDiagram (F := F) (N := E)) : Submodule T₀ E := by
  letI algebraBK : Algebra B₀ K₀ := OreLocalization.instAlgebra
  letI : SMul B₀ K₀ := algebraBK.toSMul
  letI : Algebra B₀ E :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := E)
  letI : IsScalarTower B₀ K₀ E :=
    IsScalarTower.of_algebraMap_eq fun b => by
      change
        algebraMap K₀ E (algebraMap B₀ K₀ b) =
          algebraMap K₀ E (algebraMap B₀ K₀ b)
      rfl
  letI : FiniteDimensional K₀ E :=
    D.cover.normalClosure.finiteNormal
  exact TraceIntegralSubmodule B₀ K₀ T₀ E

/-- Multipliers carrying every selected normalization section into the
trace-integral dual.  This is the direct Lean form of the trace-transporter
ideal used by the secant--frame landing statement. -/
def normalizationTraceTransporterIdeal
    (D : NormalizationDiagram (F := F) (N := E))
    (sections : Submodule T₀ E) : Ideal T₀ := by
  letI algebraBK : Algebra B₀ K₀ := OreLocalization.instAlgebra
  letI : SMul B₀ K₀ := algebraBK.toSMul
  letI : Algebra B₀ E :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := E)
  letI : IsScalarTower B₀ K₀ E :=
    IsScalarTower.of_algebraMap_eq fun b => by
      change
        algebraMap K₀ E (algebraMap B₀ K₀ b) =
          algebraMap K₀ E (algebraMap B₀ K₀ b)
      rfl
  letI : FiniteDimensional K₀ E :=
    D.cover.normalClosure.finiteNormal
  exact traceTransporterIdeal B₀ K₀ T₀ E sections

theorem mem_normalizationTraceTransporterIdeal_iff
    (D : NormalizationDiagram (F := F) (N := E))
    (sections : Submodule T₀ E) (s : T₀) :
    s ∈ normalizationTraceTransporterIdeal D sections ↔
      ∀ z ∈ sections,
        (s : E) * z ∈ normalizationTraceIntegralSubmodule D := by
  letI algebraBK : Algebra B₀ K₀ := OreLocalization.instAlgebra
  letI : SMul B₀ K₀ := algebraBK.toSMul
  letI : Algebra B₀ E :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := E)
  letI : IsScalarTower B₀ K₀ E :=
    IsScalarTower.of_algebraMap_eq fun b => by
      change
        algebraMap K₀ E (algebraMap B₀ K₀ b) =
          algebraMap K₀ E (algebraMap B₀ K₀ b)
      rfl
  letI : FiniteDimensional K₀ E :=
    D.cover.normalClosure.finiteNormal
  rw [normalizationTraceTransporterIdeal,
    mem_traceTransporterIdeal_iff]
  rfl

/-- A nonzero prescribed landing ideal and the local pole-tower witness rule
out every height-one fixed--moving prime. -/
theorem boundarySeparation_of_traceLanding
    (D : NormalizationDiagram (F := F) (N := E))
    (sections : Subgroup (NormalizationGaloisGroup D) → Submodule T₀ E)
    (candidate : Subgroup (NormalizationGaloisGroup D) → Ideal T₀)
    (hCandidate :
      ∀ (C : Subgroup (NormalizationGaloisGroup D)), C ≠ ⊥ →
        candidate C ≠ ⊥)
    (hLanding :
      ∀ (C : Subgroup (NormalizationGaloisGroup D)), C ≠ ⊥ →
        candidate C ≤
          normalizationTraceTransporterIdeal D (sections C))
    (hPole :
      ∀ (C : Subgroup (NormalizationGaloisGroup D)), C ≠ ⊥ →
        ∀ p : PrimeSpectrum T₀,
          p.asIdeal.primeHeight = 1 →
          fixedMovingBoundaryIdeal D C ≤ p.asIdeal →
          ∀ s : T₀, s ≠ 0 →
            ∃ z ∈ sections C,
              (s : E) * z ∉
                normalizationTraceIntegralSubmodule D) :
    PlanarBoundarySeparation D := by
  intro C hC p hp hFixedMoving
  obtain ⟨s, hs, hs0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (hCandidate C hC)
  obtain ⟨z, hz, hzNot⟩ :=
    hPole C hC p hp hFixedMoving s hs0
  exact hzNot
    ((mem_normalizationTraceTransporterIdeal_iff
      D (sections C) s).mp (hLanding C hC hs) z hz)

/-- Direct trace landing reaches the already-verified collision-vanishing
endgame.  The secant--frame containment and pole witness remain explicit
hypotheses. -/
theorem planarVanishing_of_traceLanding
    (M : PlanarKellerCollisionModel F)
    (sections :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N := M.algebraN
      Subgroup (NormalizationGaloisGroup M.diagram) →
        Submodule (GaloisNormalizationRing (F := F) (N := M.N)) M.N)
    (candidate :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N := M.algebraN
      Subgroup (NormalizationGaloisGroup M.diagram) →
        Ideal (GaloisNormalizationRing (F := F) (N := M.N)))
    (hCandidate :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N := M.algebraN
      ∀ C, C ≠ ⊥ → candidate C ≠ ⊥)
    (hLanding :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N := M.algebraN
      ∀ C, C ≠ ⊥ →
        candidate C ≤
          normalizationTraceTransporterIdeal M.diagram (sections C))
    (hPole :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N := M.algebraN
      ∀ C, C ≠ ⊥ →
        ∀ p : PrimeSpectrum
            (GaloisNormalizationRing (F := F) (N := M.N)),
          p.asIdeal.primeHeight = 1 →
          fixedMovingBoundaryIdeal M.diagram C ≤ p.asIdeal →
          ∀ s : GaloisNormalizationRing (F := F) (N := M.N), s ≠ 0 →
            ∃ z ∈ sections C,
              (s : M.N) * z ∉
                normalizationTraceIntegralSubmodule M.diagram) :
    obstructionIdeal F = ⊥ := by
  letI : Field M.N := M.fieldN
  letI : Algebra (PlanarBaseFunctionField F) M.N := M.algebraN
  apply planarVanishing_of_boundarySeparation M
  exact boundarySeparation_of_traceLanding
    M.diagram sections candidate hCandidate hLanding hPole

end

end CollisionIdeals.Planar
