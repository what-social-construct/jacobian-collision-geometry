import CollisionIdeals.Planar.Rigidity.Consequences
import CollisionIdeals.Planar.Research.MonogenicOrder
import CollisionIdeals.Planar.Research.PrincipalPartsStrategy

/-!
# Monogenic conductor landing

This file gives the research-layer interface corresponding to the archived boundary manuscript's
monogenic Tate--conductor reduction.  It defines an actual bounded submodule
and its transporter ideal; it does not introduce a proposition-valued bridge
or assert that the secant denominator lands in it.

The final theorems isolate the remaining local input pointwise.  At a
height-one prime containing the fixed--moving ideal, every nonzero multiplier
must fail the conductor test on some boundary section.  If a prescribed
nonzero candidate ideal nevertheless lands uniformly, this pointwise
statement gives boundary separation and hence the existing planar endgame.

The generic finite-overring lemma below records a second, stronger use of a
uniform scalar denominator.  Once the boundary-section algebra `R_C` is
constructed as a `T`-subalgebra of the fraction field, a nonzero `a` with
`a R_C \subseteq T` makes `R_C` finite over `T`; normality then forces
`R_C = T`.  This is available for the future ring-level specialization and
does not replace the present pointwise pole hypothesis.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

universe u v w

section FiniteOverring

variable (T : Type v) [CommRing T] [IsNoetherianRing T] [IsIntegrallyClosed T]
variable (N : Type w) [Field N] [Algebra T N] [IsFractionRing T N]

/-- A normal Noetherian domain has no proper overring inside its fraction
field whose denominators are uniformly cleared by one nonzero base element.

Multiplication by `a` embeds `R` linearly into `T`, so Noetherianity makes
`R` module-finite and hence integral over `T`.  Integral closedness then puts
every element of `R` back in the image of `T`; this image is the bottom
`T`-subalgebra of `N`.

In the intended specialization, `R` is the boundary-section algebra `R_C`
and `a` is the nonzero secant--Jacobian multiplier. -/
theorem subalgebra_eq_bot_of_nonzero_mul_mem_base
    (R : Subalgebra T N) (a : T) (ha : a ≠ 0)
    (hBound : ∀ r : R,
      algebraMap T N a * (r : N) ∈ Set.range (algebraMap T N)) :
    R = ⊥ := by
  let baseEquiv : T ≃ₗ[T] LinearMap.range (Algebra.linearMap T N) :=
    LinearEquiv.ofInjective (Algebra.linearMap T N)
      (IsFractionRing.injective T N)
  let multiplied : R →ₗ[T] N :=
    (LinearMap.mulLeft T (algebraMap T N a)).comp R.val.toLinearMap
  let multipliedRange : R →ₗ[T] LinearMap.range (Algebra.linearMap T N) :=
    multiplied.codRestrict _ (fun r => hBound r)
  let reduce : R →ₗ[T] T :=
    baseEquiv.symm.toLinearMap.comp multipliedRange
  have haN : algebraMap T N a ≠ 0 := by
    intro haImage
    apply ha
    apply IsFractionRing.injective T N
    simpa using haImage
  have hReduce : Function.Injective reduce := by
    intro x y hxy
    have hxyRange : multipliedRange x = multipliedRange y :=
      baseEquiv.symm.injective hxy
    have hxyN :
        algebraMap T N a * (x : N) =
          algebraMap T N a * (y : N) :=
      congrArg Subtype.val hxyRange
    exact Subtype.ext (mul_left_cancel₀ haN hxyN)
  letI : Module.Finite T R :=
    Module.Finite.of_injective reduce hReduce
  apply le_antisymm ?_ bot_le
  intro x hx
  rw [Algebra.mem_bot]
  have hxIntegralR : IsIntegral T (⟨x, hx⟩ : R) :=
    IsIntegral.of_finite T _
  have hxIntegralN : IsIntegral T x := hxIntegralR.map R.val
  exact IsIntegrallyClosed.isIntegral_iff.mp hxIntegralN

end FiniteOverring

variable (B : Type u) [CommRing B]
variable (T : Type v) [CommRing T] [Algebra B T]
variable (N : Type w) [CommRing N] [Algebra T N]

/-- The conductor ideal of the monogenic order, embedded in the ambient
`T`-algebra. -/
def monogenicConductorSubmodule (alpha : T) : Submodule T N :=
  Submodule.map (Algebra.linearMap T N)
    (monogenicOrderConductor B T alpha)

/-- The bounded conductor stage: an ambient element belongs when its
`J_alpha`-multiple lies in the embedded conductor.  In the finite separable
normalization specialization, Tate's identity identifies this with the trace
dual of `T`. -/
def monogenicConductorBoundedStage
    (alpha : T) : Submodule T N :=
  (monogenicConductorSubmodule B T N alpha).comap
    (LinearMap.mulLeft T
      (algebraMap T N (monogenicOrderJacobian B T alpha)))

theorem mem_monogenicConductorBoundedStage_iff
    (alpha : T) (z : N) :
    z ∈ monogenicConductorBoundedStage B T N alpha ↔
      algebraMap T N (monogenicOrderJacobian B T alpha) * z ∈
        monogenicConductorSubmodule B T N alpha :=
  Iff.rfl

/-- Multipliers carrying every selected boundary section into the monogenic
conductor bounded stage. -/
def monogenicConductorLandingIdeal
    (alpha : T) (sections : Submodule T N) : Ideal T :=
  boundedStageComparisonIdeal T N
    (monogenicConductorBoundedStage B T N alpha) sections

theorem mem_monogenicConductorLandingIdeal_iff
    (alpha : T) (sections : Submodule T N) (s : T) :
    s ∈ monogenicConductorLandingIdeal B T N alpha sections ↔
      ∀ z ∈ sections,
        algebraMap T N (monogenicOrderJacobian B T alpha) *
            (algebraMap T N s * z) ∈
          monogenicConductorSubmodule B T N alpha := by
  rw [monogenicConductorLandingIdeal,
    mem_boundedStageComparisonIdeal_iff]
  simp only [monogenicConductorBoundedStage, Submodule.mem_comap,
    LinearMap.mulLeft_apply, Algebra.smul_def]

section PlanarSpecialization

variable {F : PlanarPolynomialMap}
variable {E : Type} [Field E]
variable [Algebra (PlanarBaseFunctionField F) E]

local notation "B₀" => PolynomialImageAlgebra F
local notation "T₀" => GaloisNormalizationRing (F := F) (N := E)

/-- A pointwise unbounded-pole test plus one nonzero conductor-landing
multiplier for each nontrivial subgroup rules out every height-one
fixed--moving prime.

The hypothesis `hPole` is deliberately stated elementwise: it asks for the
boundary section witnessing failure of a proposed nonzero multiplier.  It is
the local DVR pole-tower assertion still missing from the formalization, not
an alias for boundary separation. -/
theorem boundarySeparation_of_monogenicConductorMultiplier
    (D : NormalizationDiagram (F := F) (N := E))
    (alpha : T₀)
    (sections : Subgroup (NormalizationGaloisGroup D) → Submodule T₀ E)
    (hMultiplier :
      ∀ (C : Subgroup (NormalizationGaloisGroup D)), C ≠ ⊥ →
        ∃ s : T₀, s ≠ 0 ∧
          s ∈ monogenicConductorLandingIdeal B₀ T₀ E alpha (sections C))
    (hPole :
      ∀ (C : Subgroup (NormalizationGaloisGroup D)), C ≠ ⊥ →
        ∀ p : PrimeSpectrum T₀,
          p.asIdeal.primeHeight = 1 →
          fixedMovingBoundaryIdeal D C ≤ p.asIdeal →
          ∀ s : T₀, s ≠ 0 →
            ∃ z ∈ sections C,
              algebraMap T₀ E
                    (monogenicOrderJacobian B₀ T₀ alpha) *
                  (algebraMap T₀ E s * z) ∉
                monogenicConductorSubmodule B₀ T₀ E alpha) :
    PlanarBoundarySeparation D := by
  intro C hC p hp hFixedMoving
  obtain ⟨s, hs0, hsLanding⟩ := hMultiplier C hC
  obtain ⟨z, hz, hzNot⟩ :=
    hPole C hC p hp hFixedMoving s hs0
  exact hzNot
    ((mem_monogenicConductorLandingIdeal_iff
      B₀ T₀ E alpha (sections C) s).mp hsLanding z hz)

/-- Ideal-containment form of
`boundarySeparation_of_monogenicConductorMultiplier`.  This is the direct
formal target for a future specialization of the nonzero secant--frame
denominator ideal. -/
theorem boundarySeparation_of_monogenicConductorLanding
    (D : NormalizationDiagram (F := F) (N := E))
    (alpha : T₀)
    (sections : Subgroup (NormalizationGaloisGroup D) → Submodule T₀ E)
    (candidate : Subgroup (NormalizationGaloisGroup D) → Ideal T₀)
    (hCandidate :
      ∀ (C : Subgroup (NormalizationGaloisGroup D)), C ≠ ⊥ →
        candidate C ≠ ⊥)
    (hLanding :
      ∀ (C : Subgroup (NormalizationGaloisGroup D)), C ≠ ⊥ →
        candidate C ≤
          monogenicConductorLandingIdeal B₀ T₀ E alpha (sections C))
    (hPole :
      ∀ (C : Subgroup (NormalizationGaloisGroup D)), C ≠ ⊥ →
        ∀ p : PrimeSpectrum T₀,
          p.asIdeal.primeHeight = 1 →
          fixedMovingBoundaryIdeal D C ≤ p.asIdeal →
          ∀ s : T₀, s ≠ 0 →
            ∃ z ∈ sections C,
              algebraMap T₀ E
                    (monogenicOrderJacobian B₀ T₀ alpha) *
                  (algebraMap T₀ E s * z) ∉
                monogenicConductorSubmodule B₀ T₀ E alpha) :
    PlanarBoundarySeparation D := by
  apply boundarySeparation_of_monogenicConductorMultiplier
    D alpha sections _ hPole
  intro C hC
  obtain ⟨s, hs, hs0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (hCandidate C hC)
  exact ⟨s, hs0, hLanding C hC hs⟩

/-- The conductor-landing input reaches the already-verified collision
vanishing endgame. -/
theorem planarVanishing_of_monogenicConductorLanding
    (M : PlanarKellerCollisionModel F)
    (alpha :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N := M.algebraN
      GaloisNormalizationRing (F := F) (N := M.N))
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
        candidate C ≤ monogenicConductorLandingIdeal
          (PolynomialImageAlgebra F)
          (GaloisNormalizationRing (F := F) (N := M.N)) M.N
          alpha (sections C))
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
              algebraMap
                    (GaloisNormalizationRing (F := F) (N := M.N)) M.N
                    (monogenicOrderJacobian
                      (PolynomialImageAlgebra F)
                      (GaloisNormalizationRing (F := F) (N := M.N)) alpha) *
                  (algebraMap
                      (GaloisNormalizationRing (F := F) (N := M.N)) M.N s * z) ∉
                monogenicConductorSubmodule
                  (PolynomialImageAlgebra F)
                  (GaloisNormalizationRing (F := F) (N := M.N)) M.N alpha) :
    obstructionIdeal F = ⊥ := by
  letI : Field M.N := M.fieldN
  letI : Algebra (PlanarBaseFunctionField F) M.N := M.algebraN
  apply planarVanishing_of_boundarySeparation M
  exact boundarySeparation_of_monogenicConductorLanding
    M.diagram alpha sections candidate hCandidate hLanding hPole

end PlanarSpecialization

end

end CollisionIdeals.Planar
