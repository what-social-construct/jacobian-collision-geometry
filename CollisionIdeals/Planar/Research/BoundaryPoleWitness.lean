import CollisionIdeals.Planar.Research.HeightOneBoundaryPole
import CollisionIdeals.Planar.Research.NormalizationTraceBound

/-!
# The boundary-section pole witness

A removed height-one prime gives a genuine section outside the normalization
ring. A hypothetical nonzero multiplier sending every section into the
trace dual would, by its bounded denominator and normal-Noetherian overring
rigidity, put every section back in the normalization ring. This proves the
pointwise witness used by trace landing without assuming landing or boundary
separation, and without needing the local-cohomology comparison sequence.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals.Planar

noncomputable section

variable {F : PlanarPolynomialMap}
variable {N : Type} [Field N]
variable [Algebra (PlanarBaseFunctionField F) N]

local instance boundaryPoleBaseAlgebra : Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

local notation "T₀" => GaloisNormalizationRing (F := F) (N := N)

/-- A height-one fixed--moving prime makes the boundary-section overring
strictly larger than the normalization ring. -/
theorem boundarySectionSubalgebra_ne_bot_of_heightOne
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) (hC : C ≠ ⊥)
    (p : PrimeSpectrum T₀) (hp : Ideal.primeHeight (R := T₀) p.asIdeal = 1)
    (hJp : fixedMovingBoundaryIdeal D C ≤ p.asIdeal) :
    boundarySectionSubalgebra D C hC ≠ ⊥ := by
  letI : IsNoetherianRing T₀ := normalization_isNoetherianRing D
  letI : IsFractionRing T₀ N := normalization_isFractionRing D
  letI := fixedMovingBoundaryOpen_nonempty D C hC
  change (affineSectionsToFractionField (N := N)
    (fixedMovingBoundaryOpen D C)).range ≠ ⊥
  apply affineSections_range_ne_bot_of_heightOne
    (fixedMovingBoundaryOpen D C) (fixedMovingBoundaryIdeal D C) _ _ p hp hJp
  · intro hzero
    apply fixedLocusIdeal_ne_bot D C hC
    apply le_bot_iff.mp
    exact (show fixedLocusIdeal C ≤ fixedMovingBoundaryIdeal D C from le_sup_left).trans
      (le_of_eq hzero)
  · intro x
    exact x.property

/-- Every nonzero proposed trace multiplier fails on an actual boundary
section when a height-one prime contains the fixed--moving ideal. -/
theorem boundarySection_poleWitness
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) (hC : C ≠ ⊥)
    (p : PrimeSpectrum T₀) (hp : Ideal.primeHeight (R := T₀) p.asIdeal = 1)
    (hJp : fixedMovingBoundaryIdeal D C ≤ p.asIdeal)
    (s : T₀) (hs : s ≠ 0) :
    ∃ z ∈ boundarySectionSubmodule D C hC,
      (s : N) * z ∉ normalizationTraceIntegralSubmodule D := by
  by_contra h
  push_neg at h
  exact (boundarySectionSubalgebra_ne_bot_of_heightOne D C hC p hp hJp)
    (boundarySectionSubalgebra_eq_bot_of_trace_bound D C hC s hs h)

end

end CollisionIdeals.Planar
