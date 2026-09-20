import CollisionIdeals.Planar.Research.BoundarySections
import CollisionIdeals.Planar.Research.BoundaryPoleWitness
import CollisionIdeals.Planar.Boundary.PrimeOrder
import CollisionIdeals.Planar.Research.SecantFrameCandidate
import CollisionIdeals.Planar.Research.TraceLanding

/-!
# The concrete secant--frame trace-landing problem

Here the section module is the image of the actual structure-sheaf ring
`R_C = Γ(Spec T \ V(J_C), O)` in the normal closure, and the prescribed
ideal is the denominator of the evaluated secant/adjugate first jets.
Neither is an arbitrary input to the endpoint theorem.

Their definitions, denominator nonvanishing, and the boundary-section pole
witness are proved. Uniform trace landing for all sections remains an
explicit hypothesis; this file does not assert that missing theorem. Its
containment already forces the section algebra to equal the normalization
ring, so it is a vanishing statement, not finite denominator clearing.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals.Planar

noncomputable section

variable {F : PlanarPolynomialMap}
variable {N : Type} [Field N]
variable [Algebra (PlanarBaseFunctionField F) N]

local notation "T₀" => GaloisNormalizationRing (F := F) (N := N)

/-- The prescribed landing containment already forces all actual boundary
sections back into the normalization ring. Denominator nonvanishing alone
does not establish this substantive vanishing statement. -/
theorem boundarySectionSubalgebra_eq_bot_of_secantFrameTraceLanding
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) (hC : C ≠ ⊥) (c : ℂ)
    (hLanding :
      secantFrameDenominatorIdeal T₀ D.cover.normalClosure C c ≤
        normalizationTraceTransporterIdeal D
          (boundarySectionSubmodule D C hC)) :
    boundarySectionSubalgebra D C hC = ⊥ := by
  letI : IsFractionRing T₀ N := normalization_isFractionRing D
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (secantFrameDenominatorIdeal_ne_bot T₀ D.cover.normalClosure C c)
  apply boundarySectionSubalgebra_eq_bot_of_trace_bound D C hC s hs0
  exact (mem_normalizationTraceTransporterIdeal_iff
    D (boundarySectionSubmodule D C hC) s).mp (hLanding hs)

/-- Landing for the prescribed secant--frame ideal contradicts the proved
pole witness in the genuine boundary-section ring. Landing is needed only
for prime-order subgroups, as in the manuscript. -/
theorem boundarySeparation_of_secantFrameTraceLanding
    (D : NormalizationDiagram (F := F) (N := N)) (c : ℂ)
    (hLanding :
      ∀ (C : Subgroup (NormalizationGaloisGroup D)) (hC : C ≠ ⊥),
        (Nat.card C).Prime →
        secantFrameDenominatorIdeal T₀ D.cover.normalClosure C c ≤
          normalizationTraceTransporterIdeal D
            (boundarySectionSubmodule D C hC)) :
    PlanarBoundarySeparation D := by
  letI : IsFractionRing T₀ N := normalization_isFractionRing D
  apply boundarySeparation_of_primeOrder D
  intro C hC hPrime p hp hFixedMoving
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (secantFrameDenominatorIdeal_ne_bot T₀ D.cover.normalClosure C c)
  obtain ⟨z, hz, hzNot⟩ :=
    boundarySection_poleWitness D C hC p hp hFixedMoving s hs0
  exact hzNot
    ((mem_normalizationTraceTransporterIdeal_iff
      D (boundarySectionSubmodule D C hC) s).mp
        (hLanding C hC hPrime hs) z hz)

/-- Concrete landing reaches the existing planar vanishing theorem for a
supplied Keller collision--normalization model; the pole witness is derived.
The frame uses the nonzero constant Jacobian determinant provided by
`M.keller`, rather than an independently supplied scalar. No uniform
landing claim is made here. -/
theorem planarVanishing_of_secantFrameTraceLanding
    (M : PlanarKellerCollisionModel F)
    (hLanding :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N := M.algebraN
      ∀ (C : Subgroup (NormalizationGaloisGroup M.diagram)) (hC : C ≠ ⊥),
        (Nat.card C).Prime →
        secantFrameDenominatorIdeal
            (GaloisNormalizationRing (F := F) (N := M.N))
            M.diagram.cover.normalClosure C (Classical.choose M.keller) ≤
          normalizationTraceTransporterIdeal M.diagram
            (boundarySectionSubmodule M.diagram C hC)) :
    obstructionIdeal F = ⊥ := by
  letI : Field M.N := M.fieldN
  letI : Algebra (PlanarBaseFunctionField F) M.N := M.algebraN
  exact planarVanishing_of_boundarySeparation M
    (boundarySeparation_of_secantFrameTraceLanding M.diagram
      (Classical.choose M.keller) hLanding)

end

end CollisionIdeals.Planar
