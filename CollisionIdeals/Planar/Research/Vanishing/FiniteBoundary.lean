import CollisionIdeals.General.Keller.ConjugateInvariantFiniteness
import CollisionIdeals.General.Keller.CollisionModel
import CollisionIdeals.General.Normalization.FiniteSource
import CollisionIdeals.Planar.Research.Vanishing.Ramification

/-!
# From an empty actual target boundary to planar vanishing

Source finiteness fills the intermediate normalization, leaving no place
for hidden inertia. The existing normalization and ramification endpoint
then gives collision-obstruction vanishing with purity and finite-etale
rigidity passed explicitly.

The actual target-boundary and conormal hypotheses feed that endpoint
through the proved source-finiteness bridge. This imports no custom
literature axioms and does not prove those boundary hypotheses.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

/-- A finite planar Keller source has vanishing collision obstruction,
relative to the two existing geometric theorem inputs. -/
theorem planarVanishing_of_source_finite
    {F : PlanarPolynomialMap}
    (hPurity : BranchPurityA2)
    (hFiniteEtaleRigidity : AffinePlaneFiniteEtaleRigidity)
    (hKeller : IsKeller F)
    [Module.Finite (PolynomialImageAlgebra F) (PolynomialSourceCoordinateRing ℂ 2)] :
    obstructionIdeal F = ⊥ := by
  let M := PolynomialKellerCollisionModel.ofIsKeller hKeller
  letI : Field M.N := M.fieldN
  letI : Algebra (PolynomialMapBaseFunctionField F) M.N := M.algebraN
  have hNoHidden : M.diagram.NoHiddenInertia := by
    rintro ⟨E, ⟨q, hq⟩, hBoundary⟩
    have hmem := hBoundary q (Nat.ne_of_gt hq)
    rw [polynomialIntermediateNormalizationBoundary_eq_empty_of_finite F] at hmem
    exact hmem
  exact planarVanishing_of_normalizedCover_noCodimensionOneRamification
    hPurity hFiniteEtaleRigidity hKeller M.diagram.cover
    (M.diagram.noCodimensionOneRamification
      M.ramifiedConjugateCentersInBoundary_of_keller hNoHidden)

variable {F : PlanarPolynomialMap} {N : Type} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]
variable [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]

/-- The unit actual target-boundary ideal feeds the existing planar
vanishing endpoint; no new boundary model or rigidity premise is supplied. -/
theorem planarVanishing_of_conjugateInvariantBoundary_eq_top
    (hPurity : BranchPurityA2)
    (hFiniteEtaleRigidity : AffinePlaneFiniteEtaleRigidity)
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F)
    (hBoundary : polynomialConjugateInvariantBoundaryIdeal D hKeller = ⊤) :
    obstructionIdeal F = ⊥ := by
  letI := polynomialSource_finite_of_conjugateInvariantBoundary_eq_top D hKeller hBoundary
  exact planarVanishing_of_source_finite hPurity hFiniteEtaleRigidity hKeller

/-- The actual two target-coordinate conormal components are sufficient
for planar obstruction vanishing, with both literature inputs explicit. -/
theorem planarVanishing_of_conjugateInvariantBoundary_conormal_eq_zero
    (hPurity : BranchPurityA2)
    (hFiniteEtaleRigidity : AffinePlaneFiniteEtaleRigidity)
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F)
    (hConormal : letI := D.finiteIntermediate
      ∀ i : Fin 2, derivationConormalComponent (polynomialImageCoordinatePartial F i)
        (polynomialConjugateInvariantBoundaryIdeal D hKeller) = 0) :
    obstructionIdeal F = ⊥ := by
  letI := polynomialSource_finite_of_conjugateInvariantBoundary_conormal_eq_zero
    D hKeller hConormal
  exact planarVanishing_of_source_finite hPurity hFiniteEtaleRigidity hKeller

/-- Finite generator derivatives provide the same conditional endpoint.
The required memberships remain the substantive Keller-specific input. -/
theorem planarVanishing_of_conjugateInvariantBoundary_generator_test
    (hPurity : BranchPurityA2)
    (hFiniteEtaleRigidity : AffinePlaneFiniteEtaleRigidity)
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F)
    (generators : Finset (PolynomialImageAlgebra F))
    (hGenerators : Ideal.span (generators : Set (PolynomialImageAlgebra F)) =
      polynomialConjugateInvariantBoundaryIdeal D hKeller)
    (hTest : letI := D.finiteIntermediate
      ∀ i : Fin 2, ∀ f ∈ generators, polynomialImageCoordinatePartial F i f ∈
        polynomialConjugateInvariantBoundaryIdeal D hKeller) :
    obstructionIdeal F = ⊥ := by
  apply planarVanishing_of_conjugateInvariantBoundary_eq_top
    hPurity hFiniteEtaleRigidity D hKeller
  apply (polynomialConjugateInvariantBoundaryIdeal_eq_top_iff D hKeller).mpr
  exact (polynomialConjugateInvariantBoundary_generator_test_iff
    D hKeller generators hGenerators).mp hTest

end

end CollisionIdeals.Planar
