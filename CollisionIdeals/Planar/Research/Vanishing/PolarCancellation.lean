import CollisionIdeals.General.Keller.ValuationCancellation
import CollisionIdeals.Planar.Research.Vanishing.BoundaryValuation

/-!
# A finite polar cancellation certificate at a ramified divisor

For the actual centered valuation in a planar normalization diagram,
nontrivial inertia supplies a moved sheet. Local collision rigidity forces
a coordinate pole. The global polynomial Keller support then supplies two
distinct dominant polar monomials in one component on that same sheet.

Target-coordinate regularity and triviality on nonzero complex constants
are derived from the existing normalization center map. They are not
additional regularity assumptions on the moved source sheet.

This records the finite cancellation that a pole-exclusion argument must
eliminate. It neither eliminates that cancellation nor proves vanishing.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals.Planar

noncomputable section

open MvPolynomial

variable {F : PlanarPolynomialMap} {N : Type} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

local notation "B₀" => PolynomialImageAlgebra F
local notation "K₀" => PolynomialMapBaseFunctionField F
local notation "T₀" => PolynomialNormalizationInExtensionRing (F := F) (N := N)

@[reducible] local instance polarCancellationBaseAlgebra : Algebra B₀ N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

@[reducible] local instance polarCancellationBaseFieldAlgebra : Algebra B₀ K₀ :=
  OreLocalization.instAlgebra

local instance polarCancellationBaseFieldSMul : SMul B₀ K₀ := Algebra.toSMul

local instance polarCancellationBaseFieldTower : IsScalarTower B₀ K₀ N :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

@[reducible] local instance polarCancellationNormalizationCommRing : CommRing T₀ :=
  Subalgebra.toCommRing (integralClosure B₀ N)

/-- Any supplied ramified divisor of the actual planar diagram forces a
moved sheet with two equally dominant polar polynomial terms. All valuation
conditions on the target and constants follow from centeredness. -/
theorem exists_polar_monomial_cancellation_at_ramified_divisor
    (D : PolynomialNormalizationDiagram (F := F) (N := N))
    (hKeller : IsPlanarKeller F)
    (E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N)) :
    letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    ∃ g σ : D.cover.normalClosure.galoisGroup,
      σ ∈ inertiaGroupAt K₀ (D.valuationAt E).valuationRing ∧
      σ ∉ D.cover.normalClosure.intermediateFixingSubgroup.map
        (MulAut.conj g).toMonoidHom ∧
      ∃ j : Fin 2, ∃ a ∈ (F j).support, ∃ b ∈ (F j).support,
        a ≠ b ∧
        (D.valuationAt E).valuationRing.valuation
            (polynomialConjugateSourceMap D.cover.normalClosure g
              (monomial a (coeff a (F j)))) =
          (D.valuationAt E).valuationRing.valuation
            (polynomialConjugateSourceMap D.cover.normalClosure g
              (monomial b (coeff b (F j)))) ∧
        1 < (D.valuationAt E).valuationRing.valuation
          (polynomialConjugateSourceMap D.cover.normalClosure g
            (monomial a (coeff a (F j)))) ∧
        ∀ m ∈ (F j).support,
          (D.valuationAt E).valuationRing.valuation
              (polynomialConjugateSourceMap D.cover.normalClosure g
                (monomial m (coeff m (F j)))) ≤
            (D.valuationAt E).valuationRing.valuation
              (polynomialConjugateSourceMap D.cover.normalClosure g
                (monomial a (coeff a (F j)))) := by
  classical
  letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  let V := (D.valuationAt E).valuationRing
  let D₀ := D.cover.normalClosure
  have hScalar (c : ℂ) (hc : c ≠ 0) :
      V.valuation (algebraMap ℂ N c) = 1 := by
    exact ground_boundaryValuation_eq_one D E c hc
  have hRegular (g : D₀.galoisGroup) (j : Fin 2) :
      V.valuation (polynomialConjugateSourceMap D₀ g (F j)) ≤ 1 := by
    exact (V.valuation_le_one_iff _).mpr
      (conjugateTarget_mem_boundaryValuationRing D E g j)
  obtain ⟨g, σ, hσ, hMoved, i, hi⟩ :=
    exists_moved_coordinate_pole_at_ramified_divisor D hKeller E
  have hPole : 1 < V.valuation (polynomialConjugateSourceMap D₀ g (X i)) := by
    apply lt_of_not_ge
    intro h
    exact hi ((V.valuation_le_one_iff _).mp h)
  obtain ⟨j, a, ha, b, hb, hab, hval, hpolar, hmax⟩ :=
    exists_dominant_monomial_pair_of_isKeller_of_coordinate_pole
      F hKeller (polynomialConjugateSourceMap D₀ g) V.valuation
      hScalar (hRegular g) i hPole
  exact ⟨g, σ, hσ, hMoved, j, a, ha, b, hb, hab, hval, hpolar, hmax⟩

end

end CollisionIdeals.Planar
