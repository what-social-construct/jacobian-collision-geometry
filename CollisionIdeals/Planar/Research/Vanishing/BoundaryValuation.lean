import CollisionIdeals.General.Normalization.Diagram
import CollisionIdeals.General.Galois.InertiaQuotient
import CollisionIdeals.Planar.Research.Vanishing.InertiaCoordinates

/-!
# Regular target values and a polar moved sheet at the same divisor

These are the geometric inputs shared by the finite cancellation and
initial-residue comparisons. Centeredness supplies the ground constants
and target values in the actual valuation ring. Nontrivial inertia and
local Keller collision rigidity supply a source coordinate outside that
same ring. No regularity of an inertia-moved source sheet is assumed.
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

@[reducible] local instance boundaryValuationBaseAlgebra : Algebra B₀ N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

@[reducible] local instance boundaryValuationBaseFieldAlgebra : Algebra B₀ K₀ :=
  OreLocalization.instAlgebra

local instance boundaryValuationBaseFieldSMul : SMul B₀ K₀ := Algebra.toSMul

local instance boundaryValuationBaseFieldTower : IsScalarTower B₀ K₀ N :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

@[reducible] local instance boundaryValuationNormalizationCommRing : CommRing T₀ :=
  Subalgebra.toCommRing (integralClosure B₀ N)

/-- The actual center map makes every ground-field constant regular. -/
theorem ground_mem_boundaryValuationRing
    (D : PolynomialNormalizationDiagram (F := F) (N := N))
    (E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N)) (c : ℂ) :
    algebraMap K₀ N (algebraMap ℂ K₀ c) ∈ (D.valuationAt E).valuationRing := by
  obtain ⟨centerMap, hCenter, _⟩ := D.valuation_centered E
  have h := (centerMap (algebraMap B₀ T₀ (algebraMap ℂ B₀ c))).property
  rw [hCenter] at h
  change algebraMap K₀ N (algebraMap B₀ K₀ (algebraMap ℂ B₀ c)) ∈ _ at h
  rwa [← IsScalarTower.algebraMap_apply ℂ B₀ K₀] at h

/-- The coefficient inclusion corestricted to the actual centered ring. -/
def boundaryGroundRingHom
    (D : PolynomialNormalizationDiagram (F := F) (N := N))
    (E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N)) :
    ℂ →+* (D.valuationAt E).valuationRing :=
  { toFun := fun c => ⟨algebraMap K₀ N (algebraMap ℂ K₀ c),
      ground_mem_boundaryValuationRing D E c⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := fun _ _ => Subtype.ext (by simp)
    map_zero' := Subtype.ext (by simp)
    map_add' := fun _ _ => Subtype.ext (by simp) }

/-- Nonzero coefficients are units in the same centered valuation ring. -/
theorem ground_boundaryValuation_eq_one
    (D : PolynomialNormalizationDiagram (F := F) (N := N))
    (E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N))
    (c : ℂ) (hc : c ≠ 0) :
    letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    (D.valuationAt E).valuationRing.valuation (algebraMap ℂ N c) = 1 := by
  letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  let V := (D.valuationAt E).valuationRing
  letI : Algebra ℂ V := (boundaryGroundRingHom D E).toAlgebra
  have hGround : (algebraMap ℂ V c : N) = algebraMap ℂ N c := rfl
  rw [← hGround]
  exact (V.valuation_eq_one_iff (algebraMap ℂ V c)).mp
    ((isUnit_iff_ne_zero.mpr hc).map (algebraMap ℂ V))

/-- Every target coordinate, on every conjugate sheet, belongs to the
same valuation ring. This is derived from centeredness, not source regularity. -/
theorem conjugateTarget_mem_boundaryValuationRing
    (D : PolynomialNormalizationDiagram (F := F) (N := N))
    (E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N))
    (g : D.cover.normalClosure.galoisGroup) (j : Fin 2) :
    letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    polynomialConjugateSourceMap D.cover.normalClosure g (F j) ∈
      (D.valuationAt E).valuationRing := by
  letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  obtain ⟨centerMap, hCenter, _⟩ := D.valuation_centered E
  let b : B₀ := ⟨F j, ⟨X j, coordinateAlgHom_X F j⟩⟩
  have hValue : polynomialConjugateSourceMap D.cover.normalClosure g (F j) =
      (centerMap (algebraMap B₀ T₀ b) : N) := by
    change polynomialConjugateSourceMapOverImage D.cover.normalClosure g
      (algebraMap B₀ (PolynomialSourceCoordinateRing ℂ 2) b) = _
    rw [(polynomialConjugateSourceMapOverImage D.cover.normalClosure g).commutes]
    exact (hCenter (algebraMap B₀ T₀ b)).symm
  rw [hValue]
  exact (centerMap (algebraMap B₀ T₀ b)).property

/-- A ramified divisor supplies an inertia-moved sheet with a source
coordinate outside the actual centered valuation ring. -/
theorem exists_moved_coordinate_pole_at_ramified_divisor
    (D : PolynomialNormalizationDiagram (F := F) (N := N))
    (hKeller : IsPlanarKeller F)
    (E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N)) :
    letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    ∃ g σ : D.cover.normalClosure.galoisGroup,
      σ ∈ inertiaGroupAt K₀ (D.valuationAt E).valuationRing ∧
      σ ∉ D.cover.normalClosure.intermediateFixingSubgroup.map
        (MulAut.conj g).toMonoidHom ∧
      ∃ i : Fin 2, polynomialConjugateSourceMap D.cover.normalClosure g (X i) ∉
        (D.valuationAt E).valuationRing := by
  letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  let V := (D.valuationAt E).valuationRing
  letI : Algebra ℂ V := (boundaryGroundRingHom D E).toAlgebra
  have hGround (c : ℂ) : (algebraMap ℂ V c : N) =
      algebraMap K₀ N (algebraMap ℂ K₀ c) := rfl
  let D₀ := D.cover.normalClosure
  letI : FiniteDimensional K₀ N := D₀.finiteNormal
  let I := inertiaGroupAt K₀ V
  let H := D₀.intermediateFixingSubgroup
  obtain ⟨g, hg⟩ := exists_conjugate_one_lt_inertiaQuotientIndex I H
    D₀.intermediateFixingSubgroup_normalCore_eq_bot (D.inertia_nontrivial E)
  have hMovedExists : ∃ σ ∈ I, σ ∉ H.map (MulAut.conj g).toMonoidHom := by
    by_contra! h
    exact (ne_of_gt hg)
      ((inertiaQuotientIndex_eq_one_iff I (H.map (MulAut.conj g).toMonoidHom)).mpr h)
  obtain ⟨σ, hσ, hMoved⟩ := hMovedExists
  obtain ⟨i, hi⟩ := exists_coordinate_not_mem_of_inertia_moves_conjugateSheet
    D₀ hKeller V hGround g σ hσ hMoved
  exact ⟨g, σ, hσ, hMoved, i, hi⟩

end

end CollisionIdeals.Planar
