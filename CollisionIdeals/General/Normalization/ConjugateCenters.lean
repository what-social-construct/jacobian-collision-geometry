import CollisionIdeals.General.Normalization.Diagram

/-!
# Conjugate centers from a centered valuation

The contraction along `g ∘ ι` is constant on `D \ G / H`: the fixing
subgroup acts on the right, and the decomposition subgroup preserves the
maximal ideal of the centered valuation ring on the left. This constructs
the center data without assuming a normalization diagram or a geometric
ramification-index formula. No classification or bijectivity is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

variable {k : Type u} [Field k] {n : ℕ}
variable {F : PolynomialSelfMap k n}
variable {N : Type u} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

local instance conjugateCentersBaseAlgebra : Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

variable (D : PolynomialNormalClosureData F N)
variable (q : PrimeSpectrum
  (PolynomialNormalizationInExtensionRing (F := F) (N := N)))

/-- The center of the sheet `gH`: contraction of `g⁻¹q` to the marked
intermediate normalization, or equivalently contraction along `g ∘ ι`. -/
def polynomialConjugateCenter (g : D.galoisGroup) :
    polynomialIntermediateNormalization F :=
  (polynomialConjugateNormalClosureModelToIntermediateNormalization D g).base q

/-- Fixing the marked field on the right leaves its center unchanged. -/
theorem polynomialConjugateCenter_right_mul
    (g : D.galoisGroup) (h : D.intermediateFixingSubgroup) :
    polynomialConjugateCenter D q (g * (h : D.galoisGroup)) =
      polynomialConjugateCenter D q g := by
  unfold polynomialConjugateCenter
  rw [polynomialConjugateNormalClosureModelToIntermediateNormalization_right_mul]

variable (V : DiscreteValuationTower (PolynomialMapBaseFunctionField F) (N := N))
variable (hCentered : PolynomialValuationCenteredAt V q)

include hCentered

/-- A decomposition element preserves the center because it preserves the
valuation ring and hence its maximal ideal. Centeredness alone suffices;
no inertia or ramification-index input is used. -/
theorem polynomialConjugateCenter_left_mul
    (d : decompositionGroupAt (PolynomialMapBaseFunctionField F) V.valuationRing)
    (g : D.galoisGroup) :
    polynomialConjugateCenter D q ((d : D.galoisGroup) * g) =
      polynomialConjugateCenter D q g := by
  obtain ⟨centerMap, hcoe, hprime⟩ := hCentered
  apply PrimeSpectrum.ext
  ext x
  change polynomialConjugateNormalizationRingMap D ((d : D.galoisGroup) * g) x ∈
      q.asIdeal ↔ polynomialConjugateNormalizationRingMap D g x ∈ q.asIdeal
  rw [← hprime]
  change centerMap (polynomialConjugateNormalizationRingMap D
      ((d : D.galoisGroup) * g) x) ∈ IsLocalRing.maximalIdeal V.valuationRing ↔
    centerMap (polynomialConjugateNormalizationRingMap D g x) ∈
      IsLocalRing.maximalIdeal V.valuationRing
  have haction : centerMap (polynomialConjugateNormalizationRingMap D
      ((d : D.galoisGroup) * g) x) =
      d • centerMap (polynomialConjugateNormalizationRingMap D g x) := by
    apply Subtype.ext
    change ((centerMap (polynomialConjugateNormalizationRingMap D
        ((d : D.galoisGroup) * g) x) : V.valuationRing) : N) =
      (d : D.galoisGroup)
        ((centerMap (polynomialConjugateNormalizationRingMap D g x) :
          V.valuationRing) : N)
    rw [hcoe, hcoe]
    rfl
  rw [haction]
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact not_congr (MulEquiv.isUnit_map
    (MulSemiringAction.toRingAut
      (decompositionGroupAt (PolynomialMapBaseFunctionField F) V.valuationRing)
      V.valuationRing d))

/-- Centers descend to the double-coset classes using the centered valuation.
This is a construction of centers, not a classification of all primes. -/
def polynomialConjugateCenterAtClass :
    DecompositionSheetClasses
      (decompositionGroupAt (PolynomialMapBaseFunctionField F) V.valuationRing)
      D.intermediateFixingSubgroup → polynomialIntermediateNormalization F :=
  fun c => Quotient.liftOn c (polynomialConjugateCenter D q) (by
    intro a b hab
    change DoubleCoset.setoid
      (decompositionGroupAt (PolynomialMapBaseFunctionField F) V.valuationRing :
        Set D.galoisGroup)
      (D.intermediateFixingSubgroup : Set D.galoisGroup) a b at hab
    rw [DoubleCoset.rel_iff] at hab
    obtain ⟨d, hd, h, hh, rfl⟩ := hab
    exact ((polynomialConjugateCenter_right_mul D q (d * a) ⟨h, hh⟩).trans
      (polynomialConjugateCenter_left_mul D q V hCentered ⟨d, hd⟩ a)).symm)

/-- The descended center recovers the actual conjugate normalization map. -/
@[simp]
theorem polynomialConjugateCenterAtClass_mk (g : D.galoisGroup) :
    polynomialConjugateCenterAtClass D q V hCentered
        (DoubleCoset.mk
          (decompositionGroupAt (PolynomialMapBaseFunctionField F) V.valuationRing)
          D.intermediateFixingSubgroup g) =
      (polynomialConjugateNormalClosureModelToIntermediateNormalization D g).base q :=
  rfl

/-- Every descended center lies above the same point of the coordinate-image base. -/
theorem polynomialConjugateCenterAtClass_mapsToBase
    (c : DecompositionSheetClasses
      (decompositionGroupAt (PolynomialMapBaseFunctionField F) V.valuationRing)
      D.intermediateFixingSubgroup) :
    (polynomialIntermediateNormalizationToBase F).base
        (polynomialConjugateCenterAtClass D q V hCentered c) =
      (polynomialNormalizationInExtensionToBase (F := F) (N := N)).base q := by
  refine Quotient.inductionOn c ?_
  intro g
  change (polynomialConjugateNormalClosureModelToIntermediateNormalization D g ≫
      polynomialIntermediateNormalizationToBase F).base q = _
  rw [polynomialConjugateNormalClosureModelToIntermediateNormalization_comp_toBase]

/-- The identity double coset has the marked, unconjugated center. -/
theorem polynomialConjugateCenterAtClass_one :
    polynomialConjugateCenterAtClass D q V hCentered
        (DoubleCoset.mk
          (decompositionGroupAt (PolynomialMapBaseFunctionField F) V.valuationRing)
          D.intermediateFixingSubgroup 1) =
      (polynomialNormalClosureModelToIntermediateNormalization D).base q := by
  rw [polynomialConjugateCenterAtClass_mk]
  apply PrimeSpectrum.ext
  ext x
  rfl

end

end CollisionIdeals
