import CollisionIdeals.General.Galois.DecompositionSheets
import CollisionIdeals.General.Normalization.Polynomial
import CollisionIdeals.General.Galois.ValuationInertia
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Unramified.Locus

/-!
# Normalization diagrams for polynomial self-maps

This file packages the dimension-independent normalization triangle and
the pointwise realization of its conjugate Galois sheets.  It contains no
dimension-specific boundary-rigidity assertion.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

variable {k : Type u} [Field k]
variable {n : ℕ}
variable {F : PolynomialSelfMap k n}
variable {N : Type u} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

/--
The finite normal-closure model has no ramification at any height-one
prime.

This is the concrete local input consumed by branch purity.
-/
def PolynomialNoCodimensionOneRamification : Prop :=
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  ∀ q :
      PrimeSpectrum
        (PolynomialNormalizationInExtensionRing (F := F) (N := N)),
    q.asIdeal.primeHeight = 1 →
      Algebra.IsUnramifiedAt
        (PolynomialImageAlgebra F) q.asIdeal

/--
An actual height-one point of the normalization at which the local
extension is ramified.
-/
def PolynomialRamifiedCodimensionOnePoint :=
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  { q :
      PrimeSpectrum
        (PolynomialNormalizationInExtensionRing (F := F) (N := N)) //
      q.asIdeal.primeHeight = 1 ∧
        ¬ Algebra.IsUnramifiedAt
          (PolynomialImageAlgebra F) q.asIdeal }

/--
A discrete valuation tower is centered at `q` when its valuation ring
contains the normalization ring and its maximal ideal contracts to `q`.
-/
def PolynomialValuationCenteredAt
    (V : DiscreteValuationTower
      (PolynomialMapBaseFunctionField F) (N := N))
    (q :
      PrimeSpectrum
        (PolynomialNormalizationInExtensionRing
          (F := F) (N := N))) : Prop :=
  ∃ centerMap :
      PolynomialNormalizationInExtensionRing (F := F) (N := N) →+*
        V.valuationRing,
    (∀ x,
      ((centerMap x : V.valuationRing) : N) = (x : N)) ∧
      (IsLocalRing.maximalIdeal V.valuationRing).comap centerMap =
        q.asIdeal

/--
The finite normalization triangle together with the pointwise realization
of its conjugate sheets.

For every genuinely ramified height-one point `E` of `Z`, the diagram
records a centered divisorial valuation, its nontrivial inertia subgroup,
and compatible centers on the intermediate normalization indexed by
double-coset classes.
-/
structure PolynomialNormalizationDiagram where
  cover : PolynomialNormalizedCover (F := F) (N := N)
  valuationAt :
    PolynomialRamifiedCodimensionOnePoint (F := F) (N := N) →
      DiscreteValuationTower
        (PolynomialMapBaseFunctionField F) (N := N)
  valuation_centered :
    ∀ E, PolynomialValuationCenteredAt (valuationAt E) E.1
  inertia_nontrivial :
    ∀ E,
      inertiaGroupAt (PolynomialMapBaseFunctionField F)
        (valuationAt E).valuationRing ≠ ⊥
  centerAtClass :
    ∀ E,
      DecompositionSheetClasses
          (decompositionGroupAt (PolynomialMapBaseFunctionField F)
            (valuationAt E).valuationRing)
          cover.normalClosure.intermediateFixingSubgroup →
        polynomialIntermediateNormalization F
  centerAtClass_mapsToBase :
    ∀ E q,
      (polynomialIntermediateNormalizationToBase F).base
          (centerAtClass E q) =
        (polynomialNormalizationInExtensionToBase
          (F := F) (N := N)).base E.1
  baseClass_center :
    ∀ E,
      centerAtClass E
          (DoubleCoset.mk
            (decompositionGroupAt (PolynomialMapBaseFunctionField F)
              (valuationAt E).valuationRing)
            cover.normalClosure.intermediateFixingSubgroup
            1) =
        (polynomialNormalClosureModelToIntermediateNormalization
          cover.normalClosure).base E.1
  centerAtRepresentative :
    ∀ E g,
      centerAtClass E
          (DoubleCoset.mk
            (decompositionGroupAt (PolynomialMapBaseFunctionField F)
              (valuationAt E).valuationRing)
            cover.normalClosure.intermediateFixingSubgroup
            g) =
        (polynomialConjugateNormalClosureModelToIntermediateNormalization
          cover.normalClosure g).base E.1

namespace PolynomialNormalizationDiagram

variable
    (D : PolynomialNormalizationDiagram (F := F) (N := N))

/-- The normal-closure leg `Z ⟶ X̄` of the packaged diagram. -/
def toIntermediate :
    polynomialNormalizationInExtension (F := F) (N := N) ⟶
      polynomialIntermediateNormalization F :=
  polynomialNormalClosureModelToIntermediateNormalization
    D.cover.normalClosure

/-- The finite normalization leg `Z ⟶ Y` of the packaged diagram. -/
def toBase
    (_D : PolynomialNormalizationDiagram (F := F) (N := N)) :
    polynomialNormalizationInExtension (F := F) (N := N) ⟶
      Spec (.of (PolynomialImageAlgebra F)) :=
  polynomialNormalizationInExtensionToBase (F := F) (N := N)

/-- The packaged normalization triangle `Z ⟶ X̄ ⟶ Y` commutes. -/
theorem triangle :
    D.toIntermediate ≫ polynomialIntermediateNormalizationToBase F =
      D.toBase :=
  polynomialNormalClosureModelToIntermediateNormalization_comp_toBase
    D.cover.normalClosure

/-- The double-coset classes indexing conjugate centers above one point. -/
abbrev sheetClasses
    (E :
      PolynomialRamifiedCodimensionOnePoint (F := F) (N := N)) :=
  DecompositionSheetClasses
    (decompositionGroupAt (PolynomialMapBaseFunctionField F)
      (D.valuationAt E).valuationRing)
    D.cover.normalClosure.intermediateFixingSubgroup

/-- The relative inertia index of one conjugate center. -/
noncomputable def inertiaIndex
    (E :
      PolynomialRamifiedCodimensionOnePoint (F := F) (N := N)) :
    D.sheetClasses E → ℕ :=
  inertiaIndexAtDoubleCoset
    (decompositionGroupAt (PolynomialMapBaseFunctionField F)
      (D.valuationAt E).valuationRing)
    (inertiaWithinDecomposition (PolynomialMapBaseFunctionField F)
      (D.valuationAt E).valuationRing)
    D.cover.normalClosure.intermediateFixingSubgroup

/-- One conjugate center remains visible in the affine-space open sheet. -/
def ConjugateCenterVisible
    (E :
      PolynomialRamifiedCodimensionOnePoint (F := F) (N := N))
    (q : D.sheetClasses E) : Prop :=
  D.centerAtClass E q ∈
    Set.range (polynomialSourceToIntermediateNormalization F).base

/--
At one ramified divisor, every conjugate center with nontrivial relative
inertia lies in the deleted boundary.
-/
def RamifiedConjugateCentersInBoundaryAt
    (E :
      PolynomialRamifiedCodimensionOnePoint (F := F) (N := N)) :
    Prop :=
  ∀ q : D.sheetClasses E,
    D.inertiaIndex E q ≠ 1 →
      D.centerAtClass E q ∈
        polynomialIntermediateNormalizationBoundary F

/--
Every ramified divisor has all of its positive-index conjugate centers in
the deleted boundary.
-/
def RamifiedConjugateCentersInBoundary : Prop :=
  ∀ E, D.RamifiedConjugateCentersInBoundaryAt E

/--
There exists a ramified divisor whose entire positive-index conjugate orbit
is hidden in the deleted boundary.
-/
def HasHiddenInertiaOrbit : Prop :=
  ∃ E,
    (∃ q : D.sheetClasses E, 1 < D.inertiaIndex E q) ∧
      D.RamifiedConjugateCentersInBoundaryAt E

/--
The boundary cannot support a complete hidden-inertia orbit.

This generic negation is the interface for a later dimension-specific
boundary-rigidity theorem.
-/
def NoHiddenInertia : Prop :=
  ¬ D.HasHiddenInertiaOrbit

/--
The identity double-coset center is exactly the contraction along the
normalization leg `Z ⟶ X̄`.
-/
theorem centerAtBaseClass
    (E :
      PolynomialRamifiedCodimensionOnePoint (F := F) (N := N)) :
    D.centerAtClass E
        (DoubleCoset.mk
          (decompositionGroupAt (PolynomialMapBaseFunctionField F)
            (D.valuationAt E).valuationRing)
          D.cover.normalClosure.intermediateFixingSubgroup
          1) =
      D.toIntermediate.base E.1 :=
  D.baseClass_center E

/-- Every packaged conjugate center lies over the image of `E` in `Y`. -/
theorem conjugateCenter_mapsToBase
    (E :
      PolynomialRamifiedCodimensionOnePoint (F := F) (N := N))
    (q : D.sheetClasses E) :
    (polynomialIntermediateNormalizationToBase F).base
        (D.centerAtClass E q) =
      D.toBase.base E.1 :=
  D.centerAtClass_mapsToBase E q

/--
Nontrivial inertia moves at least one double-coset class, expressed as a
relative inertia index greater than one.
-/
theorem exists_one_lt_inertiaIndex
    [PerfectField (PolynomialMapBaseFunctionField F)]
    (E :
      PolynomialRamifiedCodimensionOnePoint (F := F) (N := N)) :
    ∃ q : D.sheetClasses E,
      1 < D.inertiaIndex E q := by
  let A := (D.valuationAt E).valuationRing
  letI : Finite D.cover.normalClosure.galoisGroup :=
    D.cover.normalClosure.finiteGaloisGroup
  have hWithin :
      inertiaWithinDecomposition
          (PolynomialMapBaseFunctionField F) A ≠ ⊥ := by
    intro hbot
    apply D.inertia_nontrivial E
    change
      (A.inertiaSubgroup
        (PolynomialMapBaseFunctionField F)).map
          (A.decompositionSubgroup
            (PolynomialMapBaseFunctionField F)).subtype = ⊥
    change
      A.inertiaSubgroup
        (PolynomialMapBaseFunctionField F) = ⊥ at hbot
    rw [hbot, Subgroup.map_bot]
  exact
    exists_doubleCoset_one_lt_inertiaIndex
      (decompositionGroupAt (PolynomialMapBaseFunctionField F) A)
      (inertiaWithinDecomposition (PolynomialMapBaseFunctionField F) A)
      D.cover.normalClosure.intermediateFixingSubgroup
      D.cover.normalClosure.intermediateFixingSubgroup_normalCore_eq_bot
      hWithin

/--
The boundary conclusion and the no-hidden-inertia assertion exclude every
ramified height-one point.
-/
theorem ramifiedCodimensionOnePoint_isEmpty
    [PerfectField (PolynomialMapBaseFunctionField F)]
    (hBoundary : D.RamifiedConjugateCentersInBoundary)
    (hNoHidden : D.NoHiddenInertia) :
    IsEmpty
      (PolynomialRamifiedCodimensionOnePoint
        (F := F) (N := N)) := by
  constructor
  intro E
  exact
    hNoHidden
      ⟨E, D.exists_one_lt_inertiaIndex E, hBoundary E⟩

/--
The exact local conclusion consumed later by branch purity: all
height-one points of the finite normalization are unramified.
-/
theorem noCodimensionOneRamification
    [PerfectField (PolynomialMapBaseFunctionField F)]
    (hBoundary : D.RamifiedConjugateCentersInBoundary)
    (hNoHidden : D.NoHiddenInertia) :
    PolynomialNoCodimensionOneRamification
      (F := F) (N := N) := by
  intro q hq
  by_contra hRamified
  let E :
      PolynomialRamifiedCodimensionOnePoint
        (F := F) (N := N) :=
    ⟨q, hq, hRamified⟩
  exact
    (D.ramifiedCodimensionOnePoint_isEmpty
      hBoundary hNoHidden).false E

end PolynomialNormalizationDiagram

end

end CollisionIdeals
