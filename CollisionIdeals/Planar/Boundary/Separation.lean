import CollisionIdeals.Planar.NormalizationDiagram
import CollisionIdeals.General.Normalization.VisibleRamification
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Finite-group boundary separation on the planar Galois normalization

This file gives an ideal-theoretic interface for the missing planar input.
All conjugate affine sheets are pulled back to the common normal-closure
ring.  For a nontrivial subgroup `C` of the Galois group, its fixed-locus
ideal is joined with the boundary ideals of exactly the sheets moved by
`C`.  Planar boundary separation says that the resulting ideal is contained
in no height-one prime.

The pulled-back boundary ideals are canonical.  A centered divisorial
valuation shows that a ramified height-one point contains both the
fixed-locus ideal of its actual inertia subgroup and its moving-boundary
ideal.  Boundary separation therefore rules out all divisorial
ramification and plugs into the existing planar endgame.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals.Planar

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Pointwise

variable {F : PlanarPolynomialMap}
variable {N : Type} [Field N]
variable [Algebra (PlanarBaseFunctionField F) N]

/-- The coordinate ring of the common Galois normalization `Z`. -/
abbrev GaloisNormalizationRing :=
  PolynomialNormalizationInExtensionRing (F := F) (N := N)

/-- The finite Galois group acting on the conjugate sheets. -/
abbrev NormalizationGaloisGroup
    (D : NormalizationDiagram (F := F) (N := N)) :=
  D.cover.normalClosure.galoisGroup

/-- The conjugate normalization leg attached to a Galois element. -/
def conjugateToIntermediate
    (D : NormalizationDiagram (F := F) (N := N))
    (g : NormalizationGaloisGroup D) :
    polynomialNormalizationInExtension (F := F) (N := N) ⟶
      polynomialIntermediateNormalization F :=
  polynomialConjugateNormalClosureModelToIntermediateNormalization
    D.cover.normalClosure g

/-- The conjugate normalization leg depends only on the right coset `gH`. -/
theorem conjugateToIntermediate_right_mul
    (D : NormalizationDiagram (F := F) (N := N))
    (g : NormalizationGaloisGroup D)
    (h : D.cover.normalClosure.intermediateFixingSubgroup) :
    conjugateToIntermediate D
        (g * (h : NormalizationGaloisGroup D)) =
      conjugateToIntermediate D g :=
  polynomialConjugateNormalClosureModelToIntermediateNormalization_right_mul
    D.cover.normalClosure g h

/--
The pullback to the common Galois normalization of the conjugate affine
polynomial sheet.
-/
def pulledBackConjugateAffineOpen
  (D : NormalizationDiagram (F := F) (N := N))
    (g : NormalizationGaloisGroup D) :
    Set (polynomialNormalizationInExtension (F := F) (N := N)) :=
  (conjugateToIntermediate D g).base ⁻¹'
    Set.range (polynomialSourceToIntermediateNormalization F).base

/-- The pulled-back affine sheet depends only on the right coset `gH`. -/
theorem pulledBackConjugateAffineOpen_right_mul
    (D : NormalizationDiagram (F := F) (N := N))
    (g : NormalizationGaloisGroup D)
    (h : D.cover.normalClosure.intermediateFixingSubgroup) :
    pulledBackConjugateAffineOpen D
        (g * (h : NormalizationGaloisGroup D)) =
      pulledBackConjugateAffineOpen D g := by
  unfold pulledBackConjugateAffineOpen
  rw [conjugateToIntermediate_right_mul D g h]

/-- The closed complement of a pulled-back conjugate affine sheet. -/
def pulledBackConjugateBoundary
    (D : NormalizationDiagram (F := F) (N := N))
    (g : NormalizationGaloisGroup D) :
    Set (PrimeSpectrum (GaloisNormalizationRing (F := F) (N := N))) :=
  (pulledBackConjugateAffineOpen D g)ᶜ

/-- The pulled-back boundary depends only on the right coset `gH`. -/
theorem pulledBackConjugateBoundary_right_mul
    (D : NormalizationDiagram (F := F) (N := N))
    (g : NormalizationGaloisGroup D)
    (h : D.cover.normalClosure.intermediateFixingSubgroup) :
    pulledBackConjugateBoundary D
        (g * (h : NormalizationGaloisGroup D)) =
      pulledBackConjugateBoundary D g := by
  unfold pulledBackConjugateBoundary
  rw [pulledBackConjugateAffineOpen_right_mul D g h]

/--
The radical ideal cutting out the pulled-back boundary of the conjugate
sheet represented by a Galois element.
-/
def pulledBackConjugateBoundaryIdeal
    (D : NormalizationDiagram (F := F) (N := N))
    (g : NormalizationGaloisGroup D) :
    Ideal (GaloisNormalizationRing (F := F) (N := N)) :=
  PrimeSpectrum.vanishingIdeal (pulledBackConjugateBoundary D g)

/-- The canonical boundary ideal is indexed by the conjugate sheet `gH`. -/
theorem pulledBackConjugateBoundaryIdeal_right_mul
    (D : NormalizationDiagram (F := F) (N := N))
    (g : NormalizationGaloisGroup D)
    (h : D.cover.normalClosure.intermediateFixingSubgroup) :
    pulledBackConjugateBoundaryIdeal D
        (g * (h : NormalizationGaloisGroup D)) =
      pulledBackConjugateBoundaryIdeal D g := by
  unfold pulledBackConjugateBoundaryIdeal
  rw [pulledBackConjugateBoundary_right_mul D g h]

/-- The pulled-back conjugate boundary is closed. -/
theorem pulledBackConjugateBoundary_isClosed
    (D : NormalizationDiagram (F := F) (N := N))
    (g : NormalizationGaloisGroup D) :
    IsClosed (pulledBackConjugateBoundary D g) := by
  letI : IsOpenImmersion
      (polynomialSourceToIntermediateNormalization F) :=
    D.cover.intermediateOpen
  apply IsOpen.isClosed_compl
  exact
    (IsOpenImmersion.isOpen_range
      (polynomialSourceToIntermediateNormalization F)).preimage
      (conjugateToIntermediate D g).base.hom.continuous_toFun

/-- The boundary ideal cuts out exactly the pulled-back closed complement. -/
theorem zeroLocus_pulledBackConjugateBoundaryIdeal
    (D : NormalizationDiagram (F := F) (N := N))
    (g : NormalizationGaloisGroup D) :
    PrimeSpectrum.zeroLocus (pulledBackConjugateBoundaryIdeal D g) =
      pulledBackConjugateBoundary D g := by
  rw [pulledBackConjugateBoundaryIdeal,
    PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    (pulledBackConjugateBoundary_isClosed D g).closure_eq]

/-- A point is in the pulled-back boundary exactly when its conjugate center is. -/
theorem mem_pulledBackConjugateBoundary_iff
    (D : NormalizationDiagram (F := F) (N := N))
    (g : NormalizationGaloisGroup D)
    (p : PrimeSpectrum (GaloisNormalizationRing (F := F) (N := N))) :
    p ∈ pulledBackConjugateBoundary D g ↔
      (conjugateToIntermediate D g).base p ∈
        polynomialIntermediateNormalizationBoundary F :=
  Iff.rfl

/-- Membership in the pulled-back boundary gives ideal containment. -/
theorem pulledBackConjugateBoundaryIdeal_le
    (D : NormalizationDiagram (F := F) (N := N))
    (g : NormalizationGaloisGroup D)
    (p : PrimeSpectrum (GaloisNormalizationRing (F := F) (N := N)))
    (hp : p ∈ pulledBackConjugateBoundary D g) :
    pulledBackConjugateBoundaryIdeal D g ≤ p.asIdeal := by
  intro t ht
  exact
    (PrimeSpectrum.mem_vanishingIdeal
      (pulledBackConjugateBoundary D g) t).mp ht p hp

/--
A Galois automorphism over the base function field, regarded as an
automorphism over the polynomial image algebra.
-/
noncomputable def galoisEquivOverImage
    (σ : N ≃ₐ[PlanarBaseFunctionField F] N) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    N ≃ₐ[PolynomialImageAlgebra F] N := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  exact
    { σ.toRingEquiv with
      commutes' := fun b => by
        change
          σ (algebraMap (PlanarBaseFunctionField F) N
            (algebraMap (PolynomialImageAlgebra F)
              (PlanarBaseFunctionField F) b)) =
            algebraMap (PlanarBaseFunctionField F) N
              (algebraMap (PolynomialImageAlgebra F)
                (PlanarBaseFunctionField F) b)
        exact σ.commutes _ }

/-- The induced automorphism of the common Galois-normalization ring. -/
noncomputable def galoisNormalizationEquiv
    (σ : N ≃ₐ[PlanarBaseFunctionField F] N) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    GaloisNormalizationRing (F := F) (N := N) ≃ₐ[PolynomialImageAlgebra F]
      GaloisNormalizationRing (F := F) (N := N) := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  exact (galoisEquivOverImage (F := F) (N := N) σ).mapIntegralClosure

/--
Every element of the actual divisorial inertia group acts trivially modulo
the center prime on the common normalization ring.
-/
theorem inertia_sub_mem_ramifiedPrime
    (D : NormalizationDiagram (F := F) (N := N))
    (E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N))
    (σ : inertiaGroupAt (PlanarBaseFunctionField F)
      (D.valuationAt E).valuationRing)
    (t : GaloisNormalizationRing (F := F) (N := N)) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    galoisNormalizationEquiv (F := F) (N := N) σ.1 t - t ∈
      E.1.asIdeal := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  let V := (D.valuationAt E).valuationRing
  rcases D.valuation_centered E with ⟨centerMap, hcenter, hcomap⟩
  rw [← hcomap]
  change centerMap
      (galoisNormalizationEquiv (F := F) (N := N) σ.1 t - t) ∈
    IsLocalRing.maximalIdeal V
  rw [map_sub centerMap]
  rcases σ.2 with ⟨τ0, hτ0, hmap⟩
  let τ : V.inertiaSubgroup (PlanarBaseFunctionField F) := ⟨τ0, hτ0⟩
  have hτ : τ.1.1 = σ.1 := hmap
  have hinertia :
      τ.1 • centerMap t - centerMap t ∈
        IsLocalRing.maximalIdeal V := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub]
    have hker :
        MulSemiringAction.toRingAut
            (V.decompositionSubgroup (PlanarBaseFunctionField F))
            (IsLocalRing.ResidueField V) τ.1 = 1 :=
      τ.2
    rw [IsLocalRing.ResidueField.residue_smul]
    change
      (MulSemiringAction.toRingAut
          (V.decompositionSubgroup (PlanarBaseFunctionField F))
          (IsLocalRing.ResidueField V) τ.1)
            (IsLocalRing.residue V (centerMap t)) -
          IsLocalRing.residue V (centerMap t) = 0
    rw [hker]
    exact sub_self _
  have haction :
      centerMap (galoisNormalizationEquiv (F := F) (N := N) σ.1 t) =
        τ.1 • centerMap t := by
    apply Subtype.ext
    rw [hcenter]
    change σ.1 (t : N) = _
    rw [← hτ]
    change τ.1.1 (t : N) = τ.1.1 ((centerMap t : V) : N)
    rw [hcenter]
  rw [haction]
  exact hinertia

/--
The scheme-theoretic fixed-locus ideal
`(σ(t) - t | σ ∈ C, t ∈ T)` on the common normalization ring `T`.
-/
noncomputable def fixedLocusIdeal
    {D : NormalizationDiagram (F := F) (N := N)}
    (C : Subgroup (NormalizationGaloisGroup D)) :
    Ideal (GaloisNormalizationRing (F := F) (N := N)) := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  exact Ideal.span
    {z | ∃ (σ : C) (t : GaloisNormalizationRing (F := F) (N := N)),
      z = galoisNormalizationEquiv (F := F) (N := N) σ.1 t - t}

/-- Containment of the fixed-locus ideal is checked on its differences. -/
theorem fixedLocusIdeal_le_iff
    {D : NormalizationDiagram (F := F) (N := N)}
    (C : Subgroup (NormalizationGaloisGroup D))
    (I : Ideal (GaloisNormalizationRing (F := F) (N := N))) :
    fixedLocusIdeal C ≤ I ↔
      ∀ (σ : C) (t : GaloisNormalizationRing (F := F) (N := N)),
        galoisNormalizationEquiv (F := F) (N := N) σ.1 t - t ∈ I := by
  rw [fixedLocusIdeal, Ideal.span_le]
  constructor
  · intro h σ t
    exact h ⟨σ, t, rfl⟩
  · rintro h z ⟨σ, t, rfl⟩
    exact h σ t

/--
The sum of the pulled-back boundary ideals over all sheets moved by `C`.
The condition `C ≤ gHg⁻¹` is exactly the condition that `C` fixes the
sheet represented by `gH`.
-/
def movingBoundaryIdeal
    {D : NormalizationDiagram (F := F) (N := N)}
    (boundaryIdeal : NormalizationGaloisGroup D →
      Ideal (GaloisNormalizationRing (F := F) (N := N)))
    (C : Subgroup (NormalizationGaloisGroup D)) :
    Ideal (GaloisNormalizationRing (F := F) (N := N)) :=
  ⨆ (g : NormalizationGaloisGroup D)
      (_ : ¬ C ≤ D.cover.normalClosure.intermediateFixingSubgroup.map
        (MulAut.conj g).toMonoidHom),
    boundaryIdeal g

/--
The canonical ideal cutting out the intersection of the `C`-fixed locus
with the boundaries of every conjugate affine sheet moved by `C`.
-/
def fixedMovingBoundaryIdeal
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) :
    Ideal (GaloisNormalizationRing (F := F) (N := N)) :=
  fixedLocusIdeal C +
    movingBoundaryIdeal (pulledBackConjugateBoundaryIdeal D) C

/-- Membership in the moving-boundary sum is tested sheet by sheet. -/
theorem movingBoundaryIdeal_le_iff
    {D : NormalizationDiagram (F := F) (N := N)}
    (boundaryIdeal : NormalizationGaloisGroup D →
      Ideal (GaloisNormalizationRing (F := F) (N := N)))
    (C : Subgroup (NormalizationGaloisGroup D))
    (I : Ideal (GaloisNormalizationRing (F := F) (N := N))) :
    movingBoundaryIdeal boundaryIdeal C ≤ I ↔
      ∀ g, ¬ C ≤ D.cover.normalClosure.intermediateFixingSubgroup.map
          (MulAut.conj g).toMonoidHom →
        boundaryIdeal g ≤ I := by
  simp [movingBoundaryIdeal]

/-- Containment of the fixed--moving ideal is containment of both parts. -/
@[simp]
theorem fixedMovingBoundaryIdeal_le_iff
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D))
    (I : Ideal (GaloisNormalizationRing (F := F) (N := N))) :
    fixedMovingBoundaryIdeal D C ≤ I ↔
      fixedLocusIdeal C ≤ I ∧
        movingBoundaryIdeal (pulledBackConjugateBoundaryIdeal D) C ≤ I := by
  simp [fixedMovingBoundaryIdeal]

/-- Fixed-locus ideals grow with the acting subgroup. -/
theorem fixedLocusIdeal_mono
    {D : NormalizationDiagram (F := F) (N := N)}
    {C C' : Subgroup (NormalizationGaloisGroup D)}
    (h : C ≤ C') :
    fixedLocusIdeal C ≤ fixedLocusIdeal C' := by
  rw [fixedLocusIdeal_le_iff]
  intro σ t
  apply Ideal.subset_span
  exact ⟨⟨σ.1, h σ.2⟩, t, rfl⟩

/--
The moving-boundary zero locus is the intersection of the boundaries of all
conjugate sheets moved by `C`.
-/
theorem zeroLocus_movingBoundaryIdeal
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) :
    PrimeSpectrum.zeroLocus
        (R := GaloisNormalizationRing (F := F) (N := N))
        (movingBoundaryIdeal (pulledBackConjugateBoundaryIdeal D) C) =
      ⋂ (g : NormalizationGaloisGroup D),
        ⋂ (_ : ¬ C ≤ D.cover.normalClosure.intermediateFixingSubgroup.map
          (MulAut.conj g).toMonoidHom),
          pulledBackConjugateBoundary D g := by
  simp [movingBoundaryIdeal, PrimeSpectrum.zeroLocus_iSup,
    zeroLocus_pulledBackConjugateBoundaryIdeal]

/-- The fixed--moving ideal cuts out the exact common boundary fixed locus. -/
theorem zeroLocus_fixedMovingBoundaryIdeal
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) :
    PrimeSpectrum.zeroLocus
        (R := GaloisNormalizationRing (F := F) (N := N))
        (fixedMovingBoundaryIdeal D C) =
      PrimeSpectrum.zeroLocus
          (R := GaloisNormalizationRing (F := F) (N := N))
          (fixedLocusIdeal (D := D) C) ∩
        ⋂ (g : NormalizationGaloisGroup D),
          ⋂ (_ : ¬ C ≤ D.cover.normalClosure.intermediateFixingSubgroup.map
            (MulAut.conj g).toMonoidHom),
            pulledBackConjugateBoundary D g := by
  rw [show PrimeSpectrum.zeroLocus
        (R := GaloisNormalizationRing (F := F) (N := N))
        (fixedMovingBoundaryIdeal D C) =
      PrimeSpectrum.zeroLocus
          (R := GaloisNormalizationRing (F := F) (N := N))
          (fixedLocusIdeal (D := D) C : Ideal _) ∩
      PrimeSpectrum.zeroLocus
          (R := GaloisNormalizationRing (F := F) (N := N))
          (movingBoundaryIdeal
            (pulledBackConjugateBoundaryIdeal D) C : Ideal _) by
        simp [fixedMovingBoundaryIdeal, PrimeSpectrum.zeroLocus_sup],
    zeroLocus_movingBoundaryIdeal]

/--
The height-one-prime form of planar boundary separation.  It says directly
that no nontrivial fixed--moving boundary ideal is contained in a
height-one prime.  This is the formal codimension-one condition consumed by
purity; the ideal itself is defined without any height restriction.
-/
def PlanarBoundarySeparation
    (D : NormalizationDiagram (F := F) (N := N)) : Prop :=
  ∀ (C : Subgroup (NormalizationGaloisGroup D)),
    C ≠ ⊥ →
      ∀ p : PrimeSpectrum (GaloisNormalizationRing (F := F) (N := N)),
        p.asIdeal.primeHeight = 1 →
          ¬ fixedMovingBoundaryIdeal D C ≤ p.asIdeal

/--
The pulled-back-open form of moving-sheet coverage: every ramified
height-one point remains in at least one conjugate affine sheet moved by
its full divisorial inertia subgroup.
-/
def PlanarMovingSheetCoverage
    (D : NormalizationDiagram (F := F) (N := N)) : Prop :=
  ∀ E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N),
    ∃ g : NormalizationGaloisGroup D,
      ¬ inertiaGroupAt (PlanarBaseFunctionField F)
          (D.valuationAt E).valuationRing ≤
          D.cover.normalClosure.intermediateFixingSubgroup.map
            (MulAut.conj g).toMonoidHom ∧
        E.1 ∈ pulledBackConjugateAffineOpen D g

/--
The pulled-back-open statement is the representative-level form of the
existing double-coset coverage predicate.
-/
theorem planarMovingSheetCoverage_iff_conjugateCoverage
    (D : NormalizationDiagram (F := F) (N := N)) :
    PlanarMovingSheetCoverage D ↔ PlanarConjugateCoverage D := by
  letI : Finite (NormalizationGaloisGroup D) :=
    D.cover.normalClosure.finiteGaloisGroup
  constructor
  · intro hCoverage E
    obtain ⟨g, hgMoved, hgOpen⟩ := hCoverage E
    refine
      ⟨DoubleCoset.mk
          (decompositionGroupAt (PlanarBaseFunctionField F)
            (D.valuationAt E).valuationRing)
          D.cover.normalClosure.intermediateFixingSubgroup g,
        ?_, ?_⟩
    · exact
        one_lt_inertiaQuotientIndex _ _ hgMoved
    · unfold PolynomialNormalizationDiagram.ConjugateCenterVisible
      rw [D.centerAtRepresentative E g]
      exact hgOpen
  · intro hCoverage E
    obtain ⟨q, hqIndex, hqVisible⟩ := hCoverage E
    let g : NormalizationGaloisGroup D := q.out
    have hq :
        DoubleCoset.mk
            (decompositionGroupAt (PlanarBaseFunctionField F)
              (D.valuationAt E).valuationRing)
            D.cover.normalClosure.intermediateFixingSubgroup g = q :=
      DoubleCoset.out_eq' _ _ q
    refine ⟨g, ?_, ?_⟩
    · intro hgFixed
      have hIndexOne :
          D.inertiaIndex E
              (DoubleCoset.mk
                (decompositionGroupAt (PlanarBaseFunctionField F)
                  (D.valuationAt E).valuationRing)
                D.cover.normalClosure.intermediateFixingSubgroup g) = 1 :=
        (inertiaQuotientIndex_eq_one_iff _ _).mpr hgFixed
      exact (Nat.ne_of_gt (hq ▸ hqIndex)) hIndexOne
    · change
        (conjugateToIntermediate D g).base E.1 ∈
          Set.range (polynomialSourceToIntermediateNormalization F).base
      change
        (polynomialConjugateNormalClosureModelToIntermediateNormalization
          D.cover.normalClosure g).base E.1 ∈
          Set.range (polynomialSourceToIntermediateNormalization F).base
      rw [← D.centerAtRepresentative E g, hq]
      exact hqVisible

/-- A point lies in the conjugate affine open exactly when its boundary ideal is not contained. -/
theorem mem_pulledBackConjugateAffineOpen_iff
    (D : NormalizationDiagram (F := F) (N := N))
    (g : NormalizationGaloisGroup D)
    (p : PrimeSpectrum (GaloisNormalizationRing (F := F) (N := N))) :
    p ∈ pulledBackConjugateAffineOpen D g ↔
      ¬ pulledBackConjugateBoundaryIdeal D g ≤ p.asIdeal := by
  rw [← Set.notMem_compl_iff]
  change
    p ∉ pulledBackConjugateBoundary D g ↔
      ¬ pulledBackConjugateBoundaryIdeal D g ≤ p.asIdeal
  rw [← zeroLocus_pulledBackConjugateBoundaryIdeal D g]
  rfl

/--
Moving-sheet coverage at a ramified point is precisely failure of the
moving-boundary ideal to lie in its height-one prime.
-/
theorem planarMovingSheetCoverage_iff
    (D : NormalizationDiagram (F := F) (N := N)) :
    PlanarMovingSheetCoverage D ↔
      ∀ E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N),
        ¬ movingBoundaryIdeal (pulledBackConjugateBoundaryIdeal D)
            (inertiaGroupAt (PlanarBaseFunctionField F)
              (D.valuationAt E).valuationRing) ≤ E.1.asIdeal := by
  constructor
  · intro hCoverage E hMoving
    obtain ⟨g, hgMoved, hgOpen⟩ := hCoverage E
    have hgBoundary :
        pulledBackConjugateBoundaryIdeal D g ≤ E.1.asIdeal :=
      (movingBoundaryIdeal_le_iff
        (pulledBackConjugateBoundaryIdeal D)
        (inertiaGroupAt (PlanarBaseFunctionField F)
          (D.valuationAt E).valuationRing) E.1.asIdeal).mp hMoving g hgMoved
    exact
      (mem_pulledBackConjugateAffineOpen_iff D g E.1).mp hgOpen
        hgBoundary
  · intro h E
    by_contra hNoWitness
    push_neg at hNoWitness
    apply h E
    rw [movingBoundaryIdeal_le_iff]
    intro g hgMoved
    by_contra hgBoundary
    exact
      (hNoWitness g hgMoved)
        ((mem_pulledBackConjugateAffineOpen_iff D g E.1).mpr
          hgBoundary)

/--
A conjugate center with nontrivial relative inertia lies in the
corresponding pulled-back boundary on the common normalization.
-/
theorem ramifiedPoint_mem_pulledBackConjugateBoundary
    {D : NormalizationDiagram (F := F) (N := N)}
    (R : D.ConjugateRamificationRealization)
    (hEtale : AlgebraicGeometry.Etale (polynomialSourceToImageBase F))
    (E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N))
    (g : NormalizationGaloisGroup D)
    (hIndex :
      D.inertiaIndex E
        (DoubleCoset.mk
          (decompositionGroupAt (PlanarBaseFunctionField F)
            (D.valuationAt E).valuationRing)
          D.cover.normalClosure.intermediateFixingSubgroup
          g) ≠ 1) :
    E.1 ∈ pulledBackConjugateBoundary D g := by
  rw [mem_pulledBackConjugateBoundary_iff]
  change
    (polynomialConjugateNormalClosureModelToIntermediateNormalization
      D.cover.normalClosure g).base E.1 ∈
        polynomialIntermediateNormalizationBoundary F
  rw [← D.centerAtRepresentative E g]
  exact
    D.ramifiedCenter_mem_boundary R hEtale E
      (DoubleCoset.mk
        (decompositionGroupAt (PlanarBaseFunctionField F)
          (D.valuationAt E).valuationRing)
        D.cover.normalClosure.intermediateFixingSubgroup
        g)
      hIndex

/--
Valuation-theoretic boundary membership yields containment of the
canonically constructed pulled-back boundary ideal.
-/
theorem pulledBackConjugateBoundaryIdeal_le_ramifiedPrime
    {D : NormalizationDiagram (F := F) (N := N)}
    (R : D.ConjugateRamificationRealization)
    (hEtale : AlgebraicGeometry.Etale (polynomialSourceToImageBase F))
    (E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N))
    (g : NormalizationGaloisGroup D)
    (hIndex :
      D.inertiaIndex E
        (DoubleCoset.mk
          (decompositionGroupAt (PlanarBaseFunctionField F)
            (D.valuationAt E).valuationRing)
          D.cover.normalClosure.intermediateFixingSubgroup
          g) ≠ 1) :
    pulledBackConjugateBoundaryIdeal D g ≤ E.1.asIdeal :=
  pulledBackConjugateBoundaryIdeal_le D g E.1
    (ramifiedPoint_mem_pulledBackConjugateBoundary
      R hEtale E g hIndex)

/--
Every boundary ideal for a sheet moved by a subgroup of the actual inertia
group is contained in the ramified height-one prime.
-/
theorem movingBoundaryIdeal_le_ramifiedPrime
    {D : NormalizationDiagram (F := F) (N := N)}
    (R : D.ConjugateRamificationRealization)
    (hEtale : AlgebraicGeometry.Etale (polynomialSourceToImageBase F))
    (E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D))
    (hC :
      C ≤ inertiaGroupAt (PlanarBaseFunctionField F)
        (D.valuationAt E).valuationRing) :
    movingBoundaryIdeal (pulledBackConjugateBoundaryIdeal D) C ≤
      E.1.asIdeal := by
  rw [movingBoundaryIdeal_le_iff]
  intro g hg
  apply pulledBackConjugateBoundaryIdeal_le_ramifiedPrime R hEtale E g
  change
    inertiaQuotientIndex
      (inertiaGroupAt (PlanarBaseFunctionField F)
        (D.valuationAt E).valuationRing)
      (D.cover.normalClosure.intermediateFixingSubgroup.map
        (MulAut.conj g).toMonoidHom) ≠ 1
  exact
    inertiaQuotientIndex_ne_one _ _
      (fun hInertia => hg (hC.trans hInertia))

/-- Inertia fixes the residue field, hence its fixed-locus ideal lies in the center prime. -/
theorem actualInertiaFixedLocusIdeal_le_ramifiedPrime
    (D : NormalizationDiagram (F := F) (N := N))
    (E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N)) :
    fixedLocusIdeal (D := D)
        (inertiaGroupAt (PlanarBaseFunctionField F)
          (D.valuationAt E).valuationRing) ≤ E.1.asIdeal := by
  rw [fixedLocusIdeal_le_iff]
  intro σ t
  exact inertia_sub_mem_ramifiedPrime D E σ t

/--
The geometric data needed to apply the canonical boundary construction to
one planar normalization diagram.  The diagram supplies conjugate centers
and centered divisorial valuations; these fields identify those centers
valuation-theoretically, while the source map is recorded as étale over
the base.
-/
structure BoundaryIdealData
    (D : NormalizationDiagram (F := F) (N := N)) where
  ramificationRealization : D.ConjugateRamificationRealization
  sourceEtale : AlgebraicGeometry.Etale (polynomialSourceToImageBase F)

namespace BoundaryIdealData

variable {D : NormalizationDiagram (F := F) (N := N)}

/-- Every boundary moved by the full divisorial inertia group lies in its center prime. -/
theorem actualInertiaMovingBoundaryIdeal_le
    (B : BoundaryIdealData D)
    (E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N)) :
    Planar.movingBoundaryIdeal (pulledBackConjugateBoundaryIdeal D)
        (inertiaGroupAt (PlanarBaseFunctionField F)
          (D.valuationAt E).valuationRing) ≤ E.1.asIdeal :=
  movingBoundaryIdeal_le_ramifiedPrime
    B.ramificationRealization B.sourceEtale E
    (inertiaGroupAt (PlanarBaseFunctionField F)
      (D.valuationAt E).valuationRing)
    le_rfl

/--
If `C` lies in the inertia group at a ramified divisor, its complete
fixed--moving boundary ideal lies in the corresponding center prime.
-/
theorem fixedMovingBoundaryIdeal_le_ramifiedPrime
    (B : BoundaryIdealData D)
    (E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D))
    (hC : C ≤ inertiaGroupAt (PlanarBaseFunctionField F)
      (D.valuationAt E).valuationRing) :
    fixedMovingBoundaryIdeal D C ≤ E.1.asIdeal := by
  rw [fixedMovingBoundaryIdeal_le_iff]
  exact ⟨
    (fixedLocusIdeal_mono hC).trans
      (actualInertiaFixedLocusIdeal_le_ramifiedPrime D E),
    movingBoundaryIdeal_le_ramifiedPrime
      B.ramificationRealization B.sourceEtale E C hC⟩

/-- The fixed--moving ideal for the actual inertia lies at its center. -/
theorem actualInertiaFixedMovingBoundaryIdeal_le
    (B : BoundaryIdealData D)
    (E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N)) :
    fixedMovingBoundaryIdeal D
      (inertiaGroupAt (PlanarBaseFunctionField F)
        (D.valuationAt E).valuationRing) ≤ E.1.asIdeal :=
  B.fixedMovingBoundaryIdeal_le_ramifiedPrime E _ le_rfl

/-- Boundary separation excludes every ramified height-one point. -/
theorem ramifiedCodimensionOnePoint_isEmpty
    (B : BoundaryIdealData D)
    (hSeparation : PlanarBoundarySeparation D) :
    IsEmpty (PolynomialRamifiedCodimensionOnePoint (F := F) (N := N)) := by
  constructor
  intro E
  exact hSeparation
    (inertiaGroupAt (PlanarBaseFunctionField F)
      (D.valuationAt E).valuationRing)
    (D.inertia_nontrivial E) E.1 E.2.1
    (B.actualInertiaFixedMovingBoundaryIdeal_le E)

/-- The exact moving-sheet coverage condition excludes every ramified divisor. -/
theorem ramifiedCodimensionOnePoint_isEmpty_of_movingSheetCoverage
    (B : BoundaryIdealData D)
    (hCoverage : PlanarMovingSheetCoverage D) :
    IsEmpty (PolynomialRamifiedCodimensionOnePoint (F := F) (N := N)) := by
  constructor
  intro E
  exact
    ((planarMovingSheetCoverage_iff D).mp hCoverage E)
      (B.actualInertiaMovingBoundaryIdeal_le E)

/-- Boundary separation implies the existing no-hidden-inertia interface. -/
theorem noHiddenInertia
    (B : BoundaryIdealData D)
    (hSeparation : PlanarBoundarySeparation D) :
    PlanarNoHiddenInertia D := by
  intro hHidden
  obtain ⟨E, _, _⟩ := hHidden
  exact (B.ramifiedCodimensionOnePoint_isEmpty hSeparation).false E

/-- Moving-sheet coverage implies the existing no-hidden-inertia interface. -/
theorem noHiddenInertia_of_movingSheetCoverage
    (B : BoundaryIdealData D)
    (hCoverage : PlanarMovingSheetCoverage D) :
    PlanarNoHiddenInertia D := by
  intro hHidden
  obtain ⟨E, _, _⟩ := hHidden
  exact
    (B.ramifiedCodimensionOnePoint_isEmpty_of_movingSheetCoverage
      hCoverage).false E

/-- The exact codimension-one unramifiedness input consumed by purity. -/
theorem noCodimensionOneRamification
    (B : BoundaryIdealData D)
    (hSeparation : PlanarBoundarySeparation D) :
    NoCodimensionOneRamification (F := F) (N := N) := by
  intro p hp
  by_contra hRamified
  exact
    (B.ramifiedCodimensionOnePoint_isEmpty hSeparation).false
      ⟨p, hp, hRamified⟩

/-- Moving-sheet coverage supplies the codimension-one input consumed by purity. -/
theorem noCodimensionOneRamification_of_movingSheetCoverage
    (B : BoundaryIdealData D)
    (hCoverage : PlanarMovingSheetCoverage D) :
    NoCodimensionOneRamification (F := F) (N := N) := by
  intro p hp
  by_contra hRamified
  exact
    (B.ramifiedCodimensionOnePoint_isEmpty_of_movingSheetCoverage
      hCoverage).false ⟨p, hp, hRamified⟩

end BoundaryIdealData

end

end CollisionIdeals.Planar
