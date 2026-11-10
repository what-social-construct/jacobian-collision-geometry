import CollisionIdeals.Planar.Research.Vanishing.ConjugateNormalizationOpen
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Connected.Clopen

/-!
# The all-conjugate open is the normalization over the invariant open

The existing open immersion into the finite normalization and the finite
map to the existing invariant target open form a Cartesian square. The
comparison is derived from those constructed maps; it does not assert
that the invariant target open is the whole target or bound an orbit at
the omitted boundary.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 20000

namespace CollisionIdeals.Planar.Research

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

private theorem isIso_lift_of_open_of_finite
    {W Z U Y : Scheme.{u}}
    (i : W ⟶ Z) (r : W ⟶ U) (p : Z ⟶ Y) (j : U ⟶ Y)
    (h : i ≫ p = r ≫ j)
    [IsOpenImmersion i] [IsOpenImmersion j] [IsFinite r]
    [IsSeparated p] [IsIntegral Z] [Nonempty W] :
    IsIso (pullback.lift i r h) := by
  let P : Scheme.{u} := pullback p j
  let s : W ⟶ P := pullback.lift i r h
  have hfst : s ≫ pullback.fst p j = i := pullback.lift_fst i r h
  have hsnd : s ≫ pullback.snd p j = r := pullback.lift_snd i r h
  letI : IsOpenImmersion (s ≫ pullback.fst p j) := hfst.symm ▸ inferInstance
  letI : IsOpenImmersion s := IsOpenImmersion.of_comp s (pullback.fst p j)
  letI : IsFinite (s ≫ pullback.snd p j) := hsnd.symm ▸ inferInstance
  letI : IsFinite s := IsFinite.of_comp s (pullback.snd p j)
  letI : Nonempty P := by
    obtain ⟨w⟩ := ‹Nonempty W›
    exact ⟨s w⟩
  letI : IsIntegral P :=
    isIntegral_of_isOpenImmersion (pullback.fst p j)
  have hOpen : IsOpen (Set.range s) := s.isOpenEmbedding.isOpen_range
  have hClosed : IsClosed (Set.range s) := s.isClosedMap.isClosed_range
  have hRange : Set.range s = Set.univ :=
    (show IsClopen (Set.range s) from ⟨hClosed, hOpen⟩).eq_univ
      (Set.range_nonempty s)
  letI : Surjective s := ⟨Set.range_eq_univ.mp hRange⟩
  exact (isIso_iff_isOpenImmersion_and_surjective s).mpr ⟨inferInstance, inferInstance⟩

variable {F : PlanarPolynomialMap} {N : Type} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

@[reducible] local instance invariantNormalizationBaseAlgebra :
    Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

@[reducible] local instance invariantNormalizationRing :
    CommRing (PolynomialNormalizationInExtensionRing (F := F) (N := N)) :=
  Subalgebra.toCommRing (integralClosure (PolynomialImageAlgebra F) N)

@[reducible] local instance invariantNormalizationConjugateAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateAlgebra D)

@[reducible] local instance invariantNormalizationInvariantAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateInvariantAlgebra D)

@[reducible] local instance invariantNormalizationOverInvariantAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (polynomialConjugateInvariantAlgebra D) (polynomialConjugateAlgebra D) :=
  Subalgebra.toAlgebra (polynomialConjugateInvariantAlgebra D)

local instance invariantNormalizationOverInvariantSMul
    (D : PolynomialNormalClosureData F N) :
    SMul (polynomialConjugateInvariantAlgebra D) (polynomialConjugateAlgebra D) :=
  Algebra.toSMul

local instance invariantNormalizationOverInvariantModule
    (D : PolynomialNormalClosureData F N) :
    Module (polynomialConjugateInvariantAlgebra D) (polynomialConjugateAlgebra D) :=
  (polynomialConjugateInvariantAlgebra D).moduleLeft

private def invariantTargetMap (D : PolynomialNormalClosureData F N) :
    Spec (.of (polynomialConjugateAlgebra D)) ⟶
      Spec (.of (polynomialConjugateInvariantAlgebra D)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (polynomialConjugateInvariantAlgebra D) (polynomialConjugateAlgebra D)))

private def invariantTargetInclusion (D : PolynomialNormalClosureData F N) :
    Spec (.of (polynomialConjugateInvariantAlgebra D)) ⟶
      Spec (.of (PolynomialImageAlgebra F)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D)))

private theorem invariantTargetMap_comp (D : PolynomialNormalClosureData F N) :
    invariantTargetMap D ≫ invariantTargetInclusion D =
      Spec.map (CommRingCat.ofHom
        (algebraMap (PolynomialImageAlgebra F) (polynomialConjugateAlgebra D))) := by
  rw [invariantTargetMap, invariantTargetInclusion, ← Spec.map_comp]
  rfl

/-- The canonical comparison to the pullback of the original finite
normalization over the existing invariant target open. -/
def polynomialConjugateNormalizationBaseChangeMap
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F) :
    Spec (.of (polynomialConjugateAlgebra D)) ⟶
      pullback
        (polynomialNormalizationInExtensionToBase (F := F) (N := N))
        (Spec.map (CommRingCat.ofHom
          (algebraMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D)))) :=
  pullback.lift (polynomialConjugateToNormalization D hKeller) (invariantTargetMap D)
    ((polynomialConjugateToNormalization_comp_toBase D hKeller).trans
      (invariantTargetMap_comp D).symm)

/-- The all-conjugate open is exactly the finite normalization restricted
to the invariant target open. This does not fill that target open. -/
theorem polynomialConjugateNormalizationBaseChangeMap_isIso
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F) :
    IsIso (polynomialConjugateNormalizationBaseChangeMap D hKeller) := by
  let E : Type := polynomialConjugateAlgebra D
  let C : Type := polynomialConjugateInvariantAlgebra D
  let T : Type := PolynomialNormalizationInExtensionRing (F := F) (N := N)
  letI := D.finiteIntermediate
  letI : FiniteDimensional (PolynomialMapBaseFunctionField F) N := D.finiteNormal
  letI : Algebra.IsIntegral (PolynomialMapBaseFunctionField F) N :=
    ⟨fun z => IsIntegral.of_finite (PolynomialMapBaseFunctionField F) z⟩
  letI : Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N :=
    ⟨fun z => IsSeparable.of_integral (F := PolynomialMapBaseFunctionField F) z⟩
  letI : Module.Finite C E := polynomialConjugateAlgebra_finite_over_invariants D
  letI : IsFinite (invariantTargetMap D) :=
    (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap C E))).mpr
      (RingHom.finite_algebraMap.mpr inferInstance)
  letI : IsSeparated (polynomialNormalizationInExtensionToBase (F := F) (N := N)) := by
    unfold polynomialNormalizationInExtensionToBase normalizedModelToBase
    infer_instance
  letI : IsOpenImmersion (invariantTargetInclusion D) :=
    polynomialConjugateInvariantAlgebra_isOpenImmersion_of_isKeller D hKeller
  letI : IsOpenImmersion (polynomialConjugateToNormalization D hKeller) :=
    polynomialConjugateToNormalization_isOpenImmersion D hKeller
  letI : IsIntegral (polynomialNormalizationInExtension (F := F) (N := N)) :=
    inferInstanceAs (IsIntegral (Spec (.of T)))
  unfold polynomialConjugateNormalizationBaseChangeMap
  exact isIso_lift_of_open_of_finite
    (polynomialConjugateToNormalization D hKeller) (invariantTargetMap D)
    (polynomialNormalizationInExtensionToBase (F := F) (N := N))
    (invariantTargetInclusion D) _

/-- The Cartesian normalization comparison, using the original schemes
and their canonical maps. -/
def polynomialConjugateNormalizationBaseChangeIso
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F) :
    Spec (.of (polynomialConjugateAlgebra D)) ≅
      pullback
        (polynomialNormalizationInExtensionToBase (F := F) (N := N))
        (Spec.map (CommRingCat.ofHom
          (algebraMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D)))) := by
  letI := polynomialConjugateNormalizationBaseChangeMap_isIso D hKeller
  exact asIso (polynomialConjugateNormalizationBaseChangeMap D hKeller)

@[simp]
theorem polynomialConjugateNormalizationBaseChangeIso_hom_fst
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F) :
    (polynomialConjugateNormalizationBaseChangeIso D hKeller).hom ≫
        pullback.fst _ _ = polynomialConjugateToNormalization D hKeller := by
  simp [polynomialConjugateNormalizationBaseChangeIso,
    polynomialConjugateNormalizationBaseChangeMap]

@[simp]
theorem polynomialConjugateNormalizationBaseChangeIso_hom_snd
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F) :
    (polynomialConjugateNormalizationBaseChangeIso D hKeller).hom ≫
        pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (algebraMap (polynomialConjugateInvariantAlgebra D) (polynomialConjugateAlgebra D))) := by
  simp [polynomialConjugateNormalizationBaseChangeIso,
    polynomialConjugateNormalizationBaseChangeMap, invariantTargetMap]

/-- The image of the all-conjugate open is the full inverse image of the
existing invariant target open, not an additional open chosen upstairs. -/
theorem polynomialConjugateToNormalization_range_eq_preimage
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F) :
    Set.range (polynomialConjugateToNormalization D hKeller) =
      (polynomialNormalizationInExtensionToBase (F := F) (N := N)) ⁻¹'
        Set.range (Spec.map (CommRingCat.ofHom
          (algebraMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D)))) := by
  let p := polynomialNormalizationInExtensionToBase (F := F) (N := N)
  let j := invariantTargetInclusion D
  let P : Scheme := pullback p j
  let iP : P ⟶ polynomialNormalizationInExtension (F := F) (N := N) := pullback.fst p j
  let e := polynomialConjugateNormalizationBaseChangeIso D hKeller
  have hPoint (w : Spec (.of (polynomialConjugateAlgebra D))) :
      iP (e.hom w) = polynomialConjugateToNormalization D hKeller w := by
    exact congrArg (fun f => f w)
      (polynomialConjugateNormalizationBaseChangeIso_hom_fst D hKeller)
  have hRange : Set.range (polynomialConjugateToNormalization D hKeller) =
      Set.range iP := by
    apply Set.Subset.antisymm
    · rintro _ ⟨w, rfl⟩
      exact ⟨e.hom w, hPoint w⟩
    · rintro _ ⟨q, rfl⟩
      obtain ⟨w, hw⟩ := e.hom.surjective q
      exact ⟨w, (hPoint w).symm.trans (congrArg (fun a => iP a) hw)⟩
  rw [hRange]
  letI : FiniteDimensional (PolynomialMapBaseFunctionField F) N := D.finiteNormal
  letI : Algebra.IsIntegral (PolynomialMapBaseFunctionField F) N :=
    ⟨fun z => IsIntegral.of_finite (PolynomialMapBaseFunctionField F) z⟩
  letI : Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N :=
    ⟨fun z => IsSeparable.of_integral (F := PolynomialMapBaseFunctionField F) z⟩
  letI : IsOpenImmersion j :=
    polynomialConjugateInvariantAlgebra_isOpenImmersion_of_isKeller D hKeller
  exact IsOpenImmersion.range_pullbackFst j p

end

end CollisionIdeals.Planar.Research
