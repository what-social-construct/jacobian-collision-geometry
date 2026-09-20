import CollisionIdeals.General.Normalization.Model
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.RingTheory.ZariskisMainTheorem

/-!
# The open immersion into the relative integral closure

Algebraic Zariski's main theorem gives localizations of a quasi-finite
finite-type algebra that agree with localizations of its integral closure.
The resulting principal charts are open immersions and separate points.
For a normal domain, this identifies the source with an open subscheme of
the normalization in its fraction field.
-/

set_option autoImplicit false

namespace CollisionIdeals

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

private theorem specMap_injective_of_localizationAway
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (h : ∀ p : PrimeSpectrum A, ∃ r : R, f r ∉ p.asIdeal ∧
      Function.Bijective (Localization.awayMap f r)) :
    Function.Injective (PrimeSpectrum.comap f) := by
  intro p q hpq
  have hmem (r : R) : f r ∈ p.asIdeal ↔ f r ∈ q.asIdeal := by
    change r ∈ (PrimeSpectrum.comap f p).asIdeal ↔
      r ∈ (PrimeSpectrum.comap f q).asIdeal
    rw [hpq]
  obtain ⟨r, hr, hbij⟩ := h p
  have hrq : f r ∉ q.asIdeal := fun hh => hr ((hmem r).mpr hh)
  apply PrimeSpectrum.ext
  ext a
  obtain ⟨b, m, hb⟩ := Localization.awayMap_surjective_iff.mp hbij.2 a
  have hpm : f r ^ m ∉ p.asIdeal := fun hh => hr (p.isPrime.mem_of_pow_mem m hh)
  have hqm : f r ^ m ∉ q.asIdeal := fun hh => hrq (q.isPrime.mem_of_pow_mem m hh)
  rw [← p.isPrime.mul_mem_left_iff hpm, ← q.isPrime.mul_mem_left_iff hqm, ← hb]
  exact hmem b

/-- A ring map locally identified with localization away from a base
element induces an open immersion on spectra. -/
theorem isOpenImmersion_specMap_of_localizationAway
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (h : ∀ p : PrimeSpectrum A, ∃ r : R, f r ∉ p.asIdeal ∧
      Function.Bijective (Localization.awayMap f r)) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom f)) := by
  letI : Algebra R A := f.toAlgebra
  apply IsOpenImmersion.of_forall_source_exists
    (Spec.map (CommRingCat.ofHom f)) (specMap_injective_of_localizationAway f h)
  intro p
  obtain ⟨r, hr, hbij⟩ := h p
  let S := Localization.Away (f r)
  let φ : Localization.Away r →ₐ[R] S :=
    Localization.awayMapₐ (Algebra.ofId R A) r
  have hφ : Function.Bijective φ := hbij
  letI : IsLocalization.Away r S :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers r)
      (AlgEquiv.ofBijective φ hφ)
  let i : Spec (.of S) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A S))
  haveI : IsOpenImmersion i := IsOpenImmersion.of_isLocalization (f r)
  refine ⟨Spec (.of S), i, inferInstance, ?_, ?_⟩
  · change p ∈ Set.range (PrimeSpectrum.comap (algebraMap A S))
    rw [PrimeSpectrum.localization_away_comap_range S (f r)]
    exact hr
  · have hcomp : i ≫ Spec.map (CommRingCat.ofHom f) =
        Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
      rw [← Spec.map_comp]
      rfl
    rw [hcomp]
    exact IsOpenImmersion.of_isLocalization r

/-- The affine form of Zariski's main theorem: a quasi-finite finite-type
algebra is open in its relative integral closure. -/
theorem isOpenImmersion_integralClosure_of_quasiFinite
    (B A : Type u) [CommRing B] [CommRing A] [Algebra B A]
    [Algebra.FiniteType B A] [Algebra.QuasiFinite B A] :
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (integralClosure B A).val.toRingHom)) := by
  apply isOpenImmersion_specMap_of_localizationAway
  intro p
  exact Algebra.ZariskisMainProperty.of_finiteType p.asIdeal

/-- The canonical map from an integrally closed intermediate ring into
the normalization in its overring is open whenever the original algebra
is finite type and quasi-finite. -/
theorem intermediateToNormalization_isOpenImmersion
    (B A E : Type u) [CommRing B] [CommRing A] [CommRing E]
    [Algebra B A] [Algebra B E] [Algebra A E] [IsScalarTower B A E]
    [IsIntegralClosure A A E]
    [Algebra.FiniteType B A] [Algebra.QuasiFinite B A] :
    IsOpenImmersion (intermediateToNormalization (B := B) (E := E) (A := A)) := by
  let φ : integralClosure B E →ₐ[B] integralClosure B A :=
    (normalizationToIntermediate (B := B) (E := E) (A := A)).codRestrict
      (integralClosure B A) fun x => by
        apply (isIntegral_algHom_iff (IsScalarTower.toAlgHom B A E)
          (IsIntegralClosure.algebraMap_injective A A E)).mp
        change IsIntegral B (algebraMap A E
          (normalizationToIntermediate (B := B) (E := E) (A := A) x))
        rw [algebraMap_normalizationToIntermediate]
        exact x.property
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y hxy
      apply normalizationToIntermediate_injective (A := A)
      exact congrArg Subtype.val hxy
    · intro x
      refine ⟨(IsScalarTower.toAlgHom B A E).mapIntegralClosure x, ?_⟩
      apply Subtype.ext
      apply IsIntegralClosure.algebraMap_injective A A E
      simp [φ]
  let e := AlgEquiv.ofBijective φ hφ
  haveI : IsIso (CommRingCat.ofHom φ.toRingHom) :=
    inferInstanceAs (IsIso e.toRingEquiv.toCommRingCatIso.hom)
  haveI := isOpenImmersion_integralClosure_of_quasiFinite B A
  have hcomp : (normalizationToIntermediate (B := B) (E := E) (A := A)).toRingHom =
      (integralClosure B A).val.toRingHom.comp φ.toRingHom := rfl
  rw [intermediateToNormalization, hcomp, CommRingCat.ofHom_comp, Spec.map_comp]
  infer_instance

end

end CollisionIdeals
