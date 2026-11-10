import CollisionIdeals.Planar.Research.ConjugateCover
import CollisionIdeals.General.Keller.ConjugateInvariantOpen
import CollisionIdeals.General.Normalization.OpenImmersion
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.Trace.Basic

/-!
# The all-conjugate open inside the finite normalization

Normality of the invariant target open and the existing finite trace frame
identify integral normal-closure elements inside the original conjugate
algebra. No empty-boundary or fixed-orbit bound is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals.Planar.Research

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

private theorem integrallyClosed_of_specMap_isOpenImmersion
    (B C : Type u) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [CommRing C] [IsDomain C] [Algebra B C]
    (hOpen : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap B C)))) :
    IsIntegrallyClosed C := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap B C))
  letI : IsOpenImmersion f := hOpen
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ hp
  let x : PrimeSpectrum C := ⟨p, hp.isPrime⟩
  let q : PrimeSpectrum B := f.base x
  letI : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime q.asIdeal)
      q.asIdeal.primeCompl q.asIdeal.primeCompl_le_nonZeroDivisors
  let e : CommRingCat.of (Localization.AtPrime q.asIdeal) ≅
      CommRingCat.of (Localization.AtPrime p) :=
    (Spec.stalkIso (.of B) q).symm ≪≫ asIso (f.stalkMap x) ≪≫
      Spec.stalkIso (.of C) x
  exact IsIntegrallyClosed.of_equiv e.commRingCatIsoToRingEquiv

private theorem sum_fieldTrace_mul_of_deltaFrame
    {K N : Type u} [Field K] [Field N] [Algebra K N]
    [FiniteDimensional K N] [IsGalois K N]
    [DecidableEq (N ≃ₐ[K] N)]
    {r : ℕ} (a b : Fin r → N)
    (hdelta : ∀ g : N ≃ₐ[K] N,
      ∑ i, a i * g (b i) = if g = 1 then 1 else 0) (z : N) :
    ∑ i, a i * algebraMap K N (Algebra.trace K N (b i * z)) = z := by
  classical
  simp only [trace_eq_sum_automorphisms, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  simp [hdelta]

variable {F : PlanarPolynomialMap} {N : Type} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

@[reducible] local instance conjugateNormalizationBaseAlgebra :
    Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

@[reducible] local instance conjugateNormalizationConjugateAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateAlgebra D)

@[reducible] local instance conjugateNormalizationInvariantAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateInvariantAlgebra D)

local instance conjugateNormalizationInvariantBaseSMul
    (D : PolynomialNormalClosureData F N) :
    SMul (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) :=
  Algebra.toSMul

local instance conjugateNormalizationConjugateBaseSMul
    (D : PolynomialNormalClosureData F N) :
    SMul (PolynomialImageAlgebra F) (polynomialConjugateAlgebra D) :=
  Algebra.toSMul

local instance conjugateNormalizationInvariantConjugateSMul
    (D : PolynomialNormalClosureData F N) :
    SMul (polynomialConjugateInvariantAlgebra D) (polynomialConjugateAlgebra D) :=
  Algebra.toSMul

@[reducible] local instance conjugateNormalizationInvariantNormalAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (polynomialConjugateInvariantAlgebra D) N :=
  ((polynomialConjugateAlgebra D).val.comp
    (polynomialConjugateInvariantAlgebra D).val).toAlgebra

local instance conjugateNormalizationInvariantNormalSMul
    (D : PolynomialNormalClosureData F N) :
    SMul (polynomialConjugateInvariantAlgebra D) N :=
  Algebra.toSMul

local instance conjugateNormalizationInvariantConjugateTower
    (D : PolynomialNormalClosureData F N) :
    IsScalarTower (polynomialConjugateInvariantAlgebra D)
      (polynomialConjugateAlgebra D) N :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

local instance conjugateNormalizationBaseInvariantTower
    (D : PolynomialNormalClosureData F N) :
    IsScalarTower (PolynomialImageAlgebra F)
      (polynomialConjugateInvariantAlgebra D) N :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Normality of the actual invariant target open is derived from its
open immersion into the normal polynomial target. -/
theorem conjugateInvariantAlgebra_isIntegrallyClosed
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F) :
    IsIntegrallyClosed (polynomialConjugateInvariantAlgebra D) := by
  letI := D.finiteIntermediate
  letI : FiniteDimensional (PolynomialMapBaseFunctionField F) N := D.finiteNormal
  letI : Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N := inferInstance
  letI := polynomialImageAlgebra_isIntegrallyClosed_of_finiteDimensional F
  exact integrallyClosed_of_specMap_isOpenImmersion
    (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D)
    (polynomialConjugateInvariantAlgebra_isOpenImmersion_of_isKeller D hKeller)

private theorem mem_conjugateAlgebra_of_integral_invariants
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F)
    (z : N) (hz : IsIntegral (polynomialConjugateInvariantAlgebra D) z) :
    z ∈ polynomialConjugateAlgebra D := by
  classical
  let K := PolynomialMapBaseFunctionField F
  let E := polynomialConjugateAlgebra D
  let C := polynomialConjugateInvariantAlgebra D
  letI := D.finiteIntermediate
  letI : FiniteDimensional K N := D.finiteNormal
  letI : Normal K N := D.normal
  letI : Algebra.IsSeparable K N := inferInstance
  letI : IsGalois K N := IsGalois.mk
  letI : Finite D.galoisGroup := D.finiteGaloisGroup
  letI := Fintype.ofFinite D.galoisGroup
  letI : Algebra C K := polynomialConjugateInvariantAlgebraBaseFieldAlgebra D
  letI : SMul C K := Algebra.toSMul
  letI : IsScalarTower C K N := IsScalarTower.of_algebraMap_eq
    fun c => (polynomialConjugateInvariantAlgebra_baseField_algebraMap D c).symm
  letI : IsFractionRing C K := polynomialConjugateInvariantAlgebra_isFractionRing D
  letI : IsIntegrallyClosed C := conjugateInvariantAlgebra_isIntegrallyClosed D hKeller
  letI : Algebra.IsIntegral C E := polynomialConjugateAlgebra_isIntegral_over_invariants D
  obtain ⟨r, a, b, hab⟩ :=
    FiniteGroupCover.exists_deltaFrame_of_canonicalMap_surjective C E D.galoisGroup
      (conjugateGaloisMap_surjective D hKeller)
  have hDeltaN : ∀ g : D.galoisGroup,
      ∑ i, (a i : N) * g (b i : N) = if g = 1 then 1 else 0 := by
    intro g
    have hLift := congrArg (fun x : E => E.val x) (hab g)
    simp only [map_sum, map_mul] at hLift
    by_cases hg : g = 1
    · simp only [if_pos hg, map_one] at hLift ⊢
      exact hLift
    · simp only [if_neg hg, map_zero] at hLift ⊢
      exact hLift
  have hCoeff (i : Fin r) :
      ∃ c : C, algebraMap K N (algebraMap C K c) =
        algebraMap K N (Algebra.trace K N ((b i : N) * z)) := by
    have hb : IsIntegral C (b i : N) :=
      (Algebra.IsIntegral.isIntegral (R := C) (b i)).algebraMap
    obtain ⟨c, hc⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
      (Algebra.isIntegral_trace (R := C) (L := K) (F := N) (hb.mul hz))
    exact ⟨c, congrArg (algebraMap K N) hc⟩
  choose c hc using hCoeff
  have hMem : (∑ i, (a i : N) *
      algebraMap K N (Algebra.trace K N ((b i : N) * z))) ∈ E := by
    apply E.sum_mem
    intro i _
    apply E.mul_mem (a i).property
    rw [← hc i, polynomialConjugateInvariantAlgebra_baseField_algebraMap D]
    exact (c i).val.property
  rwa [sum_fieldTrace_mul_of_deltaFrame (fun i => (a i : N))
    (fun i => (b i : N)) hDeltaN z] at hMem

/-- Every element of the original finite normalization already belongs to
the all-conjugate algebra. This inclusion does not bound the latter's poles. -/
theorem polynomialNormalization_mem_conjugateAlgebra
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F)
    (t : PolynomialNormalizationInExtensionRing (F := F) (N := N)) :
    (t : N) ∈ polynomialConjugateAlgebra D := by
  have ht : IsIntegral (PolynomialImageAlgebra F) (t : N) := t.property
  exact mem_conjugateAlgebra_of_integral_invariants D hKeller (t : N)
    (IsIntegral.tower_top (R := PolynomialImageAlgebra F)
      (A := polynomialConjugateInvariantAlgebra D) ht)

/-- The same trace-frame argument proves normality of the original
all-conjugate algebra, without invoking a new étale-normality input. -/
theorem conjugateAlgebra_isIntegrallyClosed
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F) :
    IsIntegrallyClosed (polynomialConjugateAlgebra D) := by
  let E := polynomialConjugateAlgebra D
  let C := polynomialConjugateInvariantAlgebra D
  letI : IsFractionRing E N := polynomialConjugateAlgebra_isFractionRing D
  letI : Algebra.IsIntegral C E := polynomialConjugateAlgebra_isIntegral_over_invariants D
  apply (isIntegrallyClosed_iff N).mpr
  intro z hz
  exact ⟨⟨z, mem_conjugateAlgebra_of_integral_invariants D hKeller z
    (isIntegral_trans z hz)⟩, rfl⟩

/-- The canonical inclusion of the existing finite normalization in the
all-conjugate algebra. This is not the reverse orbit-containment claim. -/
def polynomialNormalizationToConjugateAlgebra
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F) :
    PolynomialNormalizationInExtensionRing (F := F) (N := N) →ₐ[PolynomialImageAlgebra F]
      polynomialConjugateAlgebra D := by
  letI : IsFractionRing (polynomialConjugateAlgebra D) N :=
    polynomialConjugateAlgebra_isFractionRing D
  letI : IsIntegrallyClosed (polynomialConjugateAlgebra D) :=
    conjugateAlgebra_isIntegrallyClosed D hKeller
  exact normalizationToIntermediate (B := PolynomialImageAlgebra F)
    (E := N) (A := polynomialConjugateAlgebra D)

@[simp]
theorem polynomialNormalizationToConjugateAlgebra_coe
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F)
    (t : PolynomialNormalizationInExtensionRing (F := F) (N := N)) :
    (polynomialNormalizationToConjugateAlgebra D hKeller t : N) = (t : N) := by
  letI : IsFractionRing (polynomialConjugateAlgebra D) N :=
    polynomialConjugateAlgebra_isFractionRing D
  letI : IsIntegrallyClosed (polynomialConjugateAlgebra D) :=
    conjugateAlgebra_isIntegrallyClosed D hKeller
  unfold polynomialNormalizationToConjugateAlgebra
  exact algebraMap_normalizationToIntermediate (A := polynomialConjugateAlgebra D) t

/-- The canonical morphism from the actual all-conjugate scheme to the
original finite normal-closure normalization. -/
def polynomialConjugateToNormalization
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F) :
    Spec (.of (polynomialConjugateAlgebra D)) ⟶
      polynomialNormalizationInExtension (F := F) (N := N) :=
  Spec.map (CommRingCat.ofHom
    (polynomialNormalizationToConjugateAlgebra D hKeller).toRingHom)

/-- The all-conjugate scheme is an open subscheme of the original finite
normalization. The statement does not assert that this open is all of it. -/
theorem polynomialConjugateToNormalization_isOpenImmersion
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F) :
    IsOpenImmersion (polynomialConjugateToNormalization D hKeller) := by
  let B := PolynomialImageAlgebra F
  let E := polynomialConjugateAlgebra D
  letI : IsFractionRing E N := polynomialConjugateAlgebra_isFractionRing D
  letI : IsIntegrallyClosed E := conjugateAlgebra_isIntegrallyClosed D hKeller
  letI : IsIntegralClosure E E N := inferInstance
  letI : Algebra.FiniteType B E := polynomialConjugateAlgebra_finiteType D
  letI : Algebra.QuasiFinite B E := polynomialConjugateAlgebra_quasiFinite_of_isKeller D hKeller
  unfold polynomialConjugateToNormalization polynomialNormalizationToConjugateAlgebra
  exact intermediateToNormalization_isOpenImmersion B E N

/-- The constructed open immersion lies over the original target. -/
theorem polynomialConjugateToNormalization_comp_toBase
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F) :
    polynomialConjugateToNormalization D hKeller ≫
        polynomialNormalizationInExtensionToBase (F := F) (N := N) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (PolynomialImageAlgebra F) (polynomialConjugateAlgebra D))) := by
  letI : IsFractionRing (polynomialConjugateAlgebra D) N :=
    polynomialConjugateAlgebra_isFractionRing D
  letI : IsIntegrallyClosed (polynomialConjugateAlgebra D) :=
    conjugateAlgebra_isIntegrallyClosed D hKeller
  unfold polynomialConjugateToNormalization polynomialNormalizationToConjugateAlgebra
  exact intermediateToNormalization_comp_toBase
    (B := PolynomialImageAlgebra F) (E := N) (A := polynomialConjugateAlgebra D)

end

end CollisionIdeals.Planar.Research
