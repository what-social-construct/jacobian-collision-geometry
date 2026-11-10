import CollisionIdeals.Planar.Research.Vanishing.ConjugateNormalizationOpen
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.AsSubring

/-!
# Local regularity of all conjugate sheets

The actual all-conjugate open is tested at points of the original finite
normalization. A point belongs to an affine open immersion exactly when
the source algebra maps over the base to that point's local ring.

No point is assumed to belong to the open, and no boundary vanishing or
uniform bound on a differential orbit is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 10000

namespace CollisionIdeals.Planar.Research

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

private theorem mem_range_specMap_iff_exists_algHom_localization
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (hOpen : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    (q : PrimeSpectrum R) :
    q ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap R A))).base ↔
      Nonempty (A →ₐ[R] Localization.AtPrime q.asIdeal) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
  letI : IsOpenImmersion f := hOpen
  constructor
  · rintro ⟨p, rfl⟩
    let q : PrimeSpectrum R := f.base p
    let l := Localization.localRingHom q.asIdeal p.asIdeal (algebraMap R A) rfl
    let e : CommRingCat.of (Localization.AtPrime q.asIdeal) ≅
        CommRingCat.of (Localization.AtPrime p.asIdeal) :=
      (Spec.stalkIso (.of R) q).symm ≪≫ asIso (f.stalkMap p) ≪≫
        Spec.stalkIso (.of A) p
    have he : e.hom = CommRingCat.ofHom l := by
      dsimp [e]
      rw [← Scheme.localRingHom_comp_stalkIso]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      change (Spec.stalkIso (.of R) (PrimeSpectrum.comap (algebraMap R A) p)).inv ≫
        (Spec.stalkIso (.of R) (PrimeSpectrum.comap (algebraMap R A) p)).hom ≫
          CommRingCat.ofHom l = CommRingCat.ofHom l
      simp
    let h : A →+* Localization.AtPrime q.asIdeal :=
      e.commRingCatIsoToRingEquiv.symm.toRingHom.comp
        (algebraMap A (Localization.AtPrime p.asIdeal))
    refine ⟨{ h with commutes' := ?_ }⟩
    intro r
    apply e.commRingCatIsoToRingEquiv.injective
    change e.commRingCatIsoToRingEquiv
        (e.commRingCatIsoToRingEquiv.symm
          (algebraMap A (Localization.AtPrime p.asIdeal) (algebraMap R A r))) = _
    rw [RingEquiv.apply_symm_apply]
    change algebraMap A (Localization.AtPrime p.asIdeal) (algebraMap R A r) =
      e.hom.hom (algebraMap R (Localization.AtPrime q.asIdeal) r)
    rw [he]
    exact (Localization.localRingHom_to_map q.asIdeal p.asIdeal
      (algebraMap R A) rfl r).symm
  · rintro ⟨h⟩
    let p : PrimeSpectrum A :=
      PrimeSpectrum.comap h.toRingHom
        ⟨IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal), inferInstance⟩
    refine ⟨p, PrimeSpectrum.ext ?_⟩
    ext r
    change h (algebraMap R A r) ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ↔ r ∈ q.asIdeal
    rw [h.commutes]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ r

private theorem algHom_eq_of_fractionRing_base
    {R A K : Type u} [CommRing R] [IsDomain R] [CommRing A]
    [Field K] [Algebra R A] [Algebra R K] [IsFractionRing R K]
    (e f : A →ₐ[R] K) (he : Function.Injective e) : f = e := by
  ext a
  obtain ⟨r, s, hs, hfrac⟩ := IsFractionRing.div_surjective (A := R) (e a)
  have hsK : algebraMap R K s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  have hCrossK : algebraMap R K s * e a = algebraMap R K r := by
    rw [mul_comm]
    exact ((div_eq_iff hsK).mp hfrac).symm
  have hCrossA : algebraMap R A s * a = algebraMap R A r := by
    apply he
    simpa only [map_mul, e.commutes] using hCrossK
  have hCrossF : algebraMap R K s * f a = algebraMap R K r := by
    simpa only [map_mul, f.commutes] using congrArg f hCrossA
  exact mul_left_cancel₀ hsK (hCrossF.trans hCrossK.symm)

variable {F : PlanarPolynomialMap} {N : Type} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

@[reducible] local instance commonOpenBaseAlgebra :
    Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

@[reducible] local instance commonOpenBaseFieldAlgebra :
    Algebra (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) :=
  OreLocalization.instAlgebra

local instance commonOpenBaseFieldSMul :
    SMul (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) :=
  Algebra.toSMul

local notation "B₀" => PolynomialImageAlgebra F
local notation "T₀" => PolynomialNormalizationInExtensionRing (F := F) (N := N)

@[reducible] local instance commonOpenNormalizationBaseAlgebra : Algebra B₀ T₀ :=
  (integralClosure B₀ N).algebra

local instance commonOpenNormalizationBaseSMul : SMul B₀ T₀ := Algebra.toSMul

@[reducible] local instance commonOpenNormalizationNormalAlgebra : Algebra T₀ N :=
  Subalgebra.toAlgebra (integralClosure B₀ N)

local instance commonOpenNormalizationNormalSMul : SMul T₀ N := Algebra.toSMul

@[reducible] local instance commonOpenConjugateBaseAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra B₀ (polynomialConjugateAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateAlgebra D)

local instance commonOpenConjugateBaseSMul (D : PolynomialNormalClosureData F N) :
    SMul B₀ (polynomialConjugateAlgebra D) := Algebra.toSMul

private theorem commonOpenNormalizationFractionRing
    (D : PolynomialNormalClosureData F N) : IsFractionRing T₀ N := by
  let K := PolynomialMapBaseFunctionField F
  letI : IsScalarTower B₀ K N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : FiniteDimensional K N := D.finiteNormal
  exact integralClosure.isFractionRing_of_finite_extension K N

/-- At an actual finite-normalization point, the all-conjugate open is
exactly the locus where every conjugate source coordinate belongs to the
same original localization inside the normal-closure field. -/
theorem polynomialConjugateToNormalization_mem_range_iff_coordinates_regular
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F)
    (q : PrimeSpectrum T₀) :
    letI : IsFractionRing T₀ N := commonOpenNormalizationFractionRing D
    q ∈ Set.range (polynomialConjugateToNormalization D hKeller).base ↔
      ∀ (g : D.galoisGroup) (i : Fin 2),
        polynomialConjugateSourceMapOverImage D g (MvPolynomial.X i) ∈
          Localization.subalgebra (A := T₀) N q.asIdeal.primeCompl
            q.asIdeal.primeCompl_le_nonZeroDivisors := by
  letI : IsFractionRing T₀ N := commonOpenNormalizationFractionRing D
  let E := polynomialConjugateAlgebra D
  let J : Subalgebra T₀ N := Localization.subalgebra (A := T₀) N q.asIdeal.primeCompl
    q.asIdeal.primeCompl_le_nonZeroDivisors
  letI : Algebra T₀ J := Subalgebra.algebra J
  letI : SMul T₀ J := Algebra.toSMul
  letI : IsLocalization q.asIdeal.primeCompl J := by
    dsimp only [J]
    exact Localization.subalgebra.isLocalization_subalgebra (A := T₀) N
      q.asIdeal.primeCompl q.asIdeal.primeCompl_le_nonZeroDivisors
  letI : Algebra T₀ E :=
    (polynomialNormalizationToConjugateAlgebra D hKeller).toRingHom.toAlgebra
  letI : IsScalarTower B₀ T₀ N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e : E →ₐ[T₀] N :=
    { E.val.toRingHom with commutes' := fun t =>
        polynomialNormalizationToConjugateAlgebra_coe D hKeller t }
  let eqLoc : Localization.AtPrime q.asIdeal ≃ₐ[T₀] J :=
    IsLocalization.algEquiv q.asIdeal.primeCompl _ _
  have hCriterion :
      q ∈ Set.range (polynomialConjugateToNormalization D hKeller).base ↔
        Nonempty (E →ₐ[T₀] J) := by
    have h := mem_range_specMap_iff_exists_algHom_localization T₀ E
      (polynomialConjugateToNormalization_isOpenImmersion D hKeller) q
    change q ∈ Set.range (polynomialConjugateToNormalization D hKeller).base ↔ _ at h
    exact h.trans ⟨fun ⟨f⟩ => ⟨eqLoc.toAlgHom.comp f⟩,
      fun ⟨f⟩ => ⟨eqLoc.symm.toAlgHom.comp f⟩⟩
  rw [hCriterion]
  constructor
  · rintro ⟨f⟩ g i
    let z : E := ⟨_, polynomialConjugateAlgebra_coordinate_mem D g i⟩
    have he : Function.Injective e := by
      intro x y h
      exact Subtype.ext h
    have hEq : J.val.comp f = e :=
      algHom_eq_of_fractionRing_base (R := T₀) (A := E) (K := N) e (J.val.comp f) he
    have hValue : (f z : N) = (z : N) := AlgHom.congr_fun hEq z
    change (z : N) ∈ J
    rw [← hValue]
    exact (f z).property
  · intro hCoordinates
    have hE : E ≤ J.restrictScalars B₀ := by
      apply Algebra.adjoin_le
      rintro z ⟨⟨g, i⟩, rfl⟩
      exact hCoordinates g i
    exact ⟨e.codRestrict J (fun z => hE z.property)⟩

/-- Outside the actual all-conjugate open, a conjugate source coordinate
fails to belong to that same normalization local ring. -/
theorem polynomialConjugateToNormalization_not_mem_range_iff_coordinate_pole
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F)
    (q : PrimeSpectrum T₀) :
    letI : IsFractionRing T₀ N := commonOpenNormalizationFractionRing D
    q ∉ Set.range (polynomialConjugateToNormalization D hKeller).base ↔
      ∃ (g : D.galoisGroup) (i : Fin 2),
        polynomialConjugateSourceMapOverImage D g (MvPolynomial.X i) ∉
          Localization.subalgebra (A := T₀) N q.asIdeal.primeCompl
            q.asIdeal.primeCompl_le_nonZeroDivisors := by
  classical
  letI : IsFractionRing T₀ N := commonOpenNormalizationFractionRing D
  simpa only [not_forall] using not_congr
    (polynomialConjugateToNormalization_mem_range_iff_coordinates_regular D hKeller q)

/-- A pole of an element of the actual conjugate algebra forces a pole
of one of its actual conjugate coordinate generators at the same point.
No ramification or hidden-inertia hypothesis is used. -/
theorem exists_conjugate_coordinate_pole_of_conjugateAlgebra_pole
    (D : PolynomialNormalClosureData F N) (q : PrimeSpectrum T₀)
    (z : N) (hz : z ∈ polynomialConjugateAlgebra D)
    (hPole : letI : IsFractionRing T₀ N := commonOpenNormalizationFractionRing D
      z ∉ Localization.subalgebra (A := T₀) N q.asIdeal.primeCompl
        q.asIdeal.primeCompl_le_nonZeroDivisors) :
    letI : IsFractionRing T₀ N := commonOpenNormalizationFractionRing D
    ∃ (g : D.galoisGroup) (i : Fin 2),
      polynomialConjugateSourceMapOverImage D g (MvPolynomial.X i) ∉
        Localization.subalgebra (A := T₀) N q.asIdeal.primeCompl
          q.asIdeal.primeCompl_le_nonZeroDivisors := by
  letI : IsFractionRing T₀ N := commonOpenNormalizationFractionRing D
  let J : Subalgebra T₀ N := Localization.subalgebra (A := T₀) N q.asIdeal.primeCompl
    q.asIdeal.primeCompl_le_nonZeroDivisors
  letI : IsScalarTower B₀ T₀ N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  by_contra! hCoordinates
  apply hPole
  have hE : polynomialConjugateAlgebra D ≤ J.restrictScalars B₀ := by
    apply Algebra.adjoin_le
    rintro z ⟨⟨g, i⟩, rfl⟩
    exact hCoordinates g i
  exact hE hz

end

end CollisionIdeals.Planar.Research
