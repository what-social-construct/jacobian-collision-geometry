import CollisionIdeals.General.Normalization.MarkedLocalIndex
import CollisionIdeals.General.Normalization.LocalIndexBaseChange

/-!
# The inertia index at a marked normalization divisor

Localizing the coordinate-image base reduces the index comparison to the
finite Dedekind tower. The intermediate prime is the contraction along the
actual marked embedding, and the inertia group belongs to the original
normalization prime. No local-index equality is supplied as an input.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

noncomputable section

universe u

attribute [local instance] Ideal.Quotient.field

variable (k B L N : Type u) [Field k] [CharZero k]
  [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B] [Algebra k B]
  [Field L] [Field N]
  [Algebra (FractionRing B) L] [Algebra (FractionRing B) N]
  [Algebra B L] [Algebra B N]
  [IsScalarTower B (FractionRing B) L] [IsScalarTower B (FractionRing B) N]
  [FiniteDimensional (FractionRing B) L] [FiniteDimensional (FractionRing B) N]
  [Algebra.IsSeparable (FractionRing B) L] [IsGalois (FractionRing B) N]

local instance divisorialIndexGaloisCommutes :
    SMulCommClass (N ≃ₐ[FractionRing B] N) B N :=
  intermediateFieldGalois_baseCommutes B (FractionRing B) N (N ≃ₐ[FractionRing B] N)

include k in
set_option maxHeartbeats 800000 in
/-- The divisorial index for the contraction along a marked embedding is
the inertia quotient index for its fixing subgroup. -/
theorem integralClosure_localRamificationIndex_eq
    (ι : L →ₐ[FractionRing B] N)
    (q : Ideal (integralClosure B N)) [q.IsPrime]
    (hq : (q.under B).primeHeight = 1) :
    localRamificationIndex (R := B) (S := integralClosure B L)
        (q.comap (ι.restrictScalars B).mapIntegralClosure.toRingHom) =
      inertiaQuotientIndex (q.inertia (N ≃ₐ[FractionRing B] N))
        ι.fieldRange.fixingSubgroup := by
  let K : Type u := FractionRing B
  let T : Type u := integralClosure B N
  let S : Type u := integralClosure B L
  let p : PrimeSpectrum B := ⟨q.under B, inferInstance⟩
  let R : Type u := Localization.AtPrime p.asIdeal
  let G : Type u := N ≃ₐ[K] N
  letI : IsDiscreteValuationRing R := heightOne_isDiscreteValuationRing p hq
  letI : IsFractionRing R K := primeLocalization_isFractionRing B p
  letI : Algebra R L := localBaseChangePrimeExtensionAlgebra B L p
  letI : Algebra R N := localBaseChangePrimeExtensionAlgebra B N p
  letI : IsScalarTower B R L := primeLocalizationExtension_isScalarTower B L p
  letI : IsScalarTower B R N := primeLocalizationExtension_isScalarTower B N p
  letI : IsScalarTower R K L := primeLocalizationExtension_fraction_isScalarTower B L p
  letI : IsScalarTower R K N := primeLocalizationExtension_fraction_isScalarTower B N p
  let U : Type u := primeBaseNormalization B N p
  let V : Type u := primeBaseNormalization B L p
  letI : Algebra T U := primeBaseNormalizationAlgebra B N p
  letI : Algebra S V := primeBaseNormalizationAlgebra B L p
  letI : IsScalarTower B T U := integralClosureBaseChange_base_isScalarTower B R N
  letI : IsScalarTower B S V := integralClosureBaseChange_base_isScalarTower B R L
  letI : IsScalarTower T U N := integralClosureBaseChange_isScalarTower B R N
  letI : IsScalarTower S V L := integralClosureBaseChange_isScalarTower B R L
  let MT := Algebra.algebraMapSubmonoid T p.asIdeal.primeCompl
  let MS := Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl
  letI : IsLocalization MT U := primeBaseNormalization_isLocalization B N p
  letI : IsLocalization MS V := primeBaseNormalization_isLocalization B L p
  letI : IsDedekindDomain U := primeBaseNormalization_isDedekindDomain B N p hq
  letI : IsDedekindDomain V := primeBaseNormalization_isDedekindDomain B L p hq
  letI : Module.Finite R U := primeBaseNormalization_finite B N p hq
  letI : Module.Finite R V := primeBaseNormalization_finite B L p hq
  letI : Module.IsTorsionFree R V := primeBaseNormalization_isTorsionFree B L p
  letI : SMulCommClass G R N := primeLocalizationExtension_galoisCommutes B N p
  letI : Algebra V U := markedIntermediateNormalizationAlgebra R K L N ι
  letI : IsScalarTower R V U := IsScalarTower.of_algebraMap_eq (fun r => by
    apply Subtype.ext
    exact ((ι.restrictScalars R).commutes r).symm)
  letI : Module.Finite V U := Module.Finite.of_restrictScalars_finite R V U
  let f := (ι.restrictScalars B).mapIntegralClosure
  let f' := (ι.restrictScalars R).mapIntegralClosure
  let Q : Ideal U := q.map (algebraMap T U)
  let P : Ideal V := Q.comap f'.toRingHom
  let m : Ideal R := p.asIdeal.map (algebraMap B R)
  have hdisjoint : Disjoint (MT : Set T) (q : Set T) :=
    Ideal.disjoint_primeCompl_of_liesOver q p.asIdeal
  letI : Q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint MT U q inferInstance hdisjoint
  have hQ : Q.under T = q :=
    IsLocalization.comap_map_of_isPrime_disjoint MT U inferInstance hdisjoint
  letI : Q.LiesOver m :=
    IsLocalization.liesOver_of_isPrime_of_disjoint
      (R' := R) (S' := U) p.asIdeal.primeCompl MT p.asIdeal hdisjoint
  letI : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (P := Q) (p := m)
  letI : P.IsPrime := Ideal.comap_isPrime f'.toRingHom Q
  letI : Q.LiesOver P := ⟨rfl⟩
  letI : P.LiesOver m := Ideal.LiesOver.tower_bot Q P m
  letI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (P := P) (p := m)
  have hm : m = IsLocalRing.maximalIdeal R :=
    IsLocalization.AtPrime.map_eq_maximalIdeal p.asIdeal R
  have hm0 : m ≠ ⊥ := by rw [hm]; exact IsDiscreteValuationRing.not_a_field R
  have hp0 : p.asIdeal ≠ ⊥ := by
    intro hp
    have hheight : p.asIdeal.height = 1 := by
      rw [Ideal.height_eq_primeHeight]
      exact hq
    simp [hp] at hheight
  have hP : P.under S = q.comap f.toRingHom := by
    change (Q.comap f'.toRingHom).comap (algebraMap S V) = q.comap f.toRingHom
    rw [Ideal.comap_comap]
    have hsquare : f'.toRingHom.comp (algebraMap S V) =
        (algebraMap T U).comp f.toRingHom := by ext x; rfl
    rw [hsquare, ← Ideal.comap_comap]
    change (Q.under T).comap f.toRingHom = _
    rw [hQ]
  letI : CharZero m.ResidueField := Algebra.charZero_of_charZero k m.ResidueField
  letI : CharZero P.ResidueField :=
    charZero_of_injective_algebraMap (algebraMap m.ResidueField P.ResidueField).injective
  letI : Algebra.IsSeparable m.ResidueField Q.ResidueField := inferInstance
  letI : Algebra.IsSeparable P.ResidueField Q.ResidueField := inferInstance
  letI : Algebra.IsSeparable (R ⧸ m) (U ⧸ Q) := inferInstance
  letI : Algebra.IsSeparable (V ⧸ P) (U ⧸ Q) := inferInstance
  have hI : Q.inertia G = q.inertia G := by
    rw [inertia_eq_of_equivariant_localization (R := T) (S := U) (G := G)
      MT Q (fun _ _ => rfl)]
    change (Q.under T).inertia G = _
    rw [hQ]
  have hlocal : localRamificationIndex (R := B) (S := S) (q.comap f.toRingHom) =
      localRamificationIndex (R := B) (S := V) P := by
    simpa only [hP] using
      (localRamificationIndex_under_of_isLocalization (B := B) MS P)
  rw [hlocal]
  haveI : P.LiesOver (IsLocalRing.maximalIdeal R) := hm ▸ inferInstanceAs (P.LiesOver m)
  rw [localRamificationIndex_localizedBase p.asIdeal hp0 P]
  exact (markedNormalization_localRamificationIndex_eq R K L N ι m hm0 P Q).trans
    (congrArg (fun I => inertiaQuotientIndex I ι.fieldRange.fixingSubgroup) hI)

end

end CollisionIdeals
