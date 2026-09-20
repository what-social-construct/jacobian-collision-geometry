import CollisionIdeals.General.Galois.RamificationIndex
import CollisionIdeals.General.Normalization.DivisorialInertia
import CollisionIdeals.General.Normalization.LocalBaseChange

/-!
# Ramification at normalization divisors

Localization of the coordinate-image base supplies the finite Dedekind
model for the inertia criterion. The local ring at a normalization divisor
is unchanged by this preliminary localization.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

noncomputable section

section Localization

variable {B T S : Type*} [CommRing B] [CommRing T] [CommRing S]
  [Algebra B T] [Algebra B S] [Algebra T S] [IsScalarTower B T S]

/-- Preliminary localization does not change the local ring at a prime.
The equivalence is over the original ring, so it also respects any supplied
scalar base. -/
def primeLocalizationEquivOfLocalization
    (M : Submonoid T) [IsLocalization M S] (Q : Ideal S) [Q.IsPrime] :
    Localization.AtPrime Q ≃ₐ[T] Localization.AtPrime (Q.under T) := by
  letI : IsLocalization.AtPrime (Localization.AtPrime Q) (Q.under T) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      M (Localization.AtPrime Q) Q
  exact IsLocalization.algEquiv (Q.under T).primeCompl
    (Localization.AtPrime Q) (Localization.AtPrime (Q.under T))

/-- A further prime localization has the same local ring before and after
preliminary localization, so unramifiedness contracts along that map. -/
theorem isUnramifiedAt_under_of_isLocalization
    (M : Submonoid T) [IsLocalization M S]
    (Q : Ideal S) [Q.IsPrime] [Algebra.IsUnramifiedAt B Q] :
    Algebra.IsUnramifiedAt B (Q.under T) := by
  exact Algebra.FormallyUnramified.of_equiv
    ((primeLocalizationEquivOfLocalization M Q).restrictScalars B)

variable {B' : Type*} [CommRing B'] [Algebra B B'] [Algebra B' S]
  [IsScalarTower B B' S] [Algebra.FormallyUnramified B B']

/-- The local criterion over a localized base implies the original
criterion; formal unramifiedness composes with base localization. -/
theorem isUnramifiedAt_under_of_localizedBase
    (M : Submonoid T) [IsLocalization M S]
    (Q : Ideal S) [Q.IsPrime] [Algebra.IsUnramifiedAt B' Q] :
    Algebra.IsUnramifiedAt B (Q.under T) := by
  letI : Algebra.IsUnramifiedAt B Q :=
    Algebra.FormallyUnramified.comp B B' (Localization.AtPrime Q)
  exact isUnramifiedAt_under_of_isLocalization (B := B) M Q

end Localization

section IntegralClosure

variable (k B N : Type*) [Field k] [CharZero k]
  [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B] [Algebra k B]
  [Field N] [Algebra (FractionRing B) N] [Algebra B N]
  [IsScalarTower B (FractionRing B) N]
  [FiniteDimensional (FractionRing B) N] [IsGalois (FractionRing B) N]

include k

set_option maxHeartbeats 800000 in
/-- In residue characteristic zero, ramification of a normalization prime
lying above a base divisor forces nontrivial inertia. The finite Dedekind
model is constructed by localizing the base, rather than supplied. -/
theorem integralClosure_inertia_ne_bot_of_not_isUnramifiedAt
    (q : Ideal (integralClosure B N)) [q.IsPrime]
    (hq : Ideal.primeHeight (R := B)
      (Ideal.under B (B := integralClosure B N) q) = 1)
    (hRam : ¬ Algebra.IsUnramifiedAt (A := integralClosure B N) B q) :
    Ideal.inertia (α := integralClosure B N) (N ≃ₐ[FractionRing B] N) q ≠ ⊥ := by
  let p : PrimeSpectrum B := ⟨q.under B, inferInstance⟩
  let Bp : Type _ := Localization.AtPrime p.asIdeal
  let T : Type _ := integralClosure B N
  let G : Type _ := N ≃ₐ[FractionRing B] N
  letI : IsDiscreteValuationRing Bp := heightOne_isDiscreteValuationRing p hq
  letI : Algebra Bp N := primeLocalizationExtensionAlgebra B N p
  letI : IsScalarTower B Bp N := primeLocalizationExtension_isScalarTower B N p
  letI : IsScalarTower Bp (FractionRing B) N :=
    primeLocalizationExtension_fraction_isScalarTower B N p
  let S : Type _ := primeBaseNormalization B N p
  letI : Algebra T S := primeBaseNormalizationAlgebra B N p
  letI : IsScalarTower T S N := integralClosureBaseChange_isScalarTower B Bp N
  letI : IsScalarTower B T S := integralClosureBaseChange_base_isScalarTower B Bp N
  let M : Submonoid T := Algebra.algebraMapSubmonoid T p.asIdeal.primeCompl
  letI : IsLocalization M S := primeBaseNormalization_isLocalization B N p
  letI : Module.Finite Bp S := primeBaseNormalization_finite B N p hq
  letI : IsDedekindDomain S := primeBaseNormalization_isDedekindDomain B N p hq
  letI : Module.IsTorsionFree Bp S := primeBaseNormalization_isTorsionFree B N p
  letI : SMulCommClass G Bp N := primeLocalizationExtension_galoisCommutes B N p
  letI : IsGaloisGroup G Bp S := primeBaseNormalization_isGaloisGroup B N p hq
  let Q : Ideal S := q.map (algebraMap T S)
  let mp : Ideal Bp := p.asIdeal.map (algebraMap B Bp)
  have hdisjoint : Disjoint (M : Set T) (q : Set T) :=
    Ideal.disjoint_primeCompl_of_liesOver q p.asIdeal
  letI : Q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M S q inferInstance hdisjoint
  have hQ : Q.under T = q :=
    IsLocalization.comap_map_of_isPrime_disjoint M S inferInstance hdisjoint
  letI : Q.LiesOver mp :=
    IsLocalization.liesOver_of_isPrime_of_disjoint
      (R' := Bp) (S' := S) p.asIdeal.primeCompl M p.asIdeal hdisjoint
  letI : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (p := mp) (P := Q)
  have hmp : mp ≠ ⊥ := by
    rw [show mp = IsLocalRing.maximalIdeal Bp from
      IsLocalization.AtPrime.map_eq_maximalIdeal p.asIdeal Bp]
    exact IsDiscreteValuationRing.not_a_field Bp
  letI : CharZero mp.ResidueField := Algebra.charZero_of_charZero k mp.ResidueField
  intro hInertia
  have hQInertia : Q.inertia G = ⊥ := by
    rw [inertia_eq_of_equivariant_localization (R := T) (S := S) (G := G)
      M Q (fun _ _ => rfl)]
    change (Q.under T).inertia G = ⊥
    rw [hQ]
    exact hInertia
  letI : Algebra.IsUnramifiedAt Bp Q :=
    (isUnramifiedAt_iff_idealInertia_eq_bot_of_residueCharZero
      (G := G) mp hmp Q).mpr hQInertia
  letI : Algebra.FormallyUnramified B Bp :=
    Algebra.FormallyUnramified.of_isLocalization p.asIdeal.primeCompl
  have hUnramified : Algebra.IsUnramifiedAt B (Q.under T) :=
    isUnramifiedAt_under_of_localizedBase (B' := Bp) M Q
  apply hRam
  simpa only [hQ] using hUnramified

end IntegralClosure

end

end CollisionIdeals
