import CollisionIdeals.General.Normalization.DivisorialValuation
import Mathlib.RingTheory.Localization.Integral
import Mathlib.FieldTheory.Galois.IsGaloisGroup

/-!
# Normalization after localization of the base

Localizing the base at a height-one prime produces a DVR. Its integral
closure in the finite separable function-field extension is a finite
Dedekind algebra, obtained by localizing the original normalization. This
is the semilocal ring on which the full Galois group acts; a single prime
localization need only be preserved by its decomposition subgroup.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

noncomputable section

section IntegralClosureBaseChange

variable (B B' N : Type*) [CommRing B] [CommRing B'] [Field N]
  [Algebra B B'] [Algebra B N] [Algebra B' N] [IsScalarTower B B' N]

/-- The canonical map of integral closures under extension of the base. -/
def integralClosureBaseChangeMap : integralClosure B N →+* integralClosure B' N where
  toFun x := ⟨x, x.property.tower_top⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Scalar structure on the new integral closure from the old one. -/
abbrev integralClosureBaseChangeAlgebra :
    Algebra (integralClosure B N) (integralClosure B' N) :=
  (integralClosureBaseChangeMap B B' N).toAlgebra

local instance localBaseChangeIntegralClosureAlgebra :
    Algebra (integralClosure B N) (integralClosure B' N) :=
  integralClosureBaseChangeAlgebra B B' N

/-- The integral-closure base-change map commutes with both inclusions. -/
theorem integralClosureBaseChange_isScalarTower :
    IsScalarTower (integralClosure B N) (integralClosure B' N) N :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The same map is compatible with the original base. -/
theorem integralClosureBaseChange_base_isScalarTower :
    IsScalarTower B (integralClosure B N) (integralClosure B' N) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Integral closure commutes with localization of the base inside a
field, where every nonzero denominator is already invertible. -/
theorem integralClosureBaseChange_isLocalization
    [IsDomain B] (M : Submonoid B)
    [IsLocalization M B'] (hM : M ≤ nonZeroDivisors B)
    (hinj : Function.Injective (algebraMap B N)) :
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure B N) M)
      (integralClosure B' N) := by
  letI := integralClosureBaseChange_isScalarTower B B' N
  letI := integralClosureBaseChange_base_isScalarTower B B' N
  letI : IsLocalization (Algebra.algebraMapSubmonoid N M) N :=
    IsLocalization.at_units _ (by
      rintro _ ⟨r, hr, rfl⟩
      exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ hinj).mpr
        (mem_nonZeroDivisors_iff_ne_zero.mp (hM hr))))
  exact IsLocalization.integralClosure M

end IntegralClosureBaseChange

section PrimeBase

variable (B N : Type*) [CommRing B] [IsDomain B] [Field N]
  [Algebra (FractionRing B) N] [Algebra B N]
  [IsScalarTower B (FractionRing B) N]

/-- The canonical action of the prime localization on the field extension. -/
abbrev primeLocalizationExtensionAlgebra (p : PrimeSpectrum B) :
    Algebra (Localization.AtPrime p.asIdeal) N :=
  ((algebraMap (FractionRing B) N).comp
    (algebraMap (Localization.AtPrime p.asIdeal) (FractionRing B))).toAlgebra

variable (p : PrimeSpectrum B)

local instance localBaseChangePrimeExtensionAlgebra :
    Algebra (Localization.AtPrime p.asIdeal) N :=
  primeLocalizationExtensionAlgebra B N p

/-- Compatibility of the localized base with the original base map. -/
theorem primeLocalizationExtension_isScalarTower :
    IsScalarTower B (Localization.AtPrime p.asIdeal) N := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change algebraMap B N r = algebraMap (FractionRing B) N
    (algebraMap (Localization.AtPrime p.asIdeal) (FractionRing B)
      (algebraMap B (Localization.AtPrime p.asIdeal) r))
  rw [← IsScalarTower.algebraMap_apply B (Localization.AtPrime p.asIdeal)
    (FractionRing B), ← IsScalarTower.algebraMap_apply B (FractionRing B) N]

omit [Algebra B N] [IsScalarTower B (FractionRing B) N] in
/-- Compatibility through the original function field. -/
theorem primeLocalizationExtension_fraction_isScalarTower :
    IsScalarTower (Localization.AtPrime p.asIdeal) (FractionRing B) N :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

local instance localBaseChangePrimeExtensionTower :
    IsScalarTower B (Localization.AtPrime p.asIdeal) N :=
  primeLocalizationExtension_isScalarTower B N p

local instance localBaseChangeFractionExtensionTower :
    IsScalarTower (Localization.AtPrime p.asIdeal) (FractionRing B) N :=
  primeLocalizationExtension_fraction_isScalarTower B N p

/-- The normalization over the localized base. It retains all primes
above the base prime, rather than choosing a decomposition-group sheet. -/
abbrev primeBaseNormalization :=
  integralClosure (Localization.AtPrime p.asIdeal) N

/-- The localized-base normalization carries the original normalization's
canonical algebra structure. -/
abbrev primeBaseNormalizationAlgebra :
    Algebra (integralClosure B N) (primeBaseNormalization B N p) :=
  integralClosureBaseChangeAlgebra B (Localization.AtPrime p.asIdeal) N

local instance localBaseChangePrimeNormalizationAlgebra :
    Algebra (integralClosure B N) (primeBaseNormalization B N p) :=
  primeBaseNormalizationAlgebra B N p

/-- This ring is the localization of the original normalization away from
the chosen base prime. -/
theorem primeBaseNormalization_isLocalization :
    IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure B N) p.asIdeal.primeCompl)
      (primeBaseNormalization B N p) :=
  integralClosureBaseChange_isLocalization B (Localization.AtPrime p.asIdeal) N
    p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors
    (algebraMap_injective_of_field_isFractionRing B N (FractionRing B) N)

variable [IsNoetherianRing B] [IsIntegrallyClosed B]
variable [FiniteDimensional (FractionRing B) N]
variable [Algebra.IsSeparable (FractionRing B) N]

omit [IsNoetherianRing B] [IsIntegrallyClosed B] in
/-- The fraction field of the localized base is still the original field. -/
theorem primeLocalization_isFractionRing :
    IsFractionRing (Localization.AtPrime p.asIdeal) (FractionRing B) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal) (FractionRing B)

local instance localBaseChangePrimeFractionRing :
    IsFractionRing (Localization.AtPrime p.asIdeal) (FractionRing B) :=
  primeLocalization_isFractionRing B p

omit [Algebra B N] [IsScalarTower B (FractionRing B) N] in
/-- Finiteness survives normalization over a height-one localized base. -/
theorem primeBaseNormalization_finite (hp : p.asIdeal.primeHeight = 1) :
    Module.Finite (Localization.AtPrime p.asIdeal) (primeBaseNormalization B N p) := by
  letI := heightOne_isDiscreteValuationRing p hp
  exact IsIntegralClosure.finite (Localization.AtPrime p.asIdeal)
    (FractionRing B) N (primeBaseNormalization B N p)

omit [Algebra B N] [IsScalarTower B (FractionRing B) N] in
/-- The localized-base normalization is Dedekind. -/
theorem primeBaseNormalization_isDedekindDomain (hp : p.asIdeal.primeHeight = 1) :
    IsDedekindDomain (primeBaseNormalization B N p) := by
  letI := heightOne_isDiscreteValuationRing p hp
  exact integralClosure.isDedekindDomain (Localization.AtPrime p.asIdeal)
    (FractionRing B) N

omit [Algebra B N] [IsScalarTower B (FractionRing B) N]
  [IsNoetherianRing B] [IsIntegrallyClosed B]
  [Algebra.IsSeparable (FractionRing B) N] in
/-- Its fraction field is the original extension field. -/
theorem primeBaseNormalization_isFractionRing :
    IsFractionRing (primeBaseNormalization B N p) N :=
  integralClosure.isFractionRing_of_finite_extension (FractionRing B) N

omit [Algebra B N] [IsScalarTower B (FractionRing B) N]
  [IsNoetherianRing B] [IsIntegrallyClosed B]
  [FiniteDimensional (FractionRing B) N] [Algebra.IsSeparable (FractionRing B) N] in
/-- The finite Dedekind algebra has no base torsion. -/
theorem primeBaseNormalization_isTorsionFree :
    Module.IsTorsionFree (Localization.AtPrime p.asIdeal)
      (primeBaseNormalization B N p) := by
  letI : Module.IsTorsionFree (Localization.AtPrime p.asIdeal) N :=
    .trans_faithfulSMul (Localization.AtPrime p.asIdeal) (FractionRing B) N
  exact IsIntegralClosure.isTorsionFree (Localization.AtPrime p.asIdeal) N

omit [Algebra B N] [IsScalarTower B (FractionRing B) N]
  [IsNoetherianRing B] [IsIntegrallyClosed B]
  [FiniteDimensional (FractionRing B) N] [Algebra.IsSeparable (FractionRing B) N] in
/-- Every function-field automorphism fixes the localized base, so acts on
its integral closure. -/
theorem primeLocalizationExtension_galoisCommutes :
    SMulCommClass (N ≃ₐ[FractionRing B] N) (Localization.AtPrime p.asIdeal) N := by
  constructor
  intro g r x
  change g (algebraMap (FractionRing B) N
      (algebraMap (Localization.AtPrime p.asIdeal) (FractionRing B) r) * x) =
    algebraMap (FractionRing B) N
      (algebraMap (Localization.AtPrime p.asIdeal) (FractionRing B) r) * g x
  rw [map_mul, g.commutes]

local instance localBaseChangeGaloisCommutes :
    SMulCommClass (N ≃ₐ[FractionRing B] N) (Localization.AtPrime p.asIdeal) N :=
  primeLocalizationExtension_galoisCommutes B N p

/-- The full field-automorphism group acts on the semilocal normalization. -/
abbrev primeBaseNormalizationGaloisAction :
    MulSemiringAction (N ≃ₐ[FractionRing B] N) (primeBaseNormalization B N p) :=
  inferInstance

omit [Algebra.IsSeparable (FractionRing B) N] in
/-- Galois invariance descends from the function fields to the finite
Dedekind normalization over the localized base. -/
theorem primeBaseNormalization_isGaloisGroup [IsGalois (FractionRing B) N]
    (hp : p.asIdeal.primeHeight = 1) :
    IsGaloisGroup (N ≃ₐ[FractionRing B] N)
      (Localization.AtPrime p.asIdeal) (primeBaseNormalization B N p) := by
  letI := heightOne_isDiscreteValuationRing p hp
  letI := primeBaseNormalization_isFractionRing B N p
  exact IsGaloisGroup.of_isFractionRing (N ≃ₐ[FractionRing B] N)
    (Localization.AtPrime p.asIdeal) (primeBaseNormalization B N p) (FractionRing B) N

end PrimeBase

end

end CollisionIdeals
