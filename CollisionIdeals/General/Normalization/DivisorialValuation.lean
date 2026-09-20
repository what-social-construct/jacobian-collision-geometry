import CollisionIdeals.General.Normalization.Diagram
import CollisionIdeals.General.Normalization.Finiteness
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.KrullDimension.LocalRing

/-!
# Divisorial valuations of the normal-closure normalization

The localization of a normal Noetherian domain at a height-one prime is a
discrete valuation ring. Its valuation on the fraction field supplies the
actual centered valuation used by normalization diagrams. Restriction to
an algebraic subfield is again discrete.

This construction does not identify inertia with scheme-theoretic
ramification, nor construct the conjugate-sheet centers.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

noncomputable section

open scoped WithZero

section LocalRing

variable {T : Type*} [CommRing T] [IsDomain T]
  [IsNoetherianRing T] [IsIntegrallyClosed T]

/-- Height-one localizations of normal Noetherian domains are DVRs. -/
theorem heightOne_isDiscreteValuationRing
    (p : PrimeSpectrum T) (hp : p.asIdeal.primeHeight = 1) :
    IsDiscreteValuationRing (Localization.AtPrime p.asIdeal) := by
  let A := Localization.AtPrime p.asIdeal
  have hdim : ringKrullDim A = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal A,
      Ideal.height_eq_primeHeight, hp]
    simp
  haveI : IsIntegrallyClosed A :=
    isIntegrallyClosed_of_isLocalization A p.asIdeal.primeCompl
      p.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : Ring.DimensionLEOne A := ⟨fun {P} =>
    Ring.krullDimLE_one_iff_of_noZeroDivisors.mp
      (Ring.krullDimLE_iff.mpr (by simp [hdim])) P⟩
  haveI : IsDedekindDomain A := { }
  exact ((IsDiscreteValuationRing.TFAE A
    (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp hdim).1).out 0 2).mpr
      (show IsDedekindDomain A from inferInstance)

end LocalRing

section Restriction

variable {K N Γ : Type*} [Field K] [Field N] [Algebra K N]
  [Algebra.IsAlgebraic K N] [LinearOrderedCommGroupWithZero Γ]

/-- A nontrivial valuation remains nontrivial on an algebraic subfield. -/
theorem valuation_isNontrivial_comap_of_isAlgebraic
    (v : Valuation N Γ) [v.IsNontrivial] :
    (v.comap (algebraMap K N)).IsNontrivial := by
  rw [Valuation.IsNontrivial_iff_exists_one_lt]
  by_contra! h
  let V := v.valuationSubring
  let f : K →+* V :=
    (algebraMap K N).codRestrict V.toSubring (fun x => h x)
  have hcomp : (algebraMap V N).comp f =
      (RingHom.id N).comp (algebraMap K N) := by ext; rfl
  obtain ⟨x, hx⟩ := Valuation.IsNontrivial.exists_one_lt (v := v)
  have hxIntegral : IsIntegral V x :=
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral.map_of_comp_eq
      f (RingHom.id N) hcomp
  exact (not_le_of_gt hx)
    ((Valuation.valuationSubring.integers v).isIntegral_iff_v_le_one.mp hxIntegral)

end Restriction

section Center

variable {T K N : Type*} [CommRing T] [IsDomain T]
  [IsNoetherianRing T] [IsIntegrallyClosed T]
  [Field K] [Field N] [Algebra K N] [Algebra.IsAlgebraic K N]
  [Algebra T N] [IsFractionRing T N]

/-- The valuation of a height-one localization, retaining its identification
with that localization. The equivalence commutes with the maps to the fraction
field, and its maximal ideal contracts to the original prime. -/
theorem exists_centered_discreteValuationTower_with_localization
    (p : PrimeSpectrum T) (hp : p.asIdeal.primeHeight = 1) :
    ∃ (V : DiscreteValuationTower K (N := N))
      (e : Localization.AtPrime p.asIdeal ≃+* V.valuationRing),
      (∀ x, ((e (algebraMap T (Localization.AtPrime p.asIdeal) x) :
        V.valuationRing) : N) = algebraMap T N x) ∧
        (IsLocalRing.maximalIdeal V.valuationRing).comap
          (e.toRingHom.comp (algebraMap T (Localization.AtPrime p.asIdeal))) =
            p.asIdeal := by
  let A := Localization.AtPrime p.asIdeal
  letI : IsDiscreteValuationRing A := heightOne_isDiscreteValuationRing p hp
  letI : Algebra A N := IsLocalization.localizationAlgebraOfSubmonoidLe
    A N p.asIdeal.primeCompl (nonZeroDivisors T) p.asIdeal.primeCompl_le_nonZeroDivisors
  letI : IsScalarTower T A N := IsLocalization.localization_isScalarTower_of_submonoid_le
    A N p.asIdeal.primeCompl (nonZeroDivisors T) p.asIdeal.primeCompl_le_nonZeroDivisors
  letI : IsFractionRing A N :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.asIdeal.primeCompl A N
  let v := (IsDiscreteValuationRing.maximalIdeal A).valuation N
  letI : (v.comap (algebraMap K N)).IsNontrivial :=
    valuation_isNontrivial_comap_of_isAlgebraic v
  let V : DiscreteValuationTower K (N := N) := {
    valuationRing := v.valuationSubring
    topDiscrete := inferInstance
    baseDiscrete := show IsDiscreteValuationRing (v.comap (algebraMap K N)).valuationSubring
      from inferInstance }
  let e : A ≃+* v.valuationSubring := IsDiscreteValuationRing.equivValuationSubring
  refine ⟨V, e, ?_, ?_⟩
  · intro x
    change algebraMap A N (algebraMap T A x) = algebraMap T N x
    exact (IsScalarTower.algebraMap_apply T A N x).symm
  · ext x
    change e (algebraMap T A x) ∈ IsLocalRing.maximalIdeal v.valuationSubring ↔ x ∈ p.asIdeal
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MulEquiv.isUnit_map e]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff A p.asIdeal x

/-- The valuation of a height-one localization is centered at the original
prime, and its restriction to any algebraic subfield is also a DVR. -/
theorem exists_centered_discreteValuationTower
    (p : PrimeSpectrum T) (hp : p.asIdeal.primeHeight = 1) :
    ∃ (V : DiscreteValuationTower K (N := N))
      (centerMap : T →+* V.valuationRing),
      (∀ x, ((centerMap x : V.valuationRing) : N) = algebraMap T N x) ∧
        (IsLocalRing.maximalIdeal V.valuationRing).comap centerMap = p.asIdeal := by
  obtain ⟨V, e, he, hp⟩ :=
    exists_centered_discreteValuationTower_with_localization (K := K) (N := N) p hp
  exact ⟨V, e.toRingHom.comp (algebraMap T (Localization.AtPrime p.asIdeal)), he, hp⟩

end Center

section Polynomial

universe u

variable {k : Type u} [Field k] {n : ℕ} {F : PolynomialSelfMap k n}
  {N : Type u} [Field N] [Algebra (PolynomialMapBaseFunctionField F) N]
  [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]

local instance divisorialBaseAlgebra : Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

set_option maxHeartbeats 800000 in
/-- Every height-one point of the finite normal-closure normalization has
a centered discrete valuation tower whose valuation ring is the local ring
at that point, compatibly with the embedding into the normal closure. -/
theorem exists_polynomialValuationCenteredAt_with_localization
    (D : PolynomialNormalClosureData F N)
    (p : PrimeSpectrum (PolynomialNormalizationInExtensionRing (F := F) (N := N)))
    (hp : Ideal.primeHeight
      (R := PolynomialNormalizationInExtensionRing (F := F) (N := N)) p.asIdeal = 1) :
    ∃ V : DiscreteValuationTower (PolynomialMapBaseFunctionField F) (N := N),
      ∃ e : Localization.AtPrime p.asIdeal ≃+* V.valuationRing,
        (∀ x : PolynomialNormalizationInExtensionRing (F := F) (N := N),
          ((e (algebraMap _ (Localization.AtPrime p.asIdeal) x) :
            V.valuationRing) : N) = (x : N)) ∧
        (IsLocalRing.maximalIdeal V.valuationRing).comap
          (e.toRingHom.comp (algebraMap _ (Localization.AtPrime p.asIdeal))) =
            p.asIdeal := by
  let B := PolynomialImageAlgebra F
  let K := PolynomialMapBaseFunctionField F
  let T := PolynomialNormalizationInExtensionRing (F := F) (N := N)
  letI algebraBK : Algebra B K := OreLocalization.instAlgebra
  letI : SMul B K := algebraBK.toSMul
  letI : Algebra B N := polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI : IsScalarTower B K N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : FiniteDimensional K N := D.finiteNormal
  letI : IsNoetherianRing B := polynomialImageAlgebra_isNoetherianRing F
  letI : Module.Finite B T := polynomialNormalClosureNormalization_finite D
  letI : IsNoetherianRing T := IsNoetherianRing.of_finite B T
  letI : IsIntegrallyClosed T := integralClosure.isIntegrallyClosedOfFiniteExtension K
  letI : IsFractionRing T N := integralClosure.isFractionRing_of_finite_extension K N
  exact exists_centered_discreteValuationTower_with_localization
    (T := T) (K := K) (N := N) p hp

/-- Every height-one point of the finite normal-closure normalization has
an actual centered discrete valuation tower. No étale or open-immersion
hypothesis is needed. -/
theorem exists_polynomialValuationCenteredAt
    (D : PolynomialNormalClosureData F N)
    (p : PrimeSpectrum (PolynomialNormalizationInExtensionRing (F := F) (N := N)))
    (hp : Ideal.primeHeight
      (R := PolynomialNormalizationInExtensionRing (F := F) (N := N)) p.asIdeal = 1) :
    ∃ V : DiscreteValuationTower (PolynomialMapBaseFunctionField F) (N := N),
      PolynomialValuationCenteredAt V p := by
  obtain ⟨V, e, he, hp⟩ := exists_polynomialValuationCenteredAt_with_localization D p hp
  exact ⟨V, e.toRingHom.comp (algebraMap _ (Localization.AtPrime p.asIdeal)), he, hp⟩

/-- The divisorial valuation tower of the normal-closure normalization at
a height-one prime. -/
def polynomialDivisorialValuation
    (D : PolynomialNormalClosureData F N)
    (p : PrimeSpectrum (PolynomialNormalizationInExtensionRing (F := F) (N := N)))
    (hp : Ideal.primeHeight
      (R := PolynomialNormalizationInExtensionRing (F := F) (N := N)) p.asIdeal = 1) :
    DiscreteValuationTower (PolynomialMapBaseFunctionField F) (N := N) :=
  (exists_polynomialValuationCenteredAt_with_localization D p hp).choose

/-- The local ring at a divisor is the valuation ring of the constructed
divisorial valuation, not merely a ring with the same center. -/
def polynomialDivisorialValuationLocalizationEquiv
    (D : PolynomialNormalClosureData F N)
    (p : PrimeSpectrum (PolynomialNormalizationInExtensionRing (F := F) (N := N)))
    (hp : Ideal.primeHeight
      (R := PolynomialNormalizationInExtensionRing (F := F) (N := N)) p.asIdeal = 1) :
    Localization.AtPrime p.asIdeal ≃+*
      (polynomialDivisorialValuation D p hp).valuationRing :=
  (exists_polynomialValuationCenteredAt_with_localization D p hp).choose_spec.choose

/-- The localization equivalence respects the normalization's embedding
in its fraction field. -/
theorem polynomialDivisorialValuationLocalizationEquiv_algebraMap
    (D : PolynomialNormalClosureData F N)
    (p : PrimeSpectrum (PolynomialNormalizationInExtensionRing (F := F) (N := N)))
    (hp : Ideal.primeHeight
      (R := PolynomialNormalizationInExtensionRing (F := F) (N := N)) p.asIdeal = 1)
    (x : PolynomialNormalizationInExtensionRing (F := F) (N := N)) :
    ((polynomialDivisorialValuationLocalizationEquiv D p hp
      (algebraMap _ (Localization.AtPrime p.asIdeal) x) :
      (polynomialDivisorialValuation D p hp).valuationRing) : N) = (x : N) :=
  (exists_polynomialValuationCenteredAt_with_localization D p hp).choose_spec.choose_spec.1 x

/-- The normalization algebra structure on the constructed valuation ring,
transported through its local-ring equivalence. -/
def polynomialDivisorialValuationAlgebra
    (D : PolynomialNormalClosureData F N)
    (p : PrimeSpectrum (PolynomialNormalizationInExtensionRing (F := F) (N := N)))
    (hp : Ideal.primeHeight
      (R := PolynomialNormalizationInExtensionRing (F := F) (N := N)) p.asIdeal = 1) :
    Algebra (PolynomialNormalizationInExtensionRing (F := F) (N := N))
      (polynomialDivisorialValuation D p hp).valuationRing :=
  ((polynomialDivisorialValuationLocalizationEquiv D p hp).toRingHom.comp
    (algebraMap _ (Localization.AtPrime p.asIdeal))).toAlgebra

/-- The constructed valuation ring is a localization of the normalization
at the defining prime, with the displayed normalization algebra structure. -/
theorem polynomialDivisorialValuation_isLocalizationAtPrime
    (D : PolynomialNormalClosureData F N)
    (p : PrimeSpectrum (PolynomialNormalizationInExtensionRing (F := F) (N := N)))
    (hp : Ideal.primeHeight
      (R := PolynomialNormalizationInExtensionRing (F := F) (N := N)) p.asIdeal = 1) :
    letI := polynomialDivisorialValuationAlgebra D p hp
    IsLocalization.AtPrime (polynomialDivisorialValuation D p hp).valuationRing
      p.asIdeal := by
  letI := polynomialDivisorialValuationAlgebra D p hp
  exact (IsLocalization.isLocalization_iff_of_ringEquiv p.asIdeal.primeCompl
    (polynomialDivisorialValuationLocalizationEquiv D p hp)).mp inferInstance

/-- The local-ring algebra structure is compatible with the original
normalization embedding into the normal-closure field. -/
theorem polynomialDivisorialValuation_isScalarTower
    (D : PolynomialNormalClosureData F N)
    (p : PrimeSpectrum (PolynomialNormalizationInExtensionRing (F := F) (N := N)))
    (hp : Ideal.primeHeight
      (R := PolynomialNormalizationInExtensionRing (F := F) (N := N)) p.asIdeal = 1) :
    letI := polynomialDivisorialValuationAlgebra D p hp
    IsScalarTower (PolynomialNormalizationInExtensionRing (F := F) (N := N))
      (polynomialDivisorialValuation D p hp).valuationRing N := by
  letI := polynomialDivisorialValuationAlgebra D p hp
  apply IsScalarTower.of_algebraMap_eq
  intro x
  exact (polynomialDivisorialValuationLocalizationEquiv_algebraMap D p hp x).symm

/-- The constructed divisorial valuation is centered at its defining prime. -/
theorem polynomialDivisorialValuation_centered
    (D : PolynomialNormalClosureData F N)
    (p : PrimeSpectrum (PolynomialNormalizationInExtensionRing (F := F) (N := N)))
    (hp : Ideal.primeHeight
      (R := PolynomialNormalizationInExtensionRing (F := F) (N := N)) p.asIdeal = 1) :
    PolynomialValuationCenteredAt (polynomialDivisorialValuation D p hp) p := by
  refine ⟨(polynomialDivisorialValuationLocalizationEquiv D p hp).toRingHom.comp
    (algebraMap _ (Localization.AtPrime p.asIdeal)), ?_, ?_⟩
  · exact polynomialDivisorialValuationLocalizationEquiv_algebraMap D p hp
  · exact
      (exists_polynomialValuationCenteredAt_with_localization D p hp).choose_spec.choose_spec.2

end Polynomial

end

end CollisionIdeals
