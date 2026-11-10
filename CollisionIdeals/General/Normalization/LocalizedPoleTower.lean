import CollisionIdeals.General.Normalization.PolynomialTransverseLocalization
import CollisionIdeals.General.Normalization.DVRPolePresentation
import CollisionIdeals.General.Normalization.TransversePoleStep
import Mathlib.RingTheory.Localization.AsSubring

/-!
# A transverse target partial constructs an actual local pole tower

At a target prime whose local ring is a DVR, a base derivation transverse
to a supplied element of the prime constructs unit numerators for all
iterated derivatives of a rational function with a pole there. The same
target prime remains a pole at every order. All localization algebras and
derivation extensions are canonical; no orbit or boundedness premise is
supplied.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

variable {k B K : Type*} [Field k] [CharZero k] [CommRing B] [IsDomain B]
  [Field K] [Algebra k B] [Algebra k K] [Algebra B K]
  [IsFractionRing B K] [IsScalarTower k B K]

/-- A pole at a target DVR has a unit numerator at every successive
derivative order for a transverse localized base derivation. The local
algebra in the conclusion is the canonical map to the fraction field. -/
theorem exists_localized_unit_pole_tower
    (dB : Derivation k B B) (p : PrimeSpectrum B)
    (hDVR : IsDiscreteValuationRing (Localization.AtPrime p.asIdeal))
    (b : B) (hb : b ∈ p.asIdeal) (hdb : dB b ∉ p.asIdeal)
    (r : K) (hr : r ∉ Localization.subalgebra.ofField K p.asIdeal.primeCompl
      p.asIdeal.primeCompl_le_nonZeroDivisors) :
    ∃ m : ℕ, 0 < m ∧
      let R := Localization.AtPrime p.asIdeal
      letI : Algebra R K := IsLocalization.localizationAlgebraOfSubmonoidLe
        R K p.asIdeal.primeCompl (nonZeroDivisors B)
          p.asIdeal.primeCompl_le_nonZeroDivisors
      ∀ n : ℕ, ∃ u : R, IsUnit u ∧
        ((localizationDerivation (nonZeroDivisors B) K dB : K → K)^[n]) r =
          algebraMap R K u / algebraMap B K b ^ (m + n) ∧
        ((localizationDerivation (nonZeroDivisors B) K dB : K → K)^[n]) r ∉
          Localization.subalgebra.ofField K p.asIdeal.primeCompl
            p.asIdeal.primeCompl_le_nonZeroDivisors := by
  let R := Localization.AtPrime p.asIdeal
  letI : IsDiscreteValuationRing R := hDVR
  letI : Algebra R K := IsLocalization.localizationAlgebraOfSubmonoidLe
    R K p.asIdeal.primeCompl (nonZeroDivisors B)
      p.asIdeal.primeCompl_le_nonZeroDivisors
  letI : IsScalarTower B R K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      R K p.asIdeal.primeCompl (nonZeroDivisors B)
        p.asIdeal.primeCompl_le_nonZeroDivisors
  letI : IsScalarTower k R K := IsScalarTower.of_algebraMap_eq fun c => by
    calc
      algebraMap k K c = algebraMap B K (algebraMap k B c) :=
        IsScalarTower.algebraMap_apply k B K c
      _ = algebraMap R K (algebraMap B R (algebraMap k B c)) :=
        IsScalarTower.algebraMap_apply B R K _
      _ = algebraMap R K (algebraMap k R c) := by
        rw [← IsScalarTower.algebraMap_apply k B R]
  letI : IsFractionRing R K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.asIdeal.primeCompl R K
  let dR : @Derivation k R R _ _ _ _ Semiring.toModule Algebra.toModule :=
    localizationDerivation p.asIdeal.primeCompl R dB
  let dK : @Derivation k K K _ _ _ _ Semiring.toModule Algebra.toModule :=
    localizationDerivation (nonZeroDivisors B) K dB
  let f : R := algebraMap B R b
  have hRange (x : K) : x ∈ Set.range (algebraMap R K) ↔
      x ∈ Localization.subalgebra.ofField K p.asIdeal.primeCompl
        p.asIdeal.primeCompl_le_nonZeroDivisors := by
    exact Localization.subalgebra.mem_range_mapToFractionRing_iff_ofField
      K p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors R x
  have hf : f ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff R p.asIdeal b).mpr hb
  have hUnit : IsUnit (dR f) := by
    change IsUnit (localizationDerivation p.asIdeal.primeCompl R dB (algebraMap B R b))
    rw [localizationDerivation_algebraMap]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff R p.asIdeal _).mpr hdb
  have hrR : r ∉ Set.range (algebraMap R K) := fun h => hr ((hRange r).mp h)
  obtain ⟨m, u, hm, hu, hPresentation⟩ :=
    exists_unit_pole_presentation_of_isUnit_derivation (R := R) (K := K)
      dR hf hUnit r hrR
  have hb0 : b ≠ 0 := by
    intro h
    apply hdb
    rw [h, map_zero]
    exact p.asIdeal.zero_mem
  have hfK : algebraMap R K f ≠ 0 := by
    simpa only [f, ← IsScalarTower.algebraMap_apply B R K, map_zero] using
      (IsFractionRing.injective B K).ne hb0
  have hExtend : ∀ a : R, dK (algebraMap R K a) = algebraMap R K (dR a) := by
    intro a
    exact localizationDerivation_algebraMap_of_tower
      p.asIdeal.primeCompl R (nonZeroDivisors B) K dB a
  have hTowers := exists_unit_iterated_transverse_pole_numerator
    (R := R) (K := K) dR dK hExtend hf hfK hUnit hu m hm
  refine ⟨m, hm, ?_⟩
  change ∀ n : ℕ, ∃ u_n : R, IsUnit u_n ∧
    ((dK : K → K)^[n]) r =
      algebraMap R K u_n / algebraMap B K b ^ (m + n) ∧
    ((dK : K → K)^[n]) r ∉
      Localization.subalgebra.ofField K p.asIdeal.primeCompl
        p.asIdeal.primeCompl_le_nonZeroDivisors
  intro n
  obtain ⟨u_n, hu_n, hIterate⟩ := hTowers n
  have hCalc : ((dK : K → K)^[n]) r =
      algebraMap R K u_n / algebraMap R K f ^ (m + n) := by
    rw [hPresentation]
    exact hIterate
  refine ⟨u_n, hu_n, ?_, ?_⟩
  · simpa only [f, ← IsScalarTower.algebraMap_apply B R K] using hCalc
  · apply mt (hRange _).mpr
    rw [hCalc]
    exact unit_pole_not_mem_range (R := R) (K := K) hf hfK hu_n (m + n)
      (lt_of_lt_of_le hm (Nat.le_add_right m n))

end

end CollisionIdeals
