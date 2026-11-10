import CollisionIdeals.General.Normalization.DVRPolePresentation
import CollisionIdeals.General.Normalization.LocalizedPoleTower
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual DVR pole towers escape every fixed finite module stage

A finite base submodule of a fraction field has a common nonzero
denominator in the local ring. In a DVR its order gives an upper bound
on the pole orders of every element of that stage, even after adding
arbitrary local-ring elements. A family with unit numerators and
successively increasing denominator powers therefore eventually escapes
each fixed finite stage, also modulo the base.

This does not put a Keller differential orbit into any one finite stage.
Finite generation of an algebra or of a function-field extension is not
such a statement.
-/

set_option autoImplicit false

namespace CollisionIdeals

section ClearingDenominators

variable {B R K : Type*} [CommRing B] [CommRing R] [IsDomain R]
  [Field K] [Algebra B R] [Algebra B K] [Algebra R K]
  [IsScalarTower B R K] [IsFractionRing R K]

/-- A finite base module stage has a common nonzero local denominator.
The base need not be Noetherian or a domain. -/
theorem exists_nonzero_clearing_denominator_of_finite_submodule
    (Λ : Submodule B K) [Module.Finite B Λ] :
    ∃ c : R, c ≠ 0 ∧
      ∀ x ∈ Λ, algebraMap R K c * x ∈ Set.range (algebraMap R K) := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.iff_fg.mp inferInstance : Λ.FG)
  obtain ⟨c, hc⟩ :=
    IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R) s
  refine ⟨c, nonZeroDivisors.coe_ne_zero c, ?_⟩
  intro x hx
  have hxSpan : x ∈ Submodule.span B (s : Set K) := by simpa only [hs] using hx
  clear hx
  induction hxSpan using Submodule.span_induction with
  | mem x hx => simpa only [Algebra.smul_def] using hc x hx
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb, mul_add]⟩
  | smul b x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨algebraMap B R b * a, ?_⟩
      rw [map_mul, ← IsScalarTower.algebraMap_apply B R K, ha, Algebra.smul_def]
      ring

end ClearingDenominators

section DVR

variable {B R K : Type*} [CommRing B] [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [Field K]
  [Algebra B R] [Algebra B K] [Algebra R K]
  [IsScalarTower B R K] [IsFractionRing R K]

/-- Every fixed finite base module stage has a bounded pole order at
the specified uniformizer, even modulo the entire local ring. The bound
is constructed from a common denominator, not assumed. -/
theorem exists_pole_order_bound_of_finite_submodule_mod_local
    {f : R} (hf : Irreducible f)
    (Λ : Submodule B K) [Module.Finite B Λ] :
    ∃ s : ℕ, ∀ (u : R), IsUnit u → ∀ l : ℕ,
      (∃ a ∈ Λ, ∃ v : R,
        algebraMap R K u / algebraMap R K f ^ l = a + algebraMap R K v) →
      l ≤ s := by
  obtain ⟨c, hc0, hc⟩ := exists_nonzero_clearing_denominator_of_finite_submodule
    (R := R) Λ
  obtain ⟨s, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hf
  refine ⟨s, ?_⟩
  intro u hu l h
  obtain ⟨a, ha, v, hEq⟩ := h
  obtain ⟨t, ht⟩ := hc a ha
  have hInteger : algebraMap R K (t + c * v) =
      algebraMap R K c * (algebraMap R K u / algebraMap R K f ^ l) := by
    rw [hEq, map_add, map_mul, ht, mul_add]
  have hfK : algebraMap R K f ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hf.ne_zero
  have hCross : algebraMap R K (t + c * v) * algebraMap R K f ^ l =
      algebraMap R K c * algebraMap R K u := by
    apply (eq_div_iff (pow_ne_zero l hfK)).mp
    simpa only [mul_div_assoc] using hInteger
  have hCrossR : c * u = (t + c * v) * f ^ l := by
    apply IsFractionRing.injective R K
    simpa only [map_mul, map_pow] using hCross.symm
  have hDiv : f ^ l ∣ c := (hu.dvd_mul_right).mp
    ⟨t + c * v, by rw [hCrossR, mul_comm]⟩
  have hPowers : f ^ l ∣ f ^ s := by
    rw [hw] at hDiv
    exact (w.isUnit.dvd_mul_left).mp hDiv
  exact (pow_dvd_pow_iff hf.ne_zero hf.1).mp hPowers

/-- A family with actual unit-numerator pole presentations eventually
escapes every fixed finite base module stage, even after arbitrary
base additions. No unbounded-valuation premise is supplied. -/
theorem eventually_not_mem_finite_submodule_mod_base_of_unit_pole_tower
    {f : R} (hf : Irreducible f) (m : ℕ) (z : ℕ → K)
    (hPole : ∀ n : ℕ, ∃ u : R, IsUnit u ∧
      z n = algebraMap R K u / algebraMap R K f ^ (m + n))
    (Λ : Submodule B K) [Module.Finite B Λ] :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ¬ ∃ a ∈ Λ, ∃ b : B, z n = a + algebraMap B K b := by
  obtain ⟨s, hs⟩ := exists_pole_order_bound_of_finite_submodule_mod_local hf Λ
  refine ⟨s + 1, ?_⟩
  intro n hn h
  obtain ⟨u, hu, hPresentation⟩ := hPole n
  obtain ⟨a, ha, b, hEq⟩ := h
  have hOrder : m + n ≤ s := hs u hu (m + n)
    ⟨a, ha, algebraMap B R b, by
      rw [← hPresentation, ← IsScalarTower.algebraMap_apply B R K, hEq]⟩
  omega

end DVR

section Localized

variable {k B K : Type*} [Field k] [CharZero k] [CommRing B] [IsDomain B]
  [Field K] [Algebra k B] [Algebra k K] [Algebra B K]
  [IsFractionRing B K] [IsScalarTower k B K]

omit [CharZero k] [Algebra k K] [IsScalarTower k B K] in
/-- A localized transverse base derivation turns a supplied family of
unit-numerator presentations into eventual escape. The local-ring and
module-instance constructions are internal to this generic theorem. -/
theorem eventually_not_mem_finite_submodule_mod_base_of_localized_unit_pole_tower
    (dB : Derivation k B B) (p : PrimeSpectrum B)
    (hDVR : IsDiscreteValuationRing (Localization.AtPrime p.asIdeal))
    (b : B) (hb : b ∈ p.asIdeal) (hdb : dB b ∉ p.asIdeal)
    (m : ℕ) (z : ℕ → K)
    (hPole :
      let R := Localization.AtPrime p.asIdeal
      letI : Algebra R K := IsLocalization.localizationAlgebraOfSubmonoidLe
        R K p.asIdeal.primeCompl (nonZeroDivisors B)
          p.asIdeal.primeCompl_le_nonZeroDivisors
      ∀ n : ℕ, ∃ u : R, IsUnit u ∧
        z n = algebraMap R K u / algebraMap B K b ^ (m + n))
    (Λ : Submodule B K) [Module.Finite B Λ] :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ¬ ∃ a ∈ Λ, ∃ c : B, z n = a + algebraMap B K c := by
  let R := Localization.AtPrime p.asIdeal
  letI : IsDiscreteValuationRing R := hDVR
  letI : Algebra R K := IsLocalization.localizationAlgebraOfSubmonoidLe
    R K p.asIdeal.primeCompl (nonZeroDivisors B)
      p.asIdeal.primeCompl_le_nonZeroDivisors
  letI : IsScalarTower B R K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      R K p.asIdeal.primeCompl (nonZeroDivisors B)
        p.asIdeal.primeCompl_le_nonZeroDivisors
  letI : IsFractionRing R K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.asIdeal.primeCompl R K
  let dR : @Derivation k R R _ _ _ _ Semiring.toModule Algebra.toModule :=
    localizationDerivation p.asIdeal.primeCompl R dB
  let f : R := algebraMap B R b
  have hfMem : f ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff R p.asIdeal b).mpr hb
  have hUnit : IsUnit (dR f) := by
    change IsUnit (localizationDerivation p.asIdeal.primeCompl R dB (algebraMap B R b))
    rw [localizationDerivation_algebraMap]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff R p.asIdeal _).mpr hdb
  have hf : Irreducible f :=
    irreducible_of_mem_maximalIdeal_of_isUnit_derivation dR hfMem hUnit
  apply eventually_not_mem_finite_submodule_mod_base_of_unit_pole_tower hf m z
    (Λ := Λ)
  intro n
  obtain ⟨u, hu, hEq⟩ := hPole n
  refine ⟨u, hu, ?_⟩
  simpa only [f, ← IsScalarTower.algebraMap_apply B R K] using hEq

/-- An actual pole of the canonically extended transverse base derivation
eventually escapes every fixed finite base stage, also modulo the base.
Both the increasing-order presentations and the cutoff are conclusions. -/
theorem eventually_not_mem_finite_submodule_mod_base_of_localized_pole
    (dB : Derivation k B B) (p : PrimeSpectrum B)
    (hDVR : IsDiscreteValuationRing (Localization.AtPrime p.asIdeal))
    (b : B) (hb : b ∈ p.asIdeal) (hdb : dB b ∉ p.asIdeal)
    (r : K) (hr : r ∉ Localization.subalgebra.ofField K p.asIdeal.primeCompl
      p.asIdeal.primeCompl_le_nonZeroDivisors)
    (Λ : Submodule B K) [Module.Finite B Λ] :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ¬ ∃ a ∈ Λ, ∃ c : B,
        ((localizationDerivation (nonZeroDivisors B) K dB : K → K)^[n]) r =
          a + algebraMap B K c := by
  obtain ⟨m, _, hTowers⟩ := exists_localized_unit_pole_tower dB p hDVR b hb hdb r hr
  apply eventually_not_mem_finite_submodule_mod_base_of_localized_unit_pole_tower
    dB p hDVR b hb hdb m
    (fun n => ((localizationDerivation (nonZeroDivisors B) K dB : K → K)^[n]) r)
    (Λ := Λ)
  dsimp only
  intro n
  obtain ⟨u, hu, hEq, _⟩ := hTowers n
  exact ⟨u, hu, hEq⟩

end Localized

end CollisionIdeals
