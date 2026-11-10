import Mathlib.RingTheory.Localization.NumDen
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal

/-!
# A target divisor witnessing a non-base rational function

Over a Noetherian unique factorization domain, a rational function outside
the base has a reduced denominator with a prime factor not dividing its
numerator. That factor constructs an actual height-one prime and a local
pole certificate. No boundary point or principal boundary equation is
supplied as a hypothesis.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

private theorem targetPole_primeHeight_span_prime_eq_one
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    (f : B) (hf : Prime f) :
    letI : (Ideal.span ({f} : Set B)).IsPrime :=
      (Ideal.span_singleton_prime hf.ne_zero).mpr hf
    (Ideal.span ({f} : Set B)).primeHeight = 1 := by
  let I := Ideal.span ({f} : Set B)
  letI : I.IsPrime := (Ideal.span_singleton_prime hf.ne_zero).mpr hf
  have hI0 : I ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hf.ne_zero
  apply le_antisymm
  · rw [← Ideal.height_eq_primeHeight]
    exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes I I
      (by simp only [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff])
  · have h := Ideal.primeHeight_add_one_le_of_lt (bot_lt_iff_ne_bot.mpr hI0)
    simpa only [← Ideal.height_eq_primeHeight, Ideal.height_bot, zero_add] using h

variable {B K : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
  [UniqueFactorizationMonoid B] [Field K] [Algebra B K] [IsFractionRing B K]

omit [IsNoetherianRing B] [UniqueFactorizationMonoid B] in
/-- The numerator/denominator certificate excludes membership in the
actual prime localization, embedded in the original fraction field. -/
theorem not_mem_localization_of_pole_certificate
    (p : PrimeSpectrum B) (r : K) (a b : B)
    (ha : a ∉ p.asIdeal) (hb : b ∈ p.asIdeal)
    (hEq : algebraMap B K a = algebraMap B K b * r) :
    r ∉ Localization.subalgebra.ofField K p.asIdeal.primeCompl
      p.asIdeal.primeCompl_le_nonZeroDivisors := by
  rintro ⟨c, s, hs, hFrac⟩
  have hs0 : s ≠ 0 := fun h => hs (h ▸ p.asIdeal.zero_mem)
  have hsK : algebraMap B K s ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective B K).ne hs0
  have hCross : a * s = b * c := by
    apply IsFractionRing.injective B K
    simp only [map_mul]
    rw [hEq, hFrac]
    simp only [mul_assoc, inv_mul_cancel₀ hsK, mul_one]
  have hProd : a * s ∈ p.asIdeal := by
    rw [hCross]
    exact p.asIdeal.mul_mem_right c hb
  rcases p.isPrime.mem_or_mem hProd with ha' | hs'
  · exact ha ha'
  · exact hs hs'

/-- A non-base rational element supplies a genuine target height-one
prime. The numerator is a unit at that prime, while the denominator
vanishes there, so the equality is a concrete local pole certificate. -/
theorem exists_heightOne_pole_certificate
    (r : K) (hr : r ∉ Set.range (algebraMap B K)) :
    ∃ (p : PrimeSpectrum B) (a b : B),
      p.asIdeal.primeHeight = 1 ∧ a ∉ p.asIdeal ∧ b ∈ p.asIdeal ∧ b ≠ 0 ∧
        algebraMap B K a = algebraMap B K b * r := by
  have hb0 : (IsFractionRing.den B r : B) ≠ 0 :=
    nonZeroDivisors.ne_zero (IsFractionRing.den B r).property
  have hbUnit : ¬ IsUnit (IsFractionRing.den B r : B) := by
    intro hb
    exact hr (IsFractionRing.isInteger_of_isUnit_den hb)
  obtain ⟨f, hf, hfb⟩ := WfDvdMonoid.exists_irreducible_factor hbUnit hb0
  have hfPrime : Prime f := hf.prime
  let p : PrimeSpectrum B :=
    ⟨Ideal.span {f}, (Ideal.span_singleton_prime hfPrime.ne_zero).mpr hfPrime⟩
  have ha : IsFractionRing.num B r ∉ p.asIdeal := by
    intro ha
    exact hfPrime.not_unit ((IsFractionRing.num_den_reduced B r)
      (Ideal.mem_span_singleton.mp ha) hfb)
  have hbK : algebraMap B K (IsFractionRing.den B r : B) ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective B K).ne hb0
  refine ⟨p, IsFractionRing.num B r, IsFractionRing.den B r,
    targetPole_primeHeight_span_prime_eq_one f hfPrime, ha,
    Ideal.mem_span_singleton.mpr hfb, hb0, ?_⟩
  exact ((div_eq_iff hbK).mp (IsFractionRing.mk'_num_den' B r)).trans (mul_comm _ _)

/-- Every non-base rational function has a pole in an actual target
height-one localization. The point is constructed, not supplied. -/
theorem exists_heightOne_local_pole
    (r : K) (hr : r ∉ Set.range (algebraMap B K)) :
    ∃ p : PrimeSpectrum B, p.asIdeal.primeHeight = 1 ∧
      r ∉ Localization.subalgebra.ofField K p.asIdeal.primeCompl
        p.asIdeal.primeCompl_le_nonZeroDivisors := by
  obtain ⟨p, a, b, hp, ha, hb, _, hEq⟩ := exists_heightOne_pole_certificate r hr
  exact ⟨p, hp, not_mem_localization_of_pole_certificate p r a b ha hb hEq⟩

end

end CollisionIdeals
