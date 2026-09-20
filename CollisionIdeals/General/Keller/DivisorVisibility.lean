import CollisionIdeals.General.Keller.Etale
import CollisionIdeals.General.Keller.Normalization
import CollisionIdeals.General.Normalization.DivisorialHeight
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal

/-!
# Visible source divisors over base hypersurfaces

A polynomial ring over a field has only constant units. Its coordinate-image
subalgebra therefore reflects units under inclusion. For a Keller map,
flatness then makes an irreducible source factor of a prime base element
contract to that base prime. This constructs a visible unramified source
divisor over each principal base divisor.

The statement is existential: it does not make every divisor of the normal
closure visible, and does not prove absence of ramification there.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

universe u

/-- A subalgebra of a polynomial ring over a reduced coefficient ring
contains all polynomial units, since those units are constants. -/
theorem polynomialSubalgebra_isUnit_coe_iff
    {k ι : Type*} [CommRing k] [IsReduced k]
    (S : Subalgebra k (MvPolynomial ι k)) (b : S) :
    IsUnit (b : MvPolynomial ι k) ↔ IsUnit b := by
  constructor
  · intro hb
    obtain ⟨c, hc, heq⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hb
    have hbc : b = algebraMap k S c := Subtype.ext heq
    rw [hbc]
    exact hc.map (algebraMap k S)
  · intro hb
    exact hb.map S.val.toRingHom

private theorem primeHeight_span_prime_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (r : R) (hr : Prime r) :
    letI : (Ideal.span ({r} : Set R)).IsPrime :=
      (Ideal.span_singleton_prime hr.ne_zero).mpr hr
    (Ideal.span ({r} : Set R)).primeHeight = 1 := by
  let I := Ideal.span ({r} : Set R)
  letI : I.IsPrime := (Ideal.span_singleton_prime hr.ne_zero).mpr hr
  have hI0 : I ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hr.ne_zero
  apply le_antisymm
  · rw [← Ideal.height_eq_primeHeight]
    exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes I I
      (by simp only [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff])
  · have h := Ideal.primeHeight_add_one_le_of_lt (bot_lt_iff_ne_bot.mpr hI0)
    simpa only [← Ideal.height_eq_primeHeight, Ideal.height_bot, zero_add] using h

/-- Every prime element of the coordinate-image base has a visible source
divisor above it. Keller flatness identifies the contracted prime, and
Keller étaleness supplies unramifiedness on this source divisor only. -/
theorem exists_visible_source_divisor_of_isKeller
    {k : Type u} [Field k] {n : ℕ}
    (F : PolynomialSelfMap k n) (hKeller : IsKeller F)
    (b : polynomialMapImageAlgebra F) (hb : Prime b) :
    ∃ q : PrimeSpectrum (SourceRing k (Fin n)),
      q.asIdeal.primeHeight = 1 ∧
      q.asIdeal.under (polynomialMapImageAlgebra F) = Ideal.span {b} ∧
      Algebra.IsUnramifiedAt (polynomialMapImageAlgebra F) q.asIdeal := by
  let B := polynomialMapImageAlgebra F
  let A := SourceRing k (Fin n)
  letI : Algebra.Etale B A := polynomialSource_etale_of_isKeller F hKeller
  have hb0 : (b : A) ≠ 0 := by
    intro h
    exact hb.ne_zero (Subtype.ext h)
  have hbunit : ¬ IsUnit (b : A) := by
    simpa only [polynomialSubalgebra_isUnit_coe_iff] using hb.not_unit
  obtain ⟨r, hr, hrb⟩ := WfDvdMonoid.exists_irreducible_factor hbunit hb0
  have hrprime : Prime r := hr.prime
  let q : PrimeSpectrum A :=
    ⟨Ideal.span {r}, (Ideal.span_singleton_prime hrprime.ne_zero).mpr hrprime⟩
  letI : q.asIdeal.IsPrime := q.isPrime
  have hqheight : q.asIdeal.primeHeight = 1 := primeHeight_span_prime_eq_one r hrprime
  let p : Ideal B := Ideal.span {b}
  letI : p.IsPrime := (Ideal.span_singleton_prime hb.ne_zero).mpr hb
  have hp0 : p ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hb.ne_zero
  have hple : p ≤ q.asIdeal.under B := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_span_singleton.mpr hrb
  have hheight : (q.asIdeal.under B).primeHeight ≤ 1 :=
    (primeHeight_under_le_of_hasGoingDown (R := B) q.asIdeal).trans_eq hqheight
  have hpheight : 1 ≤ p.primeHeight := by
    have h := Ideal.primeHeight_add_one_le_of_lt (bot_lt_iff_ne_bot.mpr hp0)
    simpa only [← Ideal.height_eq_primeHeight, Ideal.height_bot, zero_add] using h
  have hcontract : q.asIdeal.under B = p := by
    apply le_antisymm ?_ hple
    by_contra hnot
    have hstrict := Ideal.primeHeight_add_one_le_of_lt (lt_of_le_not_ge hple hnot)
    have hbad : (2 : ℕ∞) ≤ 1 := calc
      (2 : ℕ∞) = 1 + 1 := rfl
      _ ≤ p.primeHeight + 1 := add_le_add hpheight le_rfl
      _ ≤ (q.asIdeal.under B).primeHeight := hstrict
      _ ≤ 1 := hheight
    norm_num at hbad
  exact ⟨q, hqheight, hcontract, inferInstance⟩

/-- Every height-one base prime has at least one visible, unramified source
divisor. This does not say that every sheet above that base prime is visible
or that the full normal closure is unramified there. -/
theorem exists_visible_source_divisor_over_heightOne_of_isKeller
    {k : Type u} [Field k] {n : ℕ}
    (F : PolynomialSelfMap k n) (hKeller : IsKeller F)
    (p : PrimeSpectrum (polynomialMapImageAlgebra F))
    (hp : p.asIdeal.primeHeight = 1) :
    ∃ q : PrimeSpectrum (SourceRing k (Fin n)),
      q.asIdeal.primeHeight = 1 ∧
      q.asIdeal.under (polynomialMapImageAlgebra F) = p.asIdeal ∧
      Algebra.IsUnramifiedAt (polynomialMapImageAlgebra F) q.asIdeal := by
  let B := polynomialMapImageAlgebra F
  let e := (AlgEquiv.ofInjective (coordinateAlgHom F)
    (coordinateAlgHom_injective_of_isKeller F hKeller)).toMulEquiv
  letI : UniqueFactorizationMonoid B :=
    MulEquiv.uniqueFactorizationMonoid e inferInstance
  have hp0 : p.asIdeal ≠ ⊥ := by
    intro h
    have hheight : p.asIdeal.height = 1 := by rw [Ideal.height_eq_primeHeight, hp]
    simp [h] at hheight
  obtain ⟨b, hbp, hb⟩ := p.isPrime.exists_mem_prime_of_ne_bot hp0
  let I : Ideal B := Ideal.span {b}
  letI : I.IsPrime := (Ideal.span_singleton_prime hb.ne_zero).mpr hb
  have hI0 : I ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hb.ne_zero
  have hIheight : 1 ≤ I.primeHeight := by
    have h := Ideal.primeHeight_add_one_le_of_lt (bot_lt_iff_ne_bot.mpr hI0)
    simpa only [← Ideal.height_eq_primeHeight, Ideal.height_bot, zero_add] using h
  have hIle : I ≤ p.asIdeal := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hbp)
  have hIp : I = p.asIdeal := by
    apply le_antisymm hIle
    by_contra hnot
    have hstrict := Ideal.primeHeight_add_one_le_of_lt (lt_of_le_not_ge hIle hnot)
    have hbad : (2 : ℕ∞) ≤ 1 := calc
      (2 : ℕ∞) = 1 + 1 := rfl
      _ ≤ I.primeHeight + 1 := add_le_add hIheight le_rfl
      _ ≤ p.asIdeal.primeHeight := hstrict
      _ = 1 := hp
    norm_num at hbad
  obtain ⟨q, hq, hcontract, hunram⟩ := exists_visible_source_divisor_of_isKeller F hKeller b hb
  exact ⟨q, hq, hcontract.trans hIp, hunram⟩

end

end CollisionIdeals
