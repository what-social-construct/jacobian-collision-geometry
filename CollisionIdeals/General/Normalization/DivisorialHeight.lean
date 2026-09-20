import CollisionIdeals.General.Normalization.Finiteness
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.Height

/-!
# Contraction of divisors to the coordinate-image base

The coordinate-image algebra of a generically finite polynomial map is
normal. Going down therefore bounds the height of a contracted normalization
prime; integrality ensures that a nonzero prime cannot contract to zero.
In particular a normalization divisor lies over a base divisor.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

section GoingDown

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.HasGoingDown R S]

/-- Going down lifts every prime chain ending at a contracted prime. -/
theorem primeHeight_under_le_of_hasGoingDown (P : Ideal S) [P.IsPrime] :
    (P.under R).primeHeight ≤ P.primeHeight := by
  apply Order.height_le
  intro l hl
  haveI : P.LiesOver l.last.asIdeal := by
    rw [hl]
    infer_instance
  obtain ⟨L, hLength, hLast, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P
  calc
    (l.length : ℕ∞) = L.length := by rw [hLength]
    _ ≤ P.primeHeight := by
      simpa only [hLast, Ideal.primeHeight] using (Order.length_le_height_last (p := L))

end GoingDown

section IntegralNormal

variable {R S : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S]
  [Algebra.IsIntegral R S]

/-- A divisor contracts to a divisor in an integral extension of domains
with normal base. -/
theorem primeHeight_under_eq_one_of_integral_of_normal
    (P : Ideal S) [P.IsPrime] (hP : P.primeHeight = 1) :
    (P.under R).primeHeight = 1 := by
  have hnonzero : P ≠ ⊥ := by
    intro hzero
    have hheight : P.height = 1 := by rw [Ideal.height_eq_primeHeight, hP]
    simp [hzero] at hheight
  have hbase : P.under R ≠ ⊥ := Ideal.under_ne_bot R hnonzero
  apply le_antisymm
  · exact (primeHeight_under_le_of_hasGoingDown (R := R) P).trans_eq hP
  · have h := Ideal.primeHeight_add_one_le_of_lt (bot_lt_iff_ne_bot.mpr hbase)
    simpa only [← Ideal.height_eq_primeHeight, Ideal.height_bot, zero_add] using h

end IntegralNormal

section TorsionFree

variable {R S : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [CommRing S] [IsDomain S] [Algebra R S] [Module.IsTorsionFree R S]
  [Algebra.IsIntegral R S]

/-- Torsion-free form of contraction of divisors. -/
theorem primeHeight_under_eq_one_of_integral_of_normal_of_isTorsionFree
    (P : Ideal S) [P.IsPrime] (hP : P.primeHeight = 1) :
    (P.under R).primeHeight = 1 := by
  letI : FaithfulSMul R S := Module.IsTorsionFree.to_faithfulSMul
  exact primeHeight_under_eq_one_of_integral_of_normal (R := R) P hP

end TorsionFree

section IntegralClosure

variable {B N : Type*} [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
  [Field N] [Algebra B N] [Module.IsTorsionFree B N]

/-- Divisor contraction for the integral closure inside a field. -/
theorem integralClosure_primeHeight_under_eq_one
    (P : Ideal (integralClosure B N)) [P.IsPrime] (hP : P.primeHeight = 1) :
    (P.under B).primeHeight = 1 := by
  exact primeHeight_under_eq_one_of_integral_of_normal_of_isTorsionFree
    (R := B) (S := integralClosure B N) P hP

end IntegralClosure

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ} {F : PolynomialSelfMap k n}
  {N : Type u} [Field N] [Algebra (PolynomialMapBaseFunctionField F) N]

@[reducible] local instance divisorialHeightBaseAlgebra :
    Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

/-- The normal extension has no torsion over the coordinate-image base. -/
theorem polynomialNormalExtension_isTorsionFree :
    Module.IsTorsionFree (PolynomialImageAlgebra F) N := by
  let B : Type u := PolynomialImageAlgebra F
  let K : Type u := PolynomialMapBaseFunctionField F
  letI algebraBK : Algebra B K := OreLocalization.instAlgebra
  letI : SMul B K := algebraBK.toSMul
  letI : IsScalarTower B K N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.IsTorsionFree.trans_faithfulSMul B K N

/-- The normalization ring embeds into the function-field extension, so
has no torsion over the coordinate-image algebra. Keeping this certificate
separate avoids unfolding the fraction-field scalar tower in geometric uses. -/
theorem polynomialNormalizationInExtension_isTorsionFree :
    Module.IsTorsionFree (PolynomialImageAlgebra F)
      (PolynomialNormalizationInExtensionRing (F := F) (N := N)) := by
  let B : Type u := PolynomialImageAlgebra F
  let K : Type u := PolynomialMapBaseFunctionField F
  let T : Type u := PolynomialNormalizationInExtensionRing (F := F) (N := N)
  letI algebraBK : Algebra B K := OreLocalization.instAlgebra
  letI : SMul B K := algebraBK.toSMul
  letI : IsScalarTower B K N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Module.IsTorsionFree B N := .trans_faithfulSMul B K N
  exact IsIntegralClosure.isTorsionFree (A := T) B N

/-- A height-one prime of the normal-closure normalization contracts to a
height-one prime of the coordinate-image algebra. -/
theorem polynomialNormalization_primeHeight_under_eq_one
    (D : PolynomialNormalClosureData F N)
    (p : PrimeSpectrum (PolynomialNormalizationInExtensionRing (F := F) (N := N)))
    (hp : Ideal.primeHeight
      (R := PolynomialNormalizationInExtensionRing (F := F) (N := N)) p.asIdeal = 1) :
    Ideal.primeHeight (R := PolynomialImageAlgebra F)
      (Ideal.under (PolynomialImageAlgebra F)
        (B := PolynomialNormalizationInExtensionRing (F := F) (N := N)) p.asIdeal) = 1 := by
  let B : Type u := PolynomialImageAlgebra F
  letI := D.finiteIntermediate
  letI : IsIntegrallyClosed B :=
    polynomialImageAlgebra_isIntegrallyClosed_of_finiteDimensional F
  letI : Module.IsTorsionFree B N :=
    polynomialNormalExtension_isTorsionFree (F := F) (N := N)
  with_reducible exact integralClosure_primeHeight_under_eq_one (B := B) (N := N) p.asIdeal hp

end

end CollisionIdeals
