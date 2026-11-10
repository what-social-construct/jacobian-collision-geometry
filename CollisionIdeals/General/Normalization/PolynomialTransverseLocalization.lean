import CollisionIdeals.General.Normalization.PolynomialConormal
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Localized target partials with a constructed transverse element

A base derivation extends canonically to every localization. The extension
is constructed by the existing formally-étale Kähler differential
isomorphism, and is uniquely determined on the base.

For a nonzero prime in an algebra isomorphic to a characteristic-zero
polynomial ring, the existing conormal criterion constructs a coordinate
partial and an element of the prime whose derivative is outside it. The
same localized partial sends that element to a local unit. No transverse
element or local-regularity hypothesis is supplied.

This is regularity on the target localization. It does not assert that
the extended normal-closure frame preserves a normalization boundary
local ring.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CollisionIdeals

noncomputable section

section Localization

variable {k B : Type*} [CommRing k] [CommRing B] [Algebra k B]
variable (S : Submonoid B) (A : Type*) [CommRing A]
  [Algebra B A] [IsLocalization S A] [Algebra k A] [IsScalarTower k B A]

/-- The canonical extension of a base derivation to a localization.
The coefficient algebra and scalar tower are the original ones. -/
def localizationDerivation (d : Derivation k B B) : Derivation k A A := by
  letI : Algebra.FormallyEtale B A := Algebra.FormallyEtale.of_isLocalization S
  exact (((Algebra.linearMap B A).comp d.liftKaehlerDifferential).liftBaseChange A).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k B A).symm.toLinearMap
      |>.compDer (KaehlerDifferential.D k A)

@[simp]
theorem localizationDerivation_algebraMap (d : Derivation k B B) (b : B) :
    localizationDerivation S A d (algebraMap B A b) = algebraMap B A (d b) := by
  letI : Algebra.FormallyEtale B A := Algebra.FormallyEtale.of_isLocalization S
  simp [localizationDerivation,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    Derivation.liftKaehlerDifferential_comp_D]

end Localization

/-- Derivations of a localization into the same coefficient module are
determined by their values on the base. Clearing a localization
denominator proves this without a coefficient-module tower premise. -/
theorem localizationDerivation_ext
    {k B : Type*} [CommRing k] [CommRing B]
    (S : Submonoid B) (A : Type*) [CommRing A]
    [Algebra B A] [IsLocalization S A] [Algebra k A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module k M]
    (d₁ d₂ : Derivation k A M)
    (h : ∀ b : B, d₁ (algebraMap B A b) = d₂ (algebraMap B A b)) : d₁ = d₂ := by
  apply Derivation.ext
  intro a
  obtain ⟨⟨b, s⟩, hFrac⟩ := IsLocalization.surj S a
  have hProduct : d₁ (a * algebraMap B A s) = d₂ (a * algebraMap B A s) := by
    rw [hFrac, h]
  rw [d₁.leibniz, d₂.leibniz, h (s : B)] at hProduct
  have hCancel := add_left_cancel hProduct
  obtain ⟨u, hu⟩ := IsLocalization.map_units A s
  have hInv : (↑u⁻¹ : A) * algebraMap B A s = 1 := by
    rw [← hu]
    exact u.inv_mul
  have hBoth := congrArg (fun m : M => (↑u⁻¹ : A) • m) hCancel
  simpa only [smul_smul, hInv, one_smul] using hBoth

section LocalizationTower

variable {k B : Type*} [CommRing k] [CommRing B] [Algebra k B]
variable (S : Submonoid B) (A : Type*) [CommRing A]
  [Algebra B A] [IsLocalization S A] [Algebra k A] [IsScalarTower k B A]

/-- The two canonical localization extensions agree through a compatible
localization tower. This supplies compatibility between the target
local-ring partial and its fraction-field partial. -/
theorem localizationDerivation_algebraMap_of_tower
    (T : Submonoid B) (C : Type*) [CommRing C]
    [Algebra B C] [IsLocalization T C] [Algebra k C] [IsScalarTower k B C]
    [Algebra A C] [IsScalarTower B A C] [IsScalarTower k A C]
    (d : Derivation k B B) (a : A) :
    localizationDerivation T C d (algebraMap A C a) =
      algebraMap A C (localizationDerivation S A d a) := by
  have h : (localizationDerivation T C d).compAlgebraMap A =
      (Algebra.linearMap A C).compDer (localizationDerivation S A d) := by
    apply localizationDerivation_ext S A
    intro b
    change localizationDerivation T C d
        (algebraMap A C (algebraMap B A b)) =
      algebraMap A C (localizationDerivation S A d (algebraMap B A b))
    rw [← IsScalarTower.algebraMap_apply B A C,
      localizationDerivation_algebraMap, localizationDerivation_algebraMap,
      ← IsScalarTower.algebraMap_apply B A C]
  exact Derivation.congr_fun h a

end LocalizationTower

section Polynomial

variable {σ k B : Type*} [Field k] [CharZero k] [CommRing B] [Algebra k B]

private theorem exists_transported_partial_not_mem
    (e : MvPolynomial σ k ≃ₐ[k] B) (I : Ideal B)
    (hI : I ≠ ⊥) (hTop : I ≠ ⊤) :
    ∃ (i : σ) (b : B), b ∈ I ∧ polynomialEquivPartial e i b ∉ I := by
  by_contra! h
  apply hTop
  apply (forall_polynomialEquivPartial_conormalComponent_eq_zero_iff e I hI).mp
  intro i
  apply (derivationConormalComponent_eq_zero_iff _ _).mpr
  intro b hb
  exact h i b hb

omit [CharZero k] in
/-- The same transported target-coordinate partial, localized at an
actual prime of the target algebra. -/
def polynomialEquivPartialAtPrime
    (e : MvPolynomial σ k ≃ₐ[k] B) (p : PrimeSpectrum B) (i : σ) :
    Derivation k (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) :=
  localizationDerivation p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
    (polynomialEquivPartial e i)

omit [CharZero k] in
@[simp]
theorem polynomialEquivPartialAtPrime_algebraMap
    (e : MvPolynomial σ k ≃ₐ[k] B) (p : PrimeSpectrum B) (i : σ) (b : B) :
    polynomialEquivPartialAtPrime e p i
        (algebraMap B (Localization.AtPrime p.asIdeal) b) =
      algebraMap B (Localization.AtPrime p.asIdeal) (polynomialEquivPartial e i b) :=
  localizationDerivation_algebraMap p.asIdeal.primeCompl _ _ b

/-- A nonzero target prime supplies its own transverse coordinate partial
and element. The constructed localized derivative is regular on the
target localization and sends that element to a unit. -/
theorem exists_polynomialEquivPartialAtPrime_transverse
    (e : MvPolynomial σ k ≃ₐ[k] B) (p : PrimeSpectrum B)
    (hp : p.asIdeal ≠ ⊥) :
    ∃ (i : σ) (b : B), b ∈ p.asIdeal ∧
      polynomialEquivPartial e i b ∉ p.asIdeal ∧
      IsUnit (polynomialEquivPartialAtPrime e p i
        (algebraMap B (Localization.AtPrime p.asIdeal) b)) := by
  obtain ⟨i, b, hb, hdb⟩ := exists_transported_partial_not_mem e p.asIdeal hp p.isPrime.ne_top
  refine ⟨i, b, hb, hdb, ?_⟩
  rw [polynomialEquivPartialAtPrime_algebraMap]
  exact (IsLocalization.AtPrime.isUnit_to_map_iff
    (Localization.AtPrime p.asIdeal) p.asIdeal _).mpr hdb

end Polynomial

end

end CollisionIdeals
