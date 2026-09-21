import CollisionIdeals.General.Normalization.ConormalDerivation

/-!
# Polynomial-coordinate conormal components on an isomorphic algebra

An algebra equivalence from a polynomial ring transports its coordinate
partial derivatives to derivations of the target algebra. Their conormal
components vanish on an ideal precisely when the original coordinate
components vanish on its pullback.

Over a characteristic-zero field, all transported components of a nonzero
ideal vanish exactly when it is the unit ideal. This criterion does not
require a principal presentation of the ideal and does not assert that any
particular boundary ideal has vanishing components.
-/

set_option autoImplicit false

namespace CollisionIdeals

section Transport

variable {σ k B : Type*} [CommRing k] [CommRing B] [Algebra k B]

/-- A polynomial-coordinate partial derivative transported along an
algebra equivalence, using Mathlib's existing derivation-lifting API. -/
noncomputable def polynomialEquivPartial (e : MvPolynomial σ k ≃ₐ[k] B) (i : σ) :
    Derivation k B B :=
  (MvPolynomial.pderiv i).liftOfRightInverse
    (f := e) (f_inv := e.symm) e.apply_symm_apply
    (by
      intro x hx
      have hxzero : x = 0 := e.injective (hx.trans (map_zero e).symm)
      rw [hxzero, map_zero, map_zero])

/-- The transported coordinate derivation is conjugation by the supplied
polynomial algebra equivalence. -/
theorem polynomialEquivPartial_apply
    (e : MvPolynomial σ k ≃ₐ[k] B) (i : σ) (b : B) :
    polynomialEquivPartial e i b = e (MvPolynomial.pderiv i (e.symm b)) := rfl

@[simp]
theorem polynomialEquivPartial_apply_equiv
    (e : MvPolynomial σ k ≃ₐ[k] B) (i : σ) (p : MvPolynomial σ k) :
    polynomialEquivPartial e i (e p) = e (MvPolynomial.pderiv i p) := by
  rw [polynomialEquivPartial_apply, e.symm_apply_apply]

/-- A transported conormal component vanishes precisely when its original
polynomial-coordinate component vanishes on the pulled-back ideal. -/
theorem polynomialEquivPartial_conormalComponent_eq_zero_iff
    (e : MvPolynomial σ k ≃ₐ[k] B) (i : σ) (I : Ideal B) :
    derivationConormalComponent (polynomialEquivPartial e i) I = 0 ↔
      derivationConormalComponent (MvPolynomial.pderiv i) (I.comap e.toRingHom) = 0 := by
  rw [derivationConormalComponent_eq_zero_iff,
    derivationConormalComponent_eq_zero_iff]
  constructor
  · intro h p hp
    change e (MvPolynomial.pderiv i p) ∈ I
    simpa only [polynomialEquivPartial_apply_equiv] using h (e p) hp
  · intro h b hb
    have hp : e.symm b ∈ I.comap e.toRingHom := by
      change e (e.symm b) ∈ I
      simpa only [e.apply_symm_apply] using hb
    have hderiv := h (e.symm b) hp
    change e (MvPolynomial.pderiv i (e.symm b)) ∈ I at hderiv
    exact hderiv

end Transport

section CharacteristicZero

variable {σ k B : Type*} [Field k] [CharZero k] [CommRing B] [Algebra k B]

/-- For a nonzero ideal in an algebra isomorphic to a characteristic-zero
polynomial ring, all transported coordinate conormal components vanish
exactly when the ideal is the unit ideal. -/
theorem forall_polynomialEquivPartial_conormalComponent_eq_zero_iff
    (e : MvPolynomial σ k ≃ₐ[k] B) (I : Ideal B) (hI : I ≠ ⊥) :
    (∀ i, derivationConormalComponent (polynomialEquivPartial e i) I = 0) ↔ I = ⊤ := by
  have hcomap : I.comap e.toRingHom ≠ ⊥ := by
    intro h
    apply hI
    have hmap := congrArg (Ideal.map e.toRingHom) h
    rwa [Ideal.map_comap_of_surjective e.toRingHom e.surjective I,
      Ideal.map_bot] at hmap
  calc
    (∀ i, derivationConormalComponent (polynomialEquivPartial e i) I = 0) ↔
        ∀ i, derivationConormalComponent (MvPolynomial.pderiv i)
          (I.comap e.toRingHom) = 0 :=
      forall_congr' fun i => polynomialEquivPartial_conormalComponent_eq_zero_iff e i I
    _ ↔ I.comap e.toRingHom = ⊤ :=
      forall_pderiv_conormalComponent_eq_zero_iff (I.comap e.toRingHom) hcomap
    _ ↔ I = ⊤ := Ideal.comap_eq_top_iff

end CharacteristicZero

end CollisionIdeals
