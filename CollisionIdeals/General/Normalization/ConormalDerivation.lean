import CollisionIdeals.General.Normalization.DerivationIdeal
import CollisionIdeals.General.Normalization.SimplePole
import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Derivations on a conormal module

A derivation of `B` induces a `B`-linear component `I/I² → B/I` of the
conormal map. We use Mathlib's existing `Ideal.Cotangent`, not a new quotient.
Vanishing of this component is precisely preservation of the ideal.

For a principal ideal, the component is determined by the derivative of its
generator modulo the ideal. On a characteristic-zero polynomial base, all
coordinate components of a nonzero ideal vanish exactly when the ideal is
the unit ideal. No assertion here identifies an ideal with a Keller boundary
or proves preservation of such a boundary.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

section General

variable {k B : Type*} [CommRing k] [CommRing B] [Algebra k B]

/-- The component of the conormal map obtained by applying a derivation and
reducing modulo the ideal. -/
def derivationConormalComponent (d : Derivation k B B) (I : Ideal B) :
    I.Cotangent →ₗ[B] B ⧸ I :=
  Submodule.liftQ _
    { toFun := fun x => Ideal.Quotient.mk I (d x)
      map_add' := fun x y => by simp
      map_smul' := fun r x => by
        simp only [SetLike.val_smul, smul_eq_mul, d.leibniz, map_add, map_mul]
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr x.property]
        simp [Algebra.smul_def] }
    (by
      intro x hx
      change Ideal.Quotient.mk I (d x) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      apply derivation_mem_ideal_of_mem_sq d I
      apply I.mem_toCotangent_ker.mp
      exact (Submodule.Quotient.mk_eq_zero (I • ⊤ : Submodule B I)).mpr hx)

@[simp]
theorem derivationConormalComponent_toCotangent
    (d : Derivation k B B) (I : Ideal B) (x : I) :
    derivationConormalComponent d I (I.toCotangent x) =
      Ideal.Quotient.mk I (d x) := rfl

/-- Vanishing of the conormal component means that the derivation preserves
the ideal, not merely its localization. -/
theorem derivationConormalComponent_eq_zero_iff
    (d : Derivation k B B) (I : Ideal B) :
    derivationConormalComponent d I = 0 ↔ ∀ x ∈ I, d x ∈ I := by
  constructor
  · intro h x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have := LinearMap.congr_fun h (I.toCotangent ⟨x, hx⟩)
    simpa only [derivationConormalComponent_toCotangent, LinearMap.zero_apply] using this
  · intro h
    ext x
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h x x.property)

/-- For a principal ideal the entire component is tested on one generator. -/
theorem derivationConormalComponent_span_singleton_eq_zero_iff
    (d : Derivation k B B) (s : B) :
    derivationConormalComponent d (Ideal.span ({s} : Set B)) = 0 ↔
      d s ∈ Ideal.span ({s} : Set B) :=
  (derivationConormalComponent_eq_zero_iff d _).trans
    (derivation_preserves_span_singleton_iff d s)

end General

section Polynomial

variable {σ k : Type*} [Field k] [CharZero k]

/-- A nonzero ideal in a characteristic-zero polynomial ring has all
coordinate conormal components zero exactly when it is the unit ideal. -/
theorem forall_pderiv_conormalComponent_eq_zero_iff
    (I : Ideal (MvPolynomial σ k)) (hI : I ≠ ⊥) :
    (∀ i, derivationConormalComponent (MvPolynomial.pderiv i) I = 0) ↔ I = ⊤ := by
  constructor
  · intro h
    by_contra htop
    obtain ⟨x, hx, i, hi⟩ := exists_mem_pderiv_not_mem I hI htop
    exact hi ((derivationConormalComponent_eq_zero_iff _ _).mp (h i) x hx)
  · rintro rfl i
    apply (derivationConormalComponent_eq_zero_iff _ _).mpr
    exact fun _ _ => Submodule.mem_top

end Polynomial

end

end CollisionIdeals
