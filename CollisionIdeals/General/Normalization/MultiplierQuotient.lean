import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Multiplication comparisons between submodule quotients

Submodules of one ambient module give canonical quotient inclusions into
the ambient quotient. A scalar carrying one submodule into another
therefore induces the expected multiplication comparison on these standard
quotients.

The landing containment is an explicit input, not a consequence of this
construction. No new quotient structure or injectivity of the multiplier
comparison is asserted. The ambient inclusion itself is injective.
-/

set_option autoImplicit false

namespace CollisionIdeals

variable {T V : Type*} [CommRing T] [AddCommGroup V] [Module T V]

/-- Include a submodule modulo its intersection with `A` into `V / A`.
This uses the standard quotient by the comap along the subtype. -/
def submoduleQuotientToAmbient (A P : Submodule T V) :
    (P ⧸ A.comap P.subtype) →ₗ[T] V ⧸ A :=
  (A.comap P.subtype).mapQ A P.subtype le_rfl

@[simp]
theorem submoduleQuotientToAmbient_mk
    (A P : Submodule T V) (x : P) :
    submoduleQuotientToAmbient A P (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (x : V) := rfl

/-- The common ambient quotient loses no information from the submodule
quotient. No inclusion `A ≤ P` is required. -/
theorem submoduleQuotientToAmbient_injective
    (A P : Submodule T V) :
    Function.Injective (submoduleQuotientToAmbient A P) := by
  intro x y
  refine Submodule.Quotient.induction_on _ x ?_
  intro x
  refine Submodule.Quotient.induction_on _ y ?_
  intro y hxy
  apply (Submodule.Quotient.eq _).mpr
  change (x : V) - (y : V) ∈ A
  exact (Submodule.Quotient.eq A).mp hxy

/-- Multiplication by a scalar that lands in `Q` descends modulo the
common base submodule. Its containment hypothesis is the substantive
landing input in applications. -/
def multiplierSubmoduleQuotientMap
    (A P Q : Submodule T V) (s : T)
    (hLanding : ∀ x ∈ P, s • x ∈ Q) :
    (P ⧸ A.comap P.subtype) →ₗ[T] Q ⧸ A.comap Q.subtype :=
  (A.comap P.subtype).mapQ (A.comap Q.subtype)
    ((s • P.subtype).codRestrict Q (fun x => hLanding x x.property)) (by
      intro x hx
      change s • (x : V) ∈ A
      exact A.smul_mem s hx)

@[simp]
theorem multiplierSubmoduleQuotientMap_mk
    (A P Q : Submodule T V) (s : T)
    (hLanding : ∀ x ∈ P, s • x ∈ Q) (x : P) :
    multiplierSubmoduleQuotientMap A P Q s hLanding (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (⟨s • (x : V), hLanding x x.property⟩ : Q) := rfl

/-- The comparison is multiplication in the common ambient quotient.
Unlike the ambient inclusions, the comparison itself need not be injective. -/
theorem multiplierSubmoduleQuotientMap_ambient
    (A P Q : Submodule T V) (s : T)
    (hLanding : ∀ x ∈ P, s • x ∈ Q) :
    (submoduleQuotientToAmbient A Q).comp
        (multiplierSubmoduleQuotientMap A P Q s hLanding) =
      s • submoduleQuotientToAmbient A P := by
  apply LinearMap.ext
  intro q
  refine Submodule.Quotient.induction_on _ q ?_
  intro x
  rfl

end CollisionIdeals
