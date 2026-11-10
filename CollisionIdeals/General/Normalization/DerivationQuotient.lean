import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Leibniz operators modulo the base image

An additive operator on a base algebra that agrees with a base operator
on the base image descends to the standard module quotient by that image.
If the original operator satisfies the scalar Leibniz rule, so does the
quotient operator. No quotient ring or connection structure is introduced.

The construction supplies no finite stage or uniform annihilator.
-/

set_option autoImplicit false

namespace CollisionIdeals

variable {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]

/-- Descend an additive operator through the original base image. The
base operator need not be packaged separately as a derivation here. -/
def algebraQuotientDerivationOperator
    (d : B → B) (delta : S →+ S)
    (hBase : ∀ b : B, delta (algebraMap B S b) = algebraMap B S (d b)) :
    (S ⧸ LinearMap.range (Algebra.linearMap B S)) →+
      S ⧸ LinearMap.range (Algebra.linearMap B S) :=
  QuotientAddGroup.map
    (LinearMap.range (Algebra.linearMap B S)).toAddSubgroup
    (LinearMap.range (Algebra.linearMap B S)).toAddSubgroup delta fun s hs => by
      change delta s ∈ LinearMap.range (Algebra.linearMap B S)
      obtain ⟨b, rfl⟩ := hs
      exact ⟨d b, (hBase b).symm⟩

@[simp]
theorem algebraQuotientDerivationOperator_mk
    (d : B → B) (delta : S →+ S)
    (hBase : ∀ b : B, delta (algebraMap B S b) = algebraMap B S (d b)) (s : S) :
    algebraQuotientDerivationOperator d delta hBase (Submodule.Quotient.mk s) =
      Submodule.Quotient.mk (delta s) := rfl

/-- The scalar Leibniz rule descends to the same standard module quotient. -/
theorem algebraQuotientDerivationOperator_leibniz
    (d : B → B) (delta : S →+ S)
    (hBase : ∀ b : B, delta (algebraMap B S b) = algebraMap B S (d b))
    (hLeibniz : ∀ (b : B) (s : S),
      delta (b • s) = d b • s + b • delta s)
    (b : B) (q : S ⧸ LinearMap.range (Algebra.linearMap B S)) :
    algebraQuotientDerivationOperator d delta hBase (b • q) =
      d b • q + b • algebraQuotientDerivationOperator d delta hBase q := by
  refine Submodule.Quotient.induction_on _ q ?_
  intro s
  change (Submodule.Quotient.mk (delta (b • s)) :
      S ⧸ LinearMap.range (Algebra.linearMap B S)) =
    Submodule.Quotient.mk (d b • s) + Submodule.Quotient.mk (b • delta s)
  rw [hLeibniz, Submodule.Quotient.mk_add]

end CollisionIdeals
