import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# Derivations and ideal squares

This elementary ideal calculation is shared by conormal components and
local ramification criteria. It has no normalization or ramification
dependency, and does not assert that a derivation preserves an ideal.
-/

set_option autoImplicit false

namespace CollisionIdeals

variable {k S : Type*} [CommRing k] [CommRing S] [Algebra k S]

/-- A regular derivation lowers an ideal-square condition to ideal membership. -/
theorem derivation_mem_ideal_of_mem_sq
    (d : Derivation k S S) (I : Ideal S) {x : S} (hx : x ∈ I ^ 2) :
    d x ∈ I := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro a ha b hb
    rw [d.leibniz]
    exact I.add_mem (I.mul_mem_right (d b) ha) (I.mul_mem_right (d a) hb)
  · intro a b ha hb
    simpa only [map_add] using I.add_mem ha hb

end CollisionIdeals
