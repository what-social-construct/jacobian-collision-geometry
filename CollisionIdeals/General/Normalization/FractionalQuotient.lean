import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Torsion of a fractional algebra modulo the base

If a base algebra embeds into the base's fraction field, its additive
quotient by the image of the base is a torsion module. Each representative
has a denominator that clears it into the base image.

This uses the existing submodule quotient, not a quotient ring or a new
quotient structure. The denominator can depend on the representative;
neither a uniform annihilator nor finite generation is asserted.
-/

set_option autoImplicit false

namespace CollisionIdeals

variable {B S K : Type*} [CommRing B] [IsDomain B] [CommRing S] [Field K]
  [Algebra B S] [Algebra B K] [IsFractionRing B K]

/-- An algebra embedded over a domain into its fraction field is torsion
modulo the image of the base. This is elementwise denominator clearing,
not a uniform-annihilator statement. -/
theorem isTorsion_quotient_range_algebraLinearMap
    (f : S →ₐ[B] K) (hf : Function.Injective f) :
    Module.IsTorsion B (S ⧸ LinearMap.range (Algebra.linearMap B S)) := by
  intro q
  refine Quotient.inductionOn' q ?_
  intro s
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := B) (f s)
  refine ⟨⟨b, hb⟩, ?_⟩
  change (Submodule.Quotient.mk (b • s) :
    S ⧸ LinearMap.range (Algebra.linearMap B S)) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨a, ?_⟩
  apply hf
  change f (algebraMap B S a) = f (b • s)
  rw [f.commutes, map_smul, Algebra.smul_def]
  have hbK : algebraMap B K b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  simpa only [mul_comm] using (div_eq_iff hbK).mp hab

end CollisionIdeals
