import CollisionIdeals.Planar.Research.MonogenicOrder
import Mathlib.RingTheory.Derivation.Basic

/-!
# Conductor comparison for derivatives of normalization elements

A derivation into an ambient module takes the whole monogenic order into
a `T`-submodule once its values on the base and the generator lie there.
The existing conductor of this order then carries every derivative of an
element of `T` into the same submodule, by the Leibniz rule.

These are algebraic comparison lemmas. They neither construct a generator
whose derivative lies in the secant lattice nor assert that its conductor
avoids a boundary prime. The derivation takes values in the ambient module,
not necessarily in the normalization ring itself.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

section

variable {k B T N : Type*}
  [CommRing k] [CommRing B] [CommRing T] [AddCommGroup N]
  [Algebra k T] [Algebra B T] [Module T N] [Module k N]

/-- Values on the base and the generator control the derivative of every
element of the monogenic order. No integrality assumption is needed. -/
theorem derivation_mem_of_mem_monogenicOrder
    (d : Derivation k T N) (Λ : Submodule T N) (alpha : T)
    (hBase : ∀ b : B, d (algebraMap B T b) ∈ Λ)
    (hAlpha : d alpha ∈ Λ)
    {u : T} (hu : u ∈ monogenicOrder B T alpha) : d u ∈ Λ := by
  refine Algebra.adjoin_induction
    (p := fun u _ => d u ∈ Λ) ?_ hBase ?_ ?_ hu
  · intro u hu
    obtain rfl : u = alpha := Set.mem_singleton_iff.mp hu
    exact hAlpha
  · intro u v _ _ hu hv
    simpa only [map_add] using Λ.add_mem hu hv
  · intro u v _ _ hu hv
    rw [d.leibniz]
    exact Λ.add_mem (Λ.smul_mem u hv) (Λ.smul_mem v hu)

/-- The conductor carries all derivatives of `T` into any `T`-submodule
containing the derivatives of the monogenic order. This only proves a
multiplied containment, not regularity at a prime. -/
theorem conductor_smul_derivation_mem_of_order
    (d : Derivation k T N) (Λ : Submodule T N) (alpha : T)
    (hOrder : ∀ u ∈ monogenicOrder B T alpha, d u ∈ Λ)
    {c : T} (hc : c ∈ monogenicOrderConductor B T alpha)
    (t : T) : c • d t ∈ Λ := by
  have hct : c * t ∈ monogenicOrder B T alpha :=
    (mem_monogenicOrderConductor_iff B T alpha c).mp hc t
  have hcOrder : c ∈ monogenicOrder B T alpha :=
    monogenicOrderConductor_subset_order B T alpha hc
  have h := Λ.sub_mem (hOrder (c * t) hct)
    (Λ.smul_mem t (hOrder c hcOrder))
  simpa only [d.leibniz, add_sub_cancel_right] using h

/-- Generator control followed by the existing conductor comparison. -/
theorem conductor_smul_derivation_mem_of_generator
    (d : Derivation k T N) (Λ : Submodule T N) (alpha : T)
    (hBase : ∀ b : B, d (algebraMap B T b) ∈ Λ)
    (hAlpha : d alpha ∈ Λ)
    {c : T} (hc : c ∈ monogenicOrderConductor B T alpha)
    (t : T) : c • d t ∈ Λ := by
  apply conductor_smul_derivation_mem_of_order d Λ alpha ?_ hc t
  intro u hu
  exact derivation_mem_of_mem_monogenicOrder d Λ alpha hBase hAlpha hu

end

end CollisionIdeals.Planar
