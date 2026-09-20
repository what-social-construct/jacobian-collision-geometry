import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Localization.Ideal

/-!
# Clearing a localized containment of finitely generated ideals

A containment after localization can be cleared by one denominator when
the ideal on the left is finitely generated. This is ordinary localization
algebra and does not require a domain or a Noetherian hypothesis.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

/-- A single localization denominator clears a containment with a finitely
generated ideal on the left. -/
theorem exists_denominator_mul_mem_of_map_le
    {T S : Type*} [CommRing T] [CommRing S] [Algebra T S]
    (M : Submonoid T) [IsLocalization M S]
    (I J : Ideal T) (hI : I.FG)
    (hIJ : I.map (algebraMap T S) ≤ J.map (algebraMap T S)) :
    ∃ t ∈ M, ∀ x ∈ I, t * x ∈ J := by
  revert hIJ
  refine Submodule.fg_induction T T
    (fun K : Ideal T =>
      K.map (algebraMap T S) ≤ J.map (algebraMap T S) →
        ∃ t ∈ M, ∀ x ∈ K, t * x ∈ J) ?_ ?_ I hI
  · intro x hMap
    have hx : algebraMap T S x ∈ J.map (algebraMap T S) :=
      hMap (Ideal.mem_map_of_mem _ (Submodule.mem_span_singleton_self x))
    obtain ⟨t, ht, htx⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff M S J x).mp hx
    refine ⟨t, ht, ?_⟩
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    simpa only [smul_eq_mul, mul_left_comm t a x] using J.mul_mem_left a htx
  · intro K L hK hL hMap
    obtain ⟨t, ht, htx⟩ := hK ((Ideal.map_mono le_sup_left).trans hMap)
    obtain ⟨u, hu, hux⟩ := hL ((Ideal.map_mono le_sup_right).trans hMap)
    refine ⟨t * u, M.mul_mem ht hu, ?_⟩
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    have hsum := J.add_mem (J.mul_mem_left u (htx y hy))
      (J.mul_mem_left t (hux z hz))
    convert hsum using 1
    ring

end CollisionIdeals.Planar
