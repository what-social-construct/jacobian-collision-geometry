import CollisionIdeals.General.Normalization.ConormalDerivation

/-!
# Finite-generator tests for conormal components

The conormal component of a derivation vanishes exactly when the
derivation preserves the ideal. If a finite set generates the ideal,
Leibniz's rule reduces this condition to its elements. Equivalently, the
derivatives of those generators have zero image in the existing quotient
ring.

The same generating set tests any family of derivations. Finite generation
supplies such a set, but neither chooses a boundary equation nor proves
that any of these derivative classes vanish.
-/

set_option autoImplicit false

namespace CollisionIdeals

variable {k B : Type*} [CommRing k] [CommRing B] [Algebra k B]

/-- Vanishing of a conormal component can be tested on any finite ideal
generating set. No principal presentation is required. -/
theorem derivationConormalComponent_eq_zero_iff_on_generators
    (d : Derivation k B B) (I : Ideal B) (s : Finset B)
    (hs : Ideal.span (s : Set B) = I) :
    derivationConormalComponent d I = 0 ↔ ∀ f ∈ s, d f ∈ I := by
  rw [derivationConormalComponent_eq_zero_iff]
  constructor
  · intro h f hf
    apply h f
    rw [← hs]
    exact Ideal.subset_span hf
  · intro h x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem f hf => exact h f hf
    | zero => simpa only [map_zero] using I.zero_mem
    | add a b _ha _hb hda hdb =>
        simpa only [map_add] using I.add_mem hda hdb
    | smul a b hb hdb =>
        change d (a * b) ∈ I
        rw [d.leibniz]
        refine I.add_mem (I.smul_mem a hdb) ?_
        exact I.mul_mem_right (d a) (by rw [← hs]; exact hb)

/-- The finite test consists of derivative classes in the existing
quotient `B/I`, not a separately defined obstruction space. -/
theorem derivationConormalComponent_eq_zero_iff_quotient_on_generators
    (d : Derivation k B B) (I : Ideal B) (s : Finset B)
    (hs : Ideal.span (s : Set B) = I) :
    derivationConormalComponent d I = 0 ↔
      ∀ f ∈ s, Ideal.Quotient.mk I (d f) = 0 := by
  rw [derivationConormalComponent_eq_zero_iff_on_generators d I s hs]
  simp only [Ideal.Quotient.eq_zero_iff_mem]

/-- One ideal generating set simultaneously tests all the conormal
components of a supplied family of derivations. -/
theorem forall_derivationConormalComponent_eq_zero_iff_on_generators
    {ι : Sort*} (d : ι → Derivation k B B) (I : Ideal B) (s : Finset B)
    (hs : Ideal.span (s : Set B) = I) :
    (∀ i, derivationConormalComponent (d i) I = 0) ↔
      ∀ i f, f ∈ s → d i f ∈ I :=
  forall_congr' fun i =>
    derivationConormalComponent_eq_zero_iff_on_generators (d i) I s hs

/-- Finite generation supplies a finite conormal test valid for every
derivation, without selecting generators as additional geometric data. -/
theorem exists_finset_conormalTest_of_fg
    (I : Ideal B) (hI : I.FG) :
    ∃ s : Finset B, Ideal.span (s : Set B) = I ∧
      ∀ d : Derivation k B B,
        (derivationConormalComponent d I = 0 ↔ ∀ f ∈ s, d f ∈ I) := by
  obtain ⟨s, hs⟩ := hI
  exact ⟨s, hs, fun d =>
    derivationConormalComponent_eq_zero_iff_on_generators d I s hs⟩

end CollisionIdeals
