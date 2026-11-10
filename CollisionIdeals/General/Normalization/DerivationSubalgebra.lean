import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Restricting derivations to generated algebras and fractional images

Preservation of a generated algebra reduces to its base and generators.
Preservation of the base image in a fraction-field tower implies preservation
of the entire fraction-field image. Neither statement supplies preservation
of a normalization, a boundary localization, or a finite module stage.
-/

set_option autoImplicit false

namespace CollisionIdeals

section Adjoin

variable {k B N : Type*} [CommSemiring k] [CommSemiring B] [CommSemiring N]
  [Algebra k N] [Algebra B N]

/-- To preserve an algebra generated over `B`, a derivation need only
preserve its base image and send each generator into that same algebra. -/
theorem derivation_mem_adjoin_of_generators
    (d : Derivation k N N) (s : Set N)
    (hBase : ∀ b : B, d (algebraMap B N b) ∈ Algebra.adjoin B s)
    (hGenerators : ∀ x ∈ s, d x ∈ Algebra.adjoin B s)
    {z : N} (hz : z ∈ Algebra.adjoin B s) :
    d z ∈ Algebra.adjoin B s := by
  refine Algebra.adjoin_induction
    (p := fun z _ => d z ∈ Algebra.adjoin B s)
    hGenerators hBase ?_ ?_ hz
  · intro x y _ _ hx hy
    rw [map_add]
    exact (Algebra.adjoin B s).add_mem hx hy
  · intro x y hx hy hdx hdy
    rw [d.leibniz, smul_eq_mul, smul_eq_mul]
    exact (Algebra.adjoin B s).add_mem
      ((Algebra.adjoin B s).mul_mem hx hdy)
      ((Algebra.adjoin B s).mul_mem hy hdx)

end Adjoin

section FractionField

variable {k B K N : Type*} [CommRing k] [CommRing B]
  [Field K] [Field N] [Algebra B K] [IsFractionRing B K]
  [Algebra B N] [Algebra K N] [IsScalarTower B K N] [Algebra k N]

/-- A derivation preserving the embedded base image also preserves the
image of its fraction field. The argument is denominator differentiation;
it requires neither characteristic zero nor separability. -/
theorem derivation_mem_range_fractionRing_of_base
    (d : Derivation k N N)
    (hBase : ∀ b : B, d (algebraMap B N b) ∈ Set.range (algebraMap K N))
    {z : N} (hz : z ∈ Set.range (algebraMap K N)) :
    d z ∈ Set.range (algebraMap K N) := by
  obtain ⟨x, rfl⟩ := hz
  obtain ⟨a, b, _hb, rfl⟩ := IsFractionRing.div_surjective (A := B) x
  rw [map_div₀, ← IsScalarTower.algebraMap_apply B K N a,
    ← IsScalarTower.algebraMap_apply B K N b, d.leibniz_div]
  obtain ⟨da, hda⟩ := hBase a
  obtain ⟨db, hdb⟩ := hBase b
  refine ⟨(algebraMap B K b)⁻¹ ^ 2 *
    (algebraMap B K b * da - algebraMap B K a * db), ?_⟩
  simp only [map_mul, map_sub, map_pow, map_inv₀,
    ← IsScalarTower.algebraMap_apply B K N, hda, hdb, smul_eq_mul]

end FractionField

end CollisionIdeals
