import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Valuation bounds on finite base-module stages

If the base ring has valuation at most one, a finitely generated base
submodule of an overfield has a common valuation upper bound. Adding a
base element does not change this conclusion. Thus a family with
unbounded valuation cannot lie in one finite stage, even modulo the base.

These are finite-module bounds, not bounds on finite type algebras or
finite-dimensional function-field extensions. No derivative orbit is
asserted to lie in such a stage.
-/

set_option autoImplicit false

namespace CollisionIdeals

section Bounds

variable {B N Γ₀ : Type*} [CommRing B] [Field N] [Algebra B N]
  [LinearOrderedCommGroupWithZero Γ₀]

/-- Base-linear combinations preserve a common valuation bound when
every base coefficient has valuation at most one. -/
theorem valuation_le_of_mem_span
    (v : Valuation N Γ₀)
    (hBase : ∀ b : B, v (algebraMap B N b) ≤ 1)
    (s : Set N) (C : Γ₀) (hGenerators : ∀ z ∈ s, v z ≤ C)
    {z : N} (hz : z ∈ Submodule.span B s) : v z ≤ C := by
  induction hz using Submodule.span_induction with
  | mem z hz => exact hGenerators z hz
  | zero => simpa only [map_zero] using (zero_le' : (0 : Γ₀) ≤ C)
  | add x y _ _ hx hy => exact v.map_add_le hx hy
  | smul b x _ hx =>
      rw [Algebra.smul_def, map_mul]
      exact (mul_le_mul_left (hBase b) (v x)).trans
        (by simpa only [one_mul] using hx)

/-- A finite base submodule of the valued field admits one common bound.
The bound may be chosen at least one, also covering the zero stage. -/
theorem exists_valuation_bound_of_finite_submodule
    (v : Valuation N Γ₀)
    (hBase : ∀ b : B, v (algebraMap B N b) ≤ 1)
    (Λ : Submodule B N) [Module.Finite B Λ] :
    ∃ C : Γ₀, 1 ≤ C ∧ ∀ z ∈ Λ, v z ≤ C := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.iff_fg.mp inferInstance : Λ.FG)
  refine ⟨max 1 (s.sup v), le_max_left _ _, ?_⟩
  intro z hz
  apply valuation_le_of_mem_span v hBase (s : Set N) (max 1 (s.sup v))
    (fun x hx => (Finset.le_sup (f := v) hx).trans (le_max_right _ _))
  simpa only [hs] using hz

/-- The same finite-stage bound holds after adding arbitrary base
elements, so passing to classes modulo the base cannot hide an unbounded
pole tower. -/
theorem exists_valuation_bound_of_finite_submodule_mod_base
    (v : Valuation N Γ₀)
    (hBase : ∀ b : B, v (algebraMap B N b) ≤ 1)
    (Λ : Submodule B N) [Module.Finite B Λ] :
    ∃ C : Γ₀, 1 ≤ C ∧
      ∀ (z : N), z ∈ Λ → ∀ b : B, v (z + algebraMap B N b) ≤ C := by
  obtain ⟨C, hC, hΛ⟩ := exists_valuation_bound_of_finite_submodule v hBase Λ
  exact ⟨C, hC, fun z hz b => v.map_add_le (hΛ z hz) ((hBase b).trans hC)⟩

/-- A valuation-unbounded family escapes every finite base stage even
after allowing arbitrary additions from the base. -/
theorem exists_not_mem_finite_submodule_mod_base_of_unbounded_valuation
    {ι : Type*} (v : Valuation N Γ₀)
    (hBase : ∀ b : B, v (algebraMap B N b) ≤ 1)
    (z : ι → N) (hUnbounded : ∀ C : Γ₀, ∃ i : ι, C < v (z i))
    (Λ : Submodule B N) [Module.Finite B Λ] :
    ∃ i : ι, ¬ ∃ a ∈ Λ, ∃ b : B, z i = a + algebraMap B N b := by
  obtain ⟨C, _, hBound⟩ := exists_valuation_bound_of_finite_submodule_mod_base v hBase Λ
  obtain ⟨i, hi⟩ := hUnbounded C
  refine ⟨i, ?_⟩
  rintro ⟨a, ha, b, hEq⟩
  apply (not_le_of_gt hi)
  rw [hEq]
  exact hBound a ha b

end Bounds

end CollisionIdeals
