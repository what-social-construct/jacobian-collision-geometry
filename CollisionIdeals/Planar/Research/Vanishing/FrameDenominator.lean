import CollisionIdeals.Planar.Research.SecantFrameDenominator

/-!
# Denominators for derivations on a finite order

If a field derivation is regular on the base coefficients, clearing its
values on finitely many module generators clears its values on the whole
finite order. The proof uses the Leibniz rule, not linearity over the base.
It reuses the existing finite-coefficient denominator ideal.

The resulting nonzero denominator need not avoid a prescribed prime.
Consequently this statement alone does not establish regularity of an
extended Keller frame at a boundary divisor.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

universe u v w z

variable {k : Type z} [CommRing k]
variable (B : Type u) [CommRing B]
variable (T : Type v) [CommRing T] [Algebra B T]
variable (N : Type w) [Field N] [Algebra T N] [Algebra B N] [Algebra k N]
variable [IsScalarTower B T N]

/-- Under regularity on base coefficients, clearing a derivation on module
generators is equivalent to clearing it on the whole order. -/
theorem mem_finiteCoefficientDenominatorIdeal_derivation_iff
    (D : Derivation k N N)
    (hbase : ∀ b : B, D (algebraMap B N b) ∈ (1 : Submodule T N))
    {n : ℕ} (generators : Fin n → T)
    (hgen : Submodule.span B (Set.range generators) = ⊤) (s : T) :
    s ∈ finiteCoefficientDenominatorIdeal T N
        (fun i => D (algebraMap T N (generators i))) ↔
      ∀ t : T, s • D (algebraMap T N t) ∈ (1 : Submodule T N) := by
  rw [mem_finiteCoefficientDenominatorIdeal_iff]
  constructor
  · intro h t
    have ht : t ∈ Submodule.span B (Set.range generators) := by
      rw [hgen]
      trivial
    refine Submodule.span_induction (p := fun t _ =>
      s • D (algebraMap T N t) ∈ (1 : Submodule T N)) ?_ ?_ ?_ ?_ ht
    · rintro x ⟨i, rfl⟩
      exact h i
    · simp
    · intro x y hx hy ihx ihy
      rw [map_add, map_add, smul_add]
      exact (1 : Submodule T N).add_mem ihx ihy
    · intro b x hx ih
      have hvalue : algebraMap T N (b • x) =
          algebraMap B N b * algebraMap T N x := by
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply B T N]
      rw [hvalue, D.leibniz, smul_add]
      have hfirst := (1 : Submodule T N).smul_mem (algebraMap B T b) ih
      have hsecond := (1 : Submodule T N).smul_mem (s * x) (hbase b)
      convert (1 : Submodule T N).add_mem hfirst hsecond using 1
      simp only [Algebra.smul_def, Algebra.algebraMap_self_apply, map_mul,
        ← IsScalarTower.algebraMap_apply B T N]
      ring
  · intro h i
    exact h (generators i)

variable [IsDomain T] [Module.Finite B T] [IsFractionRing T N]

/-- A derivation regular on the base coefficients admits a nonzero common
denominator on a finite order inside its fraction field. -/
theorem exists_nonzero_derivation_denominator_of_finite
    (D : Derivation k N N)
    (hbase : ∀ b : B, D (algebraMap B N b) ∈ (1 : Submodule T N)) :
    ∃ s : T, s ≠ 0 ∧ ∀ t : T,
      s • D (algebraMap T N t) ∈ (1 : Submodule T N) := by
  obtain ⟨n, generators, hgen⟩ := Module.Finite.exists_fin (R := B) (M := T)
  have hnonzero := finiteCoefficientDenominatorIdeal_ne_bot T N
    (fun i : Fin n => D (algebraMap T N (generators i)))
  obtain ⟨s, hs, hsnonzero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnonzero
  exact ⟨s, hsnonzero,
    (mem_finiteCoefficientDenominatorIdeal_derivation_iff B T N D hbase
      generators hgen s).mp hs⟩

/-- Two derivations regular on the base have a simultaneous nonzero
denominator on the finite order. -/
theorem exists_nonzero_common_derivation_denominator_of_finite
    (D₀ D₁ : Derivation k N N)
    (hbase₀ : ∀ b : B, D₀ (algebraMap B N b) ∈ (1 : Submodule T N))
    (hbase₁ : ∀ b : B, D₁ (algebraMap B N b) ∈ (1 : Submodule T N)) :
    ∃ s : T, s ≠ 0 ∧
      (∀ t : T, s • D₀ (algebraMap T N t) ∈ (1 : Submodule T N)) ∧
      (∀ t : T, s • D₁ (algebraMap T N t) ∈ (1 : Submodule T N)) := by
  obtain ⟨s₀, hs₀, h₀⟩ := exists_nonzero_derivation_denominator_of_finite B T N D₀ hbase₀
  obtain ⟨s₁, hs₁, h₁⟩ := exists_nonzero_derivation_denominator_of_finite B T N D₁ hbase₁
  refine ⟨s₀ * s₁, mul_ne_zero hs₀ hs₁, ?_, ?_⟩
  · intro t
    simpa only [smul_smul, mul_comm] using (1 : Submodule T N).smul_mem s₁ (h₀ t)
  · intro t
    simpa only [smul_smul] using (1 : Submodule T N).smul_mem s₀ (h₁ t)

end

end CollisionIdeals.Planar
