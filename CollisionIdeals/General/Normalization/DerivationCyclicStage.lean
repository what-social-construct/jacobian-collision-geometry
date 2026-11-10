import CollisionIdeals.General.Normalization.PolynomialConormal
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Escape from a cyclic module stage

If a scalar kills a class but its derivative does not, the corresponding
Leibniz operator sends the class outside its cyclic span. Over a
characteristic-zero polynomial algebra, every nonzero torsion class has
such an escaping coordinate operator.

The cyclic span is the existing standard submodule, not a new stage
structure. These results do not construct a larger preserved finite stage,
prove vanishing of the class, or assert normalization-boundary regularity.
-/

set_option autoImplicit false

namespace CollisionIdeals

section General

variable {k B M : Type*} [CommRing k] [CommRing B] [Algebra k B]
  [AddCommMonoid M] [Module B M]

/-- A scalar annihilator transverse to the derivation forces the class's
derivative outside its cyclic module span. -/
theorem not_mem_span_singleton_of_leibniz_transverse
    (d : Derivation k B B) (nabla : M →+ M)
    (hLeibniz : ∀ (b : B) (m : M),
      nabla (b • m) = d b • m + b • nabla m)
    (q : M) (a : B) (haq : a • q = 0) (hdaq : d a • q ≠ 0) :
    nabla q ∉ Submodule.span B ({q} : Set M) := by
  intro hmem
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hmem
  have hanabla : a • nabla q = 0 := by
    rw [← hb, smul_comm, haq, smul_zero]
  have h := hLeibniz a q
  rw [haq, map_zero, hanabla, add_zero] at h
  exact hdaq h.symm

end General

section Polynomial

variable {σ k B M : Type*} [Field k] [CharZero k] [CommRing B] [Algebra k B]
  [AddCommMonoid M] [Module B M]

/-- Some coordinate operator escapes the cyclic span of every nonzero
torsion class. Only an annihilator for this class is needed, not a uniform
annihilator of the whole module or module-finiteness. -/
theorem exists_polynomial_leibniz_not_mem_span_singleton
    (e : MvPolynomial σ k ≃ₐ[k] B) (nabla : σ → M →+ M)
    (hLeibniz : ∀ (i : σ) (b : B) (m : M),
      nabla i (b • m) = polynomialEquivPartial e i b • m + b • nabla i m)
    (q : M) (hq : q ≠ 0)
    (hTorsion : ∃ a : B, a ≠ 0 ∧ a • q = 0) :
    ∃ i : σ, nabla i q ∉ Submodule.span B ({q} : Set M) := by
  classical
  by_contra! hStage
  let I : Ideal B := (Submodule.span B ({q} : Set M)).annihilator
  obtain ⟨a, ha, haq⟩ := hTorsion
  have hI : I ≠ ⊥ := by
    intro hzero
    apply ha
    have haI : a ∈ I := (Submodule.mem_annihilator_span_singleton q a).mpr haq
    simpa only [hzero, Ideal.mem_bot] using haI
  have hItop : I = ⊤ :=
    (forall_polynomialEquivPartial_conormalComponent_eq_zero_iff e I hI).mp (by
      intro i
      apply (derivationConormalComponent_eq_zero_iff _ _).mpr
      intro b hb
      have hbq : b • q = 0 :=
        (Submodule.mem_annihilator_span_singleton q b).mp hb
      by_contra hdb
      have hdbq : polynomialEquivPartial e i b • q ≠ 0 := by
        intro hzero
        exact hdb ((Submodule.mem_annihilator_span_singleton q _).mpr hzero)
      exact (not_mem_span_singleton_of_leibniz_transverse
        (polynomialEquivPartial e i) (nabla i) (hLeibniz i) q b hbq hdbq) (hStage i))
  apply hq
  have hone : (1 : B) ∈ I := by
    rw [hItop]
    exact Submodule.mem_top
  simpa only [one_smul] using
    (Submodule.mem_annihilator_span_singleton q (1 : B)).mp hone

end Polynomial

end CollisionIdeals
