import CollisionIdeals.General.Keller.ConjugateInvariantPole
import CollisionIdeals.Planar.Research.HeightOneBoundaryPole
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Regular pairs in the actual target boundary

A nonzero element of an ideal and a second element regular modulo it
exclude every height-one prime containing that ideal. The algebraic proof
adapts the Hodge sibling's `not_le_heightOne_of_regularPair`, using the
existing prescribed-element denominator in this project's Mathlib API.

Applied to the original target boundary ideal, the same exclusion kills
the original invariant quotient: a nonzero class already constructs a
height-one boundary prime. Pair membership and quotient regularity remain
explicit hypotheses. Neither is derived from the Keller condition here.
The target boundary is not the normalization fixed--moving ideal, and the
invariant quotient is not a redefinition of the collision obstruction.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals.Planar

noncomputable section

variable {T : Type*} [CommRing T] [IsDomain T] [IsNoetherianRing T]

/-- The regular-pair cancellation excludes height-one containment. Units
are allowed; no nonzero final quotient is required. -/
theorem not_le_heightOne_of_regularPair
    (J : Ideal T) (f g : T) (hf : f ∈ J) (hg : g ∈ J) (hf0 : f ≠ 0)
    (hRegular : IsSMulRegular (T ⧸ Ideal.span {f}) g)
    (p : PrimeSpectrum T) (hp : p.asIdeal.primeHeight = 1) :
    ¬ J ≤ p.asIdeal := by
  intro hJp
  obtain ⟨t, n, htp, hclear⟩ :=
    exists_heightOne_boundary_denominator_of_ne_zero J p hp hJp f hf0
  have hpow : g ^ n ∈ J ^ n := Ideal.pow_mem_pow hg n
  have ht : t ∈ Ideal.span {f} :=
    mem_of_isSMulRegular_quotient_of_smul_mem (hRegular.pow n)
      (by simpa only [smul_eq_mul, mul_comm] using hclear (g ^ n) hpow)
  exact htp ((Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hJp hf))) ht)

omit [IsNoetherianRing T] in
/-- A principal ideal contains such a pair only when its generator is a
unit. Thus selecting more generators of a proper principal ideal cannot
produce the required certificate. -/
theorem isUnit_of_regularPair_mem_span_singleton
    (s f g : T) (hf : f ∈ Ideal.span {s}) (hg : g ∈ Ideal.span {s})
    (hf0 : f ≠ 0) (hRegular : IsSMulRegular (T ⧸ Ideal.span {f}) g) :
    IsUnit s := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hf
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hg
  have hga : g • a ∈ Ideal.span {f} := by
    apply Ideal.mem_span_singleton.mpr
    refine ⟨b, ?_⟩
    simp only [smul_eq_mul]
    rw [ha, hb]
    ring
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp
    (mem_of_isSMulRegular_quotient_of_smul_mem hRegular hga)
  have hs : s * c = 1 := by
    apply mul_left_cancel₀ hf0
    calc
      f * (s * c) = s * (f * c) := by ring
      _ = s * a := by rw [← hc]
      _ = f * 1 := by rw [← ha, mul_one]
  exact isUnit_iff_dvd_one.mpr ⟨c, hs.symm⟩

end

end CollisionIdeals.Planar

namespace CollisionIdeals

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ} {F : PolynomialSelfMap k n}
variable {N : Type u} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]
variable [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]

@[reducible] local instance regularPairInvariantAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateInvariantAlgebra D)

local instance regularPairInvariantSMul (D : PolynomialNormalClosureData F N) :
    SMul (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) :=
  Algebra.toSMul

local instance regularPairInvariantModule (D : PolynomialNormalClosureData F N) :
    Module (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) :=
  Algebra.toModule

local notation "B₀" => PolynomialImageAlgebra F

local instance regularPairBoundaryQuotientSMul (f : B₀) :
    SMul B₀ (B₀ ⧸ Ideal.span {f}) :=
  Submodule.Quotient.instSMul (Ideal.span {f})

/-- A supplied regular pair in the actual target boundary forces each
class in the original invariant quotient to vanish. No such pair is
constructed for an arbitrary Keller map. -/
theorem polynomialConjugateInvariantQuotient_eq_zero_of_boundary_regularPair
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F)
    (f g : B₀)
    (hf : f ∈ polynomialConjugateInvariantBoundaryIdeal D hKeller)
    (hg : g ∈ polynomialConjugateInvariantBoundaryIdeal D hKeller)
    (hf0 : f ≠ 0) (hRegular : IsSMulRegular (B₀ ⧸ Ideal.span {f}) g)
    (q : polynomialConjugateInvariantAlgebra D ⧸ LinearMap.range
      (Algebra.linearMap B₀ (polynomialConjugateInvariantAlgebra D))) : q = 0 := by
  by_contra hq
  obtain ⟨_z, p, _a, _b, _hRep, hHeight, hOutside, _ha, _hb, _hb0, _hEq⟩ :=
    polynomialConjugateInvariantQuotient_exists_heightOne_boundary_pole D hKeller q hq
  have hBoundary : polynomialConjugateInvariantBoundaryIdeal D hKeller ≤ p.asIdeal := by
    have hZeroLocus : p ∈ PrimeSpectrum.zeroLocus
        (polynomialConjugateInvariantBoundaryIdeal D hKeller : Set B₀) := by
      rw [polynomialConjugateInvariantBoundaryIdeal_zeroLocus]
      exact hOutside
    exact hZeroLocus
  letI : IsNoetherianRing B₀ := polynomialImageAlgebra_isNoetherianRing F
  exact Planar.not_le_heightOne_of_regularPair _ f g hf hg hf0 hRegular p hHeight hBoundary

/-- A hypothetical nonzero original invariant class defeats every
regular-pair candidate in the actual target boundary. -/
theorem polynomialConjugateInvariantBoundary_not_regularPair_of_quotient_ne_zero
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F)
    (q : polynomialConjugateInvariantAlgebra D ⧸ LinearMap.range
      (Algebra.linearMap B₀ (polynomialConjugateInvariantAlgebra D))) (hq : q ≠ 0)
    (f g : B₀)
    (hf : f ∈ polynomialConjugateInvariantBoundaryIdeal D hKeller)
    (hg : g ∈ polynomialConjugateInvariantBoundaryIdeal D hKeller)
    (hf0 : f ≠ 0) : ¬ IsSMulRegular (B₀ ⧸ Ideal.span {f}) g := by
  intro hRegular
  exact hq (polynomialConjugateInvariantQuotient_eq_zero_of_boundary_regularPair
    D hKeller f g hf hg hf0 hRegular q)

end

end CollisionIdeals
