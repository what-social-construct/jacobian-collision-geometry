import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Ideal.Span

/-!
# Primitive eliminants and evaluation kernels

Gauss descent for a primitive one-variable eliminant.  The generic
divisibility hypothesis can be supplied by the minimal polynomial in a
fraction-field fibre; the second hypothesis says that the cleared
eliminant vanishes in the original algebra.
-/

set_option autoImplicit false

namespace CollisionIdeals

open Polynomial

noncomputable section

universe u v w

variable {A : Type u} {K : Type v} {R : Type w}
variable [CommRing A] [IsDomain A] [NormalizedGCDMonoid A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [CommRing R] [Algebra A R]

/-- A primitive polynomial that divides another polynomial after passage
to the fraction field already divides it over the base domain. -/
theorem primitive_dvd_of_fraction_map_dvd {G P : A[X]}
    (hG : G.IsPrimitive)
    (hdiv : G.map (algebraMap A K) ∣ P.map (algebraMap A K)) : G ∣ P := by
  by_cases hPzero : P = 0
  · subst P
    exact dvd_zero G
  have hcontent : P.content ≠ 0 := by
    intro hc
    exact hPzero (content_eq_zero_iff.mp hc)
  have hcontentMap : (algebraMap A K) P.content ≠ 0 :=
    by simpa using (IsFractionRing.injective A K).ne hcontent
  have hunit : IsUnit (C ((algebraMap A K) P.content) : K[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcontentMap)
  have hPmap : P.map (algebraMap A K) =
      C ((algebraMap A K) P.content) * P.primPart.map (algebraMap A K) := by
    conv_lhs => rw [P.eq_C_content_mul_primPart]
    simp
  have hprimDiv : G.map (algebraMap A K) ∣ P.primPart.map (algebraMap A K) := by
    rw [hPmap] at hdiv
    exact hunit.dvd_mul_left.mp hdiv
  have hbaseDiv : G ∣ P.primPart :=
    hG.dvd_of_fraction_map_dvd_fraction_map P.isPrimitive_primPart hprimDiv
  exact (hG.dvd_primPart_iff_dvd hPzero).mp hbaseDiv

/-- If a primitive eliminant vanishes in an algebra and divides every
generic annihilating polynomial, it generates the integral evaluation
kernel. -/
theorem eval_kernel_eq_span_primitive_eliminant (z : R) (G : A[X])
    (hG : G.IsPrimitive) (hzero : aeval z G = 0)
    (hgeneric : ∀ P : A[X], aeval z P = 0 →
      G.map (algebraMap A K) ∣ P.map (algebraMap A K)) :
    RingHom.ker (aeval z).toRingHom = Ideal.span {G} := by
  apply le_antisymm
  · intro P hP
    apply Ideal.mem_span_singleton.mpr
    apply primitive_dvd_of_fraction_map_dvd (K := K) hG
    exact hgeneric P hP
  · apply Ideal.span_le.mpr
    intro P hP
    rw [Set.mem_singleton_iff] at hP
    rw [hP]
    change aeval z G = 0
    exact hzero

end

end CollisionIdeals
