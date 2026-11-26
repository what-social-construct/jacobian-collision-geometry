import CollisionIdeals.General.Normalization.PrimitiveEliminant
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Polynomial.Tower

/-!
# Constructing the primitive relation of an actual source element

Clear the minimal polynomial over the base fraction field, then take its
primitive part. The resulting polynomial vanishes in the original source
ring and generates its evaluation kernel. Its evaluated derivative is a
nonzero base-field multiple of the minimal-polynomial derivative.

This constructs the coordinate relation itself; neither its existence nor
its integral evaluation kernel is supplied as an extra hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CollisionIdeals

open Polynomial

noncomputable section

variable {B K A L : Type*}
variable [CommRing B] [IsDomain B] [NormalizedGCDMonoid B]
variable [Field K] [Algebra B K] [IsFractionRing B K]
variable [CommRing A] [Algebra B A]
variable [Field L] [Algebra A L] [IsFractionRing A L]
variable [Algebra B L] [Algebra K L]
variable [IsScalarTower B A L] [IsScalarTower B K L]

/-- The primitive relation of an actual source element is constructed by
clearing its generic minimal polynomial and dividing out the content. -/
theorem exists_primitive_coordinate_relation
    (z : A) (hz : IsIntegral K (algebraMap A L z)) :
    ∃ (H : B[X]) (u : K), H.IsPrimitive ∧ u ≠ 0 ∧
      H.map (algebraMap B K) = C u * minpoly K (algebraMap A L z) ∧
      aeval z H = 0 ∧ RingHom.ker (aeval z).toRingHom = Ideal.span {H} ∧
      algebraMap A L (aeval z H.derivative) =
        algebraMap K L u * aeval (algebraMap A L z)
          (minpoly K (algebraMap A L z)).derivative := by
  let a := algebraMap A L z
  let m := minpoly K a
  let P := IsLocalization.integerNormalization (nonZeroDivisors B) m
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors B) m
  have hb0 : algebraMap B K (b : B) ≠ 0 :=
    by simp [nonZeroDivisors.coe_ne_zero b]
  have hPmap : P.map (algebraMap B K) = C (algebraMap B K (b : B)) * m := by
    rw [← IsScalarTower.algebraMap_smul K] at hb
    simpa only [P, Polynomial.smul_eq_C_mul] using hb
  have hm0 : m ≠ 0 := (minpoly.monic hz).ne_zero
  have hP0 : P ≠ 0 := by
    intro h
    have hmap0 := hPmap
    rw [h, Polynomial.map_zero] at hmap0
    exact (mul_ne_zero (Polynomial.C_ne_zero.mpr hb0) hm0) hmap0.symm
  have hc0 : algebraMap B K P.content ≠ 0 :=
    by simpa using (IsFractionRing.injective B K).ne (content_eq_zero_iff.not.mpr hP0)
  let H := P.primPart
  let u := algebraMap B K (b : B) / algebraMap B K P.content
  have hu : u ≠ 0 := div_ne_zero hb0 hc0
  have hcu : algebraMap B K P.content * u = algebraMap B K (b : B) := by
    dsimp [u]
    field_simp
  have hHmap : H.map (algebraMap B K) = C u * m := by
    apply mul_left_cancel₀ (show (C (algebraMap B K P.content) : K[X]) ≠ 0 by
      simpa using hc0)
    calc
      C (algebraMap B K P.content) * H.map (algebraMap B K) =
          P.map (algebraMap B K) := by
        conv_rhs => rw [P.eq_C_content_mul_primPart]
        simp only [Polynomial.map_mul, Polynomial.map_C, H]
      _ = C (algebraMap B K (b : B)) * m := hPmap
      _ = C (algebraMap B K P.content) * (C u * m) := by
        rw [← mul_assoc, ← map_mul, hcu]
  have hzero : aeval z H = 0 := by
    apply IsFractionRing.injective A L
    rw [map_zero, ← aeval_algebraMap_apply L z H, ← aeval_map_algebraMap K]
    rw [hHmap, map_mul, aeval_C]
    simp only [m, a, minpoly.aeval, mul_zero]
  have hker : RingHom.ker (aeval z).toRingHom = Ideal.span {H} := by
    apply eval_kernel_eq_span_primitive_eliminant (K := K) z H P.isPrimitive_primPart hzero
    intro Q hQ
    have hQzero : aeval a (Q.map (algebraMap B K)) = 0 := by
      rw [aeval_map_algebraMap, aeval_algebraMap_apply L z Q, hQ, map_zero]
    have hdvd : m ∣ Q.map (algebraMap B K) := minpoly.dvd K a hQzero
    rw [hHmap]
    obtain ⟨q, hq⟩ := hdvd
    refine ⟨C u⁻¹ * q, ?_⟩
    rw [hq]
    calc
      m * q = (C u * C u⁻¹) * (m * q) := by
        rw [← map_mul, mul_inv_cancel₀ hu, map_one, one_mul]
      _ = C u * m * (C u⁻¹ * q) := by ring
  refine ⟨H, u, P.isPrimitive_primPart, hu, hHmap, hzero, hker, ?_⟩
  rw [← aeval_algebraMap_apply L z H.derivative, ← aeval_map_algebraMap K]
  have hderiv : H.derivative.map (algebraMap B K) = C u * m.derivative := by
    rw [← Polynomial.derivative_map, hHmap, Polynomial.derivative_C_mul]
  rw [hderiv, map_mul, aeval_C]

end

end CollisionIdeals
