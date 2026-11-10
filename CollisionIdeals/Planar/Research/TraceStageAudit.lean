import CollisionIdeals.Planar.Research.PrincipalPartsStrategy
import Mathlib.RingTheory.Trace.Defs

/-!
# The trace-dual candidate on the target-field part

The existing trace-integral condition, evaluated at the unit of the
normalization ring, puts the field trace in the base image. On an element
already in the target field, the trace is multiplication by the extension
degree. If that degree is a unit in the base, the element itself is in the
base image. A characteristic-zero field algebra supplies the degree unit
internally for every finite field extension.

Thus intersecting the old trace-dual bounded stage with the target field
cannot produce a nonzero class modulo the base in this setting. This is a
candidate audit, not vanishing of the entire target-section quotient. No
converse, finite-stage preservation, or boundary-regularity claim is made.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar.Research

noncomputable section

variable {B K T N : Type*}
variable [CommRing B] [Field K] [CommRing T] [Field N]
variable [Algebra B K] [Algebra B T] [Algebra B N] [Algebra K N] [Algebra T N]
variable [IsScalarTower B K N] [IsScalarTower B T N]
variable [FiniteDimensional K N]

/-- Testing trace integrality against the unit already puts the field
trace in the original base image. -/
theorem traceIntegralSubmodule_trace_mem_base
    (z : N) (hz : z ∈ TraceIntegralSubmodule B K T N) :
    Algebra.trace K N z ∈ Set.range (algebraMap B K) := by
  have h := hz (1 : T)
  simpa only [map_one, mul_one] using h

/-- A trace-integral element already in the target field belongs to the
base image whenever the finite extension degree is a unit in the base. -/
theorem mem_base_of_algebraMap_mem_traceIntegralSubmodule_of_degree_isUnit
    (r : K) (hDegree : IsUnit (Module.finrank K N : B))
    (hz : algebraMap K N r ∈ TraceIntegralSubmodule B K T N) :
    r ∈ Set.range (algebraMap B K) := by
  have htrace := traceIntegralSubmodule_trace_mem_base (B := B) (K := K) (T := T)
    (algebraMap K N r) hz
  rw [Algebra.trace_algebraMap, nsmul_eq_mul] at htrace
  obtain ⟨b, hb⟩ := htrace
  obtain ⟨u, hu⟩ := hDegree
  have hcancel : (↑u⁻¹ : B) * (Module.finrank K N : B) = 1 := by
    rw [← hu]
    exact u.inv_mul
  have hdegree : algebraMap B K (Module.finrank K N : B) =
      (Module.finrank K N : K) := by simp
  refine ⟨(↑u⁻¹ : B) * b, ?_⟩
  calc
    algebraMap B K ((↑u⁻¹ : B) * b) =
        algebraMap B K (↑u⁻¹ : B) * ((Module.finrank K N : K) * r) := by
      rw [map_mul, hb]
    _ = (algebraMap B K (↑u⁻¹ : B) *
        algebraMap B K (Module.finrank K N : B)) * r := by
      rw [hdegree, mul_assoc]
    _ = r := by rw [← map_mul, hcancel, map_one, one_mul]

omit [Algebra B K] [Algebra B N] [IsScalarTower B K N] in
private theorem traceDegree_isUnit_of_charZero
    (k : Type*) [Field k] [CharZero k] [Algebra k B] :
    IsUnit (Module.finrank K N : B) := by
  have hn : Module.finrank K N ≠ 0 :=
    ne_of_gt (Module.finrank_pos (R := K) (M := N))
  have hnk : (Module.finrank K N : k) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simpa only [map_natCast] using
    (isUnit_iff_ne_zero.mpr hnk).map (algebraMap k B)

/-- In a characteristic-zero field algebra the finite extension degree is
automatically a unit, so no degree-unit hypothesis remains in this test. -/
theorem mem_base_of_algebraMap_mem_traceIntegralSubmodule_charZero
    (k : Type*) [Field k] [CharZero k] [Algebra k B]
    (r : K) (hz : algebraMap K N r ∈ TraceIntegralSubmodule B K T N) :
    r ∈ Set.range (algebraMap B K) :=
  mem_base_of_algebraMap_mem_traceIntegralSubmodule_of_degree_isUnit r
    (traceDegree_isUnit_of_charZero (B := B) (K := K) (N := N) k) hz

end

end CollisionIdeals.Planar.Research
