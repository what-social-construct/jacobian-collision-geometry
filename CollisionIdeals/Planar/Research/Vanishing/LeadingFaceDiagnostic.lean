import CollisionIdeals.General.Automorphism.Criteria
import CollisionIdeals.Planar.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A constant-Jacobian diagnostic for common leading-face zeros

The polynomial automorphism `(x + y², y + (x + y²)²)` has determinant
one. For the integer pole weights `(2, 1)`, its degree-two and degree-four
components have the common torus zero `(-1, 1)`. Thus the full Keller
identity does not by itself prohibit common dominant-face zeros.

The field-valued substitution `(x, y) = (u - t⁻², t⁻¹)` gives the outputs
`(u, t⁻¹ + u²)`: cancellation of both leading components does not make
both outputs regular. This is an algebraic negative control, not an
inertia example or a valuation above the affine target.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar.Research.LeadingFaceDiagnostic

noncomputable section

open MvPolynomial

/-- The first coordinate of the triangular-composition diagnostic. -/
def first : PlanePolynomial := X 0 + X 1 ^ 2

/-- The second coordinate of the same diagnostic. -/
def second : PlanePolynomial := X 1 + first ^ 2

/-- An actual polynomial map on the full complex affine plane. -/
def polynomialMap : PlanarPolynomialMap := ![first, second]

/-- The explicit polynomial inverse, in the target-coordinate variables. -/
def inverseMap : PlanarPolynomialMap :=
  ![X 0 - (X 1 - X 0 ^ 2) ^ 2, X 1 - X 0 ^ 2]

theorem second_sub_first_sq : second - first ^ 2 = X 1 := by
  simp [second]

theorem first_sub_recovered_second_sq :
    first - (second - first ^ 2) ^ 2 = X 0 := by
  rw [second_sub_first_sq]
  simp [first]

/-- Substituting the diagnostic into its displayed inverse recovers the
original source-coordinate polynomials. -/
theorem bind_polynomialMap_inverseMap (i : Fin 2) :
    bind₁ polynomialMap (inverseMap i) = X i := by
  fin_cases i <;> simp [inverseMap, polynomialMap, first, second]

/-- The displayed inverse is two-sided as a polynomial substitution. -/
theorem bind_inverseMap_polynomialMap (i : Fin 2) :
    bind₁ inverseMap (polynomialMap i) = X i := by
  fin_cases i <;> simp [inverseMap, polynomialMap, first, second]

/-- The diagnostic is a polynomial automorphism, not a proposed
counterexample to the Jacobian conjecture. -/
theorem polynomialMap_isPolynomialAutomorphism :
    IsPolynomialAutomorphism polynomialMap := by
  have hleft : (bind₁ inverseMap).comp (bind₁ polynomialMap) =
      AlgHom.id ℂ PlanePolynomial := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa only [AlgHom.comp_apply, bind₁_X_right, AlgHom.id_apply] using
      bind_inverseMap_polynomialMap i
  have hright : (bind₁ polynomialMap).comp (bind₁ inverseMap) =
      AlgHom.id ℂ PlanePolynomial := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa only [AlgHom.comp_apply, bind₁_X_right, AlgHom.id_apply] using
      bind_polynomialMap_inverseMap i
  have hli : Function.LeftInverse (bind₁ inverseMap) (bind₁ polynomialMap) :=
    fun p => DFunLike.congr_fun hleft p
  have hri : Function.RightInverse (bind₁ inverseMap) (bind₁ polynomialMap) :=
    fun p => DFunLike.congr_fun hright p
  exact ⟨hli.injective, hri.surjective⟩

/-- The full polynomial Jacobian identity, not only its linear part. -/
theorem polynomialMap_jacobian : planarJacobianDet polynomialMap = 1 := by
  change jacobianDet polynomialMap = 1
  rw [jacobianDet_fin_two]
  simp [polynomialMap, first, second]
  ring

theorem polynomialMap_isKeller : IsPlanarKeller polynomialMap := by
  exact ⟨1, one_ne_zero, by simpa using polynomialMap_jacobian⟩

/-- Positive pole weights, dual to additive coordinate values `(-2,-1)`.
The grading uses Mathlib's existing signed-integer weight type. -/
def weights : Fin 2 → ℤ := ![2, 1]

theorem first_isWeightedHomogeneous :
    first.IsWeightedHomogeneous weights (2 : ℤ) := by
  apply IsWeightedHomogeneous.add
  · simpa [weights] using (isWeightedHomogeneous_X (R := ℂ) weights (0 : Fin 2))
  · simpa [weights] using
      (isWeightedHomogeneous_X (R := ℂ) weights (1 : Fin 2)).pow 2

theorem first_sq_isWeightedHomogeneous :
    (first ^ 2).IsWeightedHomogeneous weights (4 : ℤ) := by
  simpa using first_isWeightedHomogeneous.pow 2

/-- The actual first-coordinate support has integer weight at most two. -/
theorem first_support_weight_le :
    ∀ a ∈ first.support, Finsupp.weight weights a ≤ (2 : ℤ) := by
  intro a ha
  exact le_of_eq (first_isWeightedHomogeneous (mem_support_iff.mp ha))

/-- The actual second-coordinate support has integer weight at most four. -/
theorem second_support_weight_le :
    ∀ a ∈ second.support, Finsupp.weight weights a ≤ (4 : ℤ) := by
  intro a ha
  change a ∈ (X (1 : Fin 2) + first ^ 2 : PlanePolynomial).support at ha
  rcases Finset.mem_union.mp (MvPolynomial.support_add ha) with hY | hSq
  · have hYHom : (X (1 : Fin 2) : PlanePolynomial).IsWeightedHomogeneous
        weights (1 : ℤ) := by
      simpa [weights] using (isWeightedHomogeneous_X (R := ℂ) weights (1 : Fin 2))
    rw [hYHom (mem_support_iff.mp hY)]
    norm_num
  · exact le_of_eq (first_sq_isWeightedHomogeneous (mem_support_iff.mp hSq))

/-- The actual degree-two Mathlib component of the first coordinate. -/
theorem first_component_two :
    weightedHomogeneousComponent weights (2 : ℤ) first = first :=
  first_isWeightedHomogeneous.weightedHomogeneousComponent_same

/-- The actual degree-four Mathlib component of the second coordinate. -/
theorem second_component_four :
    weightedHomogeneousComponent weights (4 : ℤ) second = first ^ 2 := by
  have hY : (X (1 : Fin 2) : PlanePolynomial).IsWeightedHomogeneous weights (1 : ℤ) := by
    simpa [weights] using (isWeightedHomogeneous_X (R := ℂ) weights (1 : Fin 2))
  unfold second
  rw [map_add, hY.weightedHomogeneousComponent_ne 4 (by norm_num),
    first_sq_isWeightedHomogeneous.weightedHomogeneousComponent_same, zero_add]

/-- Every other component of the first coordinate is zero. -/
theorem first_component_eq_zero (d : ℤ) (hd : d ≠ 2) :
    weightedHomogeneousComponent weights d first = 0 :=
  first_isWeightedHomogeneous.weightedHomogeneousComponent_ne d hd

/-- The second coordinate has only the degree-one and degree-four pieces. -/
theorem second_component_eq_zero (d : ℤ) (hd₁ : d ≠ 1) (hd₄ : d ≠ 4) :
    weightedHomogeneousComponent weights d second = 0 := by
  have hY : (X (1 : Fin 2) : PlanePolynomial).IsWeightedHomogeneous weights (1 : ℤ) := by
    simpa [weights] using (isWeightedHomogeneous_X (R := ℂ) weights (1 : Fin 2))
  unfold second
  rw [map_add, hY.weightedHomogeneousComponent_ne d hd₁,
    first_sq_isWeightedHomogeneous.weightedHomogeneousComponent_ne d hd₄, zero_add]

/-- A point with both coordinates nonzero on the common leading-face zero locus. -/
def leadingPoint : Fin 2 → ℂ := ![-1, 1]

theorem leadingPoint_coordinates_ne_zero (i : Fin 2) : leadingPoint i ≠ 0 := by
  fin_cases i <;> norm_num [leadingPoint]

theorem common_leading_components_zero :
    eval leadingPoint (weightedHomogeneousComponent weights (2 : ℤ) first) = 0 ∧
      eval leadingPoint (weightedHomogeneousComponent weights (4 : ℤ) second) = 0 := by
  rw [first_component_two, second_component_four]
  norm_num [first, leadingPoint]

/-- The leading components are functionally dependent even though the
full diagnostic map has Jacobian one. -/
theorem leading_components_jacobian_zero :
    jacobianDet (![first, first ^ 2] : PlanarPolynomialMap) = 0 := by
  rw [jacobianDet_fin_two]
  simp [first]
  ring

/-- An algebraic substitution that cancels the common dominant faces but
leaves the explicit `t⁻¹` term in the second output. No valuation or
affine-target regularity assumption is asserted. -/
theorem field_substitution
    {R : Type*} [Field R] [Algebra ℂ R] (t u : R) :
    aeval (![u - (t⁻¹) ^ 2, t⁻¹] : Fin 2 → R) first = u ∧
      aeval (![u - (t⁻¹) ^ 2, t⁻¹] : Fin 2 → R) second = t⁻¹ + u ^ 2 := by
  simp [first, second]

end

end CollisionIdeals.Planar.Research.LeadingFaceDiagnostic
