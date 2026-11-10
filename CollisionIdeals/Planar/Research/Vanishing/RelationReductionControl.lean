import CollisionIdeals.Planar.Research.Vanishing.LeadingFaceDiagnostic
import CollisionIdeals.Planar.Research.Vanishing.BaseFrame
import CollisionIdeals.General.Normalization.FilteredPolynomialDerivation
import CollisionIdeals.General.Normalization.DerivationOrbit

/-!
# A relations-aware higher-degree positive control

For the existing degree-four polynomial automorphism
`(x + y², y + (x + y²)²)`, two monic polynomial reductions recover the
source coordinates. Their differences give explicit division-free
certificates in the original collision ideal, not a new projector.

The same reductions place both source coordinates in one finite target
polynomial-degree stage. The actual Keller frames preserve this stage,
so all frame words on either coordinate remain uniformly bounded there.

This is an explicit automorphism control. It supplies neither such a
reduction nor a uniform bound for an arbitrary polynomial Keller map.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CollisionIdeals

noncomputable section

open MvPolynomial

/-- The selected existing source Keller frame differentiates the target
coordinate polynomials by the corresponding target partial. -/
theorem planarKellerFrame_target_coordinate
    (F : PlanarPolynomialMap) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = C c) (i j : Fin 2) :
    (Fin.cases (planarKellerFirstFrame F c)
      (fun _ => planarKellerSecondFrame F c) i :
        Derivation ℂ PlanePolynomial PlanePolynomial) (F j) =
      if j = i then 1 else 0 := by
  fin_cases i <;> fin_cases j
  · exact planarKellerFirstFrame_apply_first F c hc hJ
  · exact planarKellerFirstFrame_apply_second F c
  · exact planarKellerSecondFrame_apply_first F c
  · exact planarKellerSecondFrame_apply_second F c hc hJ

/-- Every target-polynomial degree stage is preserved by both actual
source Keller frames. This does not place arbitrary source or invariant
elements in a target-polynomial stage. -/
theorem planarKellerFrame_preserves_targetDegreeStage
    (F : PlanarPolynomialMap) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = C c) (i : Fin 2) (m : ℕ)
    {z : PlanePolynomial} (hz : z ∈ evaluationDegreeStage ℂ F m) :
    (Fin.cases (planarKellerFirstFrame F c)
      (fun _ => planarKellerSecondFrame F c) i :
        Derivation ℂ PlanePolynomial PlanePolynomial) z ∈
      evaluationDegreeStage ℂ F m := by
  apply derivation_mem_evaluationDegreeStage F
    (Fin.cases (planarKellerFirstFrame F c)
      (fun _ => planarKellerSecondFrame F c) i)
    (fun j : Fin 2 => if j = i then 1 else 0) ?_ ?_ m hz
  · intro j
    by_cases h : j = i <;> simp [h]
  · intro j
    rw [planarKellerFrame_target_coordinate F c hc hJ]
    by_cases h : j = i <;> simp [h]

namespace Planar.Research.RelationReductionControl

open LeadingFaceDiagnostic (first second polynomialMap inverseMap)

/-- Subtracting the square of the first output eliminates the second
source-coordinate difference, with no division. -/
theorem second_coordinate_difference_certificate :
    diagonalGenerator (R := ℂ) (1 : Fin 2) =
      collisionGenerator polynomialMap 1 -
        (leftRename first + rightRename first) * collisionGenerator polynomialMap 0 := by
  simp [diagonalGenerator, collisionGenerator, polynomialMap, second, first]
  ring

/-- After the second-coordinate reduction, the first source-coordinate
difference has an explicit polynomial combination of the two collisions. -/
theorem first_coordinate_difference_certificate :
    diagonalGenerator (R := ℂ) (0 : Fin 2) =
      (1 + (leftRename (X (1 : Fin 2) : PlanePolynomial) + rightRename (X 1)) *
        (leftRename first + rightRename first)) * collisionGenerator polynomialMap 0 -
      (leftRename (X (1 : Fin 2) : PlanePolynomial) + rightRename (X 1)) *
        collisionGenerator polynomialMap 1 := by
  simp [diagonalGenerator, collisionGenerator, polynomialMap, second, first]
  ring

theorem second_coordinate_difference_mem_collisionIdeal :
    diagonalGenerator (R := ℂ) (1 : Fin 2) ∈ collisionIdeal polynomialMap := by
  rw [second_coordinate_difference_certificate]
  exact (collisionIdeal polynomialMap).sub_mem
    (Ideal.subset_span (Set.mem_range_self 1))
    ((collisionIdeal polynomialMap).mul_mem_left _
      (Ideal.subset_span (Set.mem_range_self 0)))

theorem first_coordinate_difference_mem_collisionIdeal :
    diagonalGenerator (R := ℂ) (0 : Fin 2) ∈ collisionIdeal polynomialMap := by
  rw [first_coordinate_difference_certificate]
  exact (collisionIdeal polynomialMap).sub_mem
    ((collisionIdeal polynomialMap).mul_mem_left _
      (Ideal.subset_span (Set.mem_range_self 0)))
    ((collisionIdeal polynomialMap).mul_mem_left _
      (Ideal.subset_span (Set.mem_range_self 1)))

theorem coordinate_difference_mem_collisionIdeal (j : Fin 2) :
    diagonalGenerator (R := ℂ) j ∈ collisionIdeal polynomialMap := by
  fin_cases j
  · exact first_coordinate_difference_mem_collisionIdeal
  · exact second_coordinate_difference_mem_collisionIdeal

/-- Equality of the original ideals follows directly from the displayed
polynomial certificates, without invoking an automorphism criterion. -/
theorem collisionIdeal_eq_diagonalIdeal :
    collisionIdeal polynomialMap = diagonalIdeal (R := ℂ) (ι := Fin 2) := by
  apply le_antisymm (collisionIdeal_le_diagonalIdeal polynomialMap)
  rw [diagonalIdeal, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  exact coordinate_difference_mem_collisionIdeal j

/-- Select the first or second existing source Keller frame. -/
def sourceFrame (i : Fin 2) : Derivation ℂ PlanePolynomial PlanePolynomial :=
  Fin.cases (planarKellerFirstFrame polynomialMap 1)
    (fun _ => planarKellerSecondFrame polynomialMap 1) i

theorem sourceFrame_target_coordinate (i j : Fin 2) :
    sourceFrame i (polynomialMap j) = if j = i then 1 else 0 := by
  have hJ : planarJacobianDet polynomialMap = C (1 : ℂ) := by
    simpa using LeadingFaceDiagnostic.polynomialMap_jacobian
  exact planarKellerFrame_target_coordinate polynomialMap 1 one_ne_zero hJ i j

theorem inverse_polynomial_totalDegree_le_four (j : Fin 2) :
    (inverseMap j).totalDegree ≤ 4 := by
  have hTwo : (X (1 : Fin 2) - X (0 : Fin 2) ^ 2 : PlanePolynomial).totalDegree ≤ 2 :=
    (totalDegree_sub _ _).trans (by simp)
  have hFour : ((X (1 : Fin 2) - X (0 : Fin 2) ^ 2 : PlanePolynomial) ^ 2).totalDegree ≤ 4 :=
    (totalDegree_pow _ _).trans (by omega)
  fin_cases j
  · change (X (0 : Fin 2) - (X (1 : Fin 2) - X (0 : Fin 2) ^ 2) ^ 2 :
      PlanePolynomial).totalDegree ≤ 4
    exact (totalDegree_sub _ _).trans (max_le (by simp) hFour)
  · change (X (1 : Fin 2) - X (0 : Fin 2) ^ 2 : PlanePolynomial).totalDegree ≤ 4
    exact hTwo.trans (by omega)

/-- Both source coordinates lie in the same finite target-degree stage,
despite the degree-four second coordinate of the original map. -/
theorem source_coordinate_mem_fixed_stage (j : Fin 2) :
    X j ∈ evaluationDegreeStage ℂ polynomialMap 4 := by
  refine ⟨inverseMap j,
    (mem_restrictTotalDegree (Fin 2) 4 _).mpr (inverse_polynomial_totalDegree_le_four j), ?_⟩
  rw [aeval_eq_bind₁]
  exact LeadingFaceDiagnostic.bind_polynomialMap_inverseMap j

/-- Target-coordinate duality preserves the same finite stage, not a
degree bound that grows with the number of derivatives. -/
theorem sourceFrame_preserves_fixed_stage (i : Fin 2) {z : PlanePolynomial}
    (hz : z ∈ evaluationDegreeStage ℂ polynomialMap 4) :
    sourceFrame i z ∈ evaluationDegreeStage ℂ polynomialMap 4 := by
  have hJ : planarJacobianDet polynomialMap = C (1 : ℂ) := by
    simpa using LeadingFaceDiagnostic.polynomialMap_jacobian
  exact planarKellerFrame_preserves_targetDegreeStage polynomialMap 1 one_ne_zero hJ i 4 hz

/-- Every word in both actual source frames applied to either source
coordinate remains in one fixed finite coefficient-field stage. -/
theorem every_sourceFrame_word_mem_fixed_stage (j : Fin 2) (word : List (Fin 2)) :
    derivationWordAction (fun i => (sourceFrame i).toLinearMap.toAddMonoidHom)
      word (X j) ∈ evaluationDegreeStage ℂ polynomialMap 4 := by
  induction word with
  | nil => exact source_coordinate_mem_fixed_stage j
  | cons i word ih => exact sourceFrame_preserves_fixed_stage i ih

theorem fixed_stage_finite :
    Module.Finite ℂ (evaluationDegreeStage ℂ polynomialMap 4) := inferInstance

end Planar.Research.RelationReductionControl

end

end CollisionIdeals
