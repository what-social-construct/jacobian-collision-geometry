import CollisionIdeals.Planar.Research.Vanishing.BoundaryValuation
import CollisionIdeals.General.Normalization.ValuationInitialResidue
import CollisionIdeals.General.Normalization.WeightedInitialEvaluation
import CollisionIdeals.General.Normalization.Finiteness
import CollisionIdeals.General.Keller.MonomialWeights
import CollisionIdeals.Planar.Research.Vanishing.WeightedJacobian

/-!
# Weighted initial cancellation at the actual ramified divisor

The integer-valued valuation is normalized from the actual DVR subring
in the supplied normalization diagram. Its coordinate weights are the
values of the same inertia-moved sheet. Every positive-degree target
component has a normalized weighted top part with zero residue in that
same ring. Both target components have finite sharp weighted degrees,
and at least one of them is positive.

This is an evaluated residue relation, not a polynomial identity between
the two leading components or an assertion that a target shear exists.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals.Planar

noncomputable section

open MvPolynomial
open scoped WithZero

variable {F : PlanarPolynomialMap} {N : Type} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

@[reducible] local instance boundaryInitialBaseAlgebra : Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

private theorem conjugateSource_injective
    (D : PolynomialNormalClosureData F N) (g : D.galoisGroup) :
    letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    Function.Injective (polynomialConjugateSourceMap D g) := by
  letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  intro p q h
  simp only [polynomialConjugateSourceMap_apply] at h
  exact IsFractionRing.injective (PolynomialSourceCoordinateRing ℂ 2)
    (PolynomialMapSourceFunctionField F) (D.embedding.injective (g.injective h))

/-- Centeredness makes the ground field have normalized value one. -/
theorem ground_discreteBoundaryValuation_eq_one
    (D : PolynomialNormalizationDiagram (F := F) (N := N))
    (E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N))
    (c : ℂ) (hc : c ≠ 0) :
    letI : IsDiscreteValuationRing (D.valuationAt E).valuationRing :=
      (D.valuationAt E).topDiscrete
    letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    discreteValuationOfSubring (D.valuationAt E).valuationRing (algebraMap ℂ N c) = 1 := by
  letI : IsDiscreteValuationRing (D.valuationAt E).valuationRing :=
    (D.valuationAt E).topDiscrete
  letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  let v := discreteValuationOfSubring (D.valuationAt E).valuationRing
  have hle (a : ℂ) : v (algebraMap ℂ N a) ≤ 1 :=
    (discreteValuationOfSubring_le_one_iff _ _).mpr
      (ground_mem_boundaryValuationRing D E a)
  have hmul : v (algebraMap ℂ N c) * v (algebraMap ℂ N c⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one]
  apply le_antisymm (hle c)
  calc
    1 = v (algebraMap ℂ N c) * v (algebraMap ℂ N c⁻¹) := hmul.symm
    _ ≤ v (algebraMap ℂ N c) * 1 := mul_le_mul_right (hle c⁻¹) _
    _ = v (algebraMap ℂ N c) := mul_one _

/-- At a supplied ramified divisor, use the actual moved sheet and the
same DVR, not a monomial replacement of its valuation. The two sharp
degrees and all positive-degree initial residue cancellations are derived. -/
theorem exists_boundary_weighted_initial_residue_certificate
    (D : PolynomialNormalizationDiagram (F := F) (N := N))
    (hKeller : IsPlanarKeller F)
    (E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N)) :
    letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    letI : IsDiscreteValuationRing (D.valuationAt E).valuationRing :=
      (D.valuationAt E).topDiscrete
    let V := (D.valuationAt E).valuationRing
    let v := discreteValuationOfSubring V
    ∃ g σ : D.cover.normalClosure.galoisGroup,
      σ ∈ inertiaGroupAt (PolynomialMapBaseFunctionField F) V ∧
      σ ∉ D.cover.normalClosure.intermediateFixingSubgroup.map
        (MulAut.conj g).toMonoidHom ∧
      let φ := polynomialConjugateSourceMap D.cover.normalClosure g
      let w := valuationCoordinateWeights v φ
      (∃ i : Fin 2, 0 < w i) ∧
      ∃ m n : ℤ,
        weightedTotalDegree' w (F 0) = (m : WithBot ℤ) ∧
        weightedTotalDegree' w (F 1) = (n : WithBot ℤ) ∧
        (0 < m ∨ 0 < n) ∧
        ∀ (j : Fin 2) (d : ℤ),
          weightedTotalDegree' w (F j) = (d : WithBot ℤ) → 0 < d →
          ∃ a ∈ (F j).support, Finsupp.weight w a = d ∧
            ∃ z : V,
              (z : N) = φ (weightedHomogeneousComponent w d (F j)) /
                φ (monomial a (coeff a (F j))) ∧
              IsLocalRing.residue V z = 0 := by
  classical
  letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  letI : IsDiscreteValuationRing (D.valuationAt E).valuationRing :=
    (D.valuationAt E).topDiscrete
  let V := (D.valuationAt E).valuationRing
  let v := discreteValuationOfSubring V
  obtain ⟨g, σ, hσ, hMoved, i, hi⟩ :=
    exists_moved_coordinate_pole_at_ramified_divisor D hKeller E
  let φ := polynomialConjugateSourceMap D.cover.normalClosure g
  let w := valuationCoordinateWeights v φ
  have hφ : Function.Injective φ := conjugateSource_injective D.cover.normalClosure g
  have hScalar (c : ℂ) (hc : c ≠ 0) : v (algebraMap ℂ N c) = 1 :=
    ground_discreteBoundaryValuation_eq_one D E c hc
  have hRegular (j : Fin 2) : v (φ (F j)) ≤ 1 :=
    (discreteValuationOfSubring_le_one_iff V _).mpr
      (conjugateTarget_mem_boundaryValuationRing D E g j)
  have hwi : 0 < w i := (valuationCoordinateWeights_pos_iff v φ hφ i).mpr
    (lt_of_not_ge fun h => hi ((discreteValuationOfSubring_le_one_iff V _).mp h))
  letI : FiniteDimensional (PolynomialMapBaseFunctionField F)
      (PolynomialMapSourceFunctionField F) := D.cover.normalClosure.finiteIntermediate
  have hFne (j : Fin 2) : F j ≠ 0 := by
    intro h
    apply (X_ne_zero j : (X j : PlanePolynomial) ≠ 0)
    apply coordinateAlgHom_injective_of_finiteDimensional F
    simpa only [coordinateAlgHom_X, map_zero] using h
  have hFiniteDegree (j : Fin 2) :
      ∃ d : ℤ, weightedTotalDegree' w (F j) = (d : WithBot ℤ) := by
    have hbot : weightedTotalDegree' w (F j) ≠ ⊥ := by
      intro h
      exact hFne j ((weightedTotalDegree'_eq_bot_iff w (F j)).mp h)
    obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hbot
    exact ⟨d, hd.symm⟩
  obtain ⟨m, hm⟩ := hFiniteDegree 0
  obtain ⟨n, hn⟩ := hFiniteDegree 1
  have hPositive : 0 < m ∨ 0 < n := by
    obtain ⟨j, hj⟩ := exists_linearCoeff_ne_zero_of_isKeller F hKeller i
    have ha := mem_support_iff.mpr hj
    fin_cases j
    · have h := weight_le_of_weightedTotalDegree'_eq_int w (F 0) hm ha
      simp only [Finsupp.weight_single, one_smul] at h
      exact Or.inl (lt_of_lt_of_le hwi h)
    · have h := weight_le_of_weightedTotalDegree'_eq_int w (F 1) hn ha
      simp only [Finsupp.weight_single, one_smul] at h
      exact Or.inr (lt_of_lt_of_le hwi h)
  refine ⟨g, σ, hσ, hMoved, ⟨i, hwi⟩, m, n, hm, hn, hPositive, ?_⟩
  intro j d hdeg hd
  obtain ⟨a, ha⟩ := exists_coeff_ne_zero
    (weightedHomogeneousComponent_ne_zero_of_degree'_eq_int w (F j) hdeg)
  have hweight : Finsupp.weight w a = d := by
    by_contra h
    rw [coeff_weightedHomogeneousComponent, if_neg h] at ha
    exact ha rfl
  have hCoeff : coeff a (F j) ≠ 0 := by
    simpa only [coeff_weightedHomogeneousComponent, if_pos hweight] using ha
  have ht : v (φ (monomial a (coeff a (F j)))) = WithZero.exp d := by
    rw [valuation_monomial_eq_exp_weight v φ hφ hScalar a _ hCoeff, hweight]
  obtain ⟨z, hz, hres⟩ := exists_normalized_weightedComponent_residue_zero
    V φ hφ hScalar (F j) d hdeg hd (hRegular j)
    (φ (monomial a (coeff a (F j)))) ht
  exact ⟨a, mem_support_iff.mpr hCoeff, hweight, z, hz, hres⟩

/-- The nonzero initial-coordinate tuple lies in the residue field of
the original centered DVR. Every regular target component of positive
sharp degree vanishes there. This holds for each conjugate sheet. -/
theorem exists_boundary_initial_coordinate_tuple
    (D : PolynomialNormalizationDiagram (F := F) (N := N))
    (E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N))
    (g : D.cover.normalClosure.galoisGroup) :
    letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    letI : IsDiscreteValuationRing (D.valuationAt E).valuationRing :=
      (D.valuationAt E).topDiscrete
    let V := (D.valuationAt E).valuationRing
    letI : Algebra ℂ V := (boundaryGroundRingHom D E).toAlgebra
    let v := discreteValuationOfSubring V
    let φ := polynomialConjugateSourceMap D.cover.normalClosure g
    let w := valuationCoordinateWeights v φ
    ∃ z : Fin 2 → IsLocalRing.ResidueField V,
      (∀ i : Fin 2, z i ≠ 0) ∧
      ∀ (j : Fin 2) (d : ℤ),
        weightedTotalDegree' w (F j) = (d : WithBot ℤ) → 0 < d →
        aeval z (weightedHomogeneousComponent w d (F j)) = 0 := by
  letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  letI : IsDiscreteValuationRing (D.valuationAt E).valuationRing :=
    (D.valuationAt E).topDiscrete
  let V := (D.valuationAt E).valuationRing
  letI : Algebra ℂ V := (boundaryGroundRingHom D E).toAlgebra
  letI : IsScalarTower ℂ V N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let v := discreteValuationOfSubring V
  let φ := polynomialConjugateSourceMap D.cover.normalClosure g
  have hφ : Function.Injective φ := conjugateSource_injective D.cover.normalClosure g
  have hScalar (c : ℂ) (hc : c ≠ 0) : v (algebraMap ℂ N c) = 1 :=
    ground_discreteBoundaryValuation_eq_one D E c hc
  obtain ⟨π, hπ⟩ := exists_discreteValuationOfSubring_uniformizer V
  refine ⟨divisorialInitialCoordinates V φ hφ π hπ,
    divisorialInitialCoordinates_ne_zero V φ hφ π hπ, ?_⟩
  intro j d hdeg hd
  exact divisorialInitialCoordinates_weightedComponent_eq_zero
    V φ hφ hScalar π hπ (F j) d hdeg hd
    ((discreteValuationOfSubring_le_one_iff V _).mpr
      (conjugateTarget_mem_boundaryValuationRing D E g j))

/-- In the positive-degree branch, the actual initial tuple rules out
the balanced profile. A polar coordinate supplies the nonzero radial
direction. No positivity of both degrees is inferred from centeredness. -/
theorem not_boundary_balance_of_positive_degrees
    (D : PolynomialNormalizationDiagram (F := F) (N := N))
    (hKeller : IsPlanarKeller F)
    (E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N))
    (g : D.cover.normalClosure.galoisGroup) :
    letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    letI : IsDiscreteValuationRing (D.valuationAt E).valuationRing :=
      (D.valuationAt E).topDiscrete
    let V := (D.valuationAt E).valuationRing
    let v := discreteValuationOfSubring V
    let φ := polynomialConjugateSourceMap D.cover.normalClosure g
    let w := valuationCoordinateWeights v φ
    (∃ i : Fin 2, 0 < w i) →
    ∀ m n : ℤ,
      weightedTotalDegree' w (F 0) = (m : WithBot ℤ) →
      weightedTotalDegree' w (F 1) = (n : WithBot ℤ) →
      0 < m → 0 < n → m + n ≠ w 0 + w 1 := by
  letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  letI : IsDiscreteValuationRing (D.valuationAt E).valuationRing :=
    (D.valuationAt E).topDiscrete
  let V := (D.valuationAt E).valuationRing
  letI : Algebra ℂ V := (boundaryGroundRingHom D E).toAlgebra
  let v := discreteValuationOfSubring V
  let φ := polynomialConjugateSourceMap D.cover.normalClosure g
  let w := valuationCoordinateWeights v φ
  change (∃ i : Fin 2, 0 < w i) → ∀ m n : ℤ,
    weightedTotalDegree' w (F 0) = (m : WithBot ℤ) →
    weightedTotalDegree' w (F 1) = (n : WithBot ℤ) →
    0 < m → 0 < n → m + n ≠ w 0 + w 1
  intro hPole m n hPdeg hQdeg hm hn hBalance
  obtain ⟨z, hzne, hz⟩ := exists_boundary_initial_coordinate_tuple D E g
  obtain ⟨i, hi⟩ := hPole
  obtain ⟨c, hc, hJ⟩ := hKeller
  have hNotZero := not_common_zero_weightedComponents_of_balance
    F c hc hJ w m n
    (fun a ha => weight_le_of_weightedTotalDegree'_eq_int w (F 0) hPdeg ha)
    (fun a ha => weight_le_of_weightedTotalDegree'_eq_int w (F 1) hQdeg ha)
    hBalance z ⟨i, ne_of_gt hi, hzne i⟩
  exact hNotZero ⟨hz 0 m hPdeg hm, hz 1 n hQdeg hn⟩

end

end CollisionIdeals.Planar
