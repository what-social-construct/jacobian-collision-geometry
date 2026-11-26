import CollisionIdeals.General.Normalization.PrimitiveCoordinateRelation
import CollisionIdeals.General.GenericFiber.DerivativeDegreeOne
import CollisionIdeals.General.Keller.SourceIntersection
import CollisionIdeals.General.Automorphism.Criteria
import CollisionIdeals.Planar.Research.Vanishing.CoordinateRelationSecant

/-!
# Actual primitive relations for both planar source coordinates

Both relations are constructed from the original source and target rings.
Their generic scaling factors and evaluation kernels are derived. Testing
both evaluated derivatives avoids assuming Formanek's primitive-coordinate
theorem: each coordinate separately descends by the minimal-polynomial
test, and the source-intersection theorem then gives automorphy.

The required derivative memberships are not proved universally here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals.Planar

noncomputable section

open MvPolynomial

/-- Both actual coordinate kernels have constructed primitive generators,
with an explicit nonzero generic scale for their formal derivatives. -/
theorem exists_primitive_coordinate_relations_of_isKeller
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F) :
    let B := polynomialMapImageAlgebra F
    let K := PolynomialBaseFunctionField F
    let L := PolynomialSourceFunctionField (R := ℂ) (ι := Fin 2)
    ∃ (H : Fin 2 → Polynomial B) (u : Fin 2 → K),
      (∀ i, (H i).IsPrimitive) ∧ (∀ i, u i ≠ 0) ∧
      (∀ i, (H i).map (algebraMap B K) =
        Polynomial.C (u i) * minpoly K (algebraMap PlanePolynomial L (X i))) ∧
      (∀ i, Polynomial.aeval (X i : PlanePolynomial) (H i) = 0) ∧
      (∀ i, RingHom.ker (Polynomial.aeval (X i : PlanePolynomial)).toRingHom =
        Ideal.span {H i}) ∧
      (∀ i, algebraMap PlanePolynomial L
          (Polynomial.aeval (X i : PlanePolynomial) (H i).derivative) =
        algebraMap K L (u i) * Polynomial.aeval (algebraMap PlanePolynomial L (X i))
          (minpoly K (algebraMap PlanePolynomial L (X i))).derivative) := by
  let B := polynomialMapImageAlgebra F
  let K := PolynomialBaseFunctionField F
  let L := PolynomialSourceFunctionField (R := ℂ) (ι := Fin 2)
  let e := (AlgEquiv.ofInjective (coordinateAlgHom F)
    (coordinateAlgHom_injective_of_isKeller F hKeller)).toMulEquiv
  letI : UniqueFactorizationMonoid B := MulEquiv.uniqueFactorizationMonoid e inferInstance
  letI : NormalizedGCDMonoid B := Classical.choice inferInstance
  letI : FiniteDimensional K L :=
    polynomialSourceFunctionField_finiteDimensional_of_isKeller F hKeller
  have h (i : Fin 2) := exists_primitive_coordinate_relation
    (B := B) (K := K) (L := L) (X i : PlanePolynomial)
    (IsIntegral.of_finite K _)
  choose H u hprim hu hmap hzero hker hderiv using h
  exact ⟨H, u, hprim, hu, hmap, hzero, hker, hderiv⟩

/-- For a constructed relation family, membership of both evaluated
derivatives in the original target algebra suffices. No primitive-source
coordinate, normality, purity, or finite-etale rigidity input is used. -/
theorem obstructionIdeal_eq_bot_of_coordinate_relation_derivatives_mem_base
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F)
    (H : Fin 2 → Polynomial (polynomialMapImageAlgebra F))
    (u : Fin 2 → PolynomialBaseFunctionField F)
    (hu : ∀ i, u i ≠ 0)
    (hderiv : let K := PolynomialBaseFunctionField F
      let L := PolynomialSourceFunctionField (R := ℂ) (ι := Fin 2)
      ∀ i, algebraMap PlanePolynomial L
          (Polynomial.aeval (X i : PlanePolynomial) (H i).derivative) =
        algebraMap K L (u i) * Polynomial.aeval (algebraMap PlanePolynomial L (X i))
          (minpoly K (algebraMap PlanePolynomial L (X i))).derivative)
    (hbase : ∀ i, Polynomial.aeval (X i : PlanePolynomial) (H i).derivative ∈
      polynomialMapImageAlgebra F) :
    obstructionIdeal F = ⊥ := by
  let B := polynomialMapImageAlgebra F
  let K := PolynomialBaseFunctionField F
  let L := PolynomialSourceFunctionField (R := ℂ) (ι := Fin 2)
  letI : FiniteDimensional K L :=
    polynomialSourceFunctionField_finiteDimensional_of_isKeller F hKeller
  have hx (i : Fin 2) : (X i : PlanePolynomial) ∈ B := by
    let j : B := ⟨Polynomial.aeval (X i : PlanePolynomial) (H i).derivative, hbase i⟩
    have huL : algebraMap K L (u i) ≠ 0 := by
      simpa using (algebraMap K L).injective.ne (hu i)
    have hDerivative : Polynomial.aeval (algebraMap PlanePolynomial L (X i))
        (minpoly K (algebraMap PlanePolynomial L (X i))).derivative ∈
        Set.range (algebraMap K L) := by
      refine ⟨algebraMap B K j / u i, ?_⟩
      rw [map_div₀]
      apply (div_eq_iff huL).mpr
      calc
        algebraMap K L (algebraMap B K j) =
            algebraMap PlanePolynomial L (j : PlanePolynomial) := by
          rw [← IsScalarTower.algebraMap_apply B K L,
            IsScalarTower.algebraMap_apply B PlanePolynomial L]
          rfl
        _ = algebraMap K L (u i) * Polynomial.aeval
            (algebraMap PlanePolynomial L (X i))
            (minpoly K (algebraMap PlanePolynomial L (X i))).derivative := hderiv i
        _ = _ := mul_comm _ _
    exact (polynomialSource_mem_range_baseField_iff_of_isKeller F hKeller (X i)).mp
      (mem_range_of_minpoly_derivative_aeval_mem_range _
        (IsIntegral.of_finite K _) hDerivative)
  have htop : polynomialMapImageAlgebra F = ⊤ := by
    apply top_unique
    rw [← MvPolynomial.adjoin_range_X]
    exact Algebra.adjoin_le (by rintro _ ⟨i, rfl⟩; exact hx i)
  have hsurj : Function.Surjective (coordinateAlgHom F) := by
    rw [← AlgHom.range_eq_top]
    exact htop
  have hauto : IsPolynomialAutomorphism F := by
    have hbij : Function.Bijective (coordinateAlgHom F) :=
      ⟨coordinateAlgHom_injective_of_isKeller F hKeller, hsurj⟩
    simpa only [IsPolynomialAutomorphism, coordinateAlgHom, MvPolynomial.aeval_eq_bind₁]
      using hbij
  exact obstructionIdeal_eq_bot_of_isPolynomialAutomorphism hauto

end

end CollisionIdeals.Planar
