import CollisionIdeals.Planar.Research.InvariantQuotientAction
import CollisionIdeals.General.Keller.ConjugateInvariantSections
import CollisionIdeals.General.Normalization.DerivationOrbitStages
import CollisionIdeals.General.Normalization.DerivationJetTest

/-!
# Differential-orbit denominators on the actual boundary quotient

The existing quotient and Keller-frame operators are unchanged. Torsion
of a class supplies one initial annihilator and its powers clear every
fixed finite derivative order. A single denominator for all orders,
however, is equivalent to vanishing of that class by the already proved
polynomial annihilator argument.

No coherent preserved stage, uniform pole bound, or universal planar
vanishing statement is supplied as an extra premise or derived here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace CollisionIdeals

noncomputable section

variable {F : PlanarPolynomialMap} {N : Type} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

@[reducible] local instance differentialOrbitBaseAlgebra :
    Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

@[reducible] local instance differentialOrbitBaseFieldAlgebra :
    Algebra (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) :=
  OreLocalization.instAlgebra

local instance differentialOrbitBaseFieldSMul :
    SMul (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) := Algebra.toSMul

@[reducible] local instance differentialOrbitConjugateAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateAlgebra D)

@[reducible] local instance differentialOrbitInvariantAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateInvariantAlgebra D)

variable (D : PolynomialNormalClosureData F N)

local notation "B₀" => PolynomialImageAlgebra F
local notation "M₀" => polynomialConjugateInvariantAlgebra D ⧸ LinearMap.range
  (Algebra.linearMap B₀ (polynomialConjugateInvariantAlgebra D))

/-- The all-orders uniform denominator condition is an exact vanishing
criterion for the actual boundary class, not a consequence of torsion. -/
theorem planarKellerInvariantQuotient_uniform_annihilator_iff
    (c : ℂ) (hc : c ≠ 0) (hJ : planarJacobianDet F = MvPolynomial.C c)
    (q : M₀) :
    (∃ s : B₀, s ≠ 0 ∧ ∀ word : List (Fin 2),
      s • derivationWordAction
        (fun i => planarKellerInvariantQuotientOperator D c hc hJ i) word q = 0) ↔ q = 0 := by
  letI := D.finiteIntermediate
  exact exists_uniform_annihilator_derivationWords_iff
    (AlgEquiv.ofInjective (coordinateAlgHom F)
      (coordinateAlgHom_injective_of_finiteDimensional F))
    (fun i => planarKellerInvariantQuotientOperator D c hc hJ i)
    (fun i b m => planarKellerInvariantQuotientOperator_leibniz D c hc hJ i b m) q

/-- Choose one actual torsion annihilator. Its powers clear all words
at each fixed order, but the exponent grows with the order. -/
theorem planarKellerInvariantQuotient_exists_finite_order_power_annihilators
    (c : ℂ) (hc : c ≠ 0) (hJ : planarJacobianDet F = MvPolynomial.C c)
    (q : M₀) :
    ∃ a : B₀, a ≠ 0 ∧ a • q = 0 ∧
      ∀ (r : ℕ) (word : List (Fin 2)), word.length ≤ r →
        a ^ (r + 1) • derivationWordAction
          (fun i => planarKellerInvariantQuotientOperator D c hc hJ i) word q = 0 := by
  letI := D.finiteIntermediate
  letI : FiniteDimensional (PolynomialMapBaseFunctionField F) N := D.finiteNormal
  letI : Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N := inferInstance
  obtain ⟨⟨a, ha⟩, haq⟩ :=
    polynomialConjugateInvariantAlgebra_quotient_isTorsion D (x := q)
  refine ⟨a, nonZeroDivisors.ne_zero ha, haq, ?_⟩
  intro r word hword
  exact pow_order_succ_smul_derivationWordAction_eq_zero
    (fun i => polynomialImageCoordinatePartial F i)
    (fun i => planarKellerInvariantQuotientOperator D c hc hJ i)
    (fun i b m => planarKellerInvariantQuotientOperator_leibniz D c hc hJ i b m)
    a q haq r word hword

/-- A proposed target-polynomial denominator need only clear a finite
jet through its own total degree. This is a test, not an existence
assertion for a denominator meeting that degree bound. -/
theorem planarKellerInvariantQuotient_eq_zero_of_degree_jet
    (c : ℂ) (hc : c ≠ 0) (hJ : planarJacobianDet F = MvPolynomial.C c)
    (q : M₀) (r : ℕ) (f : PlanePolynomial) (hf : f ≠ 0)
    (hDegree : f.totalDegree ≤ r)
    (hJet : ∀ word : List (Fin 2), word.length ≤ r →
      (coordinateAlgHom F).rangeRestrict f • derivationWordAction
        (fun i => planarKellerInvariantQuotientOperator D c hc hJ i) word q = 0) :
    q = 0 := by
  letI := D.finiteIntermediate
  exact eq_zero_of_polynomial_annihilates_derivationJet
    (AlgEquiv.ofInjective (coordinateAlgHom F)
      (coordinateAlgHom_injective_of_finiteDimensional F))
    (fun i => planarKellerInvariantQuotientOperator D c hc hJ i)
    (fun i b m => planarKellerInvariantQuotientOperator_leibniz D c hc hJ i b m)
    q r f hf hDegree hJet

/-- Every proposed nonzero target-polynomial denominator misses a
derivative of a nonzero class by at most its total polynomial degree. -/
theorem planarKellerInvariantQuotient_denominator_degree_escape
    (c : ℂ) (hc : c ≠ 0) (hJ : planarJacobianDet F = MvPolynomial.C c)
    (q : M₀) (hq : q ≠ 0) (f : PlanePolynomial) (hf : f ≠ 0) :
    ∃ word : List (Fin 2), word.length ≤ f.totalDegree ∧
      (coordinateAlgHom F).rangeRestrict f • derivationWordAction
        (fun i => planarKellerInvariantQuotientOperator D c hc hJ i) word q ≠ 0 := by
  letI := D.finiteIntermediate
  exact exists_derivationWord_not_annihilated_length_le_degree
    (AlgEquiv.ofInjective (coordinateAlgHom F)
      (coordinateAlgHom_injective_of_finiteDimensional F))
    (fun i => planarKellerInvariantQuotientOperator D c hc hJ i)
    (fun i b m => planarKellerInvariantQuotientOperator_leibniz D c hc hJ i b m)
    q hq f hf

end

end CollisionIdeals
