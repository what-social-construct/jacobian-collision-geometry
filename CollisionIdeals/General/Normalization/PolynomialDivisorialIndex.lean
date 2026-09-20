import CollisionIdeals.General.Normalization.DivisorialIndex
import CollisionIdeals.General.Normalization.DivisorialHeight
import CollisionIdeals.General.Normalization.DivisorialInertia
import CollisionIdeals.General.Normalization.ConjugateCenters

/-!
# The local index on a conjugate polynomial sheet

The dimension-independent divisorial formula is applied to the actual
normal-closure marking `g ∘ ι`. It therefore gives the same center and
conjugated fixing subgroup used by the polynomial normalization diagram.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

noncomputable section

universe u

variable {k : Type u} [Field k] [CharZero k] {n : ℕ}
  {F : PolynomialSelfMap k n} {N : Type u} [Field N]
  [Algebra (PolynomialMapBaseFunctionField F) N]
  [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]

set_option maxHeartbeats 800000 in
/-- The actual center on `gH` has index `[I : I ∩ gHg⁻¹]`, with inertia
of the constructed divisorial valuation. -/
theorem polynomialConjugateCenter_localRamificationIndex_eq
    (D : PolynomialNormalClosureData F N)
    (q : PrimeSpectrum (PolynomialNormalizationInExtensionRing (F := F) (N := N)))
    (hq : Ideal.primeHeight
      (R := PolynomialNormalizationInExtensionRing (F := F) (N := N)) q.asIdeal = 1)
    (g : D.galoisGroup) :
    localRamificationIndex (R := PolynomialImageAlgebra F)
        (S := PolynomialIntermediateNormalizationRing F)
        (polynomialConjugateCenter D q g).asIdeal =
      inertiaQuotientIndex
        (inertiaGroupAt (PolynomialMapBaseFunctionField F)
          (polynomialDivisorialValuation D q hq).valuationRing)
        (D.intermediateFixingSubgroup.map (MulAut.conj g).toMonoidHom) := by
  let B : Type u := PolynomialImageAlgebra F
  let K : Type u := PolynomialMapBaseFunctionField F
  let L : Type u := PolynomialMapSourceFunctionField F
  letI algebraBK : Algebra B K := OreLocalization.instAlgebra
  letI : SMul B K := algebraBK.toSMul
  -- Keep this instance local to the actual normal-closure field: a
  -- polymorphic instance would also replace the source-field algebra.
  letI : Algebra B N := polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI : IsScalarTower B K N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : FiniteDimensional K L := D.finiteIntermediate
  letI : FiniteDimensional K N := D.finiteNormal
  letI : Normal K N := D.normal
  letI : IsGalois K N := IsGalois.mk
  letI : IsIntegrallyClosed B :=
    polynomialImageAlgebra_isIntegrallyClosed_of_finiteDimensional F
  letI : IsNoetherianRing B := polynomialImageAlgebra_isNoetherianRing F
  let e := g.toAlgHom.comp D.embedding
  have hindex := integralClosure_localRamificationIndex_eq k B L N e q.asIdeal
    (polynomialNormalization_primeHeight_under_eq_one D q hq)
  have hring : (e.restrictScalars B).mapIntegralClosure.toRingHom =
      (polynomialConjugateNormalizationRingMap D g).toRingHom := by
    ext x
    rfl
  rw [polynomialDivisorialValuation_inertiaGroupAt_eq D q hq]
  simpa only [hring, e, fixingSubgroup_conjugate_embedding,
    NormalClosureData.intermediateFixingSubgroup, NormalClosureData.intermediateField]
    using hindex

end

end CollisionIdeals
