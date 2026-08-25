import CollisionIdeals.General.Automorphism.Criteria
import CollisionIdeals.General.GenericFiber.CollisionDiagonal
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Localization.BaseChange

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

open scoped TensorProduct

noncomputable section

universe u v

open MvPolynomial

variable {R : Type u} [CommRing R] [IsDomain R]
variable {ι κ : Type v}

/--
A polynomial automorphism induces a trivial extension of function fields.
-/
theorem polynomialFunctionFieldExtensionTrivial_of_isPolynomialAutomorphism
    {F : ι → SourceRing R ι}
    (hF : IsPolynomialAutomorphism F) :
    PolynomialFunctionFieldExtensionTrivial F := by
  intro z
  obtain ⟨x, y, hy, hxy⟩ :=
    IsFractionRing.div_surjective
      (A := SourceRing R ι) z
  obtain ⟨px, hpx⟩ := hF.2 x
  obtain ⟨py, hpy⟩ := hF.2 y
  let bx : polynomialMapImageAlgebra F :=
    ⟨x, ⟨px, by
      simpa [coordinateAlgHom, MvPolynomial.aeval_eq_bind₁] using hpx⟩⟩
  let by' : polynomialMapImageAlgebra F :=
    ⟨y, ⟨py, by
      simpa [coordinateAlgHom, MvPolynomial.aeval_eq_bind₁] using hpy⟩⟩
  refine ⟨
    algebraMap (polynomialMapImageAlgebra F)
        (PolynomialBaseFunctionField F) bx /
      algebraMap (polynomialMapImageAlgebra F)
        (PolynomialBaseFunctionField F) by',
    ?_⟩
  rw [map_div₀]
  simp only [polynomialBaseFunctionFieldEmbedding,
    IsFractionRing.lift_algebraMap]
  change
    algebraMap (SourceRing R ι)
          (PolynomialSourceFunctionField (R := R) (ι := ι)) x /
        algebraMap (SourceRing R ι)
          (PolynomialSourceFunctionField (R := R) (ι := ι)) y = z
  exact hxy

/-- A trivial induced function-field extension has generic degree one. -/
theorem polynomialFunctionField_finrank_eq_one_of_extensionTrivial
    (F : κ → SourceRing R ι)
    (hTrivial : PolynomialFunctionFieldExtensionTrivial F) :
    Module.finrank
      (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := R) (ι := ι)) = 1 := by
  apply finrank_eq_one
    (1 : PolynomialSourceFunctionField (R := R) (ι := ι)) one_ne_zero
  intro z
  obtain ⟨c, hc⟩ := hTrivial z
  exact ⟨c, by simpa [Algebra.smul_def] using hc⟩

/-- A polynomial automorphism has generic degree one. -/
theorem polynomialFunctionField_finrank_eq_one_of_isPolynomialAutomorphism
    {F : ι → SourceRing R ι}
    (hF : IsPolynomialAutomorphism F) :
    Module.finrank
      (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := R) (ι := ι)) = 1 :=
  polynomialFunctionField_finrank_eq_one_of_extensionTrivial F
    (polynomialFunctionFieldExtensionTrivial_of_isPolynomialAutomorphism hF)

/--
If the induced function-field extension is trivial, the canonical map
`K ⊗_B A ⟶ L` is surjective.
-/
theorem polynomialGenericSourceTensorMap_surjective_of_extensionTrivial
    (F : κ → SourceRing R ι)
    (hTrivial : PolynomialFunctionFieldExtensionTrivial F) :
    Function.Surjective (polynomialGenericSourceTensorMap F) := by
  intro z
  obtain ⟨k, hk⟩ := hTrivial z
  refine ⟨k ⊗ₜ (1 : SourceRing R ι), ?_⟩
  simpa [polynomialGenericSourceTensorMap] using hk

/--
After generic base change, the collision diagonal is injective when the
induced function-field extension has degree one.
-/
theorem polynomialGenericCollisionDiagonal_injective_of_extensionTrivial
    (F : κ → SourceRing R ι)
    (hTrivial : PolynomialFunctionFieldExtensionTrivial F) :
    letI : Algebra
        (polynomialMapImageAlgebra F) (CollisionRing F) :=
      polynomialImageCollisionAlgebra F
    Function.Injective
      (Algebra.TensorProduct.map
        (AlgHom.id
          (PolynomialBaseFunctionField F)
          (PolynomialBaseFunctionField F))
        (polynomialImageCollisionDiagonal F)) := by
  let B := polynomialMapImageAlgebra F
  let A := SourceRing R ι
  let C := CollisionRing F
  let K := PolynomialBaseFunctionField F
  let L := PolynomialSourceFunctionField (R := R) (ι := ι)
  letI : Algebra B C := polynomialImageCollisionAlgebra F
  have hsurj :
      Function.Surjective (polynomialGenericSourceTensorMap F) :=
    polynomialGenericSourceTensorMap_surjective_of_extensionTrivial
      F hTrivial
  let φ : K ⊗[B] A ≃ₐ[K] L :=
    polynomialGenericSourceEquiv F hsurj
  have hmul :
      Function.Injective
        (diagonalMultiplication (B := K) (A := L)) :=
    diagonalMultiplication_injective_of_surjective hTrivial
  have hgeneric :
      Function.Injective
        (polynomialGenericCollisionDiagonal F hsurj) := by
    rw [← polynomialGenericCollisionEquiv_intertwines_diagonal F hsurj]
    exact hmul.comp (polynomialGenericCollisionEquiv F hsurj).injective
  have hcompat :
      polynomialGenericCollisionDiagonal F hsurj =
        φ.toAlgHom.comp
          (Algebra.TensorProduct.map
            (AlgHom.id K K)
            (polynomialImageCollisionDiagonal F)) := by
    rfl
  rw [hcompat] at hgeneric
  intro x y hxy
  apply hgeneric
  exact congrArg φ hxy

/--
Generic degree one kills the collision obstruction whenever the source
coordinate ring is flat over its coordinate image.
-/
theorem obstructionIdeal_eq_bot_of_functionFieldExtensionTrivial
    (F : κ → SourceRing R ι)
    (hFlat :
      Module.Flat
        (polynomialMapImageAlgebra F)
        (SourceRing R ι))
    (hTrivial : PolynomialFunctionFieldExtensionTrivial F) :
    obstructionIdeal F = ⊥ := by
  let B := polynomialMapImageAlgebra F
  let A := SourceRing R ι
  let C := CollisionRing F
  let K := PolynomialBaseFunctionField F
  letI : Algebra B C := polynomialImageCollisionAlgebra F
  letI : Module.Flat B A := hFlat
  letI : Module.Flat B C := polynomialCollisionRing_flat F
  have hDiagonal :
      Function.Injective (polynomialImageCollisionDiagonal F) :=
    injective_of_flat_source_of_baseChange
      (polynomialImageCollisionDiagonal F)
      (IsFractionRing.injective B K)
      (polynomialGenericCollisionDiagonal_injective_of_extensionTrivial
        F hTrivial)
  rw [← collisionDiagonal_ker]
  exact
    (RingHom.injective_iff_ker_eq_bot
      (polynomialImageCollisionDiagonal F).toRingHom).1 hDiagonal

end

end CollisionIdeals
