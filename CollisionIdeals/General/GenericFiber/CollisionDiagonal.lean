module

public import CollisionIdeals.General.GenericFiber.DiagonalObstruction
public import CollisionIdeals.General.GenericFiber.FunctionField
public import CollisionIdeals.General.GenericFiber.MarkedRootDecomposition
public import Mathlib.RingTheory.Flat.Localization

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

noncomputable section

open scoped TensorProduct

universe u v w

section Primitive

variable (K : Type u) (L : Type u)
variable [Field K] [Field L] [Algebra K L]

/-- Tensor multiplication viewed over `K` is the ordinary diagonal map. -/
theorem primitiveTensorDiagonal_restrictScalars :
    (primitiveTensorDiagonal K L).restrictScalars K =
      diagonalMultiplication (B := K) (A := L) := by
  rfl

end Primitive

section Polynomial

open MvPolynomial

variable {R : Type u} [CommRing R] [IsDomain R]
variable {ι κ : Type v}

/--
The affine collision diagonal after passage to the generic point and
identification `K ⊗_B A ≃ L`.
-/
noncomputable def polynomialGenericCollisionDiagonal
    (F : κ → SourceRing R ι)
    (hsurj :
      Function.Surjective (polynomialGenericSourceTensorMap F)) :
    letI : Algebra
        (polynomialMapImageAlgebra F) (CollisionRing F) :=
      polynomialImageCollisionAlgebra F
    (PolynomialBaseFunctionField F ⊗[polynomialMapImageAlgebra F]
      CollisionRing F) →ₐ[PolynomialBaseFunctionField F]
        PolynomialSourceFunctionField (R := R) (ι := ι) := by
  let B := polynomialMapImageAlgebra F
  let K := PolynomialBaseFunctionField F
  letI : Algebra B (CollisionRing F) :=
    polynomialImageCollisionAlgebra F
  exact
    (polynomialGenericSourceEquiv F hsurj).toAlgHom.comp
      (Algebra.TensorProduct.map
        (AlgHom.id K K)
        (polynomialImageCollisionDiagonal F))

set_option backward.isDefEq.respectTransparency false in
/--
The generic collision equivalence carries the base-changed affine
diagonal to multiplication on `L ⊗_K L`.
-/
theorem polynomialGenericCollisionEquiv_intertwines_diagonal
    (F : κ → SourceRing R ι)
    (hsurj :
      Function.Surjective (polynomialGenericSourceTensorMap F)) :
    letI : Algebra
        (polynomialMapImageAlgebra F) (CollisionRing F) :=
      polynomialImageCollisionAlgebra F
    ((primitiveTensorDiagonal
        (PolynomialBaseFunctionField F)
        (PolynomialSourceFunctionField (R := R) (ι := ι))).restrictScalars
          (PolynomialBaseFunctionField F)).comp
        (polynomialGenericCollisionEquiv F hsurj).toAlgHom =
      polynomialGenericCollisionDiagonal F hsurj := by
  let B := polynomialMapImageAlgebra F
  let A := SourceRing R ι
  let C := CollisionRing F
  let K := PolynomialBaseFunctionField F
  let L := PolynomialSourceFunctionField (R := R) (ι := ι)
  letI : Algebra B C := polynomialImageCollisionAlgebra F
  let φ : K ⊗[B] A ≃ₐ[K] L :=
    polynomialGenericSourceEquiv F hsurj
  rw [primitiveTensorDiagonal_restrictScalars K L]
  change
    (diagonalMultiplication (B := K) (A := L)).comp
        ((Algebra.TensorProduct.congr φ φ).toAlgHom.comp
          (polynomialGenericCollisionSelfTensorEquiv F).toAlgHom) =
      φ.toAlgHom.comp
        (Algebra.TensorProduct.map
          (AlgHom.id K K)
          (polynomialImageCollisionDiagonal F))
  erw [← AlgHom.comp_assoc]
  have hbase :=
    baseChangeSelfTensorEquiv_intertwines_diagonal B A K L φ.toAlgHom
  rw [show
      (diagonalMultiplication (B := K) (A := L)).comp
          (Algebra.TensorProduct.congr φ φ).toAlgHom =
        (diagonalMultiplication (B := K) (A := L)).comp
          (Algebra.TensorProduct.map φ.toAlgHom φ.toAlgHom) by rfl]
  change
    ((diagonalMultiplication (B := K) (A := L)).comp
        ((Algebra.TensorProduct.map φ.toAlgHom φ.toAlgHom).comp
          (baseChangeSelfTensorEquiv B A K).toAlgHom)).comp
        (Algebra.TensorProduct.congr
          (AlgEquiv.refl : K ≃ₐ[K] K)
          (collisionImageTensorEquiv F)).toAlgHom =
      φ.toAlgHom.comp
        (Algebra.TensorProduct.map
          (AlgHom.id K K)
          (polynomialImageCollisionDiagonal F))
  rw [hbase]
  ext c
  simp only [AlgHom.coe_comp, Function.comp_apply]
  change
    φ
        ((1 : K) ⊗ₜ[B]
          diagonalMultiplication (B := B) (A := A)
            (collisionImageTensorEquiv F c)) =
      φ
        ((1 : K) ⊗ₜ[B]
          polynomialImageCollisionDiagonal F c)
  have hc :=
    AlgHom.congr_fun
      (collisionImageTensorEquiv_intertwines_diagonal F) c
  change
    diagonalMultiplication (B := B) (A := A)
        (collisionImageTensorEquiv F c) =
      polynomialImageCollisionDiagonal F c at hc
  rw [hc]

/--
A nontrivial second factor in a compatible generic collision product was
already present in the affine collision ring: the affine diagonal kernel,
equivalently the obstruction ideal, is nonzero.
-/
theorem polynomial_obstructionIdeal_ne_bot_of_generic_product
    (F : κ → SourceRing R ι)
    (N : Type w) [CommRing N] [Nontrivial N]
    [Algebra (PolynomialBaseFunctionField F) N]
    (hsurj :
      Function.Surjective (polynomialGenericSourceTensorMap F))
    (e :
      letI : Algebra
          (polynomialMapImageAlgebra F) (CollisionRing F) :=
        polynomialImageCollisionAlgebra F
      (PolynomialBaseFunctionField F ⊗[polynomialMapImageAlgebra F]
          CollisionRing F) ≃ₐ[PolynomialBaseFunctionField F]
        PolynomialSourceFunctionField (R := R) (ι := ι) × N)
    (hdiag :
      letI : Algebra
          (polynomialMapImageAlgebra F) (CollisionRing F) :=
        polynomialImageCollisionAlgebra F
      (AlgHom.fst
          (PolynomialBaseFunctionField F)
          (PolynomialSourceFunctionField (R := R) (ι := ι))
          N).comp e.toAlgHom =
        polynomialGenericCollisionDiagonal F hsurj) :
    obstructionIdeal F ≠ ⊥ := by
  let B := polynomialMapImageAlgebra F
  let C := CollisionRing F
  let K := PolynomialBaseFunctionField F
  letI : Algebra B C := polynomialImageCollisionAlgebra F
  letI : Module.Flat B K :=
    IsLocalization.flat K (nonZeroDivisors B)
  have hker :
      RingHom.ker (polynomialImageCollisionDiagonal F).toRingHom ≠ ⊥ :=
    ker_ne_bot_of_flat_baseChange_product
      (polynomialImageCollisionDiagonal F)
      (polynomialGenericSourceEquiv F hsurj)
      e hdiag
  change RingHom.ker (collisionDiagonal F).toRingHom ≠ ⊥ at hker
  simpa only [collisionDiagonal_ker] using hker

end Polynomial

end

end CollisionIdeals
