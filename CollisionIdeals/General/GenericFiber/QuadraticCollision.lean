import CollisionIdeals.General.GenericFiber.CollisionDiagonal
import CollisionIdeals.General.GenericFiber.QuadraticDecomposition
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Generic quadratic collision algebras

This file composes the degree-two marked-root decomposition with the
polynomial generic-collision bridge.  It packages the compatible product

`K ⊗_B C_F ≃ L × L`

and descends its nontrivial residual factor to the affine obstruction ideal.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

noncomputable section

open scoped TensorProduct

universe u v

section Polynomial

open MvPolynomial

variable
    {R : Type u} [CommRing R] [IsDomain R]
    {ι κ : Type v}

/--
The generic collision algebra of a polynomial map, supplied with a
degree-two power basis, is the product of its diagonal and residual copies
of the source function field.
-/
def polynomialGenericQuadraticCollisionEquiv
    (F : κ → SourceRing R ι)
    [Algebra.IsSeparable
      (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := R) (ι := ι))]
    (hsurj :
      Function.Surjective (polynomialGenericSourceTensorMap F))
    (pb :
      PowerBasis
        (PolynomialBaseFunctionField F)
        (PolynomialSourceFunctionField (R := R) (ι := ι)))
    (hdegree : pb.dim = 2) :
    letI : Algebra
        (polynomialMapImageAlgebra F) (CollisionRing F) :=
      polynomialImageCollisionAlgebra F
    (PolynomialBaseFunctionField F ⊗[polynomialMapImageAlgebra F]
        CollisionRing F) ≃ₐ[PolynomialBaseFunctionField F]
      PolynomialSourceFunctionField (R := R) (ι := ι) ×
        PolynomialSourceFunctionField (R := R) (ι := ι) := by
  let B := polynomialMapImageAlgebra F
  letI : Algebra B (CollisionRing F) :=
    polynomialImageCollisionAlgebra F
  exact
    (polynomialGenericCollisionEquiv F hsurj).trans
      ((quadraticTensorDecomposition
        (PolynomialBaseFunctionField F)
        (PolynomialSourceFunctionField (R := R) (ι := ι))
        pb hdegree).restrictScalars (PolynomialBaseFunctionField F))

/--
The polynomial quadratic decomposition carries the base-changed diagonal
evaluation to projection onto the first copy of the source function field.
-/
theorem fst_polynomialGenericQuadraticCollisionEquiv
    (F : κ → SourceRing R ι)
    [Algebra.IsSeparable
      (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := R) (ι := ι))]
    (hsurj :
      Function.Surjective (polynomialGenericSourceTensorMap F))
    (pb :
      PowerBasis
        (PolynomialBaseFunctionField F)
        (PolynomialSourceFunctionField (R := R) (ι := ι)))
    (hdegree : pb.dim = 2) :
    letI : Algebra
        (polynomialMapImageAlgebra F) (CollisionRing F) :=
      polynomialImageCollisionAlgebra F
    (AlgHom.fst
        (PolynomialBaseFunctionField F)
        (PolynomialSourceFunctionField (R := R) (ι := ι))
        (PolynomialSourceFunctionField (R := R) (ι := ι))).comp
          (polynomialGenericQuadraticCollisionEquiv
            F hsurj pb hdegree).toAlgHom =
      polynomialGenericCollisionDiagonal F hsurj := by
  let B := polynomialMapImageAlgebra F
  let K := PolynomialBaseFunctionField F
  let L := PolynomialSourceFunctionField (R := R) (ι := ι)
  let C := CollisionRing F
  letI : Algebra B C := polynomialImageCollisionAlgebra F
  apply AlgHom.ext
  intro x
  change
    (quadraticTensorDecomposition K L pb hdegree
      (polynomialGenericCollisionEquiv F hsurj x)).1 =
      polynomialGenericCollisionDiagonal F hsurj x
  calc
    _ = primitiveTensorDiagonal K L
          (polynomialGenericCollisionEquiv F hsurj x) :=
      AlgHom.congr_fun
        (fst_quadraticTensorDecomposition K L pb hdegree) _
    _ = polynomialGenericCollisionDiagonal F hsurj x :=
      AlgHom.congr_fun
        (polynomialGenericCollisionEquiv_intertwines_diagonal F hsurj) x

/--
Generic degree two forces a nonzero affine collision obstruction.

The positive finrank supplies generic-source surjectivity, separability and
a power basis give the compatible product `L × L`, and localization
flatness descends the nonzero kernel of first projection to `Obs(F)`.
-/
theorem polynomial_obstructionIdeal_ne_bot_of_finrank_eq_two
    (F : κ → SourceRing R ι)
    [Algebra.IsSeparable
      (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := R) (ι := ι))]
    (hdegree :
      Module.finrank
        (PolynomialBaseFunctionField F)
        (PolynomialSourceFunctionField (R := R) (ι := ι)) = 2) :
    obstructionIdeal F ≠ ⊥ := by
  let B := polynomialMapImageAlgebra F
  let K := PolynomialBaseFunctionField F
  let L := PolynomialSourceFunctionField (R := R) (ι := ι)
  let C := CollisionRing F
  change Module.finrank K L = 2 at hdegree
  have hpositive : 0 < Module.finrank K L := by omega
  letI : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos hpositive
  let pb : PowerBasis K L := Field.powerBasisOfFiniteOfSeparable K L
  have hpbdim : pb.dim = 2 :=
    (PowerBasis.finrank pb).symm.trans hdegree
  have hsurj :
      Function.Surjective (polynomialGenericSourceTensorMap F) :=
    polynomialGenericSourceTensorMap_surjective_of_finrank_pos F <| by
      simpa [K, L] using hpositive
  letI : Algebra B C := polynomialImageCollisionAlgebra F
  let e : K ⊗[B] C ≃ₐ[K] L × L :=
    polynomialGenericQuadraticCollisionEquiv
      F hsurj pb hpbdim
  exact
    polynomial_obstructionIdeal_ne_bot_of_generic_product
      F L hsurj e
      (fst_polynomialGenericQuadraticCollisionEquiv
        F hsurj pb hpbdim)

end Polynomial

end

end CollisionIdeals
