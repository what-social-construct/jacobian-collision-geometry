import CollisionIdeals.General.GenericFiber.CollisionDiagonal
import CollisionIdeals.General.ResidualCollision.Algebra
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Generic base change of the affine residual quotient

The first step in comparing the affine first-colon residual with the
intrinsic generic residual is to regard its quotient map as a map over
the coordinate-image algebra and then base-change that map to the
target function field.

The kernel comparison with the annihilator of the generic diagonal is
kept separate. For a clopen diagonal, complementary projection kernels
give that comparison without a general localization theorem for colons.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

open scoped TensorProduct

universe u v

variable {R : Type u} [CommRing R] [IsDomain R]
variable {ι κ : Type v}

/-- The off-diagonal quotient carries the coordinate-image algebra
structure induced by the left source map. -/
noncomputable def polynomialImageOffDiagonalAlgebra
    (F : κ → SourceRing R ι) :
    Algebra (polynomialMapImageAlgebra F) (OffDiagonalRing F) :=
  (((collisionToOffDiagonal F).comp (collisionLeft F)).comp
    (Subalgebra.val (polynomialMapImageAlgebra F))).toRingHom.toAlgebra

/-- The collision-to-off-diagonal quotient preserves the coordinate-image
base algebra. -/
noncomputable def polynomialImageCollisionToOffDiagonal
    (F : κ → SourceRing R ι) :
    letI : Algebra (polynomialMapImageAlgebra F) (CollisionRing F) :=
      polynomialImageCollisionAlgebra F
    letI : Algebra (polynomialMapImageAlgebra F) (OffDiagonalRing F) :=
      polynomialImageOffDiagonalAlgebra F
    CollisionRing F →ₐ[polynomialMapImageAlgebra F] OffDiagonalRing F := by
  let B := polynomialMapImageAlgebra F
  letI : Algebra B (CollisionRing F) := polynomialImageCollisionAlgebra F
  letI : Algebra B (OffDiagonalRing F) := polynomialImageOffDiagonalAlgebra F
  exact
    { toRingHom := (collisionToOffDiagonal F).toRingHom
      commutes' := by
        intro b
        rfl }

/-- Base change of the affine residual quotient to the target function
field. Its kernel is identified separately by the complementary-projector
comparison. -/
noncomputable def polynomialGenericCollisionToOffDiagonal
    (F : κ → SourceRing R ι) :
    let B := polynomialMapImageAlgebra F
    let K := PolynomialBaseFunctionField F
    letI : Algebra B (CollisionRing F) :=
      polynomialImageCollisionAlgebra F
    letI : Algebra B (OffDiagonalRing F) :=
      polynomialImageOffDiagonalAlgebra F
    (K ⊗[B] CollisionRing F) →ₐ[K]
      (K ⊗[B] OffDiagonalRing F) := by
  let B := polynomialMapImageAlgebra F
  let K := PolynomialBaseFunctionField F
  letI : Algebra B (CollisionRing F) := polynomialImageCollisionAlgebra F
  letI : Algebra B (OffDiagonalRing F) := polynomialImageOffDiagonalAlgebra F
  exact Algebra.TensorProduct.map (AlgHom.id K K)
    (polynomialImageCollisionToOffDiagonal F)

omit [IsDomain R] in
/-- Base change retains surjectivity of the collision-to-residual quotient. -/
theorem polynomialGenericCollisionToOffDiagonal_surjective
    (F : κ → SourceRing R ι) :
    let B := polynomialMapImageAlgebra F
    let K := PolynomialBaseFunctionField F
    letI : Algebra B (CollisionRing F) :=
      polynomialImageCollisionAlgebra F
    letI : Algebra B (OffDiagonalRing F) :=
      polynomialImageOffDiagonalAlgebra F
    Function.Surjective
      (polynomialGenericCollisionToOffDiagonal F :
        (K ⊗[B] CollisionRing F) →ₐ[K]
          (K ⊗[B] OffDiagonalRing F)) := by
  let B := polynomialMapImageAlgebra F
  let K := PolynomialBaseFunctionField F
  letI : Algebra B (CollisionRing F) := polynomialImageCollisionAlgebra F
  letI : Algebra B (OffDiagonalRing F) := polynomialImageOffDiagonalAlgebra F
  change Function.Surjective
    (Algebra.TensorProduct.map (AlgHom.id K K)
      (polynomialImageCollisionToOffDiagonal F))
  apply Algebra.TensorProduct.map_surjective
  · exact Function.surjective_id
  · change Function.Surjective (collisionToOffDiagonal F)
    exact Ideal.Quotient.factor_surjective
      (collisionIdeal_le_collisionOffDiagonalIdeal F)

end

end CollisionIdeals
