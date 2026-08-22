import CollisionIdeals.ComplexThree.Cubic.FunctionField
import CollisionIdeals.ComplexThree.Statements.JacobianConjecture
import CollisionIdeals.ComplexThree.OffDiagonal
import CollisionIdeals.ComplexThree.Cubic.Branch

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

noncomputable section

open scoped TensorProduct

universe uN

/--
The structural dimension-three conclusion, without choosing coordinates
for a particular counterexample.

For a complex three-dimensional Keller map whose induced extension is
cubic and whose chosen normal-closure realization is in the nonnormal
cubic case, the generic collision algebra is

`K ⊗_B C_F ≃ L × N`.

The first factor is the diagonal factor.  The field `N` is the nonzero
residual normal-closure factor, its Galois group over `K` is `S₃`, and the
generic factor descends to a nonzero affine obstruction:

`obstructionIdeal F ≠ ⊥` and `collisionIdeal F < diagonalIdeal`.

The Keller hypothesis records the geometric setting.  The algebraic
factorization itself is supplied by the explicit generic, cubic,
normal-closure, and nonnormality data below; the residual-field
identification is constructed internally from the nonnormal cubic branch.
-/
theorem complexThreeCubicS3Collision
    (F : ComplexThreePolynomialMap)
    (hKeller : IsComplexThreeKeller F)
    (N : Type uN) [Field N]
    [Algebra ComplexThreeSourceFunctionField N]
    [Algebra (ComplexThreeBaseFunctionField F) N]
    [IsScalarTower
      (ComplexThreeBaseFunctionField F)
      ComplexThreeSourceFunctionField
      N]
    [Algebra.IsSeparable
      (ComplexThreeBaseFunctionField F)
      ComplexThreeSourceFunctionField]
    (normalClosure :
      NormalClosureData
        (ComplexThreeBaseFunctionField F)
        ComplexThreeSourceFunctionField
        N)
    (hmarked :
      normalClosure.embedding =
        IsScalarTower.toAlgHom
          (ComplexThreeBaseFunctionField F)
          ComplexThreeSourceFunctionField
          N)
    (hsurj :
      Function.Surjective (polynomialGenericSourceTensorMap F))
    (pb :
      PowerBasis
        (ComplexThreeBaseFunctionField F)
        ComplexThreeSourceFunctionField)
    (hdegree : pb.dim = 3)
    (hNotNormal :
      ¬ Normal
        (ComplexThreeBaseFunctionField F)
        ComplexThreeSourceFunctionField) :
    letI : Algebra
        (polynomialMapImageAlgebra F) (CollisionRing F) :=
      polynomialImageCollisionAlgebra F
    IsComplexThreeJacobianCounterexample F ∧
      obstructionIdeal F ≠ ⊥ ∧
      collisionIdeal F <
        diagonalIdeal (R := ℂ) (ι := Fin 3) ∧
      Nonempty (ComplexThreeOffDiagonalScheme F) ∧
      Nonempty
        (((ComplexThreeBaseFunctionField F ⊗[
              polynomialMapImageAlgebra F] CollisionRing F) ≃ₐ[
                ComplexThreeBaseFunctionField F]
              ComplexThreeSourceFunctionField × N) ×
          CubicS3CollisionWitness
            (ComplexThreeBaseFunctionField F)
            ComplexThreeSourceFunctionField
            N pb) := by
  letI : Algebra
      (polynomialMapImageAlgebra F) (CollisionRing F) :=
    polynomialImageCollisionAlgebra F
  let residualEquiv :
      CubicResidualAlgebra
          (ComplexThreeBaseFunctionField F)
          ComplexThreeSourceFunctionField
          pb ≃ₐ[ComplexThreeSourceFunctionField] N :=
    cubicResidualEquivNormalClosureOfNotNormal
      (ComplexThreeBaseFunctionField F)
      ComplexThreeSourceFunctionField N normalClosure hmarked pb hdegree
      hNotNormal
  have hObstruction : obstructionIdeal F ≠ ⊥ :=
    polynomial_obstructionIdeal_ne_bot_of_cubicResidual
      F N hsurj pb residualEquiv
  have hStrict :
      collisionIdeal F <
        diagonalIdeal (R := ℂ) (ι := Fin 3) :=
    polynomial_collisionIdeal_lt_diagonalIdeal_of_cubicResidual
      F N hsurj pb residualEquiv
  have hOffDiagonal :
      Nonempty (ComplexThreeOffDiagonalScheme F) :=
    (complexThreeOffDiagonalScheme_nonempty_iff_obstructionIdeal_ne_bot
      F).2 hObstruction
  have hCounterexample :
      IsComplexThreeJacobianCounterexample F := by
    refine ⟨hKeller, ?_⟩
    intro hAutomorphism
    exact hObstruction
      (obstructionIdeal_eq_bot_of_isPolynomialAutomorphism
        hAutomorphism)
  exact
    ⟨hCounterexample, hObstruction, hStrict, hOffDiagonal,
      exists_polynomialCubicS3CollisionWitness_of_normalClosure
        F N normalClosure hmarked hsurj pb hdegree residualEquiv
          (normalClosure.intermediateFixingSubgroup_ne_bot_of_not_normal
            hNotNormal)⟩

end

end CollisionIdeals
