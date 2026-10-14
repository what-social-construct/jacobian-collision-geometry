module

public import CollisionIdeals.ComplexThree.Cubic.GaloisGroup
public import CollisionIdeals.General.GenericFiber.CollisionDiagonal
public import CollisionIdeals.General.GenericFiber.FunctionField
public import CollisionIdeals.General.GenericFiber.MarkedRootDecomposition

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

namespace CollisionIdeals

noncomputable section

open scoped TensorProduct

universe u v w

variable
    (K : Type u) [Field K]
    (L : Type v) [Field L] [Algebra K L]

/--
The residual conjugate algebra belonging to a chosen primitive generator.

For a cubic extension this is the degree-two factor left after removing
the chosen root from the base-changed minimal polynomial.  In the
nonnormal cubic case it is a field and realizes the normal closure over
the marked-root field.
-/
abbrev CubicResidualAlgebra (pb : PowerBasis K L) :=
  AdjoinRoot (minpolyDiv K pb.gen)

/--
The canonical generic self-collision decomposition of a separable
power-basis extension.

When `pb.dim = 3`, the first factor is the marked (diagonal) root and the
second factor is the residual two-root algebra.
-/
def cubicGenericCollisionEquiv
    [Algebra.IsSeparable K L] (pb : PowerBasis K L) :
    L ⊗[K] L ≃ₐ[L] L × CubicResidualAlgebra K L pb :=
  primitiveTensorDecomposition K L pb

/--
The first factor of the generic cubic collision decomposition is exactly
tensor multiplication, hence exactly the generic diagonal.
-/
theorem fst_cubicGenericCollisionEquiv
    [Algebra.IsSeparable K L] (pb : PowerBasis K L) :
    (AlgHom.fst L L (CubicResidualAlgebra K L pb)).comp
        (cubicGenericCollisionEquiv K L pb).toAlgHom =
      primitiveTensorDiagonal K L :=
  fst_primitiveTensorDecomposition K L pb

variable
    (N : Type w) [Field N]
    [Algebra L N]

/--
Transport the residual conjugate factor to a chosen field realization
`N`.  In the intended cubic application, `N` is the normal closure.
-/
def cubicGenericCollisionEquivResidualField
    [Algebra.IsSeparable K L]
    (pb : PowerBasis K L)
    (residualEquiv : CubicResidualAlgebra K L pb ≃ₐ[L] N) :
    L ⊗[K] L ≃ₐ[L] L × N :=
  (cubicGenericCollisionEquiv K L pb).trans
    (AlgEquiv.prodCongr (AlgEquiv.refl : L ≃ₐ[L] L) residualEquiv)

/--
After identifying the residual factor with `N`, the first projection
remains tensor multiplication.
-/
theorem fst_cubicGenericCollisionEquivResidualField
    [Algebra.IsSeparable K L]
    (pb : PowerBasis K L)
    (residualEquiv : CubicResidualAlgebra K L pb ≃ₐ[L] N) :
    (AlgHom.fst L L N).comp
        (cubicGenericCollisionEquivResidualField K L N pb residualEquiv).toAlgHom =
      primitiveTensorDiagonal K L := by
  rw [← fst_cubicGenericCollisionEquiv K L pb]
  ext x
  rfl

variable [Algebra K N] [IsScalarTower K L N]

variable {C : Type*} [CommRing C] [Algebra K C]

/--
Compose any generic-fiber presentation `C ≃ L ⊗[K] L` with the cubic
residual-factor decomposition.

This is the adapter used for a polynomial collision ring after base
change to the generic point.
-/
def genericCubicResidualCollisionEquiv
    [Algebra.IsSeparable K L]
    (genericCollisionEquiv : C ≃ₐ[K] L ⊗[K] L)
    (pb : PowerBasis K L)
    (residualEquiv : CubicResidualAlgebra K L pb ≃ₐ[L] N) :
    C ≃ₐ[K] L × N :=
  genericCollisionEquiv.trans
    ((cubicGenericCollisionEquivResidualField
      K L N pb residualEquiv).restrictScalars K)

/--
The first projection after generic base change is the transported
diagonal multiplication map.
-/
theorem fst_genericCubicResidualCollisionEquiv
    [Algebra.IsSeparable K L]
    (genericCollisionEquiv : C ≃ₐ[K] L ⊗[K] L)
    (pb : PowerBasis K L)
    (residualEquiv : CubicResidualAlgebra K L pb ≃ₐ[L] N) :
    (AlgHom.fst K L N).comp
        (genericCubicResidualCollisionEquiv
          K L N genericCollisionEquiv pb residualEquiv).toAlgHom =
      ((primitiveTensorDiagonal K L).restrictScalars K).comp
        genericCollisionEquiv.toAlgHom := by
  ext x
  change
    (cubicGenericCollisionEquivResidualField
      K L N pb residualEquiv (genericCollisionEquiv x)).1 =
      primitiveTensorDiagonal K L (genericCollisionEquiv x)
  exact
    AlgHom.congr_fun
      (fst_cubicGenericCollisionEquivResidualField
        K L N pb residualEquiv)
      (genericCollisionEquiv x)

/--
A single certificate for the structural statement that the residual factor
of a nonnormal cubic collision is its normal closure, whose Galois group is
`S₃`.

The fields `genericCollisionEquiv` and `fst_genericCollisionEquiv` say

`L ⊗[K] L ≃ L × N`

with the first projection equal to the diagonal multiplication map.  The
last field identifies the Galois group of the same second factor with
`S₃ = Perm (Fin 3)`.
-/
structure CubicS3CollisionWitness
    [Algebra.IsSeparable K L] (pb : PowerBasis K L) where
  degree_eq_three : pb.dim = 3
  normalClosure : NormalClosureData K L N
  markedEmbedding :
    normalClosure.embedding = IsScalarTower.toAlgHom K L N
  genericCollisionEquiv : L ⊗[K] L ≃ₐ[L] L × N
  fst_genericCollisionEquiv :
    (AlgHom.fst L L N).comp genericCollisionEquiv.toAlgHom =
      primitiveTensorDiagonal K L
  galoisGroupEquiv :
    (N ≃ₐ[K] N) ≃* Equiv.Perm (Fin 3)

variable
    [Algebra.IsSeparable K L]

/--
Build the cubic collision witness from the shared marked-normal-closure
package.  The generic normal-closure API supplies finiteness, normality,
and core-freeness.  The marked-embedding equality ensures that the
`L`-algebra structure defining the residual collision factor is the same
marked embedding used by the normal-closure datum.
-/
def cubicS3CollisionWitnessOfNormalClosure
    [PerfectField K]
    (D : NormalClosureData K L N)
    (hmarked : D.embedding = IsScalarTower.toAlgHom K L N)
    (pb : PowerBasis K L)
    (hdegree : pb.dim = 3)
    (residualEquiv : CubicResidualAlgebra K L pb ≃ₐ[L] N)
    (hnontrivial : D.intermediateFixingSubgroup ≠ ⊥) :
    CubicS3CollisionWitness K L N pb where
  degree_eq_three := hdegree
  normalClosure := D
  markedEmbedding := hmarked
  genericCollisionEquiv :=
    cubicGenericCollisionEquivResidualField K L N pb residualEquiv
  fst_genericCollisionEquiv :=
    fst_cubicGenericCollisionEquivResidualField K L N pb residualEquiv
  galoisGroupEquiv :=
    D.galoisGroupEquivPermFinThree
      ((PowerBasis.finrank pb).trans hdegree)
      hnontrivial

/-- Existence form of `cubicS3CollisionWitnessOfNormalClosure`. -/
theorem exists_cubicS3CollisionWitness_of_normalClosure
    [PerfectField K]
    (D : NormalClosureData K L N)
    (hmarked : D.embedding = IsScalarTower.toAlgHom K L N)
    (pb : PowerBasis K L)
    (hdegree : pb.dim = 3)
    (residualEquiv : CubicResidualAlgebra K L pb ≃ₐ[L] N)
    (hnontrivial : D.intermediateFixingSubgroup ≠ ⊥) :
    Nonempty (CubicS3CollisionWitness K L N pb) :=
  ⟨cubicS3CollisionWitnessOfNormalClosure
    K L N D hmarked pb hdegree residualEquiv hnontrivial⟩

end

section PolynomialCollision

universe uR uI uN

open MvPolynomial
open scoped TensorProduct

variable
    {R : Type uR} [CommRing R] [IsDomain R]
    {ι κ : Type uI}

/--
The polynomial collision ring, after passage to the generic point of the
coordinate image, decomposes into its diagonal factor and the chosen
residual field:

`K ⊗_B C_F ≃ L × N`.

This is the promised composition of
`polynomialGenericCollisionEquiv` with the cubic decomposition.  The
surjectivity hypothesis is the explicit generic-finiteness input needed
to identify `K ⊗_B A` with `L`.
-/
noncomputable def polynomialGenericCubicResidualEquiv
    (F : κ → SourceRing R ι)
    (N : Type uN) [Field N]
    [Algebra (PolynomialSourceFunctionField (R := R) (ι := ι)) N]
    [Algebra (PolynomialBaseFunctionField F) N]
    [IsScalarTower
      (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := R) (ι := ι))
      N]
    [Algebra.IsSeparable
      (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := R) (ι := ι))]
    (hsurj :
      Function.Surjective (polynomialGenericSourceTensorMap F))
    (pb :
      PowerBasis
        (PolynomialBaseFunctionField F)
        (PolynomialSourceFunctionField (R := R) (ι := ι)))
    (residualEquiv :
      CubicResidualAlgebra
          (PolynomialBaseFunctionField F)
          (PolynomialSourceFunctionField (R := R) (ι := ι))
          pb ≃ₐ[
            PolynomialSourceFunctionField (R := R) (ι := ι)] N) :
    letI : Algebra
        (polynomialMapImageAlgebra F) (CollisionRing F) :=
      polynomialImageCollisionAlgebra F
    (PolynomialBaseFunctionField F ⊗[polynomialMapImageAlgebra F]
        CollisionRing F) ≃ₐ[PolynomialBaseFunctionField F]
      PolynomialSourceFunctionField (R := R) (ι := ι) × N := by
  let B := polynomialMapImageAlgebra F
  letI : Algebra B (CollisionRing F) :=
    polynomialImageCollisionAlgebra F
  exact
    genericCubicResidualCollisionEquiv
      (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := R) (ι := ι))
      N
      (C :=
        PolynomialBaseFunctionField F ⊗[polynomialMapImageAlgebra F]
          CollisionRing F)
      (polynomialGenericCollisionEquiv F hsurj)
      pb residualEquiv

/--
A nontrivial cubic residual field in the generic collision product forces
the affine collision obstruction to be nonzero.

This is the descent step from

`K ⊗_B C_F ≃ L × N`

back to `C_F`: compatibility with the diagonal identifies the first
projection with the base-changed affine diagonal, and flatness of
`K = Frac(B)` prevents its nonzero kernel from appearing only after
localization.
-/
theorem polynomial_obstructionIdeal_ne_bot_of_cubicResidual
    (F : κ → SourceRing R ι)
    (N : Type uN) [Field N]
    [Algebra (PolynomialSourceFunctionField (R := R) (ι := ι)) N]
    [Algebra (PolynomialBaseFunctionField F) N]
    [IsScalarTower
      (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := R) (ι := ι))
      N]
    [Algebra.IsSeparable
      (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := R) (ι := ι))]
    (hsurj :
      Function.Surjective (polynomialGenericSourceTensorMap F))
    (pb :
      PowerBasis
        (PolynomialBaseFunctionField F)
        (PolynomialSourceFunctionField (R := R) (ι := ι)))
    (residualEquiv :
      CubicResidualAlgebra
          (PolynomialBaseFunctionField F)
          (PolynomialSourceFunctionField (R := R) (ι := ι))
          pb ≃ₐ[
            PolynomialSourceFunctionField (R := R) (ι := ι)] N) :
    obstructionIdeal F ≠ ⊥ := by
  let B := polynomialMapImageAlgebra F
  let K := PolynomialBaseFunctionField F
  let L := PolynomialSourceFunctionField (R := R) (ι := ι)
  let C := CollisionRing F
  letI : Algebra B C := polynomialImageCollisionAlgebra F
  let e : K ⊗[B] C ≃ₐ[K] L × N :=
    polynomialGenericCubicResidualEquiv
      F N hsurj pb residualEquiv
  apply
    polynomial_obstructionIdeal_ne_bot_of_generic_product
      F N hsurj e
  calc
    (AlgHom.fst K L N).comp e.toAlgHom =
        ((primitiveTensorDiagonal K L).restrictScalars K).comp
          (polynomialGenericCollisionEquiv F hsurj).toAlgHom := by
            apply AlgHom.ext
            intro x
            change
              (cubicGenericCollisionEquivResidualField
                  K L N pb residualEquiv
                  (polynomialGenericCollisionEquiv F hsurj x)).1 =
                primitiveTensorDiagonal K L
                  (polynomialGenericCollisionEquiv F hsurj x)
            exact
              AlgHom.congr_fun
                (fst_cubicGenericCollisionEquivResidualField
                  K L N pb residualEquiv)
                (polynomialGenericCollisionEquiv F hsurj x)
    _ = polynomialGenericCollisionDiagonal F hsurj :=
      polynomialGenericCollisionEquiv_intertwines_diagonal
        F hsurj

/--
Equivalently, a cubic residual generic collision factor forces strict
containment of the collision ideal in the diagonal ideal.
-/
theorem polynomial_collisionIdeal_lt_diagonalIdeal_of_cubicResidual
    (F : κ → SourceRing R ι)
    (N : Type uN) [Field N]
    [Algebra (PolynomialSourceFunctionField (R := R) (ι := ι)) N]
    [Algebra (PolynomialBaseFunctionField F) N]
    [IsScalarTower
      (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := R) (ι := ι))
      N]
    [Algebra.IsSeparable
      (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := R) (ι := ι))]
    (hsurj :
      Function.Surjective (polynomialGenericSourceTensorMap F))
    (pb :
      PowerBasis
        (PolynomialBaseFunctionField F)
        (PolynomialSourceFunctionField (R := R) (ι := ι)))
    (residualEquiv :
      CubicResidualAlgebra
          (PolynomialBaseFunctionField F)
          (PolynomialSourceFunctionField (R := R) (ι := ι))
          pb ≃ₐ[
            PolynomialSourceFunctionField (R := R) (ι := ι)] N) :
    collisionIdeal F <
      diagonalIdeal (R := R) (ι := ι) := by
  apply lt_of_le_of_ne (collisionIdeal_le_diagonalIdeal F)
  intro hIdeals
  exact
    polynomial_obstructionIdeal_ne_bot_of_cubicResidual
      F N hsurj pb residualEquiv
      ((obstructionIdeal_eq_bot_iff F).2 hIdeals)

/--
Polynomial-map specialization using the shared `NormalClosureData`
package instead of separate finiteness, Galois, and core-free hypotheses.
-/
theorem exists_polynomialCubicS3CollisionWitness_of_normalClosure
    (F : κ → SourceRing R ι)
    (N : Type uN) [Field N]
    [Algebra (PolynomialSourceFunctionField (R := R) (ι := ι)) N]
    [Algebra (PolynomialBaseFunctionField F) N]
    [IsScalarTower
      (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := R) (ι := ι))
      N]
    [Algebra.IsSeparable
      (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := R) (ι := ι))]
    [PerfectField (PolynomialBaseFunctionField F)]
    (D :
      NormalClosureData
        (PolynomialBaseFunctionField F)
        (PolynomialSourceFunctionField (R := R) (ι := ι))
        N)
    (hmarked :
      D.embedding =
        IsScalarTower.toAlgHom
          (PolynomialBaseFunctionField F)
          (PolynomialSourceFunctionField (R := R) (ι := ι))
          N)
    (hsurj :
      Function.Surjective (polynomialGenericSourceTensorMap F))
    (pb :
      PowerBasis
        (PolynomialBaseFunctionField F)
        (PolynomialSourceFunctionField (R := R) (ι := ι)))
    (hdegree : pb.dim = 3)
    (residualEquiv :
      CubicResidualAlgebra
          (PolynomialBaseFunctionField F)
          (PolynomialSourceFunctionField (R := R) (ι := ι))
          pb ≃ₐ[
            PolynomialSourceFunctionField (R := R) (ι := ι)] N)
    (hnontrivial : D.intermediateFixingSubgroup ≠ ⊥) :
    letI : Algebra
        (polynomialMapImageAlgebra F) (CollisionRing F) :=
      polynomialImageCollisionAlgebra F
    Nonempty
      (((PolynomialBaseFunctionField F ⊗[polynomialMapImageAlgebra F]
          CollisionRing F) ≃ₐ[PolynomialBaseFunctionField F]
            PolynomialSourceFunctionField (R := R) (ι := ι) × N) ×
        CubicS3CollisionWitness
          (PolynomialBaseFunctionField F)
          (PolynomialSourceFunctionField (R := R) (ι := ι))
          N pb) := by
  letI : Algebra
      (polynomialMapImageAlgebra F) (CollisionRing F) :=
    polynomialImageCollisionAlgebra F
  exact
    ⟨polynomialGenericCubicResidualEquiv
        F N hsurj pb residualEquiv,
      cubicS3CollisionWitnessOfNormalClosure
        (PolynomialBaseFunctionField F)
        (PolynomialSourceFunctionField (R := R) (ι := ι))
        N D hmarked pb hdegree residualEquiv hnontrivial⟩

end PolynomialCollision

end CollisionIdeals
