import CollisionIdeals.ComplexThree.Cubic.Main
import CollisionIdeals.General.Automorphism.GenericDegreeOne
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Proved solution for the Paper I Palomar statement

The definitions below deliberately agree with the independent Mathlib-only
statement surface.  The proof then adapts the existing collision-ideal
development to that surface.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals.Palomar.PaperOne

noncomputable section

open MvPolynomial
open scoped TensorProduct

abbrev SourceRing := MvPolynomial (Fin 3) ℂ

abbrev PairRing := MvPolynomial (Sum (Fin 3) (Fin 3)) ℂ

abbrev PolynomialMap := Fin 3 → SourceRing

def leftRename : SourceRing →ₐ[ℂ] PairRing :=
  MvPolynomial.rename Sum.inl

def rightRename : SourceRing →ₐ[ℂ] PairRing :=
  MvPolynomial.rename Sum.inr

def collisionIdeal (F : PolynomialMap) : Ideal PairRing :=
  Ideal.span (Set.range fun i ↦ leftRename (F i) - rightRename (F i))

abbrev CollisionRing (F : PolynomialMap) :=
  PairRing ⧸ collisionIdeal F

def diagonalIdeal : Ideal PairRing :=
  Ideal.span (Set.range fun i : Fin 3 ↦
    (X (Sum.inl i) : PairRing) - X (Sum.inr i))

def obstructionIdeal (F : PolynomialMap) : Ideal (CollisionRing F) :=
  diagonalIdeal.map (Ideal.Quotient.mk (collisionIdeal F))

def collisionLeft (F : PolynomialMap) : SourceRing →ₐ[ℂ] CollisionRing F :=
  (Ideal.Quotient.mkₐ ℂ (collisionIdeal F)).comp leftRename

def diagonalEval : PairRing →ₐ[ℂ] SourceRing :=
  MvPolynomial.rename (Sum.elim id id)

theorem collisionIdeal_le_diagonalEval_ker (F : PolynomialMap) :
    collisionIdeal F ≤ RingHom.ker diagonalEval.toRingHom := by
  rw [collisionIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  change diagonalEval (leftRename (F i) - rightRename (F i)) = 0
  simp [diagonalEval, leftRename, rightRename, MvPolynomial.rename_rename]

def collisionDiagonal (F : PolynomialMap) :
    CollisionRing F →ₐ[ℂ] SourceRing :=
  Ideal.Quotient.liftₐ
    (collisionIdeal F) diagonalEval (collisionIdeal_le_diagonalEval_ker F)

@[simp]
theorem collisionDiagonal_collisionLeft (F : PolynomialMap) (a : SourceRing) :
    collisionDiagonal F (collisionLeft F a) = a := by
  simp [collisionDiagonal, collisionLeft, diagonalEval, leftRename,
    MvPolynomial.rename_rename]

def coordinateAlgHom (F : PolynomialMap) :
    MvPolynomial (Fin 3) ℂ →ₐ[ℂ] SourceRing :=
  MvPolynomial.aeval F

def ImageAlgebra (F : PolynomialMap) : Subalgebra ℂ SourceRing :=
  (coordinateAlgHom F).range

abbrev SourceFunctionField := FractionRing SourceRing

abbrev BaseFunctionField (F : PolynomialMap) :=
  FractionRing (ImageAlgebra F)

noncomputable def imageToSourceFunctionField (F : PolynomialMap) :
    ImageAlgebra F →+* SourceFunctionField :=
  (algebraMap SourceRing SourceFunctionField).comp
    (algebraMap (ImageAlgebra F) SourceRing)

theorem imageToSourceFunctionField_injective (F : PolynomialMap) :
    Function.Injective (imageToSourceFunctionField F) :=
  (FaithfulSMul.algebraMap_injective SourceRing SourceFunctionField).comp
    (FaithfulSMul.algebraMap_injective (ImageAlgebra F) SourceRing)

noncomputable def baseFunctionFieldEmbedding (F : PolynomialMap) :
    BaseFunctionField F →+* SourceFunctionField :=
  IsFractionRing.lift (imageToSourceFunctionField_injective F)

noncomputable instance (F : PolynomialMap) :
    Algebra (BaseFunctionField F) SourceFunctionField :=
  (baseFunctionFieldEmbedding F).toAlgebra

noncomputable instance (F : PolynomialMap) :
    IsScalarTower (ImageAlgebra F) (BaseFunctionField F)
      SourceFunctionField :=
  IsScalarTower.of_algebraMap_eq fun b ↦ by
    exact (IsFractionRing.lift_algebraMap
      (imageToSourceFunctionField_injective F) b).symm

noncomputable instance (F : PolynomialMap) :
    Algebra (ImageAlgebra F) (CollisionRing F) :=
  ((collisionLeft F).comp
    (Subalgebra.val (ImageAlgebra F))).toRingHom.toAlgebra

noncomputable def imageCollisionDiagonal (F : PolynomialMap) :
    CollisionRing F →ₐ[ImageAlgebra F] SourceRing :=
  { toRingHom := (collisionDiagonal F).toRingHom
    commutes' := fun b ↦ by
      change collisionDiagonal F (collisionLeft F b.1) = b.1
      exact collisionDiagonal_collisionLeft F b.1 }

noncomputable def genericCollisionDiagonal (F : PolynomialMap) :
    (BaseFunctionField F ⊗[ImageAlgebra F] CollisionRing F) →ₐ[
      BaseFunctionField F] SourceFunctionField := by
  let fK : BaseFunctionField F →ₐ[ImageAlgebra F] SourceFunctionField :=
    IsScalarTower.toAlgHom
      (ImageAlgebra F) (BaseFunctionField F) SourceFunctionField
  let fC : CollisionRing F →ₐ[ImageAlgebra F] SourceFunctionField :=
    (IsScalarTower.toAlgHom
      (ImageAlgebra F) SourceRing SourceFunctionField).comp
        (imageCollisionDiagonal F)
  let fB :
      (BaseFunctionField F ⊗[ImageAlgebra F] CollisionRing F) →ₐ[
        ImageAlgebra F] SourceFunctionField :=
    Algebra.TensorProduct.lift fK fC (fun _ _ ↦ mul_comm _ _)
  exact
    { toRingHom := fB.toRingHom
      commutes' := fun k ↦ by
        change fB (k ⊗ₜ[ImageAlgebra F] (1 : CollisionRing F)) =
          algebraMap (BaseFunctionField F) SourceFunctionField k
        simp [fB, fK] }

def IsKeller (F : PolynomialMap) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧
    Matrix.det (fun i j : Fin 3 ↦ pderiv j (F i)) = C c

def IsPolynomialAutomorphism (F : PolynomialMap) : Prop :=
  Function.Bijective (MvPolynomial.bind₁ F)

def IsJacobianCounterexample (F : PolynomialMap) : Prop :=
  IsKeller F ∧ ¬ IsPolynomialAutomorphism F

def KellerGaloisRigidity : Prop :=
  ∀ F : PolynomialMap, IsKeller F →
    Normal (BaseFunctionField F) SourceFunctionField →
    IsPolynomialAutomorphism F

theorem genericDegreeThreeS3Collision
    (hRigidity : KellerGaloisRigidity)
    (F : PolynomialMap)
    (hKeller : IsKeller F)
    (N : Type*) [Field N]
    [Algebra SourceFunctionField N]
    [Algebra (BaseFunctionField F) N]
    [IsScalarTower (BaseFunctionField F) SourceFunctionField N]
    (normalClosure :
      IsNormalClosure (BaseFunctionField F) SourceFunctionField N)
    (finiteNormal : FiniteDimensional (BaseFunctionField F) N)
    (hdegree :
      Module.finrank (BaseFunctionField F) SourceFunctionField = 3) :
    IsJacobianCounterexample F ∧
      obstructionIdeal F ≠ ⊥ ∧
      collisionIdeal F < diagonalIdeal ∧
      ∃ e :
          (BaseFunctionField F ⊗[ImageAlgebra F] CollisionRing F) ≃ₐ[
            BaseFunctionField F] SourceFunctionField × N,
        (AlgHom.fst
            (BaseFunctionField F) SourceFunctionField N).comp e.toAlgHom =
          genericCollisionDiagonal F ∧
        Nonempty
          ((N ≃ₐ[BaseFunctionField F] N) ≃* Equiv.Perm (Fin 3)) := by
  let K := BaseFunctionField F
  let L := SourceFunctionField
  let algebraKN : Algebra K N := inferInstance
  let towerKLN : IsScalarTower K L N := inferInstance
  letI : Algebra (CollisionIdeals.ComplexThreeBaseFunctionField F) N := by
    change Algebra K N
    exact algebraKN
  letI : IsScalarTower
      (CollisionIdeals.ComplexThreeBaseFunctionField F)
      CollisionIdeals.ComplexThreeSourceFunctionField N := by
    change IsScalarTower K L N
    exact towerKLN
  have hdegreeKL : Module.finrank K L = 3 :=
    hdegree
  have hpos : 0 < Module.finrank K L := by
    rw [hdegreeKL]
    norm_num
  letI : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos hpos
  letI : Algebra.IsAlgebraic K L :=
    Algebra.IsAlgebraic.of_finite K L
  letI : Algebra.IsSeparable K L :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  let separableKL : Algebra.IsSeparable K L := inferInstance
  letI : Algebra.IsSeparable
      (CollisionIdeals.ComplexThreeBaseFunctionField F)
      CollisionIdeals.ComplexThreeSourceFunctionField := by
    change Algebra.IsSeparable K L
    exact separableKL
  let pb : PowerBasis K L :=
    Field.powerBasisOfFiniteOfSeparable K L
  have hpbdim : pb.dim = 3 :=
    (PowerBasis.finrank pb).symm.trans hdegreeKL
  have hsurj :
      Function.Surjective
        (CollisionIdeals.polynomialGenericSourceTensorMap F) :=
    CollisionIdeals.polynomialGenericSourceTensorMap_surjective_of_finrank_pos
      F hpos
  let D : CollisionIdeals.NormalClosureData K L N :=
    { embedding := IsScalarTower.toAlgHom K L N
      normalClosure := normalClosure
      finiteIntermediate := inferInstance
      finiteNormal := finiteNormal }
  have hmarked : D.embedding = IsScalarTower.toAlgHom K L N :=
    rfl
  have hKeller' : CollisionIdeals.IsComplexThreeKeller F := by
    simpa [IsKeller, CollisionIdeals.IsComplexThreeKeller,
      CollisionIdeals.IsKeller, CollisionIdeals.jacobianDet,
      CollisionIdeals.jacobianMatrix] using hKeller
  have hNotNormal : ¬ Normal K L := by
    intro hNormal
    have hAutomorphism : IsPolynomialAutomorphism F :=
      hRigidity F hKeller hNormal
    have hAutomorphism' : CollisionIdeals.IsPolynomialAutomorphism F := by
      simpa [IsPolynomialAutomorphism,
        CollisionIdeals.IsPolynomialAutomorphism] using hAutomorphism
    have hone :=
      CollisionIdeals.polynomialFunctionField_finrank_eq_one_of_isPolynomialAutomorphism
        hAutomorphism'
    change Module.finrank K L = 1 at hone
    have : (3 : ℕ) = 1 := hdegreeKL.symm.trans hone
    norm_num at this
  obtain ⟨hCounterexample, hObstruction, hStrict, _hOffDiagonal,
      ⟨_mainEquiv, witness⟩⟩ :=
    CollisionIdeals.complexThreeCubicS3Collision
      F hKeller' N D hmarked hsurj pb hpbdim hNotNormal
  let residualEquiv :
      CollisionIdeals.CubicResidualAlgebra K L pb ≃ₐ[L] N :=
    CollisionIdeals.cubicResidualEquivNormalClosureOfNotNormal
      K L N D hmarked pb hpbdim hNotNormal
  let e :
      (K ⊗[ImageAlgebra F] CollisionRing F) ≃ₐ[K] L × N :=
    CollisionIdeals.polynomialGenericCubicResidualEquiv
      F N hsurj pb residualEquiv
  letI : Algebra
      (CollisionIdeals.polynomialMapImageAlgebra F)
      (CollisionIdeals.CollisionRing F) :=
    CollisionIdeals.polynomialImageCollisionAlgebra F
  have hcollisionDiagonal :
      CollisionIdeals.collisionDiagonal F = collisionDiagonal F := by
    rfl
  have hbaseFunctionFieldEmbedding :
      CollisionIdeals.polynomialBaseFunctionFieldEmbedding F =
        baseFunctionFieldEmbedding F := by
    rfl
  have hprojectAlgebraMap (k : K) :
      algebraMap
          (CollisionIdeals.ComplexThreeBaseFunctionField F)
          CollisionIdeals.ComplexThreeSourceFunctionField k =
        CollisionIdeals.polynomialBaseFunctionFieldEmbedding F k := by
    rfl
  have hlocalAlgebraMap (k : BaseFunctionField F) :
      algebraMap (BaseFunctionField F) SourceFunctionField k =
        baseFunctionFieldEmbedding F k := by
    rfl
  have hprojectDiagonal_tmul (k : K) (c : CollisionRing F) :
      CollisionIdeals.polynomialGenericCollisionDiagonal F hsurj
          (k ⊗ₜ[CollisionIdeals.polynomialMapImageAlgebra F] c) =
        CollisionIdeals.polynomialBaseFunctionFieldEmbedding F k *
          algebraMap SourceRing L (CollisionIdeals.collisionDiagonal F c) := by
    simp [CollisionIdeals.polynomialGenericCollisionDiagonal,
      CollisionIdeals.polynomialGenericSourceEquiv,
      CollisionIdeals.polynomialGenericSourceTensorMap,
      CollisionIdeals.polynomialImageCollisionDiagonal,
      hprojectAlgebraMap]
    exact Or.inl rfl
  have hlocalDiagonal_tmul (k : K) (c : CollisionRing F) :
      genericCollisionDiagonal F (k ⊗ₜ[ImageAlgebra F] c) =
        baseFunctionFieldEmbedding F k *
          algebraMap SourceRing SourceFunctionField (collisionDiagonal F c) := by
    simp [genericCollisionDiagonal, imageCollisionDiagonal,
      hlocalAlgebraMap]
  have hdiagProject :
      (AlgHom.fst K L N).comp e.toAlgHom =
        CollisionIdeals.polynomialGenericCollisionDiagonal F hsurj := by
    apply AlgHom.ext
    intro x
    change (e x).1 =
      CollisionIdeals.polynomialGenericCollisionDiagonal F hsurj x
    calc
      (e x).1 =
          CollisionIdeals.primitiveTensorDiagonal K L
            (CollisionIdeals.polynomialGenericCollisionEquiv F hsurj x) :=
        AlgHom.congr_fun
          (CollisionIdeals.fst_cubicGenericCollisionEquivResidualField
            K L N pb residualEquiv)
          (CollisionIdeals.polynomialGenericCollisionEquiv F hsurj x)
      _ = CollisionIdeals.polynomialGenericCollisionDiagonal F hsurj x :=
        AlgHom.congr_fun
          (CollisionIdeals.polynomialGenericCollisionEquiv_intertwines_diagonal
            F hsurj) x
  have hdiagonalIdentification :
      CollisionIdeals.polynomialGenericCollisionDiagonal F hsurj =
        genericCollisionDiagonal F := by
    apply AlgHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul k c =>
        change
          CollisionIdeals.polynomialGenericCollisionDiagonal F hsurj
              (k ⊗ₜ[CollisionIdeals.polynomialMapImageAlgebra F] c) =
            genericCollisionDiagonal F (k ⊗ₜ[ImageAlgebra F] c)
        rw [hprojectDiagonal_tmul, hlocalDiagonal_tmul,
          hbaseFunctionFieldEmbedding, hcollisionDiagonal]
        rfl
    | add x y hx hy =>
        simpa only [map_add] using congrArg₂ (fun a b ↦ a + b) hx hy
  refine ⟨?_, ?_, ?_, e, hdiagProject.trans hdiagonalIdentification,
    ⟨witness.galoisGroupEquiv⟩⟩
  · simpa [IsJacobianCounterexample, IsKeller,
      IsPolynomialAutomorphism,
      CollisionIdeals.IsComplexThreeJacobianCounterexample,
      CollisionIdeals.IsComplexJacobianCounterexample,
      CollisionIdeals.IsComplexThreeKeller, CollisionIdeals.IsKeller,
      CollisionIdeals.jacobianDet, CollisionIdeals.jacobianMatrix,
      CollisionIdeals.IsPolynomialAutomorphism] using hCounterexample
  · simpa [obstructionIdeal, diagonalIdeal, collisionIdeal, leftRename,
      rightRename, CollisionIdeals.obstructionIdeal,
      CollisionIdeals.diagonalIdeal, CollisionIdeals.diagonalGenerator,
      CollisionIdeals.collisionIdeal, CollisionIdeals.collisionGenerator,
      CollisionIdeals.leftRename,
      CollisionIdeals.rightRename] using hObstruction
  · simpa [diagonalIdeal, collisionIdeal, leftRename, rightRename,
      CollisionIdeals.diagonalIdeal, CollisionIdeals.diagonalGenerator,
      CollisionIdeals.collisionIdeal, CollisionIdeals.collisionGenerator,
      CollisionIdeals.leftRename,
      CollisionIdeals.rightRename] using hStrict

end

end CollisionIdeals.Palomar.PaperOne
