module

public import CollisionIdeals.General.FiberProduct.Basic
public import CollisionIdeals.General.FiberProduct.UniversalProperty
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

set_option autoImplicit false

namespace CollisionIdeals

universe u v w

open MvPolynomial
open scoped TensorProduct

noncomputable section

variable {R : Type u} [CommRing R]
variable {ι : Type v}
variable {κ : Type w}

/-- The map on coordinate rings determined by the coordinate polynomials `F`. -/
def coordinateAlgHom (F : κ → SourceRing R ι) :
    MvPolynomial κ R →ₐ[R] SourceRing R ι :=
  MvPolynomial.aeval F

@[simp]
theorem coordinateAlgHom_X
    (F : κ → SourceRing R ι) (j : κ) :
    coordinateAlgHom F (X j) = F j := by
  simp [coordinateAlgHom]

/--
The concrete collision quotient is the tensor-product coordinate ring of
the affine self-fiber product.

The algebra structure on the source polynomial ring is the one induced by
`tⱼ ↦ Fⱼ`.
-/
def collisionTensorEquiv (F : κ → SourceRing R ι) :
    letI : Algebra (MvPolynomial κ R) (SourceRing R ι) :=
      (coordinateAlgHom F).toRingHom.toAlgebra
    CollisionRing F ≃ₐ[R]
      SourceRing R ι ⊗[MvPolynomial κ R] SourceRing R ι := by
  let B := MvPolynomial κ R
  let A := SourceRing R ι
  let C := CollisionRing F
  letI : Algebra B A := (coordinateAlgHom F).toRingHom.toAlgebra
  letI : IsScalarTower R B A :=
    IsScalarTower.of_algebraMap_eq'
      (coordinateAlgHom F).comp_algebraMap.symm

  let TP := A ⊗[B] A

  let tensorPair : CollisionMapPair F TP :=
    { left :=
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] TP)
      right :=
        (Algebra.TensorProduct.includeRight : A →ₐ[B] TP).restrictScalars R
      agree := fun j ↦ by
        change (F j) ⊗ₜ[B] (1 : A) = (1 : A) ⊗ₜ[B] F j
        rw [← coordinateAlgHom_X F j]
        change
          algebraMap B A (X j) ⊗ₜ[B] (1 : A) =
            (1 : A) ⊗ₜ[B] algebraMap B A (X j)
        exact Algebra.TensorProduct.tmul_one_eq_one_tmul (X j) }

  let forward : C →ₐ[R] TP :=
    collisionLift tensorPair

  let leftBaseMap : B →+* C :=
    (collisionLeft F).toRingHom.comp (algebraMap B A)
  letI : Algebra B C := leftBaseMap.toAlgebra
  letI : IsScalarTower R B C := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro r
    change algebraMap R C r =
      collisionLeft F (algebraMap B A (algebraMap R B r))
    rw [← IsScalarTower.algebraMap_apply R B A]
    exact (collisionLeft F).commutes r |>.symm

  let leftMap : A →ₐ[B] C :=
    { toRingHom := (collisionLeft F).toRingHom
      commutes' := fun b ↦ rfl }

  have hcoordinate :
      (collisionRight F).comp (coordinateAlgHom F) =
        (collisionLeft F).comp (coordinateAlgHom F) := by
    apply MvPolynomial.algHom_ext
    intro j
    simpa using
      (collisionLeft_apply_F_eq_collisionRight_apply_F F j).symm

  let rightMap : A →ₐ[B] C :=
    { toRingHom := (collisionRight F).toRingHom
      commutes' := fun b ↦ by
        change collisionRight F (algebraMap B A b) =
          collisionLeft F (algebraMap B A b)
        change
          ((collisionRight F).comp (coordinateAlgHom F)) b =
            ((collisionLeft F).comp (coordinateAlgHom F)) b
        exact AlgHom.congr_fun hcoordinate b }

  let backward : TP →ₐ[R] C :=
    (Algebra.TensorProduct.productMap leftMap rightMap).restrictScalars R

  apply AlgEquiv.ofAlgHom forward backward
  · apply AlgHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero =>
        simp
    | tmul a b =>
        have hleft :
            forward (collisionLeft F a) = tensorPair.left a := by
          exact AlgHom.congr_fun (collisionLift_comp_left tensorPair) a
        have hright :
            forward (collisionRight F b) = tensorPair.right b := by
          exact AlgHom.congr_fun (collisionLift_comp_right tensorPair) b
        change
          forward
              ((Algebra.TensorProduct.productMap leftMap rightMap)
                (a ⊗ₜ[B] b)) =
            a ⊗ₜ[B] b
        rw [Algebra.TensorProduct.productMap_apply_tmul]
        change forward (collisionLeft F a * collisionRight F b) =
          a ⊗ₜ[B] b
        rw [map_mul, hleft, hright]
        change
          (a ⊗ₜ[B] (1 : A)) * ((1 : A) ⊗ₜ[B] b) =
            a ⊗ₜ[B] b
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        simp
    | add x y hx hy =>
        simpa using congrArg₂ (· + ·) hx hy
  · apply collisionHom_ext
    · apply MvPolynomial.algHom_ext
      intro i
      have hforward :
          forward (collisionLeft F (X i)) = tensorPair.left (X i) := by
        exact
          AlgHom.congr_fun (collisionLift_comp_left tensorPair) (X i)
      change backward (forward (collisionLeft F (X i))) =
        collisionLeft F (X i)
      rw [hforward]
      change
        (Algebra.TensorProduct.productMap leftMap rightMap)
            ((Algebra.TensorProduct.includeLeft : A →ₐ[R] TP) (X i)) =
          collisionLeft F (X i)
      rw [Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.productMap_apply_tmul]
      simp [leftMap]
      rw [← leftRename_X (R := R) i]
      exact collisionLeft_apply F (X i)
    · apply MvPolynomial.algHom_ext
      intro i
      have hforward :
          forward (collisionRight F (X i)) = tensorPair.right (X i) := by
        exact
          AlgHom.congr_fun (collisionLift_comp_right tensorPair) (X i)
      change backward (forward (collisionRight F (X i))) =
        collisionRight F (X i)
      rw [hforward]
      change
        (Algebra.TensorProduct.productMap leftMap rightMap)
            ((Algebra.TensorProduct.includeRight : A →ₐ[B] TP) (X i)) =
          collisionRight F (X i)
      rw [Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.productMap_apply_tmul]
      simp [rightMap]
      rw [← rightRename_X (R := R) i]
      exact collisionRight_apply F (X i)

end

end CollisionIdeals
