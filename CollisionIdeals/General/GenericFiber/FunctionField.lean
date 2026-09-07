import CollisionIdeals.General.Collision.CollisionDiagonal
import CollisionIdeals.General.FiberProduct.Polynomial
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

universe u

open scoped TensorProduct

noncomputable section

variable (B A K : Type u)
variable [CommRing B] [CommRing A] [CommRing K]
variable [Algebra B A] [Algebra B K]

private def baseChangeTensorAssoc :
    ((K ⊗[B] A) ⊗[B] A) ≃ₐ[K]
      K ⊗[B] (A ⊗[B] A) where
  toRingEquiv :=
    (Algebra.TensorProduct.assoc B B K A A).toRingEquiv
  commutes' k := by
    change
      (Algebra.TensorProduct.assoc B B K A A)
          ((k ⊗ₜ[B] (1 : A)) ⊗ₜ[B] (1 : A)) =
        k ⊗ₜ[B] ((1 : A) ⊗ₜ[B] (1 : A))
    rfl

/--
Base change distributes over a self-tensor product:

`K ⊗_B (A ⊗_B A) ≃ (K ⊗_B A) ⊗_K (K ⊗_B A)`.
-/
noncomputable def baseChangeSelfTensorEquiv :
    K ⊗[B] (A ⊗[B] A) ≃ₐ[K]
      (K ⊗[B] A) ⊗[K] (K ⊗[B] A) :=
  (baseChangeTensorAssoc B A K).symm.trans
    (Algebra.TensorProduct.cancelBaseChange
      B K K (K ⊗[B] A) A).symm

@[simp]
theorem baseChangeSelfTensorEquiv_tmul
    (k : K) (a₁ a₂ : A) :
    baseChangeSelfTensorEquiv B A K
        (k ⊗ₜ[B] (a₁ ⊗ₜ[B] a₂)) =
      (k ⊗ₜ[B] a₁) ⊗ₜ[K] ((1 : K) ⊗ₜ[B] a₂) := by
  rfl

/--
The base-change equivalence is compatible with multiplication on the two
tensor factors.  The map `φ` is the chosen identification/map from the
generic source algebra into `L`.
-/
theorem baseChangeSelfTensorEquiv_intertwines_diagonal
    (L : Type u) [CommRing L] [Algebra B L] [Algebra K L]
    [IsScalarTower B K L]
    (φ : K ⊗[B] A →ₐ[K] L) :
    (diagonalMultiplication (B := K) (A := L)).comp
          ((Algebra.TensorProduct.map φ φ).comp
            (baseChangeSelfTensorEquiv B A K).toAlgHom) =
      φ.comp
        (Algebra.TensorProduct.map
          (AlgHom.id K K)
          (diagonalMultiplication (B := B) (A := A))) := by
  apply Algebra.TensorProduct.ext'
  intro k x
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul a₁ a₂ =>
      change
        φ (k ⊗ₜ[B] a₁) * φ ((1 : K) ⊗ₜ[B] a₂) =
          φ (k ⊗ₜ[B] (a₁ * a₂))
      rw [← map_mul]
      congr 1
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      simp
  | add x y hx hy =>
      simpa only [TensorProduct.tmul_add, map_add] using
        congrArg₂ (· + ·) hx hy

end

section PolynomialCollision

universe v

open MvPolynomial

variable {R : Type u} [CommRing R]
variable {ι κ : Type v}

/-- The target polynomial ring acts on the collision ring through the left
collision projection. -/
noncomputable def collisionTargetAlgebra
    (F : κ → SourceRing R ι) :
    Algebra (MvPolynomial κ R) (CollisionRing F) :=
  ((collisionLeft F).comp (coordinateAlgHom F)).toRingHom.toAlgebra

theorem collisionTensorEquiv_collisionLeft
    (F : κ → SourceRing R ι)
    (a : SourceRing R ι) :
    letI : Algebra (MvPolynomial κ R) (SourceRing R ι) :=
      (coordinateAlgHom F).toRingHom.toAlgebra
    collisionTensorEquiv F (collisionLeft F a) =
      (Algebra.TensorProduct.includeLeft :
        SourceRing R ι →ₐ[R]
          SourceRing R ι ⊗[MvPolynomial κ R] SourceRing R ι) a := by
  letI : Algebra (MvPolynomial κ R) (SourceRing R ι) :=
    (coordinateAlgHom F).toRingHom.toAlgebra
  simp [collisionTensorEquiv, collisionLeft, collisionLift,
    collisionPairMap, leftRename]
  rw [MvPolynomial.aeval_rename]
  have h :
      MvPolynomial.aeval
          (fun i : ι =>
            (X i : SourceRing R ι) ⊗ₜ[MvPolynomial κ R]
              (1 : SourceRing R ι)) =
        (Algebra.TensorProduct.includeLeft :
          SourceRing R ι →ₐ[R]
            SourceRing R ι ⊗[MvPolynomial κ R] SourceRing R ι) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  exact AlgHom.congr_fun h a

/-- The collision-tensor equivalence, upgraded to an equivalence over the
target polynomial coordinate ring. -/
noncomputable def collisionTensorEquivOverTarget
    (F : κ → SourceRing R ι) :
    letI : Algebra (MvPolynomial κ R) (SourceRing R ι) :=
      (coordinateAlgHom F).toRingHom.toAlgebra
    letI : Algebra (MvPolynomial κ R) (CollisionRing F) :=
      collisionTargetAlgebra F
    CollisionRing F ≃ₐ[MvPolynomial κ R]
      SourceRing R ι ⊗[MvPolynomial κ R] SourceRing R ι := by
  let B := MvPolynomial κ R
  let A := SourceRing R ι
  letI : Algebra B A := (coordinateAlgHom F).toRingHom.toAlgebra
  letI : Algebra B (CollisionRing F) := collisionTargetAlgebra F
  exact
    { (collisionTensorEquiv F).toRingEquiv with
      commutes' := fun b => by
        change
          collisionTensorEquiv F
              (collisionLeft F (coordinateAlgHom F b)) =
            (coordinateAlgHom F b) ⊗ₜ[B] (1 : A)
        exact collisionTensorEquiv_collisionLeft F
          (coordinateAlgHom F b) }

/--
After extending the target polynomial ring `B` to any `B`-algebra `K`, the
base-changed collision ring is the self-tensor square of the generic source
algebra `K ⊗_B A`.
-/
noncomputable def collisionBaseChangeSelfTensorEquiv
    (F : κ → SourceRing R ι)
    (K : Type max u v) [CommRing K]
    [Algebra (MvPolynomial κ R) K] :
    letI : Algebra (MvPolynomial κ R) (SourceRing R ι) :=
      (coordinateAlgHom F).toRingHom.toAlgebra
    letI : Algebra (MvPolynomial κ R) (CollisionRing F) :=
      collisionTargetAlgebra F
    K ⊗[MvPolynomial κ R] CollisionRing F ≃ₐ[K]
      (K ⊗[MvPolynomial κ R] SourceRing R ι) ⊗[K]
        (K ⊗[MvPolynomial κ R] SourceRing R ι) := by
  let B := MvPolynomial κ R
  let A := SourceRing R ι
  letI : Algebra B A := (coordinateAlgHom F).toRingHom.toAlgebra
  letI : Algebra B (CollisionRing F) := collisionTargetAlgebra F
  exact
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : K ≃ₐ[K] K)
      (collisionTensorEquivOverTarget F)).trans
        (baseChangeSelfTensorEquiv B A K)

end PolynomialCollision

section ImageFunctionFields

universe v

open MvPolynomial

variable {R : Type u} [CommRing R] [IsDomain R]
variable {ι κ : Type v}

/-- The coordinate algebra generated by the coordinates of `F`. -/
def polynomialMapImageAlgebra
    (F : κ → SourceRing R ι) :
    Subalgebra R (SourceRing R ι) :=
  (coordinateAlgHom F).range

/-- The function field of the polynomial source. -/
abbrev PolynomialSourceFunctionField :=
  FractionRing (SourceRing R ι)

/-- The function field of the coordinate image algebra. -/
abbrev PolynomialBaseFunctionField
    (F : κ → SourceRing R ι) :=
  FractionRing (polynomialMapImageAlgebra F)

/-- The inclusion of the image algebra into the source function field. -/
noncomputable def polynomialMapImageAlgebraToFunctionField
    (F : κ → SourceRing R ι) :
    polynomialMapImageAlgebra F →+*
      PolynomialSourceFunctionField (R := R) (ι := ι) :=
  (algebraMap
      (SourceRing R ι)
      (PolynomialSourceFunctionField (R := R) (ι := ι))).comp
    (algebraMap (polynomialMapImageAlgebra F) (SourceRing R ι))

theorem polynomialMapImageAlgebraToFunctionField_injective
    (F : κ → SourceRing R ι) :
    Function.Injective
      (polynomialMapImageAlgebraToFunctionField F) :=
  (FaithfulSMul.algebraMap_injective
      (SourceRing R ι)
      (PolynomialSourceFunctionField (R := R) (ι := ι))).comp
    (FaithfulSMul.algebraMap_injective
      (polynomialMapImageAlgebra F) (SourceRing R ι))

/-- The induced embedding from the base function field to the source
function field. -/
noncomputable def polynomialBaseFunctionFieldEmbedding
    (F : κ → SourceRing R ι) :
    PolynomialBaseFunctionField F →+*
      PolynomialSourceFunctionField (R := R) (ι := ι) :=
  IsFractionRing.lift
    (polynomialMapImageAlgebraToFunctionField_injective F)

/--
The function-field extension induced by `F` is trivial.

The canonical embedding is always injective, so surjectivity is the
type-correct formulation of equality of the two function fields.
-/
def PolynomialFunctionFieldExtensionTrivial
    (F : κ → SourceRing R ι) : Prop :=
  Function.Surjective (polynomialBaseFunctionFieldEmbedding F)

/-- The function-field extension induced by `F`. -/
noncomputable def polynomialBaseFunctionFieldAlgebra
    (F : κ → SourceRing R ι) :
    Algebra
      (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := R) (ι := ι)) :=
  (polynomialBaseFunctionFieldEmbedding F).toAlgebra

noncomputable instance
    (F : κ → SourceRing R ι) :
    Algebra
      (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := R) (ι := ι)) :=
  polynomialBaseFunctionFieldAlgebra F

noncomputable instance
    (F : κ → SourceRing R ι) :
    IsScalarTower
      (polynomialMapImageAlgebra F)
      (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := R) (ι := ι)) :=
  IsScalarTower.of_algebraMap_eq fun b => by
    exact
      (IsFractionRing.lift_algebraMap
        (polynomialMapImageAlgebraToFunctionField_injective F) b).symm

/-- The canonical generic-source map `K ⊗_B A → L`. -/
noncomputable def polynomialGenericSourceTensorMap
    (F : κ → SourceRing R ι) :
    (PolynomialBaseFunctionField F ⊗[polynomialMapImageAlgebra F]
      SourceRing R ι) →ₐ[PolynomialBaseFunctionField F]
        PolynomialSourceFunctionField (R := R) (ι := ι) :=
  Algebra.TensorProduct.lift
    (Algebra.ofId
      (PolynomialBaseFunctionField F)
      (PolynomialSourceFunctionField (R := R) (ι := ι)))
    (IsScalarTower.toAlgHom
      (polynomialMapImageAlgebra F)
      (SourceRing R ι)
      (PolynomialSourceFunctionField (R := R) (ι := ι)))
    fun _ _ => mul_comm _ _

@[simp]
theorem polynomialGenericSourceTensorMap_tmul
    (F : κ → SourceRing R ι)
    (k : PolynomialBaseFunctionField F)
    (a : SourceRing R ι) :
    polynomialGenericSourceTensorMap F (k ⊗ₜ a) =
      algebraMap
          (PolynomialBaseFunctionField F)
          (PolynomialSourceFunctionField (R := R) (ι := ι)) k *
        algebraMap
          (SourceRing R ι)
          (PolynomialSourceFunctionField (R := R) (ι := ι)) a := by
  simp [polynomialGenericSourceTensorMap]

/-- The canonical generic-source map is injective. -/
theorem polynomialGenericSourceTensorMap_injective
    (F : κ → SourceRing R ι) :
    Function.Injective (polynomialGenericSourceTensorMap F) := by
  let B := polynomialMapImageAlgebra F
  let A := SourceRing R ι
  let K := PolynomialBaseFunctionField F
  let T := K ⊗[B] A
  letI : Algebra A T :=
    Algebra.TensorProduct.rightAlgebra
  letI :
      IsLocalization
        (Algebra.algebraMapSubmonoid A
          (nonZeroDivisors B)) T :=
    IsLocalization.tensorRight K (nonZeroDivisors B)
  apply
    IsLocalization.injective_of_map_algebraMap_zero
      (M := Algebra.algebraMapSubmonoid A
        (nonZeroDivisors B))
      T (polynomialGenericSourceTensorMap F).toRingHom
  intro a ha
  have haL :
      algebraMap
          (SourceRing R ι)
          (PolynomialSourceFunctionField (R := R) (ι := ι)) a = 0 := by
    change
      polynomialGenericSourceTensorMap F
          ((1 : PolynomialBaseFunctionField F) ⊗ₜ[
            polynomialMapImageAlgebra F] a) = 0 at ha
    simpa only [polynomialGenericSourceTensorMap_tmul,
      map_one, one_mul] using ha
  have ha0 : a = 0 := by
    apply
      (FaithfulSMul.algebraMap_injective
        (SourceRing R ι)
        (PolynomialSourceFunctionField (R := R) (ι := ι)))
    simpa only [map_zero] using haL
  subst a
  exact map_zero (algebraMap A T)

/--
Finite generic degree makes the canonical generic-source map
`K ⊗_B A → L` surjective.

Indeed, its range is a `K`-subalgebra of the finite extension `L/K`, hence
is a field.  Since that range contains the source coordinate ring `A`, it
also contains every fraction of `A`, and therefore all of `L = Frac(A)`.
-/
theorem polynomialGenericSourceTensorMap_surjective_of_finrank_pos
    (F : κ → SourceRing R ι)
    (hfinrank :
      0 < Module.finrank
        (PolynomialBaseFunctionField F)
        (PolynomialSourceFunctionField (R := R) (ι := ι))) :
    Function.Surjective (polynomialGenericSourceTensorMap F) := by
  let B := polynomialMapImageAlgebra F
  let A := SourceRing R ι
  let K := PolynomialBaseFunctionField F
  let L := PolynomialSourceFunctionField (R := R) (ι := ι)
  let T := K ⊗[B] A
  let φ : T →ₐ[K] L := polynomialGenericSourceTensorMap F
  let E : Subalgebra K L := φ.range
  letI : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos hfinrank
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  intro z
  obtain ⟨x, y, _hy, hxy⟩ := IsFractionRing.div_surjective (A := A) z
  have hxE :
      algebraMap (SourceRing R ι)
          (PolynomialSourceFunctionField (R := R) (ι := ι)) x ∈ E := by
    refine ⟨(1 : K) ⊗ₜ[B] x, ?_⟩
    change
      polynomialGenericSourceTensorMap F ((1 : K) ⊗ₜ[B] x) =
        algebraMap (SourceRing R ι)
          (PolynomialSourceFunctionField (R := R) (ι := ι)) x
    rw [polynomialGenericSourceTensorMap_tmul]
    simp
  have hyE :
      algebraMap (SourceRing R ι)
          (PolynomialSourceFunctionField (R := R) (ι := ι)) y ∈ E := by
    refine ⟨(1 : K) ⊗ₜ[B] y, ?_⟩
    change
      polynomialGenericSourceTensorMap F ((1 : K) ⊗ₜ[B] y) =
        algebraMap (SourceRing R ι)
          (PolynomialSourceFunctionField (R := R) (ι := ι)) y
    rw [polynomialGenericSourceTensorMap_tmul]
    simp
  let yE : E :=
    ⟨algebraMap (SourceRing R ι)
      (PolynomialSourceFunctionField (R := R) (ι := ι)) y, hyE⟩
  have hyInvE :
      (algebraMap (SourceRing R ι)
        (PolynomialSourceFunctionField (R := R) (ι := ι)) y)⁻¹ ∈ E := by
    simpa [yE] using
      E.inv_mem_of_algebraic (x := yE)
        (Algebra.IsAlgebraic.isAlgebraic (yE : L))
  have hquotE :
      algebraMap (SourceRing R ι)
          (PolynomialSourceFunctionField (R := R) (ι := ι)) x /
        algebraMap (SourceRing R ι)
          (PolynomialSourceFunctionField (R := R) (ι := ι)) y ∈ E := by
    rw [div_eq_mul_inv]
    exact E.mul_mem hxE hyInvE
  obtain ⟨t, ht⟩ := hquotE
  refine ⟨t, ?_⟩
  change φ t = z
  have ht' :
      φ t =
        algebraMap (SourceRing R ι)
            (PolynomialSourceFunctionField (R := R) (ι := ι)) x /
          algebraMap (SourceRing R ι)
            (PolynomialSourceFunctionField (R := R) (ι := ι)) y :=
    ht
  exact ht'.trans hxy

/-- The image algebra acts on the collision ring through its left source
projection. -/
noncomputable def polynomialImageCollisionAlgebra
    (F : κ → SourceRing R ι) :
    Algebra (polynomialMapImageAlgebra F) (CollisionRing F) :=
  ((collisionLeft F).comp
    (Subalgebra.val (polynomialMapImageAlgebra F))).toRingHom.toAlgebra

/-- The two canonical source maps into the tensor square over the coordinate
image agree on the coordinates of `F`. -/
noncomputable def collisionImageTensorPair
    (F : κ → SourceRing R ι) :
    CollisionMapPair F
      (SourceRing R ι ⊗[polynomialMapImageAlgebra F]
        SourceRing R ι) :=
  { left :=
      (Algebra.TensorProduct.includeLeft :
        SourceRing R ι →ₐ[R]
          SourceRing R ι ⊗[polynomialMapImageAlgebra F]
            SourceRing R ι)
    right :=
      (Algebra.TensorProduct.includeRight :
        SourceRing R ι →ₐ[polynomialMapImageAlgebra F]
          SourceRing R ι ⊗[polynomialMapImageAlgebra F]
            SourceRing R ι).restrictScalars R
    agree := fun j => by
      let b : polynomialMapImageAlgebra F :=
        ⟨F j, ⟨X j, coordinateAlgHom_X F j⟩⟩
      have hb :=
        Algebra.TensorProduct.tmul_one_eq_one_tmul
          (A := SourceRing R ι) (B := SourceRing R ι) b
      simpa [b] using hb }

/--
The collision quotient as a tensor product over the actual coordinate image
algebra.  Unlike `collisionTensorEquiv`, this uses
`B = R[F₁, ..., Fₙ]` rather than the abstract target polynomial ring.
-/
noncomputable def collisionImageTensorEquiv
    (F : κ → SourceRing R ι) :
    letI : Algebra
        (polynomialMapImageAlgebra F) (CollisionRing F) :=
      polynomialImageCollisionAlgebra F
    CollisionRing F ≃ₐ[polynomialMapImageAlgebra F]
      SourceRing R ι ⊗[polynomialMapImageAlgebra F]
        SourceRing R ι := by
  let B := polynomialMapImageAlgebra F
  let A := SourceRing R ι
  let C := CollisionRing F
  letI : Algebra B C := polynomialImageCollisionAlgebra F

  let tensorPair : CollisionMapPair F (A ⊗[B] A) :=
    collisionImageTensorPair F

  let forward : C →ₐ[R] A ⊗[B] A :=
    collisionLift tensorPair

  let leftMap : A →ₐ[B] C :=
    { toRingHom := (collisionLeft F).toRingHom
      commutes' := fun b => rfl }

  have hcoordinate :
      (collisionRight F).comp (coordinateAlgHom F) =
        (collisionLeft F).comp (coordinateAlgHom F) := by
    apply MvPolynomial.algHom_ext
    intro j
    simpa using
      (collisionLeft_apply_F_eq_collisionRight_apply_F F j).symm

  have himage :
      (collisionRight F).comp (Subalgebra.val B) =
        (collisionLeft F).comp (Subalgebra.val B) := by
    apply AlgHom.ext
    intro b
    obtain ⟨p, hp⟩ := b.property
    have hp' := AlgHom.congr_fun hcoordinate p
    change collisionRight F b.1 = collisionLeft F b.1
    rw [← hp]
    exact hp'

  let rightMap : A →ₐ[B] C :=
    { toRingHom := (collisionRight F).toRingHom
      commutes' := fun b => by
        exact AlgHom.congr_fun himage b }

  let backward : (A ⊗[B] A) →ₐ[R] C :=
    (Algebra.TensorProduct.productMap leftMap rightMap).restrictScalars R

  let eR : C ≃ₐ[R] A ⊗[B] A := by
    apply AlgEquiv.ofAlgHom forward backward
    · apply AlgHom.ext
      intro x
      induction x using TensorProduct.induction_on with
      | zero =>
          simp
      | tmul a b =>
          have hleft :
              forward (collisionLeft F a) = tensorPair.left a := by
            exact
              AlgHom.congr_fun
                (collisionLift_comp_left tensorPair) a
          have hright :
              forward (collisionRight F b) = tensorPair.right b := by
            exact
              AlgHom.congr_fun
                (collisionLift_comp_right tensorPair) b
          change
            forward
                ((Algebra.TensorProduct.productMap leftMap rightMap)
                  (a ⊗ₜ[B] b)) =
              a ⊗ₜ[B] b
          rw [Algebra.TensorProduct.productMap_apply_tmul]
          change
            forward (collisionLeft F a * collisionRight F b) =
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
            forward (collisionLeft F (X i)) =
              tensorPair.left (X i) := by
          exact
            AlgHom.congr_fun
              (collisionLift_comp_left tensorPair) (X i)
        change
          backward (forward (collisionLeft F (X i))) =
            collisionLeft F (X i)
        rw [hforward]
        change
          (Algebra.TensorProduct.productMap leftMap rightMap)
              ((Algebra.TensorProduct.includeLeft :
                A →ₐ[R] A ⊗[B] A) (X i)) =
            collisionLeft F (X i)
        rw [Algebra.TensorProduct.includeLeft_apply,
          Algebra.TensorProduct.productMap_apply_tmul]
        simp [leftMap]
        rw [← leftRename_X (R := R) i]
        exact collisionLeft_apply F (X i)
      · apply MvPolynomial.algHom_ext
        intro i
        have hforward :
            forward (collisionRight F (X i)) =
              tensorPair.right (X i) := by
          exact
            AlgHom.congr_fun
              (collisionLift_comp_right tensorPair) (X i)
        change
          backward (forward (collisionRight F (X i))) =
            collisionRight F (X i)
        rw [hforward]
        change
          (Algebra.TensorProduct.productMap leftMap rightMap)
              ((Algebra.TensorProduct.includeRight :
                A →ₐ[B] A ⊗[B] A) (X i)) =
            collisionRight F (X i)
        rw [Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.productMap_apply_tmul]
        simp [rightMap]
        rw [← rightRename_X (R := R) i]
        exact collisionRight_apply F (X i)

  exact
    { eR.toRingEquiv with
      commutes' := fun b => by
        change forward (collisionLeft F b.1) =
          b.1 ⊗ₜ[B] (1 : A)
        exact
          AlgHom.congr_fun
            (collisionLift_comp_left tensorPair) b.1 }

omit [IsDomain R] in
/--
If the source algebra is flat over the coordinate-image algebra, then so
is the collision ring.

The collision ring is the self-tensor square of the source algebra over
the coordinate image.  Tensor products preserve flatness, and flatness is
transported back across `collisionImageTensorEquiv`.
-/
theorem polynomialCollisionRing_flat
    (F : κ → SourceRing R ι)
    [Module.Flat
      (polynomialMapImageAlgebra F) (SourceRing R ι)] :
    letI : Algebra
        (polynomialMapImageAlgebra F) (CollisionRing F) :=
      polynomialImageCollisionAlgebra F
    Module.Flat
      (polynomialMapImageAlgebra F) (CollisionRing F) := by
  let B := polynomialMapImageAlgebra F
  let A := SourceRing R ι
  let C := CollisionRing F
  letI : Algebra B C := polynomialImageCollisionAlgebra F
  have hTensor : Module.Flat B (A ⊗[B] A) := inferInstance
  exact
    @Module.Flat.of_linearEquiv
      B (A ⊗[B] A) C _ _ _ _ _ hTensor
      (collisionImageTensorEquiv F).toLinearEquiv

omit [IsDomain R] in
@[simp]
theorem collisionImageTensorEquiv_collisionLeft
    (F : κ → SourceRing R ι)
    (a : SourceRing R ι) :
    letI : Algebra
        (polynomialMapImageAlgebra F) (CollisionRing F) :=
      polynomialImageCollisionAlgebra F
    collisionImageTensorEquiv F (collisionLeft F a) =
      a ⊗ₜ[polynomialMapImageAlgebra F] (1 : SourceRing R ι) := by
  letI : Algebra
      (polynomialMapImageAlgebra F) (CollisionRing F) :=
    polynomialImageCollisionAlgebra F
  change
    collisionLift (collisionImageTensorPair F)
        (collisionLeft F a) =
      a ⊗ₜ[polynomialMapImageAlgebra F] (1 : SourceRing R ι)
  exact
    AlgHom.congr_fun
      (collisionLift_comp_left (collisionImageTensorPair F)) a

omit [IsDomain R] in
@[simp]
theorem collisionImageTensorEquiv_collisionRight
    (F : κ → SourceRing R ι)
    (a : SourceRing R ι) :
    letI : Algebra
        (polynomialMapImageAlgebra F) (CollisionRing F) :=
      polynomialImageCollisionAlgebra F
    collisionImageTensorEquiv F (collisionRight F a) =
      (1 : SourceRing R ι) ⊗ₜ[polynomialMapImageAlgebra F] a := by
  letI : Algebra
      (polynomialMapImageAlgebra F) (CollisionRing F) :=
    polynomialImageCollisionAlgebra F
  change
    collisionLift (collisionImageTensorPair F)
        (collisionRight F a) =
      (1 : SourceRing R ι) ⊗ₜ[polynomialMapImageAlgebra F] a
  exact
    AlgHom.congr_fun
      (collisionLift_comp_right (collisionImageTensorPair F)) a

omit [IsDomain R] in
@[simp]
theorem collisionDiagonal_collisionLeft
    (F : κ → SourceRing R ι)
    (a : SourceRing R ι) :
    collisionDiagonal F (collisionLeft F a) = a := by
  rw [collisionLeft_apply, collisionDiagonal_mk,
    diagonalEval_leftRename]

omit [IsDomain R] in
@[simp]
theorem collisionDiagonal_collisionRight
    (F : κ → SourceRing R ι)
    (a : SourceRing R ι) :
    collisionDiagonal F (collisionRight F a) = a := by
  rw [collisionRight_apply, collisionDiagonal_mk,
    diagonalEval_rightRename]

/-- The collision diagonal as a morphism over the coordinate image algebra. -/
noncomputable def polynomialImageCollisionDiagonal
    (F : κ → SourceRing R ι) :
    letI : Algebra
        (polynomialMapImageAlgebra F) (CollisionRing F) :=
      polynomialImageCollisionAlgebra F
    CollisionRing F →ₐ[polynomialMapImageAlgebra F]
      SourceRing R ι := by
  let B := polynomialMapImageAlgebra F
  letI : Algebra B (CollisionRing F) :=
    polynomialImageCollisionAlgebra F
  exact
    { toRingHom := (collisionDiagonal F).toRingHom
      commutes' := fun b => by
        change collisionDiagonal F (collisionLeft F b.1) = b.1
        exact collisionDiagonal_collisionLeft F b.1 }

omit [IsDomain R] in
/-- The image-algebra tensor presentation carries the collision diagonal to
tensor multiplication. -/
theorem collisionImageTensorEquiv_intertwines_diagonal
    (F : κ → SourceRing R ι) :
    letI : Algebra
        (polynomialMapImageAlgebra F) (CollisionRing F) :=
      polynomialImageCollisionAlgebra F
    (diagonalMultiplication
        (B := polynomialMapImageAlgebra F)
        (A := SourceRing R ι)).comp
          (collisionImageTensorEquiv F).toAlgHom =
      polynomialImageCollisionDiagonal F := by
  let B := polynomialMapImageAlgebra F
  let A := SourceRing R ι
  let C := CollisionRing F
  letI : Algebra B C := polynomialImageCollisionAlgebra F
  letI : IsScalarTower R B C := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro r
    change algebraMap R C r =
      collisionLeft F
        (algebraMap B A (algebraMap R B r))
    rw [← IsScalarTower.algebraMap_apply R B A]
    exact (collisionLeft F).commutes r |>.symm
  apply AlgHom.restrictScalars_injective R
  apply collisionHom_ext
  · apply MvPolynomial.algHom_ext
    intro i
    change
      diagonalMultiplication
          (B := B) (A := A)
          (collisionImageTensorEquiv F
            (collisionLeft F (X i))) =
        collisionDiagonal F (collisionLeft F (X i))
    rw [collisionImageTensorEquiv_collisionLeft,
      collisionDiagonal_collisionLeft]
    change (X i : A) * 1 = X i
    simp
  · apply MvPolynomial.algHom_ext
    intro i
    change
      diagonalMultiplication
          (B := B) (A := A)
          (collisionImageTensorEquiv F
            (collisionRight F (X i))) =
        collisionDiagonal F (collisionRight F (X i))
    rw [collisionImageTensorEquiv_collisionRight,
      collisionDiagonal_collisionRight]
    change (1 : A) * X i = X i
    simp

/--
After passage to the base function field, the collision ring becomes the
self-tensor square of the generic source algebra.
-/
noncomputable def polynomialGenericCollisionSelfTensorEquiv
    (F : κ → SourceRing R ι) :
    letI : Algebra
        (polynomialMapImageAlgebra F) (CollisionRing F) :=
      polynomialImageCollisionAlgebra F
    PolynomialBaseFunctionField F ⊗[polynomialMapImageAlgebra F]
        CollisionRing F ≃ₐ[PolynomialBaseFunctionField F]
      (PolynomialBaseFunctionField F ⊗[polynomialMapImageAlgebra F]
          SourceRing R ι) ⊗[PolynomialBaseFunctionField F]
        (PolynomialBaseFunctionField F ⊗[polynomialMapImageAlgebra F]
          SourceRing R ι) := by
  let B := polynomialMapImageAlgebra F
  let A := SourceRing R ι
  let K := PolynomialBaseFunctionField F
  letI : Algebra B (CollisionRing F) :=
    polynomialImageCollisionAlgebra F
  exact
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : K ≃ₐ[K] K)
      (collisionImageTensorEquiv F)).trans
        (baseChangeSelfTensorEquiv B A K)

/--
The generic source equivalence `K ⊗_B A ≃ L`, bundled from the canonical
injective map and the explicit generic-finiteness/surjectivity input.
-/
noncomputable def polynomialGenericSourceEquiv
    (F : κ → SourceRing R ι)
    (hsurj :
      Function.Surjective (polynomialGenericSourceTensorMap F)) :
    (PolynomialBaseFunctionField F ⊗[polynomialMapImageAlgebra F]
      SourceRing R ι) ≃ₐ[PolynomialBaseFunctionField F]
        PolynomialSourceFunctionField (R := R) (ι := ι) :=
  AlgEquiv.ofBijective
    (polynomialGenericSourceTensorMap F)
    ⟨polynomialGenericSourceTensorMap_injective F, hsurj⟩

/-- If the generic-source map is surjective (as it is for a generically
finite polynomial map), the canonical generic collision map is an
equivalence. -/
noncomputable def polynomialGenericCollisionEquiv
    (F : κ → SourceRing R ι)
    (hsurj :
      Function.Surjective (polynomialGenericSourceTensorMap F)) :
    letI : Algebra
        (polynomialMapImageAlgebra F) (CollisionRing F) :=
      polynomialImageCollisionAlgebra F
    PolynomialBaseFunctionField F ⊗[polynomialMapImageAlgebra F]
        CollisionRing F ≃ₐ[PolynomialBaseFunctionField F]
      PolynomialSourceFunctionField (R := R) (ι := ι) ⊗[
        PolynomialBaseFunctionField F]
        PolynomialSourceFunctionField (R := R) (ι := ι) := by
  let B := polynomialMapImageAlgebra F
  let K := PolynomialBaseFunctionField F
  let L := PolynomialSourceFunctionField (R := R) (ι := ι)
  letI : Algebra B (CollisionRing F) :=
    polynomialImageCollisionAlgebra F
  let e : (K ⊗[B] SourceRing R ι) ≃ₐ[K] L :=
    polynomialGenericSourceEquiv F hsurj
  exact
    (polynomialGenericCollisionSelfTensorEquiv F).trans
      (Algebra.TensorProduct.congr e e)

end ImageFunctionFields

end CollisionIdeals
