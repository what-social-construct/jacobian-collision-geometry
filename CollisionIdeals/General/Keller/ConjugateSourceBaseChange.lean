import CollisionIdeals.General.Keller.Etale
import CollisionIdeals.General.Galois.ConjugateInvariantField
import CollisionIdeals.General.Galois.ConjugateInvariantFiniteType
import Mathlib.RingTheory.Flat.Basic

/-!
# The original source is finite over the actual invariant target open

The original source, base changed from `B` to the existing fixed algebra
`C = E^G`, embeds in the all-conjugate algebra `E`. Injectivity uses the
Keller flatness of the source and the existing generic-source embedding.
Since `E` is finite over the Noetherian ring `C`, this gives finiteness of
the original source over this actual open, without assuming finiteness
over the whole target or asserting that the open is the whole target.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 10000

namespace CollisionIdeals

open scoped TensorProduct

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ}
variable {F : PolynomialSelfMap k n} {N : Type u} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

@[reducible] local instance finiteLocusBaseAlgebra :
    Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

@[reducible] local instance finiteLocusBaseFieldAlgebra :
    Algebra (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) :=
  OreLocalization.instAlgebra

@[reducible] local instance finiteLocusSourceAlgebra :
    Algebra (PolynomialImageAlgebra F) (PolynomialSourceCoordinateRing k n) :=
  Subalgebra.toAlgebra (PolynomialImageAlgebra F)

local instance finiteLocusSourceSMul :
    SMul (PolynomialImageAlgebra F) (PolynomialSourceCoordinateRing k n) := Algebra.toSMul

local instance finiteLocusSourceModule :
    Module (PolynomialImageAlgebra F) (PolynomialSourceCoordinateRing k n) :=
  (PolynomialImageAlgebra F).moduleLeft

local instance finiteLocusBaseFieldSMul :
    SMul (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) := Algebra.toSMul

local instance finiteLocusBaseFieldModule :
    Module (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) := Algebra.toModule

@[reducible] local instance finiteLocusConjugateAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateAlgebra D)

@[reducible] local instance finiteLocusInvariantAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateInvariantAlgebra D)

local instance finiteLocusConjugateSMul (D : PolynomialNormalClosureData F N) :
    SMul (PolynomialImageAlgebra F) (polynomialConjugateAlgebra D) := Algebra.toSMul

local instance finiteLocusConjugateModule (D : PolynomialNormalClosureData F N) :
    Module (PolynomialImageAlgebra F) (polynomialConjugateAlgebra D) := Algebra.toModule

local instance finiteLocusInvariantSMul (D : PolynomialNormalClosureData F N) :
    SMul (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) := Algebra.toSMul

local instance finiteLocusInvariantModule (D : PolynomialNormalClosureData F N) :
    Module (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) := Algebra.toModule

@[reducible] local instance finiteLocusOverInvariantAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (polynomialConjugateInvariantAlgebra D) (polynomialConjugateAlgebra D) :=
  Subalgebra.toAlgebra (polynomialConjugateInvariantAlgebra D)

local instance finiteLocusOverInvariantSMul (D : PolynomialNormalClosureData F N) :
    SMul (polynomialConjugateInvariantAlgebra D) (polynomialConjugateAlgebra D) := Algebra.toSMul

local instance finiteLocusOverInvariantModule (D : PolynomialNormalClosureData F N) :
    Module (polynomialConjugateInvariantAlgebra D) (polynomialConjugateAlgebra D) :=
  (polynomialConjugateInvariantAlgebra D).moduleLeft

local instance finiteLocusInvariantTower (D : PolynomialNormalClosureData F N) :
    IsScalarTower (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D)
      (polynomialConjugateAlgebra D) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

local notation "B₀" => PolynomialImageAlgebra F
local notation "A₀" => PolynomialSourceCoordinateRing k n
local notation "K₀" => PolynomialMapBaseFunctionField F
local notation "L₀" => PolynomialMapSourceFunctionField F

@[reducible] local instance finiteLocusBaseInvariantAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra B₀ (polynomialConjugateInvariantBaseAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateInvariantBaseAlgebra D)

local instance finiteLocusBaseInvariantSMul (D : PolynomialNormalClosureData F N) :
    SMul B₀ (polynomialConjugateInvariantBaseAlgebra D) := Algebra.toSMul

local instance finiteLocusBaseInvariantModule (D : PolynomialNormalClosureData F N) :
    Module B₀ (polynomialConjugateInvariantBaseAlgebra D) := Algebra.toModule

local instance finiteLocusInvariantSelfModule (D : PolynomialNormalClosureData F N) :
    Module (polynomialConjugateInvariantAlgebra D) (polynomialConjugateInvariantAlgebra D) :=
  Semiring.toModule

local instance finiteLocusInvariantSelfSMul (D : PolynomialNormalClosureData F N) :
    SMul (polynomialConjugateInvariantAlgebra D) (polynomialConjugateInvariantAlgebra D) :=
  (finiteLocusInvariantSelfModule D).toSMul

local instance finiteLocusInvariantSelfDistribMulAction (D : PolynomialNormalClosureData F N) :
    DistribMulAction (polynomialConjugateInvariantAlgebra D)
      (polynomialConjugateInvariantAlgebra D) :=
  (finiteLocusInvariantSelfModule D).toDistribMulAction

local instance finiteLocusInvariantSMulComm (D : PolynomialNormalClosureData F N) :
    SMulCommClass (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D)
      (polynomialConjugateInvariantAlgebra D) :=
  Algebra.to_smulCommClass

local instance finiteLocusTensorSMul (D : PolynomialNormalClosureData F N) :
    SMul (polynomialConjugateInvariantAlgebra D)
      (polynomialConjugateInvariantAlgebra D ⊗[B₀] A₀) :=
  TensorProduct.leftHasSMul

local instance finiteLocusTensorModule (D : PolynomialNormalClosureData F N) :
    Module (polynomialConjugateInvariantAlgebra D)
      (polynomialConjugateInvariantAlgebra D ⊗[B₀] A₀) :=
  TensorProduct.leftModule

@[reducible] local instance finiteLocusTensorAlgebra (D : PolynomialNormalClosureData F N) :
    Algebra (polynomialConjugateInvariantAlgebra D)
      (polynomialConjugateInvariantAlgebra D ⊗[B₀] A₀) :=
  Algebra.TensorProduct.leftAlgebra

/-- The marked original source ring, corestricted to the same all-conjugate
algebra which already contains every conjugate source. -/
private def markedSourceToConjugate (D : PolynomialNormalClosureData F N) :
    A₀ →ₐ[B₀] polynomialConjugateAlgebra D :=
  (polynomialConjugateSourceMapOverImage D 1).codRestrict _
    (polynomialConjugateAlgebra_polynomial_mem D 1)

private def invariantToBaseField [Algebra.IsSeparable K₀ N]
    (D : PolynomialNormalClosureData F N) :
    polynomialConjugateInvariantAlgebra D →ₐ[B₀] K₀ :=
  (polynomialConjugateInvariantBaseAlgebra D).val.comp
    (polynomialConjugateInvariantBaseEquiv D).symm.toAlgHom

/-- The original source base changed to the actual fixed algebra maps
canonically to the all-conjugate algebra. -/
def polynomialSourceInvariantBaseChangeMap (D : PolynomialNormalClosureData F N) :
    polynomialConjugateInvariantAlgebra D ⊗[B₀] A₀ →ₐ[polynomialConjugateInvariantAlgebra D]
      polynomialConjugateAlgebra D :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (markedSourceToConjugate D)
    (fun _ _ => mul_comm _ _)

@[simp]
theorem polynomialSourceInvariantBaseChangeMap_tmul (D : PolynomialNormalClosureData F N)
    (c : polynomialConjugateInvariantAlgebra D) (a : A₀) :
    (polynomialSourceInvariantBaseChangeMap D (c ⊗ₜ[B₀] a) : N) =
      (c.val : N) * polynomialConjugateSourceMapOverImage D 1 a := rfl

private theorem polynomialSourceInvariantBaseChangeMap_toNormal
    [Algebra.IsSeparable K₀ N] (D : PolynomialNormalClosureData F N)
    (x : polynomialConjugateInvariantAlgebra D ⊗[B₀] A₀) :
    (polynomialSourceInvariantBaseChangeMap D x : N) =
      D.embedding (polynomialGenericSourceTensorMap F
        (((invariantToBaseField D).toLinearMap.rTensor A₀) x)) := by
  let lhs : polynomialConjugateInvariantAlgebra D ⊗[B₀] A₀ →+ N :=
    (polynomialConjugateAlgebra D).val.toAddMonoidHom.comp
      (polynomialSourceInvariantBaseChangeMap D).toAddMonoidHom
  let rhs : polynomialConjugateInvariantAlgebra D ⊗[B₀] A₀ →+ N :=
    D.embedding.toAddMonoidHom.comp
      ((polynomialGenericSourceTensorMap F).toAddMonoidHom.comp
        ((invariantToBaseField D).toLinearMap.rTensor A₀).toAddMonoidHom)
  change lhs x = rhs x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c a =>
      change (c.val : N) * polynomialConjugateSourceMapOverImage D 1 a =
        D.embedding
          (algebraMap K₀ L₀ (invariantToBaseField D c) *
            algebraMap A₀ L₀ a)
      rw [map_mul, D.embedding.commutes]
      have hValue := polynomialConjugateInvariantAlgebra_baseField_algebraMap D c
      change algebraMap K₀ N (invariantToBaseField D c) = (c.val : N) at hValue
      rw [hValue]
      simp only [polynomialConjugateSourceMapOverImage_apply, AlgEquiv.one_apply]
  | add x y hx hy => rw [lhs.map_add, rhs.map_add, hx, hy]

/-- Keller flatness makes the canonical source base-change map injective.
No finiteness of the original source over the target is supplied. -/
theorem polynomialSourceInvariantBaseChangeMap_injective
    [Algebra.IsSeparable K₀ N]
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    Function.Injective (polynomialSourceInvariantBaseChangeMap D) := by
  letI : Module.Flat B₀ A₀ :=
    KellerEtaleBridge.toKellerFlatBridge F (kellerEtaleBridge F) hKeller
  let inc := invariantToBaseField D
  have hInc : Function.Injective inc := by
    intro x y hxy
    exact (polynomialConjugateInvariantBaseEquiv D).symm.injective (Subtype.ext hxy)
  have hTensor : Function.Injective (inc.toLinearMap.rTensor A₀) :=
    Module.Flat.rTensor_preserves_injective_linearMap inc.toLinearMap hInc
  intro x y hxy
  apply hTensor
  apply polynomialGenericSourceTensorMap_injective F
  apply D.embedding.injective
  have hN := congrArg (fun z : polynomialConjugateAlgebra D => (z : N)) hxy
  simpa only [polynomialSourceInvariantBaseChangeMap_toNormal] using hN

/-- The original polynomial source is module-finite after base change to
the actual invariant target open. The larger open has not been filled. -/
theorem polynomialSourceInvariantBaseChange_finite
    [Algebra.IsSeparable K₀ N]
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    Module.Finite (polynomialConjugateInvariantAlgebra D)
      (polynomialConjugateInvariantAlgebra D ⊗[B₀] A₀) := by
  letI : IsNoetherianRing B₀ := polynomialImageAlgebra_isNoetherianRing F
  letI := polynomialConjugateInvariantAlgebra_finiteType D
  letI : IsNoetherianRing (polynomialConjugateInvariantAlgebra D) :=
    Algebra.FiniteType.isNoetherianRing B₀ _
  letI : Module.Finite (polynomialConjugateInvariantAlgebra D) (polynomialConjugateAlgebra D) :=
    polynomialConjugateAlgebra_finite_over_invariants D
  letI : IsNoetherian (polynomialConjugateInvariantAlgebra D) (polynomialConjugateAlgebra D) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  let f : (polynomialConjugateInvariantAlgebra D ⊗[B₀] A₀) →ₗ[polynomialConjugateInvariantAlgebra D]
      polynomialConjugateAlgebra D := (polynomialSourceInvariantBaseChangeMap D).toLinearMap
  have hf : Function.Injective f := polynomialSourceInvariantBaseChangeMap_injective D hKeller
  exact Module.Finite.of_injective f hf

/-- Étaleness of the original source persists over the same fixed-algebra
base change. Combined with the preceding theorem, this is a finite étale
source over the actual target open, not over the whole target. -/
theorem polynomialSourceInvariantBaseChange_etale
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    Algebra.Etale (polynomialConjugateInvariantAlgebra D)
      (polynomialConjugateInvariantAlgebra D ⊗[B₀] A₀) := by
  letI := polynomialSource_etale_of_isKeller F hKeller
  infer_instance

end

end CollisionIdeals
