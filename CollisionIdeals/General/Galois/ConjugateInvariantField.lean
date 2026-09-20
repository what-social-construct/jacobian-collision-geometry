import CollisionIdeals.General.Galois.ConjugateInvariants
import Mathlib.RingTheory.Localization.AsSubring

/-!
# The fixed algebra inside the target function field

Pulling the all-conjugate algebra back along `K → N` realizes its
intersection with the embedded base field as an existing `Subalgebra B K`.
In the separable case this is canonically equivalent to the fixed algebra
already constructed in `ConjugateInvariants`, not a new quotient object.
Its fraction field is `K`.

This supplies the ring-theoretic birational comparison. It does not assert
that the fixed algebra is `B`, that its spectrum is an open subscheme of
the target, or that the boundary vanishes. No Keller hypothesis is used.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ}
variable {F : PolynomialSelfMap k n}
variable {N : Type u} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

/-- The target-field realization of the all-conjugate invariant algebra,
formed by the existing subalgebra pullback along `K → N`. -/
def polynomialConjugateInvariantBaseAlgebra
    (D : PolynomialNormalClosureData F N) :
    Subalgebra (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI : IsScalarTower (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) N :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (polynomialConjugateAlgebra D).comap
    (IsScalarTower.toAlgHom (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) N)

@[simp]
theorem polynomialConjugateInvariantBaseAlgebra_mem_iff
    (D : PolynomialNormalClosureData F N) (x : PolynomialMapBaseFunctionField F) :
    x ∈ polynomialConjugateInvariantBaseAlgebra D ↔
      algebraMap (PolynomialMapBaseFunctionField F) N x ∈ polynomialConjugateAlgebra D :=
  Iff.rfl

/-- Every `B`-subalgebra of its fraction field has that same fraction field.
This applies to the actual pullback without a separability hypothesis. -/
theorem polynomialConjugateInvariantBaseAlgebra_isFractionRing
    (D : PolynomialNormalClosureData F N) :
    IsFractionRing (polynomialConjugateInvariantBaseAlgebra D)
      (PolynomialMapBaseFunctionField F) := by
  infer_instance

/-- The base-field inclusion maps the actual pullback into the already
constructed fixed algebra. -/
def polynomialConjugateInvariantBaseToFixed
    (D : PolynomialNormalClosureData F N) :
    polynomialConjugateInvariantBaseAlgebra D →ₐ[PolynomialImageAlgebra F]
      polynomialConjugateInvariantAlgebra D := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI : IsScalarTower (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) N :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f : polynomialConjugateInvariantBaseAlgebra D →ₐ[PolynomialImageAlgebra F] N :=
    (IsScalarTower.toAlgHom (PolynomialImageAlgebra F)
      (PolynomialMapBaseFunctionField F) N).comp
        (polynomialConjugateInvariantBaseAlgebra D).val
  let fE := f.codRestrict (polynomialConjugateAlgebra D) fun x => x.property
  exact fE.codRestrict (polynomialConjugateInvariantAlgebra D) fun x =>
    (polynomialConjugateInvariantAlgebra_mem_iff D (fE x)).mpr
      (fun g => g.commutes (x : PolynomialMapBaseFunctionField F))

@[simp]
theorem polynomialConjugateInvariantBaseToFixed_apply
    (D : PolynomialNormalClosureData F N)
    (x : polynomialConjugateInvariantBaseAlgebra D) :
    ((polynomialConjugateInvariantBaseToFixed D x).val : N) =
      algebraMap (PolynomialMapBaseFunctionField F) N x := rfl

/-- In a separable normal closure, the pullback to `K` is precisely the
existing fixed algebra, with its original `B`-algebra structure. -/
def polynomialConjugateInvariantBaseEquiv
    [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]
    (D : PolynomialNormalClosureData F N) :
    polynomialConjugateInvariantBaseAlgebra D ≃ₐ[PolynomialImageAlgebra F]
      polynomialConjugateInvariantAlgebra D := by
  apply AlgEquiv.ofBijective (polynomialConjugateInvariantBaseToFixed D)
  constructor
  · intro x y h
    apply Subtype.ext
    apply (algebraMap (PolynomialMapBaseFunctionField F) N).injective
    exact congrArg (fun z : polynomialConjugateInvariantAlgebra D => (z.val : N)) h
  · intro z
    obtain ⟨x, hx⟩ :=
      (polynomialConjugateInvariantAlgebra_mem_iff_baseField D z.val).mp z.property
    have hxE : x ∈ polynomialConjugateInvariantBaseAlgebra D := by
      rw [polynomialConjugateInvariantBaseAlgebra_mem_iff, hx]
      exact z.val.property
    refine ⟨⟨x, hxE⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hx

/-- The canonical embedding of the existing fixed algebra into `K`,
transported through its target-field realization. It is explicit to avoid
introducing a competing global algebra instance. -/
def polynomialConjugateInvariantAlgebraBaseFieldAlgebra
    [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]
    (D : PolynomialNormalClosureData F N) :
    Algebra (polynomialConjugateInvariantAlgebra D) (PolynomialMapBaseFunctionField F) :=
  ((algebraMap (polynomialConjugateInvariantBaseAlgebra D) (PolynomialMapBaseFunctionField F)).comp
    (polynomialConjugateInvariantBaseEquiv D).toRingEquiv.symm.toRingHom).toAlgebra

/-- The embedding of the fixed algebra in `K` agrees, after `K → N`, with
its original inclusion in the all-conjugate algebra. -/
theorem polynomialConjugateInvariantAlgebra_baseField_algebraMap
    [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]
    (D : PolynomialNormalClosureData F N) (z : polynomialConjugateInvariantAlgebra D) :
    letI : Algebra (polynomialConjugateInvariantAlgebra D) (PolynomialMapBaseFunctionField F) :=
      polynomialConjugateInvariantAlgebraBaseFieldAlgebra D
    algebraMap (PolynomialMapBaseFunctionField F) N
        (algebraMap (polynomialConjugateInvariantAlgebra D) (PolynomialMapBaseFunctionField F) z) =
      (z.val : N) := by
  have h := congrArg (fun w : polynomialConjugateInvariantAlgebra D => (w.val : N))
    ((polynomialConjugateInvariantBaseEquiv D).apply_symm_apply z)
  exact h

set_option synthInstance.maxHeartbeats 80000 in
/-- The fixed-algebra embedding into `K` is compatible with the original
coordinate-image base map. -/
theorem polynomialConjugateInvariantAlgebra_baseField_imageTower
    [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]
    (D : PolynomialNormalClosureData F N) :
    letI : Algebra (polynomialConjugateInvariantAlgebra D) (PolynomialMapBaseFunctionField F) :=
      polynomialConjugateInvariantAlgebraBaseFieldAlgebra D
    IsScalarTower (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D)
      (PolynomialMapBaseFunctionField F) := by
  letI : Algebra (polynomialConjugateInvariantAlgebra D) (PolynomialMapBaseFunctionField F) :=
    polynomialConjugateInvariantAlgebraBaseFieldAlgebra D
  apply IsScalarTower.of_algebraMap_eq
  intro b
  exact (congrArg
    (fun x : polynomialConjugateInvariantBaseAlgebra D =>
      (x : PolynomialMapBaseFunctionField F))
    ((polynomialConjugateInvariantBaseEquiv D).symm.commutes b)).symm

set_option synthInstance.maxHeartbeats 80000 in
/-- The fixed-algebra embedding into `K` agrees with the original inclusion
in the normal closure as a scalar tower. -/
theorem polynomialConjugateInvariantAlgebra_baseField_normalTower
    [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]
    (D : PolynomialNormalClosureData F N) :
    letI : Algebra (polynomialConjugateInvariantAlgebra D) (PolynomialMapBaseFunctionField F) :=
      polynomialConjugateInvariantAlgebraBaseFieldAlgebra D
    IsScalarTower (polynomialConjugateInvariantAlgebra D) (PolynomialMapBaseFunctionField F) N := by
  letI : Algebra (polynomialConjugateInvariantAlgebra D) (PolynomialMapBaseFunctionField F) :=
    polynomialConjugateInvariantAlgebraBaseFieldAlgebra D
  exact IsScalarTower.of_algebraMap_eq fun z =>
    (polynomialConjugateInvariantAlgebra_baseField_algebraMap D z).symm

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 80000 in
/-- The original fixed algebra, not just its pullback presentation, has
the target function field as its fraction field. Fractions from `B` already
suffice, and the normal-closure comparison makes its embedding injective. -/
theorem polynomialConjugateInvariantAlgebra_isFractionRing
    [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]
    (D : PolynomialNormalClosureData F N) :
    letI : Algebra (polynomialConjugateInvariantAlgebra D) (PolynomialMapBaseFunctionField F) :=
      polynomialConjugateInvariantAlgebraBaseFieldAlgebra D
    IsFractionRing (polynomialConjugateInvariantAlgebra D) (PolynomialMapBaseFunctionField F) := by
  letI : Algebra (polynomialConjugateInvariantAlgebra D) (PolynomialMapBaseFunctionField F) :=
    polynomialConjugateInvariantAlgebraBaseFieldAlgebra D
  letI : SMul (polynomialConjugateInvariantAlgebra D) (PolynomialMapBaseFunctionField F) :=
    Algebra.toSMul
  letI : IsScalarTower (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D)
      (PolynomialMapBaseFunctionField F) :=
    polynomialConjugateInvariantAlgebra_baseField_imageTower D
  have hinj : Function.Injective
      (algebraMap (polynomialConjugateInvariantAlgebra D) (PolynomialMapBaseFunctionField F)) := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    rw [← polynomialConjugateInvariantAlgebra_baseField_algebraMap D x,
      ← polynomialConjugateInvariantAlgebra_baseField_algebraMap D y, h]
  letI : FaithfulSMul (polynomialConjugateInvariantAlgebra D) (PolynomialMapBaseFunctionField F) :=
    (faithfulSMul_iff_algebraMap_injective (polynomialConjugateInvariantAlgebra D)
      (PolynomialMapBaseFunctionField F)).mpr hinj
  refine IsFractionRing.of_field (polynomialConjugateInvariantAlgebra D)
    (PolynomialMapBaseFunctionField F) fun z => ?_
  obtain ⟨a, b, _hb, hab⟩ := IsFractionRing.div_surjective (A := PolynomialImageAlgebra F) z
  refine ⟨algebraMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) a,
    algebraMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) b, ?_⟩
  simpa only [← IsScalarTower.algebraMap_apply (PolynomialImageAlgebra F)
    (polynomialConjugateInvariantAlgebra D) (PolynomialMapBaseFunctionField F)] using hab.symm

end

end CollisionIdeals
