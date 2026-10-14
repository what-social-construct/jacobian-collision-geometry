module

public import CollisionIdeals.General.FiberProduct.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

open scoped TensorProduct

universe uB uA uC uK uD uN

variable
    {B : Type uB}
    {A : Type uA}
    {C : Type uC}
    {K : Type uK}
    {D : Type uD}
    {N : Type uN}
    [CommRing B]
    [CommRing A]
    [CommRing C]
    [CommRing K]
    [CommRing D]
    [CommRing N]

/--
Injectivity descends from a flat generic base change when the source of
the map is flat.

Flatness of `C` makes the canonical map `C → K ⊗[B] C` injective as soon
as `B → K` is injective.  Injectivity of the base-changed map then detects
equality already in `C`.
-/
theorem injective_of_flat_source_of_baseChange
    [Algebra B A]
    [Algebra B C]
    [Algebra B K]
    [Module.Flat B C]
    (μ : C →ₐ[B] A)
    (hBK : Function.Injective (algebraMap B K))
    (hbase :
      Function.Injective
        (Algebra.TensorProduct.map (AlgHom.id K K) μ)) :
    Function.Injective μ := by
  intro x y hxy
  apply
    Algebra.TensorProduct.includeRight_injective
      (A := K) (B := C) hBK
  apply hbase
  simpa only [Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
    using congrArg
      (Algebra.TensorProduct.includeRight :
        A →ₐ[B] K ⊗[B] A) hxy

/--
If `K → L` is surjective, multiplication `L ⊗[K] L → L` is injective.

Indeed every element of the left tensor factor is a scalar, so the
canonical right inclusion is a left inverse to multiplication.
-/
theorem diagonalMultiplication_injective_of_surjective
    {K : Type uK}
    {L : Type uK}
    [CommRing K]
    [CommRing L]
    [Algebra K L]
    (hKL : Function.Surjective (algebraMap K L)) :
    Function.Injective
      (diagonalMultiplication (B := K) (A := L)) := by
  let ι : L →ₐ[K] L ⊗[K] L :=
    Algebra.TensorProduct.includeRight
  have hleft :
      ι.comp (diagonalMultiplication (B := K) (A := L)) =
        AlgHom.id K (L ⊗[K] L) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    obtain ⟨k, rfl⟩ := hKL x
    simp only [AlgHom.coe_comp, Function.comp_apply,
      diagonalMultiplication, Algebra.TensorProduct.lmul'_apply_tmul,
      AlgHom.coe_id, id_eq, ι,
      Algebra.TensorProduct.includeRight_apply]
    rw [← Algebra.smul_def]
    conv_rhs =>
      rw [← mul_one (algebraMap K L k), ← Algebra.smul_def]
    exact
      (TensorProduct.tmul_smul
        (R := K) (R' := K) k (1 : L) y)
  apply Function.LeftInverse.injective (g := ι)
  intro z
  exact AlgHom.congr_fun hleft z

/--
The first projection of a product presentation with a nontrivial second
factor is not injective.

The explicit kernel witness is the inverse image of `(0, 1)`.
-/
theorem fst_comp_productEquiv_not_injective
    [Nontrivial N]
    (e : C ≃+* D × N) :
    ¬ Function.Injective ((RingHom.fst D N).comp e.toRingHom) := by
  intro h
  have hzeroOne : e.symm (0, (1 : N)) = 0 := by
    apply h
    simp
  have h01 : (0 : N) = 1 := by
    have hImage := congrArg (fun x => (e x).2) hzeroOne
    simpa using hImage.symm
  exact zero_ne_one h01

/--
Noninjectivity of a compatible generic product factor descends across a
flat base change.

If `μ : C → A` were injective, flatness of `K` over `B` would make
`K ⊗_B μ` injective.  The equivalence `φ` preserves injectivity, whereas
the compatible product description identifies this map with a first
projection having the nonzero kernel element `(0, 1)`.
-/
theorem not_injective_of_flat_baseChange_product
    [Algebra B A]
    [Algebra B C]
    [Algebra B K]
    [IsScalarTower B K K]
    [Module.Flat B K]
    [Algebra K D]
    [Algebra K N]
    [Nontrivial N]
    (μ : C →ₐ[B] A)
    (φ : K ⊗[B] A ≃ₐ[K] D)
    (e : K ⊗[B] C ≃ₐ[K] D × N)
    (hdiag :
      (AlgHom.fst K D N).comp e.toAlgHom =
        φ.toAlgHom.comp
          (Algebra.TensorProduct.map (AlgHom.id K K) μ)) :
    ¬ Function.Injective μ := by
  intro hμ
  have hbase :
      Function.Injective
        (Algebra.TensorProduct.map (AlgHom.id K K) μ) :=
    Module.Flat.lTensor_preserves_injective_linearMap μ.toLinearMap hμ
  have hfst :
      Function.Injective ((AlgHom.fst K D N).comp e.toAlgHom) := by
    rw [hdiag]
    exact φ.injective.comp hbase
  exact (fst_comp_productEquiv_not_injective e.toRingEquiv) hfst

/--
Ideal-theoretic form of `not_injective_of_flat_baseChange_product`: the
kernel of the original diagonal map is already nonzero before passing to
the generic fiber.
-/
theorem ker_ne_bot_of_flat_baseChange_product
    [Algebra B A]
    [Algebra B C]
    [Algebra B K]
    [IsScalarTower B K K]
    [Module.Flat B K]
    [Algebra K D]
    [Algebra K N]
    [Nontrivial N]
    (μ : C →ₐ[B] A)
    (φ : K ⊗[B] A ≃ₐ[K] D)
    (e : K ⊗[B] C ≃ₐ[K] D × N)
    (hdiag :
      (AlgHom.fst K D N).comp e.toAlgHom =
        φ.toAlgHom.comp
          (Algebra.TensorProduct.map (AlgHom.id K K) μ)) :
    RingHom.ker μ.toRingHom ≠ ⊥ := by
  intro hker
  have hμ : Function.Injective μ :=
    (RingHom.injective_iff_ker_eq_bot μ.toRingHom).2 hker
  exact
    not_injective_of_flat_baseChange_product
      μ φ e hdiag hμ

/--
In a product presentation whose first projection is the diagonal, the
annihilator of the diagonal kernel is exactly the kernel of the residual
projection.

This is the product-ring calculation `ann(0 × N) = D × 0`.  It takes place
entirely after generic base change, so it does not assert that localization
commutes with an affine first-colon ideal.
-/
theorem annihilator_diagonalKernel_eq_residualKernel
    [Algebra K C]
    [Algebra K D]
    [Algebra K N]
    (e : C ≃ₐ[K] D × N) :
    (RingHom.ker
      ((AlgHom.fst K D N).comp e.toAlgHom)).annihilator =
        RingHom.ker
          ((AlgHom.snd K D N).comp e.toAlgHom) := by
  ext x
  constructor
  · intro hx
    rw [RingHom.mem_ker]
    have hy :
        e.symm (0, (1 : N)) ∈
          RingHom.ker
            ((AlgHom.fst K D N).comp e.toAlgHom) := by
      rw [RingHom.mem_ker]
      simp
    have hxy : x * e.symm (0, (1 : N)) = 0 :=
      Submodule.mem_annihilator.mp hx _ hy
    have he := congrArg (fun z : C => (e z).2) hxy
    simpa using he
  · intro hx
    apply Submodule.mem_annihilator.mpr
    intro y hy
    apply e.injective
    have hx' : (e x).2 = 0 := by
      simpa [RingHom.mem_ker] using hx
    have hy' : (e y).1 = 0 := by
      simpa [RingHom.mem_ker] using hy
    ext
    · simp [map_mul, hy']
    · simp [map_mul, hx']

/--
The residual quotient of a generic collision product is its second factor.

If `e : C ≃ D × N` identifies the generic collision diagonal with the first
projection, quotienting `C` by the annihilator of that diagonal kernel gives
`N`.  This is the intrinsic off-diagonal quotient of the generic product.
Identifying it with `K ⊗[B] OffDiagonalRing F` additionally requires the
separate localization--colon comparison and is deliberately not claimed
here.
-/
noncomputable def genericOffDiagonalEquivResidual
    [Algebra K C]
    [Algebra K D]
    [Algebra K N]
    (e : C ≃ₐ[K] D × N) :
    C ⧸ (RingHom.ker
      ((AlgHom.fst K D N).comp e.toAlgHom)).annihilator ≃+* N :=
  (Ideal.quotEquivOfEq
      (annihilator_diagonalKernel_eq_residualKernel e)).trans
    (RingHom.quotientKerEquivOfSurjective (by
      intro n
      exact ⟨e.symm (0, n), by simp⟩))

/-- Although `genericOffDiagonalEquivResidual` is stated as a ring
equivalence to remain universe-polymorphic, it preserves the generic base
field action. -/
@[simp]
theorem genericOffDiagonalEquivResidual_algebraMap
    [Algebra K C]
    [Algebra K D]
    [Algebra K N]
    (e : C ≃ₐ[K] D × N) (k : K) :
    genericOffDiagonalEquivResidual e
        (algebraMap K
          (C ⧸ (RingHom.ker
            ((AlgHom.fst K D N).comp e.toAlgHom)).annihilator) k) =
      algebraMap K N k := by
  change
    ((AlgHom.snd K D N).comp e.toAlgHom) (algebraMap K C k) =
      algebraMap K N k
  simp

end

end CollisionIdeals
