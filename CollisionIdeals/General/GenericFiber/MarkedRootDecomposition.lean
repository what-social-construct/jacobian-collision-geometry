module

public import Mathlib.FieldTheory.Minpoly.MinpolyDiv
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Basis

@[expose] public section

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

open Polynomial
open scoped TensorProduct

universe u v

variable (K : Type u) (L : Type v)
variable [Field K] [Field L] [Algebra K L]

/-- Multiplication on `L ⊗[K] L`, regarded as an `L`-algebra map via the
left tensor factor. -/
def primitiveTensorDiagonal :
    L ⊗[K] L →ₐ[L] L where
  __ := Algebra.TensorProduct.lmul' K
  commutes' x := by simp

/--
The power basis obtained from `pb` by base change along `K → L`.

Its generator is the copy `1 ⊗ pb.gen` coming from the right tensor
factor.
-/
def primitiveTensorPowerBasis (pb : PowerBasis K L) :
    PowerBasis L (L ⊗[K] L) where
  gen := 1 ⊗ₜ[K] pb.gen
  dim := pb.dim
  basis := pb.basis.baseChange L
  basis_eq_pow i := by
    rw [Module.Basis.baseChange_apply, pb.basis_eq_pow]
    simp

@[simp]
theorem primitiveTensorPowerBasis_gen (pb : PowerBasis K L) :
    (primitiveTensorPowerBasis K L pb).gen = 1 ⊗ₜ[K] pb.gen :=
  rfl

/--
The minimal polynomial of the generator of the base-changed power basis is
the scalar extension of the original minimal polynomial.
-/
theorem minpoly_primitiveTensorPowerBasis (pb : PowerBasis K L) :
    minpoly L (primitiveTensorPowerBasis K L pb).gen =
      (minpoly K pb.gen).map (algebraMap K L) := by
  let pbT := primitiveTensorPowerBasis K L pb
  have hroot :
      Polynomial.aeval pbT.gen ((minpoly K pb.gen).map (algebraMap K L)) = 0 := by
    have hmaps :
        (algebraMap L (L ⊗[K] L)).comp (algebraMap K L) =
          (Algebra.TensorProduct.includeRight : L →ₐ[K] L ⊗[K] L).toRingHom.comp
            (algebraMap K L) := by
      ext k
      simp
    have hformula :=
      Polynomial.map_aeval_eq_aeval_map hmaps (minpoly K pb.gen) pb.gen
    change
      Polynomial.aeval
          ((Algebra.TensorProduct.includeRight : L →ₐ[K] L ⊗[K] L) pb.gen)
          ((minpoly K pb.gen).map (algebraMap K L)) = 0
    calc
      _ =
          (Algebra.TensorProduct.includeRight : L →ₐ[K] L ⊗[K] L)
            (Polynomial.aeval pb.gen (minpoly K pb.gen)) := by
              simpa using hformula.symm
      _ = 0 := by rw [minpoly.aeval, map_zero]
  apply Eq.symm
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic pbT.isIntegral_gen)
      ((minpoly.monic pb.isIntegral_gen).map (algebraMap K L))
      (minpoly.dvd L pbT.gen hroot)
  rw [Polynomial.natDegree_map, pb.natDegree_minpoly, pbT.natDegree_minpoly]
  rfl

/--
The self-tensor product of a power-basis extension is the quotient by the
base-changed minimal polynomial.
-/
def primitiveTensorEquivAdjoinRoot (pb : PowerBasis K L) :
    L ⊗[K] L ≃ₐ[L]
      AdjoinRoot ((minpoly K pb.gen).map (algebraMap K L)) := by
  let fL := (minpoly K pb.gen).map (algebraMap K L)
  let pbT := primitiveTensorPowerBasis K L pb
  refine (AdjoinRoot.equiv' fL pbT ?_ ?_).symm
  · have hm := minpoly_primitiveTensorPowerBasis K L pb
    rw [hm]
    change Polynomial.aeval (AdjoinRoot.root fL) fL = 0
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  · dsimp [fL]
    rw [← minpoly_primitiveTensorPowerBasis K L pb]
    exact minpoly.aeval L pbT.gen

@[simp]
theorem primitiveTensorEquivAdjoinRoot_gen (pb : PowerBasis K L) :
    primitiveTensorEquivAdjoinRoot K L pb
        (primitiveTensorPowerBasis K L pb).gen =
      AdjoinRoot.root ((minpoly K pb.gen).map (algebraMap K L)) := by
  let fL : L[X] := (minpoly K pb.gen).map (algebraMap K L)
  let pbT := primitiveTensorPowerBasis K L pb
  have hy : Polynomial.aeval (AdjoinRoot.root fL) (minpoly L pbT.gen) = 0 := by
    rw [minpoly_primitiveTensorPowerBasis K L pb]
    change Polynomial.aeval (AdjoinRoot.root fL) fL = 0
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  change pbT.lift (AdjoinRoot.root fL) hy pbT.gen = AdjoinRoot.root fL
  exact PowerBasis.lift_gen pbT (AdjoinRoot.root fL) hy

/--
For a separable power-basis extension, the linear factor belonging to the
chosen generator is coprime to the remaining conjugate polynomial.
-/
theorem isCoprime_span_X_sub_C_minpolyDiv
    [Algebra.IsSeparable K L] (pb : PowerBasis K L) :
    IsCoprime
      (Ideal.span ({X - C pb.gen} : Set L[X]))
      (Ideal.span ({minpolyDiv K pb.gen} : Set L[X])) := by
  rw [Ideal.isCoprime_span_singleton_iff]
  let fL := (minpoly K pb.gen).map (algebraMap K L)
  have hderivK :
      Polynomial.aeval pb.gen (derivative (minpoly K pb.gen)) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable K pb.gen).aeval_derivative_ne_zero
      (minpoly.aeval K pb.gen)
  have hderivL : (derivative fL).eval pb.gen ≠ 0 := by
    dsimp [fL]
    rw [Polynomial.derivative_map, Polynomial.eval_map]
    simpa [Polynomial.aeval_def] using hderivK
  have hcop :=
    Polynomial.isCoprime_of_is_root_of_eval_derivative_ne_zero fL pb.gen hderivL
  exact hcop

/--
CRT decomposes the quotient by the base-changed minimal polynomial into
the chosen-root factor and the remaining-conjugates factor.
-/
def adjoinRootMinpolyEquivProd
    [Algebra.IsSeparable K L] (pb : PowerBasis K L) :
    AdjoinRoot ((minpoly K pb.gen).map (algebraMap K L)) ≃ₐ[L]
      L × AdjoinRoot (minpolyDiv K pb.gen) := by
  let fL : L[X] := (minpoly K pb.gen).map (algebraMap K L)
  let q : L[X] := minpolyDiv K pb.gen
  let I : Ideal L[X] := Ideal.span ({X - C pb.gen} : Set L[X])
  let J : Ideal L[X] := Ideal.span ({q} : Set L[X])
  have hcop : IsCoprime I J := by
    simpa [I, J, q] using isCoprime_span_X_sub_C_minpolyDiv K L pb
  have hspan : Ideal.span ({fL} : Set L[X]) = I * J := by
    dsimp [fL, I, J, q]
    rw [← minpolyDiv_spec K pb.gen]
    rw [Ideal.span_singleton_mul_span_singleton]
    congr 2
    exact mul_comm _ _
  let e₀ :
      AdjoinRoot fL ≃ₐ[L] L[X] ⧸ I * J :=
    Ideal.quotientEquivAlgOfEq L hspan
  let eCRT₀ :
      (L[X] ⧸ I * J) ≃+* (L[X] ⧸ I) × (L[X] ⧸ J) :=
    Ideal.quotientMulEquivQuotientProd I J hcop
  let eCRT :
      (L[X] ⧸ I * J) ≃ₐ[L] (L[X] ⧸ I) × (L[X] ⧸ J) :=
    AlgEquiv.ofRingEquiv (f := eCRT₀) (by
      intro x
      rfl)
  let eJ :
      (L[X] ⧸ J) ≃ₐ[L] AdjoinRoot (minpolyDiv K pb.gen) :=
    Ideal.quotientEquivAlgOfEq L (by simp [J, q])
  exact e₀.trans <| eCRT.trans <|
    AlgEquiv.prodCongr
      (Polynomial.quotientSpanXSubCAlgEquiv pb.gen)
      eJ

@[simp]
theorem fst_adjoinRootMinpolyEquivProd_root
    [Algebra.IsSeparable K L] (pb : PowerBasis K L) :
    (adjoinRootMinpolyEquivProd K L pb
      (AdjoinRoot.root ((minpoly K pb.gen).map (algebraMap K L)))).1 =
        pb.gen := by
  let fL : L[X] := (minpoly K pb.gen).map (algebraMap K L)
  let q : L[X] := minpolyDiv K pb.gen
  let I : Ideal L[X] := Ideal.span ({X - C pb.gen} : Set L[X])
  let J : Ideal L[X] := Ideal.span ({q} : Set L[X])
  have hcop : IsCoprime I J := by
    simpa [I, J, q] using isCoprime_span_X_sub_C_minpolyDiv K L pb
  have hspan : Ideal.span ({fL} : Set L[X]) = I * J := by
    dsimp [fL, I, J, q]
    rw [← minpolyDiv_spec K pb.gen]
    rw [Ideal.span_singleton_mul_span_singleton]
    congr 2
    exact mul_comm _ _
  rw [← AdjoinRoot.mk_X]
  change
    (Polynomial.quotientSpanXSubCAlgEquiv pb.gen)
      ((Ideal.quotientMulEquivQuotientProd I J hcop
        ((Ideal.quotientEquivAlgOfEq L hspan)
          (Ideal.Quotient.mk (Ideal.span ({fL} : Set L[X])) X))).1) =
      pb.gen
  rw [Ideal.quotientEquivAlgOfEq_mk]
  rw [Ideal.quotientMulEquivQuotientProd_fst]
  rw [Ideal.Quotient.factor_mk]
  rw [Polynomial.quotientSpanXSubCAlgEquiv_mk]
  simp

/--
A separable simple extension splits its self-tensor product into the
diagonal factor and the quotient by the remaining conjugate polynomial.
-/
def primitiveTensorDecomposition
    [Algebra.IsSeparable K L] (pb : PowerBasis K L) :
    L ⊗[K] L ≃ₐ[L] L × AdjoinRoot (minpolyDiv K pb.gen) :=
  (primitiveTensorEquivAdjoinRoot K L pb).trans
    (adjoinRootMinpolyEquivProd K L pb)

/--
The first CRT factor in `primitiveTensorDecomposition` is exactly the
diagonal multiplication map.
-/
theorem fst_primitiveTensorDecomposition
    [Algebra.IsSeparable K L] (pb : PowerBasis K L) :
    (AlgHom.fst L L (AdjoinRoot (minpolyDiv K pb.gen))).comp
        (primitiveTensorDecomposition K L pb).toAlgHom =
      primitiveTensorDiagonal K L := by
  let pbT := primitiveTensorPowerBasis K L pb
  apply pbT.algHom_ext
  change
    (primitiveTensorDecomposition K L pb pbT.gen).1 =
      primitiveTensorDiagonal K L pbT.gen
  calc
    _ =
        (adjoinRootMinpolyEquivProd K L pb
          (AdjoinRoot.root ((minpoly K pb.gen).map (algebraMap K L)))).1 := by
            rw [primitiveTensorDecomposition]
            change
              (adjoinRootMinpolyEquivProd K L pb
                (primitiveTensorEquivAdjoinRoot K L pb
                  (primitiveTensorPowerBasis K L pb).gen)).1 =
                _
            rw [primitiveTensorEquivAdjoinRoot_gen]
    _ = pb.gen := fst_adjoinRootMinpolyEquivProd_root K L pb
    _ = primitiveTensorDiagonal K L pbT.gen := by
      simp [pbT, primitiveTensorDiagonal]

@[simp]
theorem fst_primitiveTensorDecomposition_apply
    [Algebra.IsSeparable K L] (pb : PowerBasis K L)
    (x : L ⊗[K] L) :
    (primitiveTensorDecomposition K L pb x).1 =
      primitiveTensorDiagonal K L x :=
  AlgHom.congr_fun (fst_primitiveTensorDecomposition K L pb) x

end

end CollisionIdeals
