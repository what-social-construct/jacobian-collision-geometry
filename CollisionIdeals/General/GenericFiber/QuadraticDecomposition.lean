import CollisionIdeals.General.GenericFiber.MarkedRootDecomposition

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

open Polynomial
open scoped TensorProduct

universe u v

variable (K : Type u) (L : Type v)
variable [Field K] [Field L] [Algebra K L]

/--
For a degree-two power-basis extension, the residual factor left after
removing the marked root is canonically an `L`-algebra copy of `L`.
-/
private def quadraticResidualEquiv
    (pb : PowerBasis K L)
    (hdegree : pb.dim = 2) :
    AdjoinRoot (minpolyDiv K pb.gen) ≃ₐ[L] L := by
  let r : L := -(minpolyDiv K pb.gen).coeff 0
  have hqdegree : (minpolyDiv K pb.gen).natDegree = 1 := by
    have h := natDegree_minpolyDiv_succ pb.isIntegral_gen
    rw [pb.natDegree_minpoly, hdegree] at h
    omega
  have hq : minpolyDiv K pb.gen = X - C r := by
    calc
      minpolyDiv K pb.gen = X + C ((minpolyDiv K pb.gen).coeff 0) :=
        (minpolyDiv_monic pb.isIntegral_gen).eq_X_add_C hqdegree
      _ = X - C r := by simp [r]
  exact
    (Ideal.quotientEquivAlgOfEq L (by rw [hq])).trans
      (Polynomial.quotientSpanXSubCAlgEquiv r)

/--
A separable quadratic extension has two generic collision sheets: its
self-tensor product is the product of the marked diagonal copy of `L` and
one residual copy of `L`.
-/
def quadraticTensorDecomposition
    [Algebra.IsSeparable K L]
    (pb : PowerBasis K L)
    (hdegree : pb.dim = 2) :
    L ⊗[K] L ≃ₐ[L] L × L :=
  (primitiveTensorDecomposition K L pb).trans
    (AlgEquiv.prodCongr
      (AlgEquiv.refl : L ≃ₐ[L] L)
      (quadraticResidualEquiv K L pb hdegree))

/--
The first projection of the quadratic tensor decomposition is exactly
tensor multiplication, hence the marked generic diagonal.
-/
theorem fst_quadraticTensorDecomposition
    [Algebra.IsSeparable K L]
    (pb : PowerBasis K L)
    (hdegree : pb.dim = 2) :
    (AlgHom.fst L L L).comp
        (quadraticTensorDecomposition K L pb hdegree).toAlgHom =
      primitiveTensorDiagonal K L := by
  rw [← fst_primitiveTensorDecomposition K L pb]
  ext x
  rfl

end

end CollisionIdeals
