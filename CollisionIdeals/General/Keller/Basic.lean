module

public import CollisionIdeals.General.Collision.Diagonal
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

set_option autoImplicit false

namespace CollisionIdeals

universe u

open MvPolynomial

noncomputable section

/-- A polynomial self-map of affine `n`-space over `R`. -/
abbrev PolynomialSelfMap
    (R : Type u) [CommRing R] (n : ℕ) :=
  Fin n → SourceRing R (Fin n)

/-- The Jacobian matrix of a polynomial self-map. -/
def jacobianMatrix
    {R : Type u} [CommRing R] {n : ℕ}
    (F : PolynomialSelfMap R n) :
    Matrix (Fin n) (Fin n) (SourceRing R (Fin n)) :=
  fun i j ↦ pderiv j (F i)

/-- The Jacobian determinant of a polynomial self-map. -/
def jacobianDet
    {R : Type u} [CommRing R] {n : ℕ}
    (F : PolynomialSelfMap R n) :
    SourceRing R (Fin n) :=
  Matrix.det (jacobianMatrix F)

/-- The generic determinant specializes to the usual `2 × 2` formula. -/
theorem jacobianDet_fin_two
    {R : Type u} [CommRing R]
    (F : PolynomialSelfMap R 2) :
    jacobianDet F =
      pderiv 0 (F 0) * pderiv 1 (F 1) -
        pderiv 1 (F 0) * pderiv 0 (F 1) := by
  rw [jacobianDet, Matrix.det_fin_two]
  rfl

/--
A Keller map over a field has constant nonzero Jacobian determinant.

The dimension is arbitrary; the planar and complex-three predicates are
specializations of this definition.
-/
def IsKeller
    {K : Type u} [Field K] {n : ℕ}
    (F : PolynomialSelfMap K n) : Prop :=
  ∃ c : K, c ≠ 0 ∧ jacobianDet F = C c

end

end CollisionIdeals
