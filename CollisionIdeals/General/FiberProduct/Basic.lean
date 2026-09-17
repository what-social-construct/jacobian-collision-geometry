import Mathlib.RingTheory.TensorProduct.Maps

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

open Algebra
open scoped TensorProduct

universe u

variable {B A : Type u}
variable [CommRing B] [CommRing A] [Algebra B A]

/-- The coordinate algebra of the affine self-fiber product. -/
abbrev SelfFiberProductAlgebra :=
  A ⊗[B] A

/-- Multiplication is dual to the diagonal map into the self-fiber product. -/
def diagonalMultiplication :
    SelfFiberProductAlgebra (B := B) (A := A) →ₐ[B] A :=
  TensorProduct.lmul' B

end

end CollisionIdeals
