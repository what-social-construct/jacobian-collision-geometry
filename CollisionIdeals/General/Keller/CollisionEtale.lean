import CollisionIdeals.General.GenericFiber.FunctionField
import CollisionIdeals.General.Keller.Etale

/-!
# Étaleness of the actual Keller collision ring

The collision ring is the self-tensor square of the polynomial source over
the coordinate-image algebra.  Keller étaleness survives this base change,
and the tensor-product description transports it to the actual collision
quotient.  No finiteness of the collision projection is asserted here.
-/

set_option autoImplicit false

namespace CollisionIdeals

open scoped TensorProduct

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-- For a Keller map, the first projection of the actual collision scheme
is étale.  The algebra structure is induced by `collisionLeft F`. -/
theorem polynomialCollisionRing_etale_left_of_isKeller
    (F : PolynomialSelfMap k n) (hKeller : IsKeller F) :
    letI : Algebra (SourceRing k (Fin n)) (CollisionRing F) :=
      (collisionLeft F).toRingHom.toAlgebra
    Algebra.Etale (SourceRing k (Fin n)) (CollisionRing F) := by
  let B := polynomialMapImageAlgebra F
  let A := SourceRing k (Fin n)
  let C := CollisionRing F
  letI : Algebra B C := polynomialImageCollisionAlgebra F
  letI : Algebra A C := (collisionLeft F).toRingHom.toAlgebra
  letI : Algebra.Etale B A := polynomialSource_etale_of_isKeller F hKeller
  haveI : Algebra.Etale A (A ⊗[B] A) := Algebra.Etale.baseChange B A A
  let e : C ≃ₐ[A] A ⊗[B] A :=
    { (collisionImageTensorEquiv F).toRingEquiv with
      commutes' := fun a => by
        change collisionImageTensorEquiv F (collisionLeft F a) =
          a ⊗ₜ[B] (1 : A)
        exact collisionImageTensorEquiv_collisionLeft F a }
  exact Algebra.Etale.of_equiv e.symm

end

end CollisionIdeals
