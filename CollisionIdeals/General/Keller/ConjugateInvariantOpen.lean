import CollisionIdeals.General.Galois.ConjugateInvariantField
import CollisionIdeals.General.Galois.ConjugateInvariantFiniteType
import CollisionIdeals.General.Keller.ConjugateUnramified
import CollisionIdeals.General.Normalization.QuasiFiniteDescent
import CollisionIdeals.General.Normalization.BirationalOpen
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# The actual fixed algebra defines a target open

Keller unramifiedness makes the all-conjugate algebra quasi-finite over the
coordinate-image algebra. Quasi-finiteness descends through the integral
inclusion of its fixed algebra, whose finite type follows from Artin--Tate.
Under separability its fraction field is the target function field, so
Zariski's main theorem identifies its spectrum with an open in the normal
target.

This constructs the open from the existing fixed algebra, without assuming
an open model, flatness of the all-conjugate algebra, or a free-action
quotient. It does not assert that the open is the whole target, or that its
boundary or the collision obstruction vanishes.
-/

set_option autoImplicit false

namespace CollisionIdeals

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

private theorem quasiFinite_of_unramified
    (B E : Type*) [CommRing B] [CommRing E] [Algebra B E]
    [Algebra.Unramified B E] : Algebra.QuasiFinite B E := by
  infer_instance

variable {k : Type u} [Field k] {n : ℕ}
variable {F : PolynomialSelfMap k n}
variable {N : Type u} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

set_option synthInstance.maxHeartbeats 80000 in
/-- The actual all-conjugate algebra is quasi-finite over the
coordinate-image base under the Keller condition. -/
theorem polynomialConjugateAlgebra_quasiFinite_of_isKeller
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    Algebra.QuasiFinite (PolynomialImageAlgebra F)
      (polynomialConjugateAlgebra D) := by
  letI := polynomialConjugateAlgebra_unramified_of_isKeller D hKeller
  exact quasiFinite_of_unramified (PolynomialImageAlgebra F) (polynomialConjugateAlgebra D)

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 80000 in
/-- Quasi-finiteness descends to the existing fixed algebra through its
integral inclusion in the all-conjugate algebra. -/
theorem polynomialConjugateInvariantAlgebra_quasiFinite_of_isKeller
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    Algebra.QuasiFinite (PolynomialImageAlgebra F)
      (polynomialConjugateInvariantAlgebra D) := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI := polynomialConjugateInvariantAlgebra_finiteType D
  letI := polynomialConjugateAlgebra_quasiFinite_of_isKeller D hKeller
  letI := polynomialConjugateAlgebra_isIntegral_over_invariants D
  letI : IsScalarTower (PolynomialImageAlgebra F)
      (polynomialConjugateInvariantAlgebra D) (polynomialConjugateAlgebra D) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact quasiFinite_of_integral_injective_extension (PolynomialImageAlgebra F)
    (polynomialConjugateInvariantAlgebra D) (polynomialConjugateAlgebra D)
    (fun _ _ h => Subtype.ext h)

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 80000 in
/-- The same fixed algebra now defines an actual affine open of the
target. This does not prove surjectivity of the open immersion. -/
theorem polynomialConjugateInvariantAlgebra_isOpenImmersion_of_isKeller
    [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D)))) := by
  letI := D.finiteIntermediate
  letI := polynomialImageAlgebra_isIntegrallyClosed_of_finiteDimensional F
  letI := polynomialConjugateInvariantAlgebra_finiteType D
  letI := polynomialConjugateInvariantAlgebra_quasiFinite_of_isKeller D hKeller
  letI : Algebra (polynomialConjugateInvariantAlgebra D) (PolynomialMapBaseFunctionField F) :=
    polynomialConjugateInvariantAlgebraBaseFieldAlgebra D
  letI : SMul (polynomialConjugateInvariantAlgebra D) (PolynomialMapBaseFunctionField F) :=
    Algebra.toSMul
  letI : SMul (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) :=
    Algebra.toSMul
  letI : IsScalarTower (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D)
      (PolynomialMapBaseFunctionField F) :=
    polynomialConjugateInvariantAlgebra_baseField_imageTower D
  letI := polynomialConjugateInvariantAlgebra_isFractionRing D
  exact isOpenImmersion_specMap_of_quasiFinite_birational (PolynomialImageAlgebra F)
    (polynomialConjugateInvariantAlgebra D) (PolynomialMapBaseFunctionField F)
    (IsFractionRing.injective (polynomialConjugateInvariantAlgebra D)
      (PolynomialMapBaseFunctionField F))

set_option synthInstance.maxHeartbeats 80000 in
/-- The actual target open, using the standard open range of the fixed
algebra's spectrum map. No separate quotient or open-model datum is chosen. -/
def polynomialConjugateInvariantTargetOpen
    [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    (Spec (.of (PolynomialImageAlgebra F))).Opens := by
  letI := polynomialConjugateInvariantAlgebra_isOpenImmersion_of_isKeller D hKeller
  exact (Spec.map (CommRingCat.ofHom
    (algebraMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D)))).opensRange

set_option synthInstance.maxHeartbeats 80000 in
/-- The constructed target open is affine because its source is the
spectrum of the existing fixed algebra. -/
theorem polynomialConjugateInvariantTargetOpen_isAffineOpen
    [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    IsAffineOpen (polynomialConjugateInvariantTargetOpen D hKeller) := by
  letI := polynomialConjugateInvariantAlgebra_isOpenImmersion_of_isKeller D hKeller
  exact isAffineOpen_opensRange (Spec.map (CommRingCat.ofHom
    (algebraMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D))))

end

end CollisionIdeals
