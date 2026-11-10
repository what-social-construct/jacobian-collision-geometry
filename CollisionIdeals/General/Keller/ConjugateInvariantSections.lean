import CollisionIdeals.General.Keller.ConjugateInvariantOpen
import CollisionIdeals.General.Keller.ConjugateInvariantCriterion
import CollisionIdeals.General.Normalization.AffineOpenSections
import CollisionIdeals.General.Normalization.FractionalQuotient

/-!
# Sections of the actual invariant target open

The existing fixed algebra is identified over the original coordinate-image
base with the sections on its actual target open. The identification
descends to the standard module quotients by the base image. The fixed
algebra modulo the base is torsion, by its existing embedding in the target
function field; the denominator can depend on the class.
The module is zero exactly when the actual target boundary is empty.

These statements do not identify the quotient with Mathlib's filtered-Ext
local cohomology, supply compatible derivations, or prove a uniform
annihilator, finiteness, or boundary vanishing.
-/

set_option autoImplicit false

namespace CollisionIdeals

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ}
variable {F : PolynomialSelfMap k n} {N : Type u} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]
variable [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]

-- Use Mathlib's original section algebra, with the base written unbundled.
local instance (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    Algebra (PolynomialImageAlgebra F)
      Γ(Spec (.of (PolynomialImageAlgebra F)),
        polynomialConjugateInvariantTargetOpen D hKeller) :=
  inferInstanceAs (Algebra (PolynomialImageAlgebra F)
    ((Spec.structureSheaf (PolynomialImageAlgebra F)).val.obj
      (Opposite.op (polynomialConjugateInvariantTargetOpen D hKeller))))

set_option synthInstance.maxHeartbeats 80000 in
/-- The actual fixed algebra is the section algebra of the already
constructed target open, compatibly with restriction from the base. -/
def polynomialConjugateInvariantSectionsEquiv
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    polynomialConjugateInvariantAlgebra D ≃ₐ[PolynomialImageAlgebra F]
      Γ(Spec (.of (PolynomialImageAlgebra F)),
        polynomialConjugateInvariantTargetOpen D hKeller) := by
  letI := polynomialConjugateInvariantAlgebra_isOpenImmersion_of_isKeller D hKeller
  exact affineOpenSectionsAlgEquiv (PolynomialImageAlgebra F)
    (polynomialConjugateInvariantAlgebra D)

set_option synthInstance.maxHeartbeats 80000 in
/-- Modulo the original base, the fixed algebra and the actual target-open
sections give the same module. These are not ideal quotients. -/
def polynomialConjugateInvariantSectionsQuotientEquiv
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    (polynomialConjugateInvariantAlgebra D ⧸ LinearMap.range
      (Algebra.linearMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D)))
      ≃ₗ[PolynomialImageAlgebra F]
    Γ(Spec (.of (PolynomialImageAlgebra F)),
      polynomialConjugateInvariantTargetOpen D hKeller) ⧸
      LinearMap.range (Algebra.linearMap (PolynomialImageAlgebra F)
        Γ(Spec (.of (PolynomialImageAlgebra F)),
          polynomialConjugateInvariantTargetOpen D hKeller)) := by
  letI := polynomialConjugateInvariantAlgebra_isOpenImmersion_of_isKeller D hKeller
  exact affineOpenSectionsQuotientEquiv (PolynomialImageAlgebra F)
    (polynomialConjugateInvariantAlgebra D)

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 80000 in
/-- The actual fixed algebra modulo the base is torsion. This needs no
Keller condition: its target-function-field embedding clears each class's
denominator, not all denominators uniformly. -/
theorem polynomialConjugateInvariantAlgebra_quotient_isTorsion
    (D : PolynomialNormalClosureData F N) :
    Module.IsTorsion (PolynomialImageAlgebra F)
      (polynomialConjugateInvariantAlgebra D ⧸ LinearMap.range
        (Algebra.linearMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D))) := by
  let f : polynomialConjugateInvariantAlgebra D →ₐ[PolynomialImageAlgebra F]
      PolynomialMapBaseFunctionField F :=
    (polynomialConjugateInvariantBaseAlgebra D).val.comp
      (polynomialConjugateInvariantBaseEquiv D).symm.toAlgHom
  apply isTorsion_quotient_range_algebraLinearMap f
  intro x y h
  apply (polynomialConjugateInvariantBaseEquiv D).symm.injective
  exact Subtype.ext h

set_option synthInstance.maxHeartbeats 80000 in
/-- Vanishing of this same module quotient detects the actual empty target
boundary, using the previously proved base-map surjectivity criterion. -/
theorem polynomialConjugateInvariantAlgebra_quotient_subsingleton_iff_boundary_eq_top
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    Subsingleton (polynomialConjugateInvariantAlgebra D ⧸ LinearMap.range
      (Algebra.linearMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D))) ↔
      polynomialConjugateInvariantBoundaryIdeal D hKeller = ⊤ := by
  rw [Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top]
  exact polynomialConjugateInvariantAlgebra_surjective_iff_boundary_eq_top D hKeller

end

end CollisionIdeals
