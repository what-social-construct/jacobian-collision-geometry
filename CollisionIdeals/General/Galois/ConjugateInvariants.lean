import CollisionIdeals.General.Galois.ConjugateFractionField
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Invariants of the all-conjugate polynomial algebra

The normal-closure Galois action restricts faithfully to the existing
all-conjugate algebra. Its fixed algebra is Mathlib's
`FixedPoints.subalgebra`, and the all-conjugate algebra is module-finite
over it. Faithfulness is not scheme-theoretic freeness of the action.

These are ordinary finite-group invariant-ring statements. They require
neither a Keller hypothesis nor an étale quotient construction, and they
do not imply finiteness over the coordinate-image algebra. When the normal
closure is separable, fixed elements are precisely the elements lying in
the embedded base function field.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ}
variable {F : PolynomialSelfMap k n}
variable {N : Type u} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

@[reducible] local instance conjugateInvariantsBaseAlgebra :
    Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

/-- Galois stability of the existing algebra, packaged for Mathlib's
restriction-of-action API. -/
instance polynomialConjugateAlgebra_invariantSubring
    (D : PolynomialNormalClosureData F N) :
    IsInvariantSubring D.galoisGroup (polynomialConjugateAlgebra D).toSubring where
  smul_mem g _ hz := polynomialConjugateAlgebra_galois_mem D g hz

/-- The normal-closure Galois action restricted to the all-conjugate algebra. -/
instance polynomialConjugateAlgebra_galoisAction
    (D : PolynomialNormalClosureData F N) :
    MulSemiringAction D.galoisGroup (polynomialConjugateAlgebra D) :=
  inferInstanceAs
    (MulSemiringAction D.galoisGroup (polynomialConjugateAlgebra D).toSubring)

@[simp]
theorem polynomialConjugateAlgebra_coe_galois_smul
    (D : PolynomialNormalClosureData F N) (g : D.galoisGroup)
    (z : polynomialConjugateAlgebra D) :
    ((g • z : polynomialConjugateAlgebra D) : N) = g (z : N) := rfl

/-- An automorphism of the normal closure is determined by its restriction
to the all-conjugate algebra. This asserts faithfulness, not freeness on
the spectrum. -/
instance polynomialConjugateAlgebra_faithfulGaloisAction
    (D : PolynomialNormalClosureData F N) :
    FaithfulSMul D.galoisGroup (polynomialConjugateAlgebra D) where
  eq_of_smul_eq_smul {g h} hgh := by
    letI := polynomialConjugateAlgebra_isFractionRing D
    have heq : g.toRingHom = h.toRingHom := by
      apply IsFractionRing.ringHom_ext (A := polynomialConjugateAlgebra D)
      intro z
      exact congrArg Subtype.val (hgh z)
    apply AlgEquiv.ext
    intro z
    exact RingHom.congr_fun heq z

/-- The restricted action fixes the coordinate-image scalars. -/
instance polynomialConjugateAlgebra_galoisSMulCommClass
    (D : PolynomialNormalClosureData F N) :
    SMulCommClass D.galoisGroup (PolynomialImageAlgebra F)
      (polynomialConjugateAlgebra D) where
  smul_comm g b z := by
    apply Subtype.ext
    change g (algebraMap (PolynomialImageAlgebra F) N b * (z : N)) =
      algebraMap (PolynomialImageAlgebra F) N b * g (z : N)
    rw [map_mul]
    change g (algebraMap (PolynomialMapBaseFunctionField F) N
      (algebraMap (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) b)) *
        g (z : N) = _
    rw [g.commutes]
    rfl

/-- The fixed algebra of the actual all-conjugate action; no separate
quotient-ring construction is introduced. -/
def polynomialConjugateInvariantAlgebra
    (D : PolynomialNormalClosureData F N) :
    Subalgebra (PolynomialImageAlgebra F) (polynomialConjugateAlgebra D) :=
  FixedPoints.subalgebra (PolynomialImageAlgebra F)
    (polynomialConjugateAlgebra D) D.galoisGroup

/-- The inherited commutative-ring structure, made explicit so clients do
not need to reconstruct the nested subalgebra's base parameters. -/
instance polynomialConjugateInvariantAlgebra_commRing
    (D : PolynomialNormalClosureData F N) :
    CommRing (polynomialConjugateInvariantAlgebra D) :=
  Subalgebra.toCommRing (R := PolynomialImageAlgebra F)
    (A := polynomialConjugateAlgebra D) (polynomialConjugateInvariantAlgebra D)

/-- Fixedness in the subalgebra is the original normal-closure fixedness. -/
theorem polynomialConjugateInvariantAlgebra_mem_iff
    (D : PolynomialNormalClosureData F N) (z : polynomialConjugateAlgebra D) :
    z ∈ polynomialConjugateInvariantAlgebra D ↔
      ∀ g : D.galoisGroup, g (z : N) = (z : N) := by
  change (∀ g : D.galoisGroup, g • z = z) ↔ _
  constructor
  · intro hz g
    exact congrArg Subtype.val (hz g)
  · intro hz g
    exact Subtype.ext (hz g)

/-- Every fixed element is, by construction, in the fixed algebra. -/
instance polynomialConjugateInvariantAlgebra_isInvariant
    (D : PolynomialNormalClosureData F N) :
    Algebra.IsInvariant (polynomialConjugateInvariantAlgebra D)
      (polynomialConjugateAlgebra D) D.galoisGroup where
  isInvariant z hz := ⟨⟨z, hz⟩, rfl⟩

/-- Finite-group invariants make the all-conjugate algebra an integral
extension of its fixed algebra. -/
theorem polynomialConjugateAlgebra_isIntegral_over_invariants
    (D : PolynomialNormalClosureData F N) :
    Algebra.IsIntegral (polynomialConjugateInvariantAlgebra D)
      (polynomialConjugateAlgebra D) := by
  letI : Finite D.galoisGroup := D.finiteGaloisGroup
  exact Algebra.IsInvariant.isIntegral
    (polynomialConjugateInvariantAlgebra D) (polynomialConjugateAlgebra D) D.galoisGroup

/-- The actual all-conjugate algebra is module-finite over its fixed
algebra. This is not finiteness over the coordinate-image algebra. -/
theorem polynomialConjugateAlgebra_finite_over_invariants
    (D : PolynomialNormalClosureData F N) :
    Module.Finite (polynomialConjugateInvariantAlgebra D)
      (polynomialConjugateAlgebra D) := by
  letI := polynomialConjugateAlgebra_isIntegral_over_invariants D
  letI := polynomialConjugateAlgebra_finiteType D
  letI : IsScalarTower (PolynomialImageAlgebra F)
      (polynomialConjugateInvariantAlgebra D) (polynomialConjugateAlgebra D) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra.FiniteType (polynomialConjugateInvariantAlgebra D)
      (polynomialConjugateAlgebra D) :=
    Algebra.FiniteType.of_restrictScalars_finiteType (PolynomialImageAlgebra F)
      (polynomialConjugateInvariantAlgebra D) (polynomialConjugateAlgebra D)
  exact Algebra.IsIntegral.finite (R := polynomialConjugateInvariantAlgebra D)
    (A := polynomialConjugateAlgebra D)

/-- In a separable normal closure, the fixed algebra is exactly the part
of the all-conjugate algebra lying in the embedded base function field. -/
theorem polynomialConjugateInvariantAlgebra_mem_iff_baseField
    [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]
    (D : PolynomialNormalClosureData F N) (z : polynomialConjugateAlgebra D) :
    z ∈ polynomialConjugateInvariantAlgebra D ↔
      (z : N) ∈ Set.range (algebraMap (PolynomialMapBaseFunctionField F) N) := by
  letI : FiniteDimensional (PolynomialMapBaseFunctionField F) N := D.finiteNormal
  letI : Normal (PolynomialMapBaseFunctionField F) N := D.normal
  letI : IsGalois (PolynomialMapBaseFunctionField F) N := IsGalois.mk
  exact (polynomialConjugateInvariantAlgebra_mem_iff D z).trans
    (IsGalois.mem_range_algebraMap_iff_fixed (F := PolynomialMapBaseFunctionField F)
      (E := N) (z : N)).symm

end

end CollisionIdeals
