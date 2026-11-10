import CollisionIdeals.Planar.Research.ConjugateFixedLocus
import CollisionIdeals.Planar.Research.GaloisTensorEquiv
import CollisionIdeals.General.Keller.ConjugateUnramified
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The finite étale cover over the actual invariant algebra

The base here is the existing fixed algebra of the all-conjugate algebra,
not the whole coordinate-image algebra. The fixed-locus certificate supplies
the graph separation used to construct a finite trace-dual frame.

These comparisons do not fill the target open or prove obstruction vanishing.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar.Research

open scoped TensorProduct

noncomputable section

variable {F : PlanarPolynomialMap} {N : Type} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

@[reducible] local instance conjugateCoverBaseAlgebra :
    Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

@[reducible] local instance conjugateCoverImageAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateAlgebra D)

@[reducible] local instance conjugateCoverInvariantBaseAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateInvariantAlgebra D)

local instance conjugateCoverImageSMul (D : PolynomialNormalClosureData F N) :
    SMul (PolynomialImageAlgebra F) (polynomialConjugateAlgebra D) :=
  Algebra.toSMul

local instance conjugateCoverInvariantBaseSMul (D : PolynomialNormalClosureData F N) :
    SMul (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) :=
  Algebra.toSMul

/-- The actual invariant algebra acts by scalars fixed by the Galois group. -/
instance conjugateInvariantGaloisSMulCommClass
    (D : PolynomialNormalClosureData F N) :
    SMulCommClass D.galoisGroup (polynomialConjugateInvariantAlgebra D)
      (polynomialConjugateAlgebra D) where
  smul_comm σ r z := by
    change σ • ((r : polynomialConjugateAlgebra D) * z) =
      (r : polynomialConjugateAlgebra D) * (σ • z)
    rw [smul_mul', r.property σ]

local instance conjugateCoverImageInvariantTower
    (D : PolynomialNormalClosureData F N) :
    IsScalarTower (PolynomialImageAlgebra F)
      (polynomialConjugateInvariantAlgebra D) (polynomialConjugateAlgebra D) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Keller formal unramifiedness passes from the coordinate-image base
to the actual invariant algebra by restriction of scalars. -/
theorem conjugateAlgebra_formallyUnramified_over_invariants
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F) :
    Algebra.FormallyUnramified (polynomialConjugateInvariantAlgebra D)
      (polynomialConjugateAlgebra D) := by
  letI := polynomialConjugateAlgebra_formallyUnramified_of_isKeller D hKeller
  exact Algebra.FormallyUnramified.of_restrictScalars (PolynomialImageAlgebra F)
    (polynomialConjugateInvariantAlgebra D) (polynomialConjugateAlgebra D)

/-- The canonical graph map for the existing action on the actual
all-conjugate algebra, over its existing invariant algebra. -/
def conjugateGaloisMap (D : PolynomialNormalClosureData F N) :
    polynomialConjugateAlgebra D ⊗[polynomialConjugateInvariantAlgebra D]
      polynomialConjugateAlgebra D →ₐ[polynomialConjugateInvariantAlgebra D]
      (D.galoisGroup → polynomialConjugateAlgebra D) :=
  FiniteGroupCover.canonicalMap (polynomialConjugateInvariantAlgebra D)
    (polynomialConjugateAlgebra D) D.galoisGroup

@[simp]
theorem conjugateGaloisMap_tmul (D : PolynomialNormalClosureData F N)
    (a b : polynomialConjugateAlgebra D) (g : D.galoisGroup) :
    conjugateGaloisMap D (a ⊗ₜ[polynomialConjugateInvariantAlgebra D] b) g =
      a * (g • b) := rfl

/-- The evaluated-projector fixed-locus certificate separates all graphs
already in the actual all-conjugate algebra. -/
theorem conjugateGaloisMap_surjective
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F) :
    Function.Surjective (conjugateGaloisMap D) := by
  letI : Finite D.galoisGroup := D.finiteGaloisGroup
  exact FiniteGroupCover.canonicalMap_surjective
    (polynomialConjugateInvariantAlgebra D) (polynomialConjugateAlgebra D)
    D.galoisGroup (span_galoisDifferences_eq_top D hKeller)

/-- A finite trace-dual frame makes the actual all-conjugate algebra
projective over its invariant algebra. No freeness hypothesis is supplied. -/
theorem conjugateAlgebra_projective_over_invariants
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F) :
    Module.Projective (polynomialConjugateInvariantAlgebra D)
      (polynomialConjugateAlgebra D) := by
  classical
  letI : Finite D.galoisGroup := D.finiteGaloisGroup
  letI := Fintype.ofFinite D.galoisGroup
  exact FiniteGroupCover.projective_of_canonicalMap_surjective
    (polynomialConjugateInvariantAlgebra D) (polynomialConjugateAlgebra D)
    D.galoisGroup (fun _ _ h => Subtype.ext h)
    (conjugateGaloisMap_surjective D hKeller)

/-- The actual all-conjugate algebra is étale over its fixed algebra,
not asserted finite over the original coordinate-image algebra. -/
theorem conjugateAlgebra_etale_over_invariants
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F) :
    Algebra.Etale (polynomialConjugateInvariantAlgebra D)
      (polynomialConjugateAlgebra D) := by
  letI := polynomialConjugateAlgebra_finite_over_invariants D
  letI := conjugateAlgebra_projective_over_invariants D hKeller
  letI := Module.finitePresentation_of_projective
    (polynomialConjugateInvariantAlgebra D) (polynomialConjugateAlgebra D)
  letI := conjugateAlgebra_formallyUnramified_over_invariants D hKeller
  exact Algebra.Etale.of_formallyUnramified_of_flat

/-- Integral injectivity and the proved flatness give faithful flatness
over the actual invariant algebra. This does not fill the target open. -/
theorem conjugateAlgebra_faithfullyFlat_over_invariants
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F) :
    Module.FaithfullyFlat (polynomialConjugateInvariantAlgebra D)
      (polynomialConjugateAlgebra D) := by
  letI := conjugateAlgebra_projective_over_invariants D hKeller
  letI := polynomialConjugateAlgebra_isIntegral_over_invariants D
  have hIntegral :
      (algebraMap (polynomialConjugateInvariantAlgebra D)
        (polynomialConjugateAlgebra D)).IsIntegral :=
    algebraMap_isIntegral_iff.mpr inferInstance
  exact Module.FaithfullyFlat.of_comap_surjective
    (hIntegral.comap_surjective (fun _ _ h => Subtype.ext h))

/-- The canonical action-graph map is an algebra equivalence: the affine
algebraic torsor comparison, over the same invariant algebra. -/
def conjugateGaloisEquiv
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F) :
    polynomialConjugateAlgebra D ⊗[polynomialConjugateInvariantAlgebra D]
      polynomialConjugateAlgebra D ≃ₐ[polynomialConjugateInvariantAlgebra D]
      (D.galoisGroup → polynomialConjugateAlgebra D) := by
  classical
  letI : Finite D.galoisGroup := D.finiteGaloisGroup
  letI := Fintype.ofFinite D.galoisGroup
  exact FiniteGroupCover.canonicalEquiv
    (polynomialConjugateInvariantAlgebra D) (polynomialConjugateAlgebra D)
    D.galoisGroup (fun _ _ h => Subtype.ext h)
    (conjugateGaloisMap_surjective D hKeller)

@[simp]
theorem conjugateGaloisEquiv_tmul
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F)
    (a b : polynomialConjugateAlgebra D) (g : D.galoisGroup) :
    conjugateGaloisEquiv D hKeller
      (a ⊗ₜ[polynomialConjugateInvariantAlgebra D] b) g = a * (g • b) := rfl

end

end CollisionIdeals.Planar.Research
