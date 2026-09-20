import CollisionIdeals.General.Galois.CanonicalNormalClosure
import CollisionIdeals.General.Keller.Unramified
import CollisionIdeals.General.Normalization.Polynomial
import Mathlib.RingTheory.Unramified.Field

/-!
# Generic finiteness from the unramified coordinate algebra

Localizing an essentially finite type unramified algebra at its generic
point gives a finite separable field extension.  The construction uses the
coordinate-image algebra, so it does not need a separately chosen copy of
the target polynomial ring. The Keller condition supplies unramifiedness,
and hence finite separability and a canonical marked Galois closure.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-- The source is of finite type over its coordinate-image algebra. -/
theorem polynomialSource_finiteType_overImage (F : PolynomialSelfMap k n) :
    Algebra.FiniteType (polynomialMapImageAlgebra F) (SourceRing k (Fin n)) := by
  exact Algebra.FiniteType.of_restrictScalars_finiteType
    k (polynomialMapImageAlgebra F) (SourceRing k (Fin n))

/-- The source function field is essentially of finite type over the
coordinate-image function field. -/
theorem polynomialSourceFunctionField_essFiniteType (F : PolynomialSelfMap k n) :
    Algebra.EssFiniteType (PolynomialMapBaseFunctionField F)
      (PolynomialMapSourceFunctionField F) := by
  let B := polynomialMapImageAlgebra F
  let A := SourceRing k (Fin n)
  let K := PolynomialMapBaseFunctionField F
  let L := PolynomialMapSourceFunctionField F
  letI : Algebra.FiniteType B A := polynomialSource_finiteType_overImage F
  letI : Algebra.EssFiniteType A L :=
    Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors A)
  letI : Algebra.EssFiniteType B L := Algebra.EssFiniteType.comp B A L
  exact Algebra.EssFiniteType.of_comp B K L

/-- Formal unramifiedness passes from the coordinate algebra to the
induced extension of function fields. -/
theorem polynomialSourceFunctionField_formallyUnramified
    (F : PolynomialSelfMap k n)
    [Algebra.FormallyUnramified (polynomialMapImageAlgebra F) (SourceRing k (Fin n))] :
    Algebra.FormallyUnramified (PolynomialMapBaseFunctionField F)
      (PolynomialMapSourceFunctionField F) := by
  let B := polynomialMapImageAlgebra F
  let A := SourceRing k (Fin n)
  let K := PolynomialMapBaseFunctionField F
  let L := PolynomialMapSourceFunctionField F
  letI : Algebra.FormallyUnramified A L :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors A)
  letI : Algebra.FormallyUnramified B L := Algebra.FormallyUnramified.comp B A L
  exact Algebra.FormallyUnramified.of_restrictScalars B K L

/-- An unramified polynomial coordinate algebra induces a finite
function-field extension. -/
theorem polynomialSourceFunctionField_finiteDimensional_of_formallyUnramified
    (F : PolynomialSelfMap k n)
    [Algebra.FormallyUnramified (polynomialMapImageAlgebra F) (SourceRing k (Fin n))] :
    FiniteDimensional (PolynomialMapBaseFunctionField F)
      (PolynomialMapSourceFunctionField F) := by
  letI := polynomialSourceFunctionField_essFiniteType F
  letI := polynomialSourceFunctionField_formallyUnramified F
  exact Algebra.FormallyUnramified.finite_of_free
    (PolynomialMapBaseFunctionField F) (PolynomialMapSourceFunctionField F)

/-- The same extension is separable, without a characteristic-zero
assumption. -/
theorem polynomialSourceFunctionField_isSeparable_of_formallyUnramified
    (F : PolynomialSelfMap k n)
    [Algebra.FormallyUnramified (polynomialMapImageAlgebra F) (SourceRing k (Fin n))] :
    Algebra.IsSeparable (PolynomialMapBaseFunctionField F)
      (PolynomialMapSourceFunctionField F) := by
  letI := polynomialSourceFunctionField_essFiniteType F
  letI := polynomialSourceFunctionField_formallyUnramified F
  exact Algebra.FormallyUnramified.isSeparable
    (PolynomialMapBaseFunctionField F) (PolynomialMapSourceFunctionField F)

/-- A Keller map has finite generic degree. -/
theorem polynomialSourceFunctionField_finiteDimensional_of_isKeller
    (F : PolynomialSelfMap k n) (hKeller : IsKeller F) :
    FiniteDimensional (PolynomialMapBaseFunctionField F)
      (PolynomialMapSourceFunctionField F) := by
  letI := polynomialSource_formallyUnramified_of_isKeller F hKeller
  exact polynomialSourceFunctionField_finiteDimensional_of_formallyUnramified F

/-- The generic extension of a Keller map is separable in any characteristic. -/
theorem polynomialSourceFunctionField_isSeparable_of_isKeller
    (F : PolynomialSelfMap k n) (hKeller : IsKeller F) :
    Algebra.IsSeparable (PolynomialMapBaseFunctionField F)
      (PolynomialMapSourceFunctionField F) := by
  letI := polynomialSource_formallyUnramified_of_isKeller F hKeller
  exact polynomialSourceFunctionField_isSeparable_of_formallyUnramified F

/-- The canonical normal closure of the generic extension of a polynomial map. -/
abbrev PolynomialCanonicalNormalClosure (F : PolynomialSelfMap k n) :=
  CanonicalNormalClosure (PolynomialMapBaseFunctionField F)
    (PolynomialMapSourceFunctionField F)

/-- The Keller condition constructs marked finite normal-closure data;
normal-closure existence is not a separate input. -/
def polynomialCanonicalNormalClosureData
    (F : PolynomialSelfMap k n) (hKeller : IsKeller F) :
    PolynomialNormalClosureData F (PolynomialCanonicalNormalClosure F) := by
  letI := polynomialSourceFunctionField_finiteDimensional_of_isKeller F hKeller
  exact canonicalNormalClosureData
    (PolynomialMapBaseFunctionField F) (PolynomialMapSourceFunctionField F)

/-- The canonical normal closure of a Keller generic extension is separable. -/
theorem polynomialCanonicalNormalClosure_isSeparable
    (F : PolynomialSelfMap k n) (hKeller : IsKeller F) :
    Algebra.IsSeparable (PolynomialMapBaseFunctionField F)
      (PolynomialCanonicalNormalClosure F) := by
  letI := polynomialSourceFunctionField_isSeparable_of_isKeller F hKeller
  exact canonicalNormalClosure_isSeparable
    (PolynomialMapBaseFunctionField F) (PolynomialMapSourceFunctionField F)

/-- The canonical normal closure of a Keller generic extension is Galois. -/
theorem polynomialCanonicalNormalClosure_isGalois
    (F : PolynomialSelfMap k n) (hKeller : IsKeller F) :
    IsGalois (PolynomialMapBaseFunctionField F)
      (PolynomialCanonicalNormalClosure F) := by
  letI := polynomialSourceFunctionField_finiteDimensional_of_isKeller F hKeller
  letI := polynomialSourceFunctionField_isSeparable_of_isKeller F hKeller
  exact canonicalNormalClosure_isGalois
    (PolynomialMapBaseFunctionField F) (PolynomialMapSourceFunctionField F)

end

end CollisionIdeals
