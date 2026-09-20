import CollisionIdeals.General.Normalization.ImageGeometry
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Flat.Basic

/-!
The local geometric interfaces supplied by the Keller condition:
scheme-theoretic étaleness and algebraic flatness.
-/

set_option autoImplicit false

namespace CollisionIdeals

open AlgebraicGeometry

noncomputable section

universe u

variable {K : Type u} [Field K]
variable {n : ℕ}

/--
The scheme-theoretic Jacobian-criterion obligation for a polynomial
self-map: the Keller condition makes the map to its coordinate image
étale.

The theorem `kellerEtaleBridge` in `General.Keller.Etale` proves this
interface using the graph presentation over the coordinate-image algebra
and its invertible Jacobian.
-/
def KellerEtaleBridge
    (F : PolynomialSelfMap K n) : Prop :=
  IsKeller F →
    Etale (polynomialSourceToImageBase F)

/--
The algebraic flatness obligation supplied by the Keller condition: the
source polynomial ring is flat over the coordinate image algebra.
-/
def KellerFlatBridge
    (F : PolynomialSelfMap K n) : Prop :=
  IsKeller F →
    Module.Flat
      (polynomialMapImageAlgebra F)
      (SourceRing K (Fin n))

/-- Scheme-theoretic étaleness of the polynomial map supplies its algebraic
flatness bridge. -/
theorem KellerEtaleBridge.toKellerFlatBridge
    (F : PolynomialSelfMap K n)
    (hEtale : KellerEtaleBridge F) :
    KellerFlatBridge F := by
  intro hKeller
  have hScheme : Etale (polynomialSourceToImageBase F) :=
    hEtale hKeller
  have hRing :
      RingHom.Etale
        (algebraMap
          (polynomialMapImageAlgebra F)
          (SourceRing K (Fin n))) := by
    exact HasRingHomProperty.Spec_iff.mp hScheme
  letI :
      Algebra.Etale
        (polynomialMapImageAlgebra F)
        (SourceRing K (Fin n)) :=
    hRing
  infer_instance

end

end CollisionIdeals
