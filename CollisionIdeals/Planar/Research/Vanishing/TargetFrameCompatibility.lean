import CollisionIdeals.Planar.Research.InvariantFrame
import CollisionIdeals.General.Galois.ConjugateInvariantField

/-!
# Target-field differentiation of the actual invariant frame

Any target fraction-field derivation extending the transported coordinate
partial agrees with the existing Keller frame on the actual fixed algebra.
Denominator clearing proves the comparison from its already established
base values and target-coordinate Leibniz rule.

This identifies the original operator, not a newly supplied action. It
does not assert preservation of a normalization lattice or a uniform
bound on the derivative orbit.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace CollisionIdeals

noncomputable section

private theorem fractionField_frame_compatible
    {k B C K : Type*} [CommRing k] [CommRing B] [Nontrivial B] [CommRing C] [Field K]
    [Algebra k B] [Algebra k K] [Algebra B C] [Algebra B K] [IsFractionRing B K]
    (dB : Derivation k B B) (dC : C →+ C) (dK : Derivation k K K)
    (j : C →ₐ[B] K) (hj : Function.Injective j)
    (hCBase : ∀ b : B, dC (algebraMap B C b) = algebraMap B C (dB b))
    (hCLeibniz : ∀ (b : B) (z : C), dC (b • z) = dB b • z + b • dC z)
    (hKBase : ∀ b : B, dK (algebraMap B K b) = algebraMap B K (dB b)) (z : C) :
    dK (j z) = j (dC z) := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := B) (j z)
  have hbK : algebraMap B K b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hrelK : algebraMap B K a = algebraMap B K b * j z := by
    calc
      algebraMap B K a = j z * algebraMap B K b := (div_eq_iff hbK).mp hab
      _ = algebraMap B K b * j z := mul_comm _ _
  have hrel : algebraMap B C a = b • z := by
    apply hj
    rw [j.commutes, map_smul]
    simpa only [Algebra.smul_def] using hrelK
  have hFrame := congrArg j (congrArg dC hrel)
  rw [hCBase, hCLeibniz, map_add, map_smul, map_smul, j.commutes] at hFrame
  have hDerivative := congrArg dK hrelK
  rw [hKBase, dK.leibniz, hKBase] at hDerivative
  simp only [Algebra.smul_def] at hFrame
  simp only [Algebra.smul_def, Algebra.algebraMap_self_apply] at hDerivative
  apply mul_left_cancel₀ hbK
  apply add_left_cancel (a := algebraMap B K (dB b) * j z)
  calc
    algebraMap B K (dB b) * j z + algebraMap B K b * dK (j z) =
        algebraMap B K b * dK (j z) + algebraMap B K (dB b) * j z := add_comm _ _
    _ = algebraMap B K b * dK (j z) + j z * algebraMap B K (dB b) :=
      congrArg (fun t : K => algebraMap B K b * dK (j z) + t) (mul_comm _ _)
    _ = algebraMap B K (dB a) := hDerivative.symm
    _ = algebraMap B K (dB b) * j z + algebraMap B K b * j (dC z) := hFrame

variable {F : PlanarPolynomialMap} {N : Type} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]
variable [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]

@[reducible] local instance targetFrameBaseAlgebra :
    Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

@[reducible] local instance targetFrameBaseFieldAlgebra :
    Algebra (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) :=
  OreLocalization.instAlgebra

local instance targetFrameBaseFieldSMul :
    SMul (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) := Algebra.toSMul

@[reducible] local instance targetFrameInvariantAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateInvariantAlgebra D)

local instance targetFrameInvariantSMul (D : PolynomialNormalClosureData F N) :
    SMul (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) := Algebra.toSMul

local notation "B₀" => PolynomialImageAlgebra F
local notation "K₀" => PolynomialMapBaseFunctionField F

/-- A derivation of the original target function field extending the
transported target partial computes the already constructed invariant
Keller frame under its canonical target-field embedding. The compatibility
hypothesis concerns only base polynomials, not invariant elements. -/
theorem planarKellerInvariantFrame_baseField_compatible
    (D : PolynomialNormalClosureData F N) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = MvPolynomial.C c) (i : Fin 2)
    (dK : Derivation ℂ K₀ K₀)
    (hBase : letI := D.finiteIntermediate
      ∀ b : B₀, dK (algebraMap B₀ K₀ b) =
        algebraMap B₀ K₀ (polynomialImageCoordinatePartial F i b))
    (z : polynomialConjugateInvariantAlgebra D) :
    dK ((polynomialConjugateInvariantBaseEquiv D).symm z : K₀) =
      ((polynomialConjugateInvariantBaseEquiv D).symm
        (planarKellerInvariantFrame D c hc hJ i z) : K₀) := by
  letI := D.finiteIntermediate
  let C := polynomialConjugateInvariantAlgebra D
  let e := polynomialConjugateInvariantBaseEquiv D
  let j : C →ₐ[B₀] K₀ :=
    (polynomialConjugateInvariantBaseAlgebra D).val.comp e.symm.toAlgHom
  have hj : Function.Injective j := Subtype.val_injective.comp e.symm.injective
  change dK (j z) = j (planarKellerInvariantFrame D c hc hJ i z)
  exact fractionField_frame_compatible (polynomialImageCoordinatePartial F i)
    (planarKellerInvariantFrame D c hc hJ i) dK j hj
    (fun b => planarKellerInvariantFrame_algebraMap D c hc hJ i b)
    (fun b w => planarKellerInvariantFrame_leibniz D c hc hJ i b w) hBase z

end

end CollisionIdeals
