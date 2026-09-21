import CollisionIdeals.General.Normalization.OpenImmersion
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Birational quasi-finite algebras over a normal base

A finite-type quasi-finite algebra embedded over `B` in its fraction field
is the coordinate ring of an open subscheme of `Spec B` when `B` is
integrally closed. The proof identifies its relative integral closure
with `B` and applies the existing affine Zariski-main theorem.

No normality assumption on the intermediate algebra, flatness hypothesis,
or group-action freeness is needed. An open immersion does not assert
that the open is the whole target.
-/

set_option autoImplicit false

namespace CollisionIdeals

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- An injective intermediate algebra in the fraction field of a normal
base gives an open immersion when it is finite type and quasi-finite.
The intermediate algebra is not assumed integrally closed. -/
theorem isOpenImmersion_specMap_of_quasiFinite_birational
    (B I K : Type u) [CommRing B] [CommRing I] [Field K]
    [Algebra B I] [Algebra B K] [Algebra I K]
    [IsScalarTower B I K] [IsFractionRing B K] [IsIntegrallyClosed B]
    [Algebra.FiniteType B I] [Algebra.QuasiFinite B I]
    (hinj : Function.Injective (algebraMap I K)) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B I))) := by
  let φ : B →ₐ[B] integralClosure B I := Algebra.ofId B (integralClosure B I)
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y hxy
      apply IsFractionRing.injective B K
      have hxyI : algebraMap B I x = algebraMap B I y := congrArg Subtype.val hxy
      simpa only [IsScalarTower.algebraMap_apply B I K] using
        congrArg (algebraMap I K) hxyI
    · intro x
      have hxK : IsIntegral B (algebraMap I K (x : I)) :=
        x.property.map (IsScalarTower.toAlgHom B I K)
      obtain ⟨b, hb⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hxK
      refine ⟨b, Subtype.ext (hinj ?_)⟩
      exact (IsScalarTower.algebraMap_apply B I K b).symm.trans hb
  let e := AlgEquiv.ofBijective φ hφ
  haveI : IsIso (CommRingCat.ofHom φ.toRingHom) :=
    inferInstanceAs (IsIso e.toRingEquiv.toCommRingCatIso.hom)
  haveI := isOpenImmersion_integralClosure_of_quasiFinite B I
  have hcomp : algebraMap B I =
      (integralClosure B I).val.toRingHom.comp φ.toRingHom := rfl
  rw [hcomp, CommRingCat.ofHom_comp, Spec.map_comp]
  infer_instance

end

end CollisionIdeals
