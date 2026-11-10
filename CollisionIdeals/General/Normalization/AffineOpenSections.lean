import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Sections on the image of an affine open immersion

An algebra whose spectrum embeds openly in `Spec B` is canonically the
section algebra of that image. The equivalence respects the existing
base maps and therefore identifies the corresponding module quotients
by the base. These are module quotients, not quotient rings.

This file makes no local-cohomology comparison and asserts no finiteness
or uniform annihilator for either quotient.
-/

set_option autoImplicit false

namespace CollisionIdeals

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable (B C : Type u) [CommRing B] [CommRing C] [Algebra B C]
variable [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B C)))]

-- Expose the existing structure-sheaf algebra, not a transported action.
local instance : Algebra B Γ(Spec (.of B),
    (Spec.map (CommRingCat.ofHom (algebraMap B C))).opensRange) :=
  inferInstanceAs (Algebra B ((Spec.structureSheaf B).val.obj (Opposite.op
    (Spec.map (CommRingCat.ofHom (algebraMap B C))).opensRange)))

/-- The existing algebra is the section ring on the open image of its
spectrum map. No alternate open or section-ring model is chosen. -/
def affineOpenSectionsIso :
    CommRingCat.of C ≅ Γ(Spec (.of B),
      (Spec.map (CommRingCat.ofHom (algebraMap B C))).opensRange) :=
  (Scheme.ΓSpecIso (.of C)).symm ≪≫
    IsOpenImmersion.ΓIsoTop (Spec.map (CommRingCat.ofHom (algebraMap B C)))

/-- The section-ring identification carries the algebra's base map to
ordinary restriction of target functions. -/
theorem affineOpenSectionsIso_hom_comp :
    CommRingCat.ofHom (algebraMap B C) ≫ (affineOpenSectionsIso B C).hom =
      CommRingCat.ofHom (algebraMap B Γ(Spec (.of B),
        (Spec.map (CommRingCat.ofHom (algebraMap B C))).opensRange)) := by
  simp only [affineOpenSectionsIso, Iso.trans_hom, Iso.symm_hom,
    IsOpenImmersion.ΓIsoTop]
  rw [Scheme.ΓSpecIso_inv_naturality_assoc]
  dsimp only [Scheme.Hom.appTop]
  rw [Scheme.Hom.app_eq_appLE]
  simp only [Scheme.Hom.preimage_top]
  rw [Scheme.Hom.appLE_appIso_inv_assoc
    (Spec.map (CommRingCat.ofHom (algebraMap B C))) (U := ⊤) (V := ⊤) le_rfl]
  simp only [Functor.mapIso_hom, Iso.op_hom, eqToIso.inv, ← Functor.map_comp]
  rfl

/-- The same canonical section identification, retaining the base algebra
structure rather than only the abstract ring structure. -/
def affineOpenSectionsAlgEquiv :
    C ≃ₐ[B] Γ(Spec (.of B),
      (Spec.map (CommRingCat.ofHom (algebraMap B C))).opensRange) where
  __ := (affineOpenSectionsIso B C).commRingCatIsoToRingEquiv
  commutes' b := congrArg (fun f : CommRingCat.of B ⟶ _ => f b)
    (affineOpenSectionsIso_hom_comp B C)

/-- The section identification induces the usual module equivalence modulo
the image of the base. The base image is not treated as an ideal. -/
def affineOpenSectionsQuotientEquiv :
    (C ⧸ LinearMap.range (Algebra.linearMap B C)) ≃ₗ[B]
      Γ(Spec (.of B),
        (Spec.map (CommRingCat.ofHom (algebraMap B C))).opensRange) ⧸
      LinearMap.range (Algebra.linearMap B Γ(Spec (.of B),
        (Spec.map (CommRingCat.ofHom (algebraMap B C))).opensRange)) := by
  apply Submodule.Quotient.equiv _ _ (affineOpenSectionsAlgEquiv B C).toLinearEquiv
  ext s
  constructor
  · rintro ⟨c, ⟨b, rfl⟩, rfl⟩
    exact ⟨b, ((affineOpenSectionsAlgEquiv B C).commutes b).symm⟩
  · rintro ⟨b, rfl⟩
    exact ⟨algebraMap B C b, ⟨b, rfl⟩,
      (affineOpenSectionsAlgEquiv B C).commutes b⟩

@[simp]
theorem affineOpenSectionsQuotientEquiv_mk (c : C) :
    affineOpenSectionsQuotientEquiv B C (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (affineOpenSectionsAlgEquiv B C c) := rfl

end

end CollisionIdeals
