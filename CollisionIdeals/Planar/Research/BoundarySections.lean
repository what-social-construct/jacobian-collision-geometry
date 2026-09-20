import CollisionIdeals.Planar.Boundary.Separation
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Localization.Integral

/-!
# Sections on the complement of the fixed--moving boundary

The boundary-section ring is the actual structure-sheaf section ring of
`Spec T \ V(J_C)`.  Its map into the normal-closure field is the germ at the
generic point, followed by the canonical identification of fraction fields.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals.Planar

noncomputable section

open AlgebraicGeometry CategoryTheory

section AffineSections

variable {T N : Type} [CommRing T] [IsDomain T] [Field N]
variable [Algebra T N] [IsFractionRing T N]

instance affineSectionsAlgebra (U : (Spec (.of T)).Opens) :
    Algebra T Γ(Spec (.of T), U) :=
  inferInstanceAs (Algebra T ((Spec.structureSheaf T).val.obj (Opposite.op U)))

local instance : Algebra T (Spec (.of T)).functionField :=
  (StructureSheaf.toStalk T (genericPoint (Spec (.of T)))).hom.toAlgebra

local instance : IsFractionRing T (Spec (.of T)).functionField :=
  functionField_isFractionRing_of_affine (CommRingCat.of T)

/-- Evaluation of a genuine section at the generic point, in a specified
fraction field of the affine coordinate ring. -/
def affineSectionsToFractionField
    (U : (Spec (.of T)).Opens) [Nonempty U] :
    Γ(Spec (.of T), U) →ₐ[T] N where
  toRingHom :=
    (IsLocalization.algEquiv (nonZeroDivisors T)
      (Spec (.of T)).functionField N).toRingHom.comp
        ((Spec (.of T)).germToFunctionField U).hom
  commutes' t := by
    change
      (IsLocalization.algEquiv (nonZeroDivisors T)
        (Spec (.of T)).functionField N)
        (((Spec (.of T)).germToFunctionField U)
          (algebraMap T Γ(Spec (.of T), U) t)) = _
    have h := StructureSheaf.algebraMap_germ_apply (R := T) U
      (genericPoint (Spec (.of T)))
      (((genericPoint_spec (Spec (.of T))).mem_open_set_iff U.isOpen).mpr
        (by simpa using (inferInstance : Nonempty U))) t
    change ((Spec (.of T)).germToFunctionField U)
      (algebraMap T Γ(Spec (.of T), U) t) =
      algebraMap T (Spec (.of T)).functionField t at h
    rw [h]
    exact AlgEquiv.commutes _ t

theorem affineSectionsToFractionField_injective
    (U : (Spec (.of T)).Opens) [Nonempty U] :
    Function.Injective (affineSectionsToFractionField (N := N) U) :=
  (IsLocalization.algEquiv (nonZeroDivisors T)
    (Spec (.of T)).functionField N).injective.comp
      ((Spec (.of T)).germToFunctionField_injective U)

end AffineSections

variable {F : PlanarPolynomialMap}
variable {N : Type} [Field N]
variable [Algebra (PlanarBaseFunctionField F) N]

local notation "T₀" => GaloisNormalizationRing (F := F) (N := N)

/-- The normal-closure field is the fraction field of its normalization
ring; this follows from the finite normal extension already in the model. -/
theorem normalization_isFractionRing
    (D : NormalizationDiagram (F := F) (N := N)) :
    IsFractionRing T₀ N := by
  letI algebraBK : Algebra (PolynomialImageAlgebra F) (PlanarBaseFunctionField F) :=
    OreLocalization.instAlgebra
  letI : SMul (PolynomialImageAlgebra F) (PlanarBaseFunctionField F) :=
    algebraBK.toSMul
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI : IsScalarTower (PolynomialImageAlgebra F)
      (PlanarBaseFunctionField F) N :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : FiniteDimensional (PlanarBaseFunctionField F) N :=
    D.cover.normalClosure.finiteNormal
  exact integralClosure.isFractionRing_of_finite_extension
    (PlanarBaseFunctionField F) N

/-- The open set on which the boundary sections are regular. -/
def fixedMovingBoundaryOpen
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) : (Spec (.of T₀)).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (fixedMovingBoundaryIdeal D C))ᶜ,
    (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

/-- A nontrivial subgroup has a nonzero fixed-locus ideal: the action on
the normalization is faithful because its fraction field is `N`. -/
theorem fixedLocusIdeal_ne_bot
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) (hC : C ≠ ⊥) :
    fixedLocusIdeal C ≠ ⊥ := by
  letI : IsFractionRing T₀ N := normalization_isFractionRing D
  intro h
  apply hC
  rw [Subgroup.eq_bot_iff_forall]
  intro σ hσ
  have hfix := (fixedLocusIdeal_le_iff C (⊥ : Ideal T₀)).mp (le_of_eq h)
  have heq : σ.toRingHom = (1 : NormalizationGaloisGroup D).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := T₀)
    intro t
    have ht := hfix ⟨σ, hσ⟩ t
    have ht' : galoisNormalizationEquiv (F := F) (N := N) σ t = t :=
      sub_eq_zero.mp (by simpa only [Ideal.mem_bot] using ht)
    exact congrArg (fun a : T₀ => (a : N)) ht'
  exact AlgEquiv.ext fun x => congrArg (fun f : N →+* N => f x) heq

/-- The generic point is retained whenever the subgroup is nontrivial. -/
theorem fixedMovingBoundaryOpen_nonempty
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) (hC : C ≠ ⊥) :
    Nonempty (fixedMovingBoundaryOpen D C) := by
  refine ⟨⟨(⊥ : PrimeSpectrum T₀), ?_⟩⟩
  change ¬ fixedMovingBoundaryIdeal D C ≤ (⊥ : Ideal T₀)
  intro h
  apply fixedLocusIdeal_ne_bot D C hC
  apply le_bot_iff.mp
  exact le_trans (show fixedLocusIdeal C ≤ fixedMovingBoundaryIdeal D C from le_sup_left) h

/-- The actual structure-sheaf section ring `Γ(Spec T \ V(J_C), O)`. -/
abbrev BoundarySectionRing
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) :=
  Γ(Spec (.of T₀), fixedMovingBoundaryOpen D C)

/-- The boundary section ring embedded in the specified normal closure. -/
def boundarySectionsToNormalClosure
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) (hC : C ≠ ⊥) :
    BoundarySectionRing D C →ₐ[T₀] N := by
  letI := normalization_isFractionRing D
  letI := fixedMovingBoundaryOpen_nonempty D C hC
  exact affineSectionsToFractionField (fixedMovingBoundaryOpen D C)

theorem boundarySectionsToNormalClosure_injective
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) (hC : C ≠ ⊥) :
    Function.Injective (boundarySectionsToNormalClosure D C hC) := by
  letI := normalization_isFractionRing D
  letI := fixedMovingBoundaryOpen_nonempty D C hC
  exact affineSectionsToFractionField_injective (fixedMovingBoundaryOpen D C)

/-- `R_C` as the subalgebra of `N` consisting precisely of regular sections
on the complement of the fixed--moving boundary. -/
def boundarySectionSubalgebra
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) (hC : C ≠ ⊥) :
    Subalgebra T₀ N :=
  (boundarySectionsToNormalClosure D C hC).range

/-- The concrete section subalgebra is canonically isomorphic to `Γ(U_C,O)`. -/
def boundarySectionsEquivSubalgebra
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) (hC : C ≠ ⊥) :
    BoundarySectionRing D C ≃ₐ[T₀] boundarySectionSubalgebra D C hC :=
  AlgEquiv.ofInjective (boundarySectionsToNormalClosure D C hC)
    (boundarySectionsToNormalClosure_injective D C hC)

/-- The boundary-section module consumed by the trace transporter. -/
def boundarySectionSubmodule
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) (hC : C ≠ ⊥) :
    Submodule T₀ N :=
  (boundarySectionSubalgebra D C hC).toSubmodule

@[simp]
theorem mem_boundarySectionSubalgebra_iff
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) (hC : C ≠ ⊥) (z : N) :
    z ∈ boundarySectionSubalgebra D C hC ↔
      ∃ s : BoundarySectionRing D C, boundarySectionsToNormalClosure D C hC s = z :=
  Iff.rfl

@[simp]
theorem mem_boundarySectionSubmodule_iff
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) (hC : C ≠ ⊥) (z : N) :
    z ∈ boundarySectionSubmodule D C hC ↔
      ∃ s : BoundarySectionRing D C, boundarySectionsToNormalClosure D C hC s = z :=
  Iff.rfl

/-- Every normalization-ring element restricts to a boundary section. -/
theorem normalization_mem_boundarySectionSubalgebra
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) (hC : C ≠ ⊥) (t : T₀) :
    (t : N) ∈ boundarySectionSubalgebra D C hC :=
  (boundarySectionSubalgebra D C hC).algebraMap_mem t

end

end CollisionIdeals.Planar
