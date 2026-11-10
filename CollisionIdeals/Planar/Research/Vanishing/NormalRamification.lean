import CollisionIdeals.General.Galois.Descent
import CollisionIdeals.General.Keller.Normalization
import CollisionIdeals.General.Normalization.Construction
import CollisionIdeals.General.Normalization.VisibleConjugateCenter

/-!
# Normal generic extensions have no divisorial ramification

For a Keller map whose original function-field extension is normal, the
marked field fills its normal closure. Its fixing subgroup is therefore
trivial. A visible conjugate center supplies one inertia-fixed sheet, and
the regular sheet action forces that inertia subgroup to be trivial.
This contradicts the nontrivial inertia carried by any ramified divisor.

The canonical endpoint constructs the diagram and its local-index
realization internally. No purity, finite-étale rigidity, vanishing, or
boundary-emptiness hypothesis is used here.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

universe u

/-- With trivial sheet stabilizer, inertia fixing one sheet is trivial. -/
theorem inertia_eq_bot_of_invisibleAt_of_subgroup_eq_bot
    {G : Type u} [Group G] (I H : Subgroup G)
    (s : GaloisSheets H) (hH : H = ⊥)
    (hs : InertiaInvisibleAt I H s) : I = ⊥ := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective s
  have hfixed : InertiaInvisibleAt I H
      (g • ((1 : G) : GaloisSheets H)) := by simpa using hs
  have hle := (inertiaInvisibleAt_conjugateSheet_iff I H g).mp hfixed
  rw [hH, Subgroup.map_bot] at hle
  exact le_bot_iff.mp hle

variable {k : Type u} [Field k] {n : ℕ} {F : PolynomialSelfMap k n}
  {N : Type u} [Field N] [Algebra (PolynomialMapBaseFunctionField F) N]

/-- Normality here is normality of the original source extension `L/K`,
not just the automatic normality of its supplied closure `N/K`. -/
theorem PolynomialNormalizationDiagram.noCodimensionOneRamification_of_normal
    [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]
    (D : PolynomialNormalizationDiagram (F := F) (N := N))
    (R : D.ConjugateRamificationRealization) (hKeller : IsKeller F)
    (hNormal : Normal (PolynomialMapBaseFunctionField F)
      (PolynomialMapSourceFunctionField F)) :
    PolynomialNoCodimensionOneRamification (F := F) (N := N) := by
  have hH : D.cover.normalClosure.intermediateFixingSubgroup = ⊥ := by
    have hTop : D.cover.normalClosure.intermediateField = ⊤ :=
      AlgHom.fieldRange_eq_top.mpr
        (D.cover.normalClosure.normal_iff_embedding_surjective.mp hNormal)
    change D.cover.normalClosure.intermediateField.fixingSubgroup = ⊥
    rw [hTop, IntermediateField.fixingSubgroup_top]
  intro q hq
  by_contra hRamified
  let E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N) :=
    ⟨q, hq, hRamified⟩
  obtain ⟨s, hs⟩ := D.exists_inertiaFixedSheet_of_isKeller R hKeller E
  exact D.inertia_nontrivial E
    (inertia_eq_bot_of_invisibleAt_of_subgroup_eq_bot _ _ s hH hs)

/-- In characteristic zero, Keller and normality of the original generic
extension give the exact canonical no-ramification input to branch purity.
All diagram and local-index data is constructed rather than supplied. -/
theorem polynomialCanonicalNoCodimensionOneRamification_of_isKeller_of_normal
    [CharZero k] (F : PolynomialSelfMap k n) (hKeller : IsKeller F)
    (hNormal : Normal (PolynomialMapBaseFunctionField F)
      (PolynomialMapSourceFunctionField F)) :
    PolynomialNoCodimensionOneRamification
      (F := F) (N := PolynomialCanonicalNormalClosure F) := by
  letI := polynomialCanonicalNormalClosure_isSeparable F hKeller
  let C := polynomialNormalizedCoverOfIsKeller F hKeller
  exact (polynomialNormalizationDiagramOfCover C).noCodimensionOneRamification_of_normal
    (polynomialNormalizationDiagramOfCover_ramificationRealization C) hKeller hNormal

end

end CollisionIdeals
