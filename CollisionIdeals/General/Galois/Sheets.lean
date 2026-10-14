module

public import Mathlib.GroupTheory.GroupAction.Quotient

@[expose] public section

set_option autoImplicit false

namespace CollisionIdeals

universe u

noncomputable section

variable {G : Type u} [Group G]

/-- The sheets of the intermediate quotient associated with `H ≤ G`. -/
abbrev GaloisSheets (H : Subgroup G) :=
  G ⧸ H

/--
An inertia subgroup is invisible at a sheet when every inertia element fixes
that sheet. In geometric applications this is the group-theoretic content
of the intermediate sheet being unramified.
-/
def InertiaInvisibleAt
    (I H : Subgroup G) (s : GaloisSheets H) : Prop :=
  ∀ i : I, (i : G) • s = s

/-- Inertia is invisible on every sheet belonging to a specified visible locus. -/
def InertiaInvisibleOn
    (I H : Subgroup G) (visible : Set (GaloisSheets H)) : Prop :=
  ∀ s, s ∈ visible → InertiaInvisibleAt I H s

/--
The visible sheets detect inertia if an inertia subgroup fixing all of them
must be trivial.
-/
def VisibleSheetsDetectInertia
    (H : Subgroup G) (visible : Set (GaloisSheets H)) : Prop :=
  ∀ I : Subgroup G, InertiaInvisibleOn I H visible → I = ⊥

theorem inertiaInvisibleAt_iff_le_stabilizer
    (I H : Subgroup G) (s : GaloisSheets H) :
    InertiaInvisibleAt I H s ↔
      I ≤ MulAction.stabilizer G s := by
  constructor
  · intro h g hg
    rw [MulAction.mem_stabilizer_iff]
    exact h ⟨g, hg⟩
  · intro h i
    exact
      (MulAction.mem_stabilizer_iff.mp
        (h i.property))

theorem inertiaInvisibleAt_baseSheet_iff
    (I H : Subgroup G) :
    InertiaInvisibleAt I H ((1 : G) : GaloisSheets H) ↔ I ≤ H := by
  rw [inertiaInvisibleAt_iff_le_stabilizer,
    MulAction.stabilizer_quotient]

/-- The stabilizer of the sheet `gH` is the conjugate `gHg⁻¹`. -/
theorem inertiaInvisibleAt_conjugateSheet_iff
    (I H : Subgroup G) (g : G) :
    InertiaInvisibleAt I H
        (g • ((1 : G) : GaloisSheets H)) ↔
      I ≤ H.map (MulAut.conj g).toMonoidHom := by
  rw [inertiaInvisibleAt_iff_le_stabilizer,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    MulAction.stabilizer_quotient]

/--
An inertia subgroup fixes every sheet of `G/H` exactly when it lies in the
normal core of `H`.
-/
theorem inertiaInvisibleOn_univ_iff_le_normalCore
    (I H : Subgroup G) :
    InertiaInvisibleOn I H Set.univ ↔ I ≤ H.normalCore := by
  rw [H.normalCore_eq_ker]
  constructor
  · intro h g hg
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    intro s
    change g • s = s
    exact h s (Set.mem_univ s) ⟨g, hg⟩
  · intro h s _ i
    have hi :
        (i : G) ∈
          (MulAction.toPermHom G (GaloisSheets H)).ker :=
      h i.property
    rw [MonoidHom.mem_ker] at hi
    have hs := Equiv.congr_fun hi s
    simpa using hs

/-- Core-free intermediate subgroups make the full sheet set detect inertia. -/
theorem visibleSheetsDetectInertia_univ_of_normalCore_eq_bot
    (H : Subgroup G) (hcore : H.normalCore = ⊥) :
    VisibleSheetsDetectInertia H Set.univ := by
  intro I hI
  apply le_bot_iff.mp
  rw [← hcore]
  exact (inertiaInvisibleOn_univ_iff_le_normalCore I H).mp hI

/--
In a core-free coset action, every nontrivial inertia subgroup moves at
least one sheet.
-/
theorem exists_sheet_moved_of_normalCore_eq_bot
    (I H : Subgroup G) (hcore : H.normalCore = ⊥)
    (hI : I ≠ ⊥) :
    ∃ s : GaloisSheets H, ¬ InertiaInvisibleAt I H s := by
  by_contra hAll
  have hInvisible : InertiaInvisibleOn I H Set.univ := by
    intro s _
    exact Classical.byContradiction fun hs ↦
      hAll ⟨s, hs⟩
  exact
    hI
      (visibleSheetsDetectInertia_univ_of_normalCore_eq_bot
        H hcore I hInvisible)

end

end CollisionIdeals
