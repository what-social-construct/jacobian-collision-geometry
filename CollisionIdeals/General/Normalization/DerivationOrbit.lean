import CollisionIdeals.General.Normalization.DerivationAnnihilator
import CollisionIdeals.General.Normalization.DerivationCyclicStage

/-!
# Differential words and their uniform annihilators

The differential orbit is the standard base-module span of all finite
words in the supplied additive operators. The Leibniz rules make this
same span invariant; no coherence or finite generation is assumed.

Over a characteristic-zero polynomial base, one nonzero scalar killing
every word therefore kills the original class by the existing
annihilator theorem. This packages the conditional endgame and its
contrapositive. It does not construct a uniform annihilator from
elementwise torsion or from finite-order denominator bounds.
-/

set_option autoImplicit false

namespace CollisionIdeals

section Words

variable {σ M : Type*} [AddCommMonoid M]

/-- Apply a finite word of additive operators, with the head acting last. -/
def derivationWordAction (nabla : σ → M →+ M) (word : List σ) (q : M) : M :=
  word.foldr (fun i m => nabla i m) q

@[simp]
theorem derivationWordAction_nil (nabla : σ → M →+ M) (q : M) :
    derivationWordAction nabla [] q = q := rfl

@[simp]
theorem derivationWordAction_cons (nabla : σ → M →+ M)
    (i : σ) (word : List σ) (q : M) :
    derivationWordAction nabla (i :: word) q = nabla i (derivationWordAction nabla word q) := rfl

end Words

section Orbit

variable {σ k B M : Type*} [CommRing k] [CommRing B] [Algebra k B]
  [AddCommMonoid M] [Module B M]

/-- The existing module span of all finite differential words of a class. -/
def derivationOrbitSpan (B : Type*) [CommRing B] [Module B M]
    (nabla : σ → M →+ M) (q : M) : Submodule B M :=
  Submodule.span B (Set.range fun word : List σ => derivationWordAction nabla word q)

theorem derivationWordAction_mem_orbitSpan
    (nabla : σ → M →+ M) (q : M) (word : List σ) :
    derivationWordAction nabla word q ∈ derivationOrbitSpan B nabla q :=
  Submodule.subset_span ⟨word, rfl⟩

theorem self_mem_derivationOrbitSpan (nabla : σ → M →+ M) (q : M) :
    q ∈ derivationOrbitSpan B nabla q :=
  derivationWordAction_mem_orbitSpan nabla q []

/-- The Leibniz rules preserve the orbit span, including scalar multiples
of word values. Commutation of the operators is not required. -/
theorem derivationOrbitSpan_operator_mem
    (d : σ → Derivation k B B) (nabla : σ → M →+ M)
    (hLeibniz : ∀ (i : σ) (b : B) (m : M),
      nabla i (b • m) = d i b • m + b • nabla i m)
    (q : M) (i : σ) {m : M} (hm : m ∈ derivationOrbitSpan B nabla q) :
    nabla i m ∈ derivationOrbitSpan B nabla q := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
      obtain ⟨word, rfl⟩ := hm
      exact derivationWordAction_mem_orbitSpan nabla q (i :: word)
  | zero =>
      simpa only [map_zero] using (derivationOrbitSpan B nabla q).zero_mem
  | add x y _ _ hx hy =>
      rw [map_add]
      exact (derivationOrbitSpan B nabla q).add_mem hx hy
  | smul b x hx ih =>
      rw [hLeibniz]
      exact (derivationOrbitSpan B nabla q).add_mem
        ((derivationOrbitSpan B nabla q).smul_mem _ hx)
        ((derivationOrbitSpan B nabla q).smul_mem _ ih)

end Orbit

section Polynomial

variable {σ k B M : Type*} [Field k] [CharZero k] [CommRing B] [Algebra k B]
  [AddCommMonoid M] [Module B M]

/-- A nonzero scalar annihilating every differential word forces the
original class to vanish. The whole orbit need not be finite over B. -/
theorem eq_zero_of_uniform_annihilator_derivationWords
    (e : MvPolynomial σ k ≃ₐ[k] B) (nabla : σ → M →+ M)
    (hLeibniz : ∀ (i : σ) (b : B) (m : M),
      nabla i (b • m) = polynomialEquivPartial e i b • m + b • nabla i m)
    (q : M) (s : B) (hs : s ≠ 0)
    (hKill : ∀ word : List σ, s • derivationWordAction nabla word q = 0) :
    q = 0 := by
  let S := derivationOrbitSpan B nabla q
  let nablaS : σ → S →+ S := fun i =>
    { toFun := fun m => ⟨nabla i m,
        derivationOrbitSpan_operator_mem (fun i => polynomialEquivPartial e i)
          nabla hLeibniz q i m.property⟩
      map_zero' := Subtype.ext (map_zero (nabla i))
      map_add' := fun x y => Subtype.ext (map_add (nabla i) (x : M) (y : M)) }
  have hLeibnizS : ∀ (i : σ) (b : B) (m : S),
      nablaS i (b • m) = polynomialEquivPartial e i b • m + b • nablaS i m := by
    intro i b m
    apply Subtype.ext
    exact hLeibniz i b m
  have hsAnn : s ∈ Module.annihilator B S := by
    apply (Submodule.mem_annihilator_span _ s).mpr
    rintro ⟨m, word, rfl⟩
    exact hKill word
  have hAnn : Module.annihilator B S ≠ ⊥ := by
    intro h
    exact hs (by simpa only [h, Ideal.mem_bot] using hsAnn)
  letI : Subsingleton S :=
    subsingleton_of_annihilator_ne_bot_of_polynomial_leibniz e nablaS hLeibnizS hAnn
  have hzero : (⟨q, self_mem_derivationOrbitSpan nabla q⟩ : S) = 0 :=
    Subsingleton.elim _ _
  exact congrArg (fun m : S => (m : M)) hzero

/-- Every proposed nonzero scalar misses some derivative word of a
nonzero class. No torsion hypothesis or uniform pole bound is assumed. -/
theorem exists_derivationWord_not_annihilated
    (e : MvPolynomial σ k ≃ₐ[k] B) (nabla : σ → M →+ M)
    (hLeibniz : ∀ (i : σ) (b : B) (m : M),
      nabla i (b • m) = polynomialEquivPartial e i b • m + b • nabla i m)
    (q : M) (hq : q ≠ 0) (s : B) (hs : s ≠ 0) :
    ∃ word : List σ, s • derivationWordAction nabla word q ≠ 0 := by
  by_contra! hKill
  exact hq (eq_zero_of_uniform_annihilator_derivationWords e nabla hLeibniz q s hs hKill)

/-- The all-orders uniform-annihilator condition is equivalent to
vanishing, not an automatic consequence of torsion at each finite order. -/
theorem exists_uniform_annihilator_derivationWords_iff
    (e : MvPolynomial σ k ≃ₐ[k] B) (nabla : σ → M →+ M)
    (hLeibniz : ∀ (i : σ) (b : B) (m : M),
      nabla i (b • m) = polynomialEquivPartial e i b • m + b • nabla i m)
    (q : M) :
    (∃ s : B, s ≠ 0 ∧
      ∀ word : List σ, s • derivationWordAction nabla word q = 0) ↔ q = 0 := by
  constructor
  · rintro ⟨s, hs, hKill⟩
    exact eq_zero_of_uniform_annihilator_derivationWords e nabla hLeibniz q s hs hKill
  · intro hq
    letI : Nontrivial B := e.symm.toEquiv.nontrivial
    refine ⟨1, one_ne_zero, ?_⟩
    intro word
    rw [hq, one_smul]
    induction word with
    | nil => rfl
    | cons i word ih => simp only [derivationWordAction_cons, ih, map_zero]

end Polynomial

end CollisionIdeals
