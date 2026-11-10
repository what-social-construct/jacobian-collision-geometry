import CollisionIdeals.General.Normalization.DerivationAnnihilator
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite stages preserved by polynomial-coordinate Leibniz operators

An invariant finite submodule of a torsion module inherits the existing
coordinate Leibniz action, so the polynomial annihilator theorem makes
that submodule zero. A finite subspace over the coefficient field also
supplies such a stage: take its standard span over the polynomial base.

These are conditional stage engines. They do not construct a finite
preserved stage in any particular boundary quotient, and require no
commutation of the additive operators.
-/

set_option autoImplicit false

namespace CollisionIdeals

section Span

variable {σ k B M : Type*} [CommRing k] [CommRing B] [Algebra k B]
  [AddCommMonoid M] [Module B M]

/-- To preserve the base-module span, it suffices to preserve its
generators modulo that same span. Scalar combinations use Leibniz,
not base-linearity of the operators. -/
theorem leibniz_operator_mem_span_of_generator_mem
    (d : σ → Derivation k B B) (nabla : σ → M →+ M)
    (hLeibniz : ∀ (i : σ) (b : B) (m : M),
      nabla i (b • m) = d i b • m + b • nabla i m)
    (s : Set M)
    (hGenerators : ∀ (i : σ) (m : M), m ∈ s →
      nabla i m ∈ Submodule.span B s)
    (i : σ) {m : M} (hm : m ∈ Submodule.span B s) :
    nabla i m ∈ Submodule.span B s := by
  induction hm using Submodule.span_induction with
  | mem x hx => exact hGenerators i x hx
  | zero => simpa only [map_zero] using (Submodule.span B s).zero_mem
  | add x y _ _ hx hy =>
      rw [map_add]
      exact (Submodule.span B s).add_mem hx hy
  | smul b x hx ih =>
      rw [hLeibniz]
      exact (Submodule.span B s).add_mem
        ((Submodule.span B s).smul_mem _ hx)
        ((Submodule.span B s).smul_mem _ ih)

end Span

section Polynomial

variable {σ k B M : Type*} [Field k] [CharZero k] [CommRing B] [Algebra k B]
  [AddCommMonoid M] [Module B M]

/-- A finite submodule preserved by all polynomial-coordinate Leibniz
operators is zero when its ambient module is torsion. Stability is
explicit; it does not follow from finite generation alone. -/
theorem subsingleton_finite_stable_submodule_of_polynomial_leibniz
    (e : MvPolynomial σ k ≃ₐ[k] B) (nabla : σ → M →+ M)
    (hLeibniz : ∀ (i : σ) (b : B) (m : M),
      nabla i (b • m) = polynomialEquivPartial e i b • m + b • nabla i m)
    (S : Submodule B M) [Module.Finite B S]
    (hStable : ∀ (i : σ) (m : M), m ∈ S → nabla i m ∈ S)
    (hTorsion : Module.IsTorsion B M) : Subsingleton S := by
  let nablaS : σ → S →+ S := fun i =>
    { toFun := fun m => ⟨nabla i m, hStable i m m.property⟩
      map_zero' := Subtype.ext (map_zero (nabla i))
      map_add' := fun x y => Subtype.ext (map_add (nabla i) (x : M) (y : M)) }
  have hLeibnizS : ∀ (i : σ) (b : B) (m : S),
      nablaS i (b • m) = polynomialEquivPartial e i b • m + b • nablaS i m := by
    intro i b m
    apply Subtype.ext
    exact hLeibniz i b m
  have hTorsionS : Module.IsTorsion B S := by
    intro m
    obtain ⟨a, ha⟩ := hTorsion (x := (m : M))
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact ha
  exact subsingleton_of_finite_torsion_of_polynomial_leibniz
    e nablaS hLeibnizS hTorsionS

/-- Every ambient element of such a finite preserved stage is zero. -/
theorem eq_zero_of_mem_finite_stable_submodule
    (e : MvPolynomial σ k ≃ₐ[k] B) (nabla : σ → M →+ M)
    (hLeibniz : ∀ (i : σ) (b : B) (m : M),
      nabla i (b • m) = polynomialEquivPartial e i b • m + b • nabla i m)
    (S : Submodule B M) [Module.Finite B S]
    (hStable : ∀ (i : σ) (m : M), m ∈ S → nabla i m ∈ S)
    (hTorsion : Module.IsTorsion B M) {q : M} (hq : q ∈ S) : q = 0 := by
  letI : Subsingleton S :=
    subsingleton_finite_stable_submodule_of_polynomial_leibniz
      e nabla hLeibniz S hStable hTorsion
  exact congrArg (fun m : S => (m : M))
    (show (⟨q, hq⟩ : S) = 0 from Subsingleton.elim _ _)

end Polynomial

section CoefficientSubspace

variable {σ k B M : Type*} [Field k] [CharZero k] [CommRing B] [Algebra k B]
  [AddCommMonoid M] [Module B M] [Module k M] [IsScalarTower k B M]

/-- A coefficient-field finite subspace, preserved by all frame
operators, generates a finite preserved base-module stage. Its elements
therefore vanish in any torsion module with the polynomial Leibniz action.
No finite generation of the whole ambient module is assumed. -/
theorem eq_zero_of_mem_finite_stable_coefficient_subspace
    (e : MvPolynomial σ k ≃ₐ[k] B) (nabla : σ → M →+ M)
    (hLeibniz : ∀ (i : σ) (b : B) (m : M),
      nabla i (b • m) = polynomialEquivPartial e i b • m + b • nabla i m)
    (V : Submodule k M) [Module.Finite k V]
    (hStable : ∀ (i : σ) (m : M), m ∈ V → nabla i m ∈ V)
    (hTorsion : Module.IsTorsion B M) {q : M} (hq : q ∈ V) : q = 0 := by
  let S : Submodule B M := Submodule.span B (V : Set M)
  have hVfg : V.FG := Module.Finite.iff_fg.mp inferInstance
  letI : Module.Finite B S := Module.Finite.of_fg hVfg.span
  have hSStable : ∀ (i : σ) (m : M), m ∈ S → nabla i m ∈ S := by
    intro i m hm
    exact leibniz_operator_mem_span_of_generator_mem
      (fun i => polynomialEquivPartial e i) nabla hLeibniz (V : Set M)
      (fun i m hm => Submodule.subset_span (hStable i m hm)) i hm
  exact eq_zero_of_mem_finite_stable_submodule
    e nabla hLeibniz S hSStable hTorsion (Submodule.subset_span hq)

end CoefficientSubspace

section Lift

variable {σ k B M E N : Type*} [Field k] [CharZero k]
  [CommRing B] [Algebra k B]
  [AddCommMonoid M] [Module B M] [Module k M] [IsScalarTower k B M]
  [AddCommGroup E] [Module k E] [AddCommGroup N] [Module k N]

/-- A finite preserved subspace in an ambient coefficient-field module
can be pulled back through an injective lift and then mapped into the
torsion quotient. The image is a finite stable coefficient subspace,
so the existing polynomial annihilator argument kills its elements.

The injection and both operator compatibilities are explicit. No
finiteness of the ambient lift or of the whole quotient is required. -/
theorem eq_zero_of_mem_finite_stable_lift
    (e : MvPolynomial σ k ≃ₐ[k] B) (nabla : σ → M →+ M)
    (hLeibniz : ∀ (i : σ) (b : B) (m : M),
      nabla i (b • m) = polynomialEquivPartial e i b • m + b • nabla i m)
    (hTorsion : Module.IsTorsion B M)
    (ι : E →ₗ[k] N) (hι : Function.Injective ι) (π : E →ₗ[k] M)
    (dE : σ → E →+ E) (dN : σ → N →+ N)
    (hLift : ∀ (i : σ) (r : E), ι (dE i r) = dN i (ι r))
    (hQuotient : ∀ (i : σ) (r : E), π (dE i r) = nabla i (π r))
    (U : Submodule k N) [Module.Finite k U]
    (hStable : ∀ (i : σ) (n : N), n ∈ U → dN i n ∈ U)
    (r : E) (hr : ι r ∈ U) : π r = 0 := by
  let Vpre : Submodule k E := U.comap ι
  let pullToU : Vpre →ₗ[k] U :=
    (ι.comp Vpre.subtype).codRestrict U (fun x => x.property)
  have hPull : Function.Injective pullToU := by
    intro x y hxy
    apply Subtype.ext
    apply hι
    exact congrArg (fun z : U => (z : N)) hxy
  letI : Module.Finite k Vpre := FiniteDimensional.of_injective pullToU hPull
  let V : Submodule k M := Vpre.map π
  letI : Module.Finite k V := inferInstanceAs (Module.Finite k (Vpre.map π))
  have hVStable : ∀ (i : σ) (m : M), m ∈ V → nabla i m ∈ V := by
    intro i m hm
    obtain ⟨x, hx, rfl⟩ := hm
    refine Submodule.mem_map.mpr ⟨dE i x, ?_, hQuotient i x⟩
    change ι (dE i x) ∈ U
    rw [hLift]
    exact hStable i (ι x) hx
  exact eq_zero_of_mem_finite_stable_coefficient_subspace
    e nabla hLeibniz V hVStable hTorsion
    (Submodule.mem_map.mpr ⟨r, hr, rfl⟩)

end Lift

end CollisionIdeals
