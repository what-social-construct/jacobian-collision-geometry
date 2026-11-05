import CollisionIdeals.ComplexThree.Cubic.NormalBranch
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Connected.Clopen
import Mathlib.Data.List.TFAE

/-!
# Cubic residual criteria

Fieldness, irreducibility, and connectedness characterize the nonnormal
branch of a separable cubic extension. The normal branch is split. All
criteria concern the existing residual algebra and marked generator.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

open Polynomial

universe u v

variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]

/-- The residual conjugate algebra is a field exactly when its defining
polynomial is irreducible. This criterion does not require the Keller condition. -/
theorem isField_cubicResidualAlgebra_iff_irreducible (pb : PowerBasis K L) :
    IsField (CubicResidualAlgebra K L pb) ↔
      Irreducible (minpolyDiv K pb.gen) := by
  constructor
  · intro h
    have hmax :
        (Ideal.span ({minpolyDiv K pb.gen} : Set L[X])).IsMaximal :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr h
    exact ((Ideal.span_singleton_prime
      (minpolyDiv_monic pb.isIntegral_gen).ne_zero).mp hmax.isPrime).irreducible
  · intro h
    letI : Fact (Irreducible (minpolyDiv K pb.gen)) := ⟨h⟩
    exact Field.toIsField _

/-- A residual field has connected spectrum. -/
theorem connectedSpace_cubicResidualAlgebra_of_isField
    (pb : PowerBasis K L) (h : IsField (CubicResidualAlgebra K L pb)) :
    ConnectedSpace (PrimeSpectrum (CubicResidualAlgebra K L pb)) := by
  letI : IsDomain (CubicResidualAlgebra K L pb) := h.isDomain
  infer_instance

private theorem not_connectedSpace_sum
    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] [Nonempty Y] : ¬ ConnectedSpace (X ⊕ Y) := by
  intro h
  letI := h
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨y⟩ := ‹Nonempty Y›
  have heq : Set.range (Sum.inl : X → X ⊕ Y) = Set.univ :=
    isClopen_range_inl.eq_univ ⟨Sum.inl x, ⟨x, rfl⟩⟩
  have hmem : Sum.inr y ∈ Set.range (Sum.inl : X → X ⊕ Y) := by
    rw [heq]
    trivial
  simp at hmem

/-- A split residual quadratic has disconnected spectrum: the two factors
give two nonempty clopen components. -/
theorem not_connectedSpace_cubicResidualAlgebra_of_equiv_prod
    (pb : PowerBasis K L) (e : CubicResidualAlgebra K L pb ≃ₐ[L] L × L) :
    ¬ ConnectedSpace (PrimeSpectrum (CubicResidualAlgebra K L pb)) := by
  intro h
  letI := h
  let eh := (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).trans
    (PrimeSpectrum.primeSpectrumProdHomeo (R := L) (S := L))
  haveI : ConnectedSpace (PrimeSpectrum L ⊕ PrimeSpectrum L) :=
    eh.surjective.connectedSpace eh.continuous
  exact not_connectedSpace_sum (PrimeSpectrum L) (PrimeSpectrum L) inferInstance

section SeparableCubic

variable [Algebra.IsSeparable K L]

/-- The cubic residual algebra is a field exactly in the nonnormal branch. -/
theorem isField_cubicResidualAlgebra_iff_not_normal
    (pb : PowerBasis K L) (hdegree : pb.dim = 3) :
    IsField (CubicResidualAlgebra K L pb) ↔ ¬ Normal K L :=
  (isField_cubicResidualAlgebra_iff_irreducible K L pb).trans
    (irreducible_minpolyDiv_iff_not_normal K L pb hdegree)

/-- Connectedness detects the nonnormal branch of a separable cubic extension. -/
theorem connectedSpace_cubicResidualAlgebra_iff_not_normal
    (pb : PowerBasis K L) (hdegree : pb.dim = 3) :
    ConnectedSpace (PrimeSpectrum (CubicResidualAlgebra K L pb)) ↔
      ¬ Normal K L := by
  constructor
  · intro hconnected hnormal
    exact not_connectedSpace_cubicResidualAlgebra_of_equiv_prod K L pb
      (cubicResidualEquivProdOfNormal K L pb hdegree hnormal) hconnected
  · intro hnormal
    exact connectedSpace_cubicResidualAlgebra_of_isField K L pb
      ((isField_cubicResidualAlgebra_iff_not_normal K L pb hdegree).mpr hnormal)

/-- A cubic residual spectrum is connected exactly when its algebra is a field. -/
theorem connectedSpace_cubicResidualAlgebra_iff_isField
    (pb : PowerBasis K L) (hdegree : pb.dim = 3) :
    ConnectedSpace (PrimeSpectrum (CubicResidualAlgebra K L pb)) ↔
      IsField (CubicResidualAlgebra K L pb) :=
  (connectedSpace_cubicResidualAlgebra_iff_not_normal K L pb hdegree).trans
    (isField_cubicResidualAlgebra_iff_not_normal K L pb hdegree).symm

/-- The four equivalent conditions of the manuscript's connected cubic residual
factor proposition, with the same residual algebra and marked generator. -/
theorem cubicResidual_tfae
    (pb : PowerBasis K L) (hdegree : pb.dim = 3) :
    List.TFAE [
      ConnectedSpace (PrimeSpectrum (CubicResidualAlgebra K L pb)),
      IsField (CubicResidualAlgebra K L pb),
      Irreducible (minpolyDiv K pb.gen),
      ¬ Normal K L] := by
  simp only [List.tfae_cons_cons, List.tfae_singleton, and_true]
  exact ⟨connectedSpace_cubicResidualAlgebra_iff_isField K L pb hdegree,
    isField_cubicResidualAlgebra_iff_irreducible K L pb,
    irreducible_minpolyDiv_iff_not_normal K L pb hdegree⟩

end SeparableCubic

end

end CollisionIdeals
