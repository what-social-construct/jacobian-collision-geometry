module

/-
SPDX-License-Identifier: Apache-2.0

Adapted from AxiomMath/Stacks, StacksCore/FieldTheory/Normal/Closure.lean,
`IsNormalClosure.finiteDimensional` (Stacks Project tag 09DT), at commit
f8e70c5dd04bfabcb423d5e325461f527c85a5d6:
https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksCore/FieldTheory/Normal/Closure.lean#L204

The proof is adapted to the project's Mathlib version by using its existing
finite-dimensional instance for relative normal closures.
The accompanying AXIOM-STACKS-LICENSE contains the upstream license.
-/

public import Mathlib.FieldTheory.Normal.Closure

@[expose] public section

/-!
# Finiteness of a supplied normal closure

A normal closure of a finite extension is finite over the base, independently
of the chosen realization of that closure.
-/

set_option autoImplicit false

namespace CollisionIdeals

/-- Any supplied normal closure of a finite field extension is finite. -/
theorem finiteDimensional_of_isNormalClosure
    (K L N : Type*) [Field K] [Field L] [Field N]
    [Algebra K L] [Algebra K N] [FiniteDimensional K L]
    (hclosure : IsNormalClosure K L N) : FiniteDimensional K N := by
  have htop : IntermediateField.normalClosure K L N = ⊤ :=
    ((Algebra.IsAlgebraic.isNormalClosure_iff (F := K) (K := L) (L := N)).mp
      hclosure).2
  haveI : FiniteDimensional K (⊤ : IntermediateField K N) := by
    rw [← htop]
    infer_instance
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end CollisionIdeals
