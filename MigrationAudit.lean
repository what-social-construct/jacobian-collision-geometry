module

import CollisionIdeals.ComplexThree.Cubic.Canonical
import CollisionIdeals.Palomar.PaperOne.Solution

/-! Downstream visibility and axiom audit for the isolated Lean 4.35 migration. -/

#check CollisionIdeals.complexThreeGenericDegreeThreeS3Collision
#check CollisionIdeals.complexThree_counterexample_iff_keller_of_finrank_eq_three
#check CollisionIdeals.Palomar.PaperOne.genericDegreeThreeS3Collision

#print axioms CollisionIdeals.complexThreeGenericDegreeThreeS3Collision
#print axioms CollisionIdeals.complexThree_counterexample_iff_keller_of_finrank_eq_three
#print axioms CollisionIdeals.Palomar.PaperOne.genericDegreeThreeS3Collision
