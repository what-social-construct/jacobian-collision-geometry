import CollisionIdeals.Planar.Basic
import CollisionIdeals.Planar.ExplicitSecant
import CollisionIdeals.Planar.GenericDegreeTwo
import CollisionIdeals.Planar.Statements
import CollisionIdeals.Planar.Equivalences

/-!
# Planar collision geometry

The public planar import exposes the stable secant construction, the standard
Jacobian-conjecture statements, and the generic-degree-two rigidity theorem.
The full planar-vanishing research program remains available
through its precise modules and the separate `CollisionIdeals.Planar.Research`
umbrella, but is not part of this focused import spine. Its goal is the existing
`PlanarVanishing` statement, with the proof spine and object bench indexed in
`Planar/Research/Vanishing/README.md`.
-/
