import CollisionIdeals.Planar.Research.PrincipalPartsStrategy
import CollisionIdeals.Planar.Research.FixedMovingBoundaryPrincipalParts
import CollisionIdeals.Planar.Research.FinitePrincipalPartsControl
import CollisionIdeals.Planar.ConjugateSecantEvaluation
import CollisionIdeals.Planar.ExplicitSecant
import CollisionIdeals.Planar.KellerFrame
import CollisionIdeals.Planar.Research.SecantFrameDenominator
import CollisionIdeals.Planar.Research.MonogenicOrder
import CollisionIdeals.Planar.Research.MonogenicTraceDual
import CollisionIdeals.Planar.Research.TateReconstruction
import CollisionIdeals.Planar.Research.MonogenicLanding
import CollisionIdeals.Planar.Research.TraceLanding
import CollisionIdeals.Planar.Research.CompletedTameRamification

/-!
# Prospective planar rigidity mechanisms

This umbrella preserves the experimental modules behind the archived boundary manuscript's
two-statements/one-morphism reduction without placing them in the stable
`CollisionIdeals.Planar` import spine:

* a hidden fixed--moving divisor produces an unbounded DVR pole tower;
* the generic trace-integral carrier is Mathlib's trace dual; its concrete
  finite, locally bounded planar specialization remains separate;
* explicit divided differences and the polynomial Keller frame supply a
  canonical finite coefficient package with a nonzero denominator ideal;
* a chosen integral primitive generator for the secant--trace comparison uses
  Mathlib's monogenic order, power basis, hypersurface presentation, Jacobian
  element, and conductor directly;
* finite Tate reconstruction and the generic monogenic/overorder
  trace-dual--conductor identities are proved;
* the monogenic conductor stage and its actual transporter ideal are defined,
  a generic normal-Noetherian finite-overring collapse is proved, and an
  explicit pointwise pole witness plus a nonzero landing candidate is proved
  to imply boundary separation and the existing planar endgame;
* independently of the monogenic comparison, the trace-integral dual and its
  transporter are specialized to the normalization diagram, and a supplied
  nonzero trace-landing candidate plus the pointwise pole witness is wired
  directly to boundary separation and collision vanishing;
* the missing Keller-specific theorem says that this prescribed ideal is
  contained in the trace transporter for the whole pole tower.

The last item is not packaged as another abstract bridge here.  Constructing
it is the research problem, while the stable planar API begins only after the
height-one premise has been established.
-/
