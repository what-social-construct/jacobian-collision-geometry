import CollisionIdeals.General.Normalization.BaseTransversality
import CollisionIdeals.General.Normalization.SimplePole
import CollisionIdeals.General.Normalization.ConormalDerivation
import CollisionIdeals.General.Normalization.DerivationAnnihilator
import CollisionIdeals.General.Galois.ConjugateAlgebra
import CollisionIdeals.General.Galois.ConjugateFractionField
import CollisionIdeals.General.Galois.ConjugateInvariants
import CollisionIdeals.General.Galois.ConjugateInvariantField
import CollisionIdeals.General.Keller.ConjugateUnramified
import CollisionIdeals.General.Keller.ConjugateInvariantOpen
import CollisionIdeals.General.Keller.ConjugateInvariantBoundary
import CollisionIdeals.General.Keller.ConjugateInvariantSections
import CollisionIdeals.General.Keller.ConjugateInvariantNormalizationQuotient
import CollisionIdeals.General.Keller.ConjugateInvariantConormal
import CollisionIdeals.General.Keller.ConjugateInvariantFiniteness
import CollisionIdeals.General.Normalization.DerivationCriterion
import CollisionIdeals.General.Keller.DivisorVisibility
import CollisionIdeals.General.Keller.SourceIntersection
import CollisionIdeals.General.Keller.ConjugateInvariantSource
import CollisionIdeals.General.Keller.ConjugateInvariantCriterion
import CollisionIdeals.General.Keller.MonomialWeights
import CollisionIdeals.General.Normalization.VisibleConjugateCenter
import CollisionIdeals.Planar.Research.Vanishing.BaseFrame
import CollisionIdeals.Planar.Research.Vanishing.CyclicStage
import CollisionIdeals.Planar.Research.Vanishing.DifferentialOrbit
import CollisionIdeals.Planar.Research.Vanishing.TotalDegreeTwoStage
import CollisionIdeals.General.Normalization.FractionalNormalization
import CollisionIdeals.General.Normalization.DerivationFractionalStage
import CollisionIdeals.General.Normalization.TransversePoleStep
import CollisionIdeals.Planar.Research.Vanishing.FrameDenominator
import CollisionIdeals.Planar.Research.Vanishing.SecantReduction
import CollisionIdeals.Planar.Research.Vanishing.ConductorComparison
import CollisionIdeals.Planar.Research.Vanishing.ConductorLocalization
import CollisionIdeals.Planar.Research.Vanishing.GeneratorDerivative
import CollisionIdeals.Planar.Research.Vanishing.LocalizedJacobianDiagnostic
import CollisionIdeals.Planar.Research.Vanishing.LocalCollision
import CollisionIdeals.Planar.Research.Vanishing.InertiaCoordinates
import CollisionIdeals.Planar.Research.Vanishing.PolarCancellation
import CollisionIdeals.Planar.Research.Vanishing.BoundaryInitialResidue
import CollisionIdeals.Planar.Research.Vanishing.WeightedJacobian
import CollisionIdeals.Planar.Research.Vanishing.LeadingFaceDiagnostic
import CollisionIdeals.Planar.Research.Vanishing.CancellationBudget
import CollisionIdeals.Planar.Research.Vanishing.TwoSidedCancellation
import CollisionIdeals.Planar.Research.Vanishing.OppositeDegreeExclusion
import CollisionIdeals.Planar.Research.Vanishing.GaloisDescent
import CollisionIdeals.Planar.Research.Vanishing.Ramification
import CollisionIdeals.Planar.Research.Vanishing.GaloisRigidity
import CollisionIdeals.Planar.Research.Vanishing.FiniteBoundary
import CollisionIdeals.Planar.Research.Vanishing.BoundaryCriterion
import CollisionIdeals.Planar.Research.PrincipalPartsStrategy
import CollisionIdeals.Planar.Research.TraceStageAudit
import CollisionIdeals.Planar.Research.FixedMovingBoundaryPrincipalParts
import CollisionIdeals.Planar.Research.FinitePrincipalPartsControl
import CollisionIdeals.Planar.ConjugateSecantEvaluation
import CollisionIdeals.Planar.ExplicitSecant
import CollisionIdeals.Planar.Research.EvaluatedProjector
import CollisionIdeals.Planar.Research.ConjugateFixedLocus
import CollisionIdeals.Planar.Research.ConjugateCover
import CollisionIdeals.General.Keller.ConjugateSourceBaseChange
import CollisionIdeals.Planar.Research.Vanishing.ConjugateNormalizationOpen
import CollisionIdeals.General.Keller.ConjugateInvariantPole
import CollisionIdeals.Planar.Research.Vanishing.InvariantNormalizationBaseChange
import CollisionIdeals.Planar.Research.Vanishing.ConjugateCommonOpen
import CollisionIdeals.Planar.Research.Vanishing.TargetPoleTower
import CollisionIdeals.Planar.Research.Vanishing.TargetFiniteStage
import CollisionIdeals.Planar.Research.Vanishing.CollisionFrameRelations
import CollisionIdeals.Planar.Research.Vanishing.RelationReductionControl
import CollisionIdeals.Planar.Research.Vanishing.TargetBoundaryRegularPair
import CollisionIdeals.Planar.Research.Vanishing.VisibleSourcePole
import CollisionIdeals.Planar.KellerFrame
import CollisionIdeals.Planar.Research.SecantFrameDenominator
import CollisionIdeals.Planar.Research.FiniteDenominatorCounterexample
import CollisionIdeals.Planar.Research.KellerFrameExtension
import CollisionIdeals.Planar.Research.InvariantQuotientAction
import CollisionIdeals.Planar.Research.BoundarySections
import CollisionIdeals.Planar.Research.BoundaryMultiplierComparison
import CollisionIdeals.Planar.Research.BoundarySectionLocalization
import CollisionIdeals.Planar.Research.LocalizationDenominator
import CollisionIdeals.Planar.Research.HeightOneBoundaryPole
import CollisionIdeals.Planar.Research.NormalizationTraceBound
import CollisionIdeals.Planar.Research.BoundaryPoleWitness
import CollisionIdeals.Planar.Research.SecantFrameCandidate
import CollisionIdeals.Planar.Research.MonogenicOrder
import CollisionIdeals.Planar.Research.MonogenicTraceDual
import CollisionIdeals.Planar.Research.TateReconstruction
import CollisionIdeals.Planar.Research.MonogenicLanding
import CollisionIdeals.Planar.Research.TraceLanding
import CollisionIdeals.Planar.Research.SecantFrameTraceLanding
import CollisionIdeals.Planar.Research.CompletedTameRamification

/-!
# Planar vanishing research

The central research target is the existing `CollisionIdeals.PlanarVanishing`:
the collision obstruction vanishes for every planar Keller map. The current
findings characterize conjugate-coordinate descent and empty target boundary,
with their conditional rigidity consequences. They do not prove either
condition universally. Divisorial unramifiedness, boundary/trace landing, and
finite derivative lattices remain research alternatives. The full target has
no generic-degree restriction.

`Planar/Research/Vanishing/README.md` indexes the primary proof spine and the
object bench. The spine records the missing planar implication and the
conditional endgame; the bench records what each construction contributes,
alternative routes, and negative controls. Existing definitions and import
paths are retained rather than duplicated for the research organization.

This umbrella keeps the experimental modules separate from the public
`CollisionIdeals.Planar` import spine. The available work includes:

* the actual algebra generated by all conjugate source coordinates is
  constructed over the coordinate-image base; it contains every conjugate
  polynomial sheet, is Galois-stable, has finite type, and has the supplied
  normal closure as its fraction field. The restricted action and fixed
  algebra use Mathlib's existing invariant-ring objects; the algebra is
  module-finite over its fixed algebra, not necessarily over the
  coordinate-image base;
* the canonical explicit off-diagonal projector evaluates to zero on
  identical collision sheets and one on distinct sheets in a domain.
  Applied in the actual all-conjugate algebra of a planar Keller map,
  these identities make the difference ideal of every nonidentity Galois
  element the unit ideal. Its scheme-theoretic fixed quotient is the zero
  ring, and the existing inertia subgroup is trivial at every proper ideal
  of that algebra. These certificates feed a Chinese-remainder graph
  comparison and a finite trace-dual frame. The all-conjugate algebra is
  finite etale and faithfully flat over its existing fixed algebra, and
  the canonical action-graph tensor map is an algebra equivalence.
  This is an affine algebraic torsor certificate, not a bundled
  scheme-level torsor object. It does not exclude setwise-stable primes,
  fill the target open, or eliminate omitted-boundary inertia;
* under separability the fixed algebra is realized
  inside the target function field and has that field as its fraction
  field. The Keller condition makes the all-conjugate algebra unramified
  over the coordinate-image base. Artin--Tate, quasi-finite descent, and
  birational Zariski main now identify the fixed algebra's spectrum with
  an actual affine target open. Its reduced boundary ideal is constructed,
  radical, nonzero, and finitely generated. A principal presentation is not
  yet packaged; boundary emptiness is not inferred;
* the same fixed algebra is canonically the section algebra of that actual
  target open, over the original base. The induced module quotients by the
  base image are equivalent. The fixed-algebra quotient is torsion and
  vanishes exactly when the actual target boundary is empty. This supplies
  neither a uniform annihilator nor a comparison with filtered-Ext local
  cohomology;
* an alternative boundary criterion uses two components of Mathlib's existing
  conormal module. Their vanishing is equivalent to ideal preservation,
  hence to the unit ideal over a characteristic-zero polynomial base. The
  actual boundary criterion now identifies componentwise vanishing with
  the target open being the whole target, without a principal presentation.
  Any finite ideal generating set gives a finite first-derivative test.
  Empty target boundary implies actual source finiteness, which fills the
  intermediate normalization and reaches the existing planar endpoint with
  purity and finite-etale rigidity explicit, without custom-axiom imports
  in the new conditional endpoint module.
  The reverse implication follows directly from vanishing collision
  equations: all conjugate source coordinates coincide. Thus actual
  target-boundary emptiness, fixed-algebra source regularity, and conormal
  vanishing are equivalent to collision-obstruction vanishing, with only
  the two geometric inputs above. No Ax--Grothendieck or Keller--Galois
  rigidity input is needed for that boundary characterization.
  Actual Keller-specific conormal vanishing remains open;
* a regular pair in the actual target-boundary ideal excludes the
  height-one prime extracted from a nonzero invariant quotient class.
  The resulting quotient-vanishing implication is conditional on the
  pair. A separate algebraic diagnostic proves that a principal ideal
  containing such a pair has a unit generator. The affine-open/UFD
  argument identifying the actual boundary as principal is recorded in
  the source ledger, not yet packaged in Lean; choosing two existing
  boundary generators does not construct the missing pair;
* native diagonal evaluation kills the same-image relation ideal, so an
  inverse relation modulo that ideal already inverts the marked source
  polynomial. An inverse of a source nonunit in the actual conjugate
  algebra would therefore require additional marked-kernel relations.
  This restricts inverse certificates, not all finite derivative
  reductions modulo the same-image ideal;
* the original polar invariant representative remains polar at a
  constructed visible source divisor over the same target prime. The
  numerator is a unit and the denominator lies in the source-local
  maximal ideal. The original coefficient identity transports through
  K into L; neither faithful-flatness input nor source regularity is
  assumed. Foreign conjugate coordinates need not lie in L, so this
  does not evaluate the mixed-sheet expression term by term in that
  source localization or prove its poles cancel;
* visible source divisors imply divisibility reflection and the classical
  source/base-field intersection property. A fixed-algebra element regular
  on the marked polynomial source therefore belongs to the target base.
  Thus the fixed algebra meets the marked source exactly in the base.
  Regularity of every fixed element on that source is equivalent to
  surjectivity of the canonical base map and to the actual boundary ideal
  being the unit ideal. The criterion uses the existing embeddings and
  asserts neither source regularity nor empty boundary for every map;
* a derivation regular in the actual prime localization and transverse to
  a base element forces local index one, hence unramifiedness at a DVR prime
  with separable residue extension;
* every nonzero proper polynomial ideal in characteristic zero has a
  transverse coordinate partial; the actual Keller frames recover target
  partial derivatives on arbitrary target polynomials, also after extension
  to the normal closure. Regularity at a boundary prime is not supplied;
* additive operators satisfying the target-coordinate Leibniz rules preserve
  the module annihilator under every target partial. In a characteristic-zero
  polynomial algebra, a nonzero annihilator therefore forces the module to
  vanish. The existing normal-closure Keller frames preserve the actual
  fixed algebra and descend to additive operators on its standard module
  quotient by the target base. Their target-coordinate Leibniz rules are
  proved, with no operator-existence or frame-preservation premise.
  An arbitrary-degree preserved finite stage or uniform annihilator is
  not constructed;
* the same quotient now has a differential-word denominator test. One
  scalar annihilating the entire orbit is equivalent to vanishing of
  the class. More sharply, a fixed target-polynomial denominator clearing
  words through its own total degree already forces vanishing. Ordinary
  torsion gives only powers `a^(r+1)` at derivative order `r`, not that
  degree threshold or an all-orders uniform bound;
* in total polynomial degree at most two, finite preserved stages are now
  constructed in the actual quotient. The ground-polynomial presentation
  uses the same finite conjugate-coordinate family and original algebra.
  Affine frame generator values preserve finite coefficient-field degree
  stages; invariant pullback and quotient image then give a finite
  preserved base-module stage. The annihilator argument proves every
  class zero. This is a total-degree benchmark, not the generic-degree-two
  result or a stage bound for arbitrary planar maps;
* the original polynomial source, base changed to the same invariant
  algebra, embeds in the all-conjugate algebra and is finite over that
  invariant base. Keller étaleness persists under this base change. This
  comparison is dimension-independent and belongs to the general folder;
* in the planar construction, stalk isomorphisms prove normality of the
  invariant target open. The existing finite trace frame then proves
  normality of the all-conjugate algebra and puts the original finite
  normalization inside it. The resulting scheme map is an open immersion
  over the original target. This is the inclusion `T` into `E`, not
  containment of a Keller orbit in a fixed fractional `T`-stage;
* a hypothetical nonzero class in the original invariant quotient now
  constructs a target height-one boundary point, its DVR, and a polar
  invariant representative. Reduced numerator/denominator data supply
  the point; no boundary divisor is supplied separately. This target
  pole does not assert ramification or nontrivial inertia;
* the all-conjugate open is canonically the finite normalization over
  the existing invariant target open. The actual pullback comparison is
  an isomorphism, compatible with both projections. This identifies the
  omitted normalization points with the inverse image of the target
  boundary. Membership is equivalent to regularity of every conjugate
  coordinate in the same normalization local ring; outside this open,
  one coordinate is nonregular. No ramification or differential-orbit
  bound is asserted;
* at the constructed target DVR, a target-coordinate partial and a
  transverse parameter are derived from the polynomial base. The polar
  representative has a unit numerator over a positive power of that
  parameter. Its successive derivatives have unit numerators and
  denominator exponents increasing by one; each stays outside that same
  local ring. The canonical field partial agrees with the original
  invariant Keller frame at every order. This proves the pole-growth
  calculation, not containment in a fixed finite stage;
* the same selected invariant-frame ray eventually escapes every fixed
  finite base submodule of the original normal closure, even modulo
  base additions. A common local denominator constructs a pole-order
  bound for each stage; the exact increasing pole orders violate that
  bound. Pullback along the original field inclusion transfers the test
  to the target field. Every fixed scalar image of the original finite
  normalization is covered. This is a conditional escape certificate,
  not the missing Keller-specific upper bound or planar vanishing;
* the actual lifted polynomial frame kills each mixed-sheet same-image
  relation exactly. Their generated ideal lies in the existing evaluation
  kernel, and both ideals are preserved by the frame. No equality of
  those two ideals or replacement presentation of `E` is assumed;
* target-polynomial degree stages are preserved by the actual source
  Keller frames in arbitrary total degree. For the existing degree-four
  automorphism control, explicit division-free collision certificates
  recover the source coordinates and put every frame word on them in
  one finite target-degree-four stage. This is a concrete positive
  control, not a reduction of arbitrary mixed-sheet invariant elements;
* fixed fractional images of the actual finite normalization are finite
  base modules and have a common valuation bound, also modulo the base.
  A regular transverse derivative at a supplied target local ring
  constructs unit numerators at every successive pole order. The exact
  quotient rule explains why one-step denominator clearing gives growing
  stages, not a fixed one. Containment of the actual Keller orbit in one
  finite image remains unproved; preserving the whole shifted lattice is
  stronger and is obstructed by its basic denominator element;
* the concrete cyclic finite stage of a nonzero quotient class is not
  preserved by both coordinate operators: one derivative escapes its span.
  The older trace-integral stage also supplies no nonzero target-field
  class when the normal-closure degree is a base unit, as it is over a
  characteristic-zero field algebra. These are candidate tests, not a
  finite-stage construction or a planar-vanishing theorem;
* preserving the cyclic simple-pole module with denominator `s` is
  equivalent to preserving the principal ideal `(s)`. This tests a proposed
  boundary invariant; finite clearing of secant first jets does not prove
  its preservation or identify their denominator with the reduced boundary;
* clearing a derivation on finite module generators clears the whole order
  by Leibniz, without incorrectly treating the frame as base-linear;
* in dimension two the adjugate and its first jets add no generators to the
  evaluated secant lattice and do not change its denominator ideal;
* control of a monogenic generator gives a conductor-multiplied comparison
  for all normalization derivatives. Once a conductor element is inverted,
  generator control is equivalent to control of all derivatives;
* differentiating the generator's minimal polynomial retains the varying
  base coefficients and identifies the exact missing divisibility by the
  monogenic Jacobian. Separability gives nonzero Jacobian, not local
  invertibility or the required divisibility;
* the actual polynomial source reflects units from its coordinate-image
  base. Keller flatness and factorization produce a visible unramified
  source divisor over every height-one base prime; this is existence of one
  sheet, not unramifiedness of every normal-closure sheet;
* lying-over and Galois transitivity realize that source divisor as an
  actual conjugate center. With the supplied local-index realization, its
  sheet is fixed by inertia; this does not make inertia trivial;
* two local Keller collision maps with equal coordinate residues coincide.
  Applied directly to valuation inertia, this forces a nonregular source
  coordinate on every inertia-moved sheet, without an index realization.
  At a supplied actual ramified divisor, centeredness and core-freeness
  now give a moved sheet with two distinct equally dominant polar terms
  in one component's polynomial support. This finite cancellation
  certificate assumes no source regularity; excluding the resonance by
  the full constant-Jacobian identity in general remains open. A signed
  weighted-component calculation now gives its exact leading Jacobian:
  the Keller constant in the balanced degree, zero off that balance.
  Signed Euler excludes balanced common zeros with nonzero weighted
  radial vector, also over coefficient-field extensions. An actual
  polynomial automorphism supplies a strict-degree negative control:
  both leading forms cancel, while a lower polar output remains.
  Reusing the earlier frame calculus now bounds a supplied leading-power
  cancellation by the weighted Jacobian defect. The actual residual is
  proved nonzero and its sharp degree is derived, including negative
  degrees. Exponent-one target subtraction preserves Keller and the
  same image range, and strictly decreases a nonnegative defect; no
  further legal step or general power-map Keller property is assumed.
  The actual boundary DVR now supplies signed coordinate weights and
  nonzero initial residues on the same moved sheet. Every positive-degree
  target initial form vanishes at that tuple. Both target-shear
  orientations preserve regular target values in the same ring, but
  existence of a polynomial leading-power relation with an exponent one
  remains open. Zero leading Jacobian excludes opposite strict degree
  signs, not the balanced identity-map control.
  Closure does not supply the missing source-coordinate regularity;
* in every dimension, each source variable occurs as a nonzero linear
  coefficient of some Keller component. Nonnegative integer weights on
  all component supports therefore force nonnegative coordinate weights.
  Regularity for an arbitrary valuation does not supply the support premise;
* descent of all conjugate source coordinates to the marked original field
  is equivalent to normality of that original extension. This characterization
  gives obstruction vanishing with the accepted Keller--Galois rigidity input;
  universal descent remains unproved. Its failure
  supplies a conjugate coordinate moved by an element fixing the original
  field, not an inertia or residue-agreement witness;
* an explicit rational-plane diagnostic has determinant one in coordinates
  on a proper open source, while its target-dual derivative is not in the
  polynomial normalization ring. It is not a polynomial Keller map on the
  whole affine plane. Its cubic variant even reaches every complex target
  point, so existence of a visible sheet alone does not repair the gap;
* the direct no-ramification endgame uses the canonical finite normalized
  cover constructed from the Keller condition, without requiring the larger
  collision model's conjugate-center and inertia-index realization;
* normality of the original function-field extension makes the marked
  fixing subgroup trivial. A visible inertia-fixed sheet then rules out
  divisorial ramification. Purity and affine-plane finite-etale rigidity
  yield field triviality and obstruction vanishing. The source-intersection
  theorem gives polynomial invertibility without Ax--Grothendieck, deriving
  `ComplexKellerGaloisRigidity 2` from those two explicit geometric inputs.
  Neither universal planar vanishing nor dimension-three rigidity follows;
* a removed height-one fixed--moving prime produces an actual section
  outside the normalization ring, by localized ideal-power containment and
  finite denominator clearing;
* the generic trace-integral carrier is Mathlib's trace dual, and an integral
  generic basis supplies a nonzero denominator for its full normalization
  specialization;
* the polynomial Keller frame extends to the source fraction field and
  marked normal closure, preserves each conjugate polynomial sheet, and
  supplies the actual secant/adjugate first jets with a nonzero denominator;
* the genuine section ring of the fixed--moving open complement embeds in
  the normal-closure field, defining the boundary-section subalgebra;
* bounded-overring rigidity proves the global section pole witness: at a
  height-one fixed--moving prime, every nonzero multiplier fails the trace
  test on some actual section; no local-cohomology comparison is needed;
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
  transporter are specialized to the normalization diagram; the concrete
  section ring and secant--frame ideal are wired to boundary separation and
  collision vanishing for a supplied model and the stated literature inputs,
  conditional on landing for prime-order subgroups (sufficient by the proved
  Cauchy reduction), with the pole witness derived;
* the missing Keller-specific theorem says that this prescribed ideal is
  contained in the trace transporter for the whole pole tower;
* the landing audit separates finite coefficient clearing from uniform
  control: an explicit polynomial negative control has a nonzero finite
  denominator but zero overring transporter, and the actual secant--frame
  containment is proved to force `R_C = T`;
* the tame local calculation leaves inertia-invariant poles at all
  multiples of the ramification index. A logarithmic eigenvalue identity
  does not remove these poles or give the missing uniform bound.

On the alternative trace route, the missing containment is not packaged as
another abstract bridge here. Proving it requires a Keller-specific argument
controlling all sections, not just a nonzero finite denominator. On the active
finite route, the missing comparison concerns the two actual boundary
conormal classes; it is not a whole-pole-tower bound. Neither route's
conditional endgame nor the model construction proves planar vanishing.
-/
