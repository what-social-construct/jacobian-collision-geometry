# Manuscripts

Build the standalone papers from this directory with:

```bash
latexmk -pdf paper1.tex
latexmk -pdf paper2.tex
```

`main.tex` is the earlier combined manuscript retained for comparison.

The paper follows the Lean dependency spine.  Every mathematical section
ends with the corresponding Lean source files.

The status distinction in the paper is intentional:

- branch purity, finite-étale rigidity of `𝔸²_ℂ`, and
  Ax–Grothendieck are standard literature theorems represented by explicit
  interfaces in Lean;
- a supplied `PolynomialKellerCollisionModel`, specialized as
  `PlanarKellerCollisionModel`, contains the normalization diagram, Keller
  bridges, and `ConjugateRamificationRealization`; from these data Lean
  canonically constructs the pulled-back conjugate boundary ideals and
  proves their valuation-theoretic containment at ramified divisors;
- `PlanarBoundaryCoherence` and `PlanarRamificationRigidity` are global and
  divisorial formulations of the same fixed-map endpoint.  Their universal
  validity is not proved; the formal interfaces use the explicit
  `BoundaryCoherenceBridge` and `RamificationRigidityBridge`, while
  moving-sheet coverage and boundary separation are alternative explicit
  codimension-one hypotheses;
- the manuscript proves the classical normal/Galois case by boundary-divisor
  rigidity and consequently excludes generic degree two; this argument is
  not yet part of the Lean development;
- branch purity is applied only after every height-one point has been shown
  unramified; finite-étale rigidity then gives $N=K$, and collision descent
  gives $q_F=0$ and $I_R=I_\Delta$;
- the stable boundary API canonically joins the inertia-fixed locus to the
  boundaries of all moved sheets.  The research reduction now consists of
  two geometric statements, a finite Tate--conductor reduction, and one
  missing morphism: the fixed--moving module
  has an unbounded DVR pole tower at a hidden divisor; the trace-dual quotient
  is finite and locally bounded; and the explicit first-jet secant--frame
  denominator ideal must be contained in the trace-transporter ideal.  A
  merely nonzero intersection would only restate boundary separation.  The
  polynomial frame and explicit divided-difference secant are formalized,
  together with a generic nonzero denominator theorem.  The research layer
  also reuses Mathlib's monogenic order, power basis, hypersurface, Jacobian,
  conductor, and trace-dual objects.  The generic trace-integral carrier is
  identified with Mathlib's trace dual; finite power-basis Tate
  reconstruction and the generic monogenic/overorder conductor--trace-dual
  identities are proved.  The conductor bounded stage and its landing ideal
  are also defined; a generic normal-Noetherian finite-overring collapse and
  a conditional pointwise-pole route to the existing endgame are proved.  The
  local-cohomology/DVR pole theorem needed by the pointwise-pole route,
  concrete normalization and
  quotient specialization, actual \((g,\sigma g)\) overlap coefficient family,
  and uniform candidate containment are not yet formalized.  The first-jet
  ideal is the designated candidate, while any finite jet order would suffice;
  full ideal inclusion is choice-free, although one explicitly prescribed
  nonzero landing scalar would be enough;
- repository-wide manuscript/Lean parity and the deletion gates for legacy or
  optional research objects are recorded in `../SEMANTIC-PARITY.md`;
- the dimension-three theorem is an abstract implication from explicit
  generic-source surjectivity, cubic power-basis, nonnormality, and marked
  normal-closure data.  It now constructs the residual normal-closure
  equivalence and the nontrivial fixing subgroup internally.  It concludes
  `IsComplexThreeJacobianCounterexample F`, but does not instantiate these
  conditions with a concrete polynomial map.
