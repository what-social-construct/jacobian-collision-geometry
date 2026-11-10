# Research source ledger

Sources and applicability checks for planar vanishing, the shared collision
construction, and the separate characteristic-two investigation. This ledger
records what a source can support, which hypotheses must be matched, and
whether its proposed use is a direct dependency or an analogy.

Last updated: 2026-11-09. This initial inventory covers the five recent papers
and selected existing inputs; it is not a complete audit of the bibliography.

The [bibliography](../../../paper/references.bib) owns citation metadata.
The [semantic parity table](../../../SEMANTIC-PARITY.md) owns notation and
manuscript–Lean correspondences. The [proof spine](Vanishing/PROOF-SPINE.md)
owns the current argument, and the [object bench](Vanishing/OBJECT-BENCH.md)
owns alternative constructions and diagnostic examples.

## Reading and proof status

| Status | Meaning |
| --- | --- |
| Read | The specified statements or proof passages were inspected. This is not an independent verification of the entire paper. |
| Independently checked | A specified argument was checked separately; the entry states its scope. This does not mean Lean checked it. |
| Formalized | The entry identifies a local Lean declaration with a proof. Its hypotheses remain part of the result. |
| Explicit input | A theorem is passed as a hypothesis. A definition of its proposition is not a proof of it. |
| Named axiom | A local `axiom` supplies the statement in the identified older wrapper. This is distinct from an upstream proof by the AXIOM project. |

The five recent papers below are **read**, with selected applicability
arguments checked separately. None has been imported as a Lean theorem or
added to either manuscript by this ledger update.

## Recent papers

| Source and version | Current role | Project destination |
| --- | --- | --- |
| [Steklov, arXiv 2610.16760v2](https://arxiv.org/html/2610.16760v2) | Contradiction mechanism to investigate by analogy | Characteristic-zero coherent boundary modules |
| [Shao, arXiv 2610.31289v1](https://arxiv.org/html/2610.31289v1) | Boundary extension comparison | Integral bounds and torsor extension |
| [Johnson, arXiv 2610.41843v1](https://arxiv.org/html/2610.41843v1) | Galois orbit comparison; main hypothesis does not match our base | Field and group hypothesis checks |
| [Moore and Zhu, arXiv 2611.02398v1](https://arxiv.org/html/2611.02398v1) | Artin–Schreier comparison | Separate characteristic-two research |
| [Watanabe, arXiv 2610.41237v1](https://arxiv.org/html/2610.41237v1) | Projective rigidity comparison | Research background, not a current proof input |

### Steklov on Galois coinvariants

Benjamin Steklov, *Galois coinvariants and fundamental groups of arithmetic
schemes*, v2, 30 October 2026.

- **Passages read:** Theorems A and B and Proposition 2.2, especially its
  rational coinvariant and determinant argument.
- **Hypotheses:** The base field is finitely generated. Theorem A assumes a
  geometrically connected, geometrically unibranch variety and a Galois
  extension whose Galois group has abelianization of finite exponent.
  Proposition 2.2 additionally uses pure representations of nonzero
  Frobenius weight and specified compatibility conditions.
- **Conclusion:** The specified prime-to-characteristic abelian coinvariants
  are finite. With the section required for the nonabelian action,
  characteristic zero gives the FAb
  property: every open subgroup has finite abelianization. This is not
  triviality, and the full coinvariant group can remain infinite.
- **Project use:** Investigate an analogous incompatibility between a finite
  coherent boundary stage and a derivation action. This is our proposed
  coherent argument below, not an application of Proposition 2.2.
- **Applicability check:** Every finite group, including $S_3$ and $C_2$,
  is FAb. A finite sheet representation has root-of-unity eigenvalues,
  so the nonzero-weight criterion does not directly apply to that representation.
- **Lean status:** No adaptation of this paper. Existing support modules are
  [boundary principal parts](../Boundary/PrincipalParts.lean) and their
  [fixed–moving specialization](FixedMovingBoundaryPrincipalParts.lean).

### Shao on integral structure sheaves

Xinyu Shao, *Cohomology of integral structure sheaves for open varieties*,
v1, 22 October 2026.

- **Passages read:** Theorems 1.9/4.1 and 1.14/4.16, the small-group
  definitions in Section 4.3, and Remark 4.17.
- **Setting and conclusion:** The base is a mixed-characteristic perfectoid
  field containing all roots of unity. Theorem 4.1 assumes a normal affinoid
  adic space locally of finite type, a closed subset $D$ of positive codimension,
  and smooth complement. It gives
  $\mathcal O^+(X\setminus D)=\mathcal O^+(X)$ for bounded integral sections,
  not all $\mathcal O$-sections. The derived inverse-limit vanishing is almost.
- **Torsor scope:** Extension concerns sufficiently small subgroups of an
  analytic group with good reduction, on a logarithmic pro-Kummer-étale
  ambient space. It does not assert ordinary unramified extension for
  an arbitrary finite Galois cover.
- **Project use:** Compare extension after integral control with our
  uniform-bound-to-$R_C=T$ argument. Keller-derived bounds and the change
  of geometric setting remain separate tasks.
- **Lean status:** No adaptation. [NormalizationTraceBound.lean](NormalizationTraceBound.lean)
  is our existing algebraic comparison, not Shao's analytic theorem.

### Johnson on large fields

Will Johnson, *A conjecture on Galois groups and large fields*, v1,
30 October 2026.

- **Passages read:** Conjecture 1.2, Theorem 1.3, and the proof sketch.
- **Hypothesis:** A fixed prime $p$ divides the degree of no finite Galois
  extension of the base field. This concerns the absolute Galois group,
  not just one selected finite closure; $p$ need not be the characteristic.
- **Status of conclusions:** General largeness is conjectural. The proved
  abelian-variety density and stated low-genus curve results retain the
  prime-to-$p$ hypothesis and assume the field is perfect.
- **Project use:** The orbit argument is a comparison, not a boundary
  regularity theorem. Nontransitivity alone need not produce a fixed point.
- **Independent applicability check:** Our complex Keller base is
  $K=\mathbb C(P,Q)$, with $P,Q$ algebraically independent. For every
  prime $\ell$, $Z^\ell-P$ is Eisenstein over
  $\mathbb C(Q)[P]$. Since $\mathbb C$ contains the roots of unity,
  $K(P^{1/\ell})/K$ is cyclic of degree $\ell$. Thus this $K$
  fails the proposed hypothesis for every prime. This calculation is ours,
  not a result attributed to Johnson; it is not packaged in Lean here.
- **Lean status:** No adaptation or new assumption.

### Moore and Zhu on Artin–Schreier covers

Robert Moore and Hui June Zhu, *A Global Generic Locus for Elementary Abelian
$p$-covers of $\mathbb P^1$ with two Ramification Points*, v1, 2 November 2026.

- **Passages read:** The introduction, Theorem 1.1, and the scope of the
  characteristic-two case in Proposition 6.4.
- **Setting:** Covers $y^{p^\ell}-y=f(x)$ with two prescribed poles and
  pole orders prime to $p$. Here genericity means minimality of the
  Newton polygon, not generic degree of a polynomial map.
- **Conclusion and range:** A coefficient-space open locus controls
  genericity after reduction at all sufficiently large primes. The
  threshold may depend on the coefficient tuple, and permitted ranks satisfy
  $\ell\mid[k_{\mathfrak p}:\mathbb F_p]$. Proposition 6.4 also treats the special
  case $p=2$, with both pole orders equal to one.
- **Project use:** Artin–Schreier comparison for the separate
  characteristic-two outline. The elementary field substitution
  $t=az$ changes $t^2+at+b=0$ to $z^2+z=b/a^2$ when $a\ne0$.
  If $a$ vanishes at the selected divisor, this is not an integral
  coordinate change there. Actual normalization, pole data, and residue
  inseparability still require proofs.
- **Lean status:** No adaptation; no characteristic-two inertia claim is
  promoted to a theorem by this entry.

### Watanabe on flag varieties

Kiwamu Watanabe, *Odd-Degree Rigidity and a Numerical Characterization of
Complete Flag Varieties*, v1, 30 October 2026.

- **Passages read:** Theorem 1.1, Proposition 2.1, and the main proof outline.
- **Hypotheses and conclusion:** A smooth complex Fano variety with the dimension
  and Picard number of a complete flag variety is isomorphic to that flag
  if it admits a continuous map to it of odd topological degree. The
  conclusion concerns the varieties, not invertibility of the given map.
- **Project use:** A numerical positivity contradiction is methodological
  background. Our affine normalization is not supplied with these
  projective hypotheses. Proposition 2.1 excludes surfaces in certain
  contraction fibers; it does not exclude coordinate poles or inertia.
- **Lean status:** No adaptation. No correspondence with our $S_3$
  normal closure follows from an abstract Weyl-group resemblance.

## Existing theorem inputs and formalization sources

### Geometric endgame inputs

The statements below are separated in
[External/Interfaces.lean](../External/Interfaces.lean). Their use must be
read from the individual theorem, not inferred from an umbrella import.

| Statement | Local status and use | Source record |
| --- | --- | --- |
| `BranchPurityA2` | Explicit input to the current normalized-cover endgame; also supplied by a named axiom in older wrappers. No local proof of the interface. | [Stacks 0BMB](https://stacks.math.columbia.edu/tag/0BMB), statement and proof inspected. Its normal-source, regular-base, quasi-finite, dimension, and codimension-one hypotheses must be matched by a formal adapter. |
| `AffinePlaneFiniteEtaleRigidity` | Explicit input asserting that an étale finite normal-closure cover of the complex affine plane has trivial extension; also a named axiom in older wrappers. | `SGA1` in the bibliography is a background reference. An exact theorem locator and proof adapter are not recorded here as verified. |
| `ComplexKellerGaloisRigidity n` | A theorem-target proposition in [General/Automorphism/GaloisRigidity.lean](../../General/Automorphism/GaloisRigidity.lean), not itself an installed axiom. The planar value is derived from the two inputs above in [Vanishing/GaloisRigidity.lean](Vanishing/GaloisRigidity.lean); dimension three remains separate. | Existing bibliography entries include Campbell, Razar, and Wright. Their exact theorem-to-interface attribution requires a separate source check. |
| `PlanarAxGrothendieck` | A named axiom in older automorphism wrappers. The new planar normal-case proof instead uses the proved source-intersection theorem. | `Ax1969` in the bibliography; no imported proof is recorded here. |

The named axioms are visible in
[External/Assumptions.lean](../External/Assumptions.lean).
Passing either geometric interface as a hypothesis does not prove it, and
deriving Keller–Galois rigidity from them does not add an independent proof
of those inputs.

### AXIOM adaptation for finite normal closures

- **Source:** [AxiomMath/Stacks, pinned commit
  f8e70c5dd04bfabcb423d5e325461f527c85a5d6](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksCore/FieldTheory/Normal/Closure.lean#L204),
  `IsNormalClosure.finiteDimensional`, corresponding to
  [Stacks 09DT](https://stacks.math.columbia.edu/tag/09DT).
- **Formalized local result:** `finiteDimensional_of_isNormalClosure` in
  [FiniteNormalClosure.lean](../../General/Galois/FiniteNormalClosure.lean):
  a supplied normal closure of a finite field extension is finite.
- **Provenance:** The local file names the upstream declaration and commit,
  adapts the proof to the project's Mathlib, and retains
  [Apache 2.0 terms](../../General/Galois/AXIOM-STACKS-LICENSE).
- **Scope:** This is not a proof of Keller–Galois rigidity, branch purity,
  affine-plane finite-étale rigidity, or Ax–Grothendieck.

### Stacks sources for boundary comparisons

| Source | Relevant statement | Local status and remaining comparison |
| --- | --- | --- |
| [0DWR](https://stacks.math.columbia.edu/tag/0DWR), Lemma 51.2.2 | For a finitely generated support ideal, the open-complement sequence relates sections to support local cohomology. | Statement and proof inspected. For a nontrivial $C$ and our domain $T$, the nonempty $U_C=\mathrm{Spec}T\setminus V(\mathfrak J_C)$ gives the mathematical comparison $R_C/T\simeq H^1_{\mathfrak J_C}(T)$. The comparison between these actual Lean objects is not yet packaged. |
| [0BST](https://stacks.math.columbia.edu/tag/0BST), Lemma 58.12.4 | For a finite group acting on a ring, the inclusion of the full fixed ring into the inertia fixed ring is étale at the contracted prime. | Source proof and a corresponding pinned AXIOM Frontier implementation were inspected; that upstream proof was not replayed or adapted here. This theorem does not place an arbitrary inertia-moved source coordinate in the chosen local ring. |

The inspected upstream inertia candidate is
`MulSemiringAction.exists_etale_away_fixedPoints_inertia` in
[`StacksFrontier/RingTheory/Invariant/Inertia.lean`](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/RingTheory/Invariant/Inertia.lean).
It is a candidate formalization source, unlike the already adapted finite
normal-closure lemma above.

At that same pinned commit, two further AXIOM Frontier candidates support
the next coherent checkpoint:

- [The low degree exact sequence](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/RingTheory/LocalCohomology/LowDegree/CechSectionsComparison.lean),
  `Stacks.LocalCohomology.exact_lowDegreeSequence`, for a finitely
  generated ideal and a sheaf identified with the restricted module sheaf.
- [The derivation action](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/RingTheory/LocalCohomology/DerivationAction.lean),
  `Stacks.LocalCohomology.derivationOperator`, for a commutative ring,
  finitely generated support ideal, and base derivation; it supplies an
  additive operator and Leibniz identity without assuming ideal preservation.

Their statements and selected proof passages have been inspected, not
replayed or imported here. They use AXIOM's derived local-cohomology model.
Our `BoundaryPrincipalParts` uses Mathlib's filtered-Ext model; an
explicit comparison of these representations is still required.

The pinned AXIOM snapshot uses Lean 4.34.0-rc2; this development uses
Lean 4.28.0. Its derived-Ext colimit comparison is therefore not a
drop-in adapter for our older filtered-Ext functor. A genuine comparison
must identify the Ext models and their transition maps before passing
to colimits and matching the actual restriction map.

Other Stacks tags in the bibliography remain source pointers, not an
automatic assertion that their proofs or all project specializations have
been imported. Add a precise entry when using one for a new implication.

## Coherent derivation analogy

This is a project argument inspired by Steklov's contradiction mechanism,
not a theorem attributed to his paper. It stays with the existing
characteristic-zero construction.

Let $B\simeq k[u_1,\ldots,u_n]$, where $k$ is a field of characteristic zero.
Suppose a $B$-module $M$ has a nonzero annihilator and additive
operators satisfying

```math
\nabla_i(bm)=\partial_i(b)m+b\nabla_i(m).
```

If $aM=0$, applying this identity shows $\partial_i(a)M=0$.
Thus the annihilator is preserved by every target partial. The proved
[characteristic-zero transversality theorem](../../General/Normalization/BaseTransversality.lean)
forces that nonzero annihilator to be the unit ideal, hence $M=0$.
No commutativity or flatness of the operators is needed for this argument.
A finite module supported on a proper closed boundary supplies a nonzero
annihilator; an explicit uniform annihilator also suffices.

**Formalized mechanism:** [DerivationAnnihilator.lean](../../General/Normalization/DerivationAnnihilator.lean)
proves annihilator preservation as
`derivation_mem_annihilator_of_leibniz`, the characteristic-zero
conclusion as
`subsingleton_of_annihilator_ne_bot_of_polynomial_leibniz`, and its
finite-torsion corollary as
`subsingleton_of_finite_torsion_of_polynomial_leibniz`.
The main conclusion needs no module-finiteness assumption; the corollary
uses Mathlib's existing finite-torsion annihilator theorem.

**Application status:** The generic exclusion takes operators as
hypotheses. The actual section-quotient operators are constructed below;
the filtered-Ext cohomology comparison and frame-stable finite boundary
stage remain open. This is not an imported Steklov theorem.

[FractionalQuotient.lean](../../General/Normalization/FractionalQuotient.lean)
proves elementwise torsion for the standard module quotient of any
algebra embedded over a domain in its fraction field. Each class has a
denominator; the theorem supplies neither one denominator for all classes
nor finite generation. This distinction is essential when applying the
annihilator exclusion.

[ConjugateInvariantSections.lean](../../General/Keller/ConjugateInvariantSections.lean)
uses the original affine target open to identify $E^G$ with its section
algebra over $B$, hence the corresponding standard module quotients.
It proves that $E^G/B$ is torsion without Keller, and under Keller that its
vanishing is equivalent to the actual target boundary being empty.
This is the section-side bridge, not an imported local-cohomology
comparison. The direct quotient route does not take an $H^1$ comparison
as an additional premise.

[InvariantFrame.lean](InvariantFrame.lean) proves that the actual
normal-closure Keller frames preserve both $E$ and the embedded $K$,
hence $E^G$, with the original target-base action.
[InvariantQuotientAction.lean](InvariantQuotientAction.lean) descends
them to the same $E^G/B$ and proves the target-coordinate Leibniz rules.
The existence theorem takes marked normal-closure data and Keller,
not a supplied action. Its algebraic helpers are independently proved in
[DerivationSubalgebra.lean](../../General/Normalization/DerivationSubalgebra.lean)
and [DerivationQuotient.lean](../../General/Normalization/DerivationQuotient.lean).
Preserved finite-stage control and a uniform annihilator are not derived.

[DerivationCyclicStage.lean](../../General/Normalization/DerivationCyclicStage.lean)
and its [actual quotient specialization](Vanishing/CyclicStage.lean)
prove that a nonzero torsion class has some coordinate derivative outside
its finite cyclic span. This is a failure certificate for $Bq$, not a
larger-stage construction or an assertion that nonzero classes exist.

[DerivationOrbit.lean](../../General/Normalization/DerivationOrbit.lean)
uses that same action on the span of all finite frame words. Its
all-orders annihilator criterion reuses the existing polynomial
annihilator theorem, without a coherence or commuting-operator input.
[DerivationJetTest.lean](../../General/Normalization/DerivationJetTest.lean)
independently proves a finite threshold by strong degree induction using
the existing nonzero-partial and degree-drop lemmas: a fixed nonzero
target polynomial killing words through its own total degree forces
vanishing. [The planar specialization](Vanishing/DifferentialOrbit.lean)
retains the actual quotient and frame operators.

[DerivationOrbitStages.lean](../../General/Normalization/DerivationOrbitStages.lean)
proves the separate finite-order estimate $a^{r+1}$ from an initial
annihilator $a$. It gives no degree improvement or fixed all-orders
denominator. The sheaf interpretation remains the standard section
quotient; [Stacks, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
supplies the mathematical support-local-cohomology sequence. The finite
module and ascending-chain facts in
[Stacks, Tag 00IK](https://stacks.math.columbia.edu/tag/00IK) do not assert
that this boundary quotient or its differential orbit is finite.

The low-total-degree stage construction is now independent of a supplied
stability premise. [ConjugatePolynomialPresentation.lean](../../General/Galois/ConjugatePolynomialPresentation.lean)
identifies the range of ground-polynomial evaluation with the original
$E$ restricted to the ground field. The finite family is the existing
conjugate source-coordinate family, not a second algebra.
[FilteredPolynomialDerivation.lean](../../General/Normalization/FilteredPolynomialDerivation.lean)
uses Mathlib's `restrictTotalDegree` and its finite evaluation image;
affine generator values imply preservation by a proved polynomial lift.
[LowTotalDegreeFrame.lean](Vanishing/LowTotalDegreeFrame.lean) derives
those affine values from total coordinate degree at most two and the
existing conjugate-frame identities.

[TotalDegreeTwoStage.lean](Vanishing/TotalDegreeTwoStage.lean) pulls the
finite stage to invariants, projects to the existing quotient, and
uses [DerivationFiniteStage.lean](../../General/Normalization/DerivationFiniteStage.lean)
to apply the torsion annihilator theorem. No finite stage, uniform
denominator, or rigidity theorem is assumed in this application. The
result concerns total polynomial degree, not generic degree. The
ordinary finite-module/coherent-sheaf interpretation on a Noetherian
affine scheme is [Stacks, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ),
whose equivalent conditions were checked directly; no new sheaf model
or literature axiom is used in the module proof. Higher-degree growth
and adapted-stage construction remain separate research questions.

[ConjugateSourceBaseChange.lean](../../General/Keller/ConjugateSourceBaseChange.lean)
uses the original Keller flatness, the fixed-algebra embedding into $K$,
and the generic-source tensor embedding to prove that the original
source restricted to $U_F$ is finite étale. Its module finiteness comes
from an injection into the existing finite $E/E^G$, not a supplied
finiteness premise over $B$. This result is dimension-independent.

[ConjugateNormalizationOpen.lean](Vanishing/ConjugateNormalizationOpen.lean)
derives normality of the invariant open using stalk isomorphisms, then
uses the existing finite delta frame and integral field traces to prove
normality of $E$. It constructs the inclusion $T\hookrightarrow E$ and
the resulting open immersion over the original target. These are native
proofs from the Keller construction, not a new étale-normality axiom.
The scheme comparison does not construct a bounded orbit or establish
boundary emptiness. The general fact that a quasi-finite morphism is
finite over some dense target open is [Stacks, Tag 03I1](https://stacks.math.columbia.edu/tag/03I1);
that source does not identify our particular invariant open or establish
its maximality.

[TargetPoleWitness.lean](../../General/Normalization/TargetPoleWitness.lean)
uses Mathlib's reduced numerator and denominator to construct a height-one
polar prime in a Noetherian UFD. Its localization exclusion only needs a
domain and the coefficient certificate. The general codimension-one
principle for normal Noetherian domains is [Stacks, Tag 031T](https://stacks.math.columbia.edu/tag/031T),
whose statement and proof were checked; the implementation proves its
UFD application directly, without importing that statement as an axiom.
[ConjugateInvariantPole.lean](../../General/Keller/ConjugateInvariantPole.lean)
applies the extraction to the actual invariant quotient, excludes the
constructed prime from $U_F$ by contraction, and derives its target DVR
and local pole. A nonzero class is a contradiction hypothesis, not an
existence assertion for counterexamples.

[InvariantNormalizationBaseChange.lean](Vanishing/InvariantNormalizationBaseChange.lean)
constructs the Cartesian normalization comparison and its image formula.
[ConjugateCommonOpen.lean](Vanishing/ConjugateCommonOpen.lean) derives the
same-local-ring regularity criterion using stalk isomorphisms, fraction
uniqueness, and the existing coordinate generators. These are native
proofs from the constructed maps, not new boundary or ramification
premises. A polar target boundary point is not automatically a ramified
normalization divisor, and none of these comparisons supplies the
Keller-specific uniform derivative bound.

[FractionalNormalization.lean](../../General/Normalization/FractionalNormalization.lean)
uses the existing finite integral closure, standard `LinearMap.range`,
and a fixed field multiplier to construct finite fractional candidates.
[ValuationFiniteStage.lean](../../General/Normalization/ValuationFiniteStage.lean)
proves their common valuation bound, including base additions.
[DerivationFractionalStage.lean](../../General/Normalization/DerivationFractionalStage.lean)
derives the exact quotient-rule defect and next-exponent estimate.
[TransversePoleStep.lean](../../General/Normalization/TransversePoleStep.lean)
constructs unit numerators for successive transverse derivatives in a
local algebra over a characteristic-zero field. These are algebraic
proofs using Mathlib, not new literature assumptions. The separate
invariant-quotient construction above now extracts a target boundary
divisor, DVR, and polar representative. Neither construction supplies
Keller-specific containment of an entire orbit in a fixed candidate.
A target-field DVR pole tower and an inertia-moved sheet at a
normalization divisor remain different objects.

[TraceStageAudit.lean](TraceStageAudit.lean) proves that trace-integral
elements already in the target field lie in the base image when the
extension degree is a base unit. Its characteristic-zero field-algebra
corollary derives the unit condition. Consequently the fixed-field part
of this old bounded stage has zero class in $E^G/B$; its original role in
the $N/T$ trace strategy is unchanged. The degree in this test is $[N:K]$,
not the generic degree $[L:K]$ or the ambient dimension. No broader
coprimality or polynomial-invertibility conclusion is asserted.

Use the existing [conormal module and components](../../General/Keller/ConjugateInvariantConormal.lean),
[support local cohomology](../Boundary/PrincipalParts.lean), and
[trace-integral lattice](PrincipalPartsStrategy.lean) when testing this idea.
Keep the following distinctions explicit:

- The conormal components $\mathfrak b_F/\mathfrak b_F^2\to B/\mathfrak b_F$
  measure failure of ideal preservation; they are not connection
  endomorphisms of the conormal module.
- The full pole module need not be finite over $B$. Finite generation as
  a differential module is not finiteness over $B$.
- A finite pole stage need not be preserved by transverse differentiation.
  For example, differentiating $s^{-1}$ produces $-s^{-2}$.
- A field derivation acts on a quotient only after the relevant
  submodules are shown to be stable. In particular, an action on
  $T^\dagger/T$ cannot be inferred from an action on $N$.
- A new application must retain the actual boundary ideal, ambient ring,
  and divisor, and identify the step that specifically uses planar Keller
  geometry rather than only the dimension-independent construction.

## Original collision and multiplier comparison

The archived
[secant and boundary manuscript](../../../manuscript-archive/secant-projectors-and-boundary-inertia-for-planar-keller-maps.tex)
already defines the trace transporter and conditional map
$R_C/T\to T^\dagger/T$, $[r]\mapsto[sr]$, in its trace-landing
comparison. Its conjugate-sheet overlap discussion constructs
$C_F^\circ\to\Gamma(U_g\cap U_{\sigma g},\mathcal O)$ and distinguishes
that factorization from landing for arbitrary boundary sections.
This is project provenance, not a new external theorem input.

[BoundaryMultiplierComparison.lean](BoundaryMultiplierComparison.lean)
recovers the standard quotient map and its ambient multiplication formula.
The trace-dual containment uses
`Submodule.one_le_traceDual_one` in Mathlib's
`RingTheory/DedekindDomain/Different.lean`, after the existing
`traceIntegralSubmodule_eq_traceDual` identification.
[ConjugateInvariantNormalizationQuotient.lean](../../General/Keller/ConjugateInvariantNormalizationQuotient.lean)
independently derives $E^G/B\hookrightarrow N/T$ from the original
embeddings and normal-base integrality. Neither statement imports uniform
landing or an inclusion $E^G\subseteq R_C$.

The original collision-ring identities already prove the local
contradiction in [LocalCollision.lean](Vanishing/LocalCollision.lean).
[InertiaCoordinates.lean](Vanishing/InertiaCoordinates.lean) specializes
it to an inertia-moved sheet. Its regularity at the chosen divisor,
or an appropriate local section-domain adapter for the trace route,
still has to be derived from the full polynomial-source geometry.

## Polynomial pole cancellation

The generic finite-sum source is Mathlib's
`Valuation.map_sum_eq_of_lt` in
`RingTheory/Valuation/Basic.lean`: a uniquely maximal summand determines
the value of the sum. The project
[finite-sum cancellation lemma](../../General/Normalization/ValuationCancellation.lean)
uses this to extract two distinct maximal summands when the sum's value
is smaller than one of its terms.

The [polynomial specialization](../../General/Keller/ValuationCancellation.lean)
uses the already proved nonzero linear occurrence of each Keller source
coordinate. [PolarCancellation.lean](Vanishing/PolarCancellation.lean)
combines this with the original center map and local inertia argument on
the same divisor. These are local project proofs, not imported claims
from the recent papers. They certify repeated dominant polar terms,
not their exclusion; the full higher-degree constant-Jacobian constraint
is not used by the generic polynomial step.

## Weighted Jacobian test

The existing objects are Mathlib's `IsWeightedHomogeneous` and
`weightedHomogeneousComponent` in
`RingTheory/MvPolynomial/WeightedHomogeneous.lean`.
[WeightedComponents.lean](../../General/Normalization/WeightedComponents.lean)
proves signed-integer derivative and top-product comparisons.
In the pinned Mathlib, `EulerIdentity.lean` provides weighted Euler
for natural-number weights; the project
[WeightedEuler.lean](../../General/Normalization/WeightedEuler.lean)
proves the integer-weight statement from the existing derivative
coefficient formula.

[WeightedJacobian.lean](Vanishing/WeightedJacobian.lean) derives the
balanced/strict formula from the full constant-Jacobian equation and
excludes balanced common zeros with nonzero weighted radial vector.
This is a local formalization of the algebraic constraint, not an
imported theorem from a research preprint or a universal pole exclusion.

[LeadingFaceDiagnostic.lean](Vanishing/LeadingFaceDiagnostic.lean)
checks an explicit global polynomial automorphism with common strict
leading-face zeros. Unlike the earlier proper-open diagnostics, it
satisfies the full polynomial Keller condition. Its substitution leaves
a lower polar output, so it is not a ramified valuation above the affine
target. This distinguishes the tested face-level shortcut from the
still-open complete pole argument.

## Cancellation budget and recovered frame calculus

The exact subtraction formula
$J(P,Q^r-\lambda P^s)=rQ^{r-1}c$ is a specialization of the existing
`planarKellerSecondFrame_coordinateAlgHom` in
[BaseFrame.lean](Vanishing/BaseFrame.lean), present in commit
`550715e` (2026-09-19). The inverse-Jacobian frame proposition is
preserved in the [archived planar manuscript](../../../manuscript-archive/secant-projectors-and-boundary-inertia-for-planar-keller-maps.tex).
[PolynomialSubtraction.lean](Vanishing/PolynomialSubtraction.lean)
exposes this specialization and the actual inverse target shear.
No new chain-rule infrastructure or theorem input is introduced.

[Vénéreau, *A parachute for the degree of a polynomial in algebraically independent ones*, v2](https://arxiv.org/html/0704.1561v2)
is the classical comparison. The definition and properties of the
parachute and their chain-rule proof were read. They concern ordinary
total degree over a characteristic-zero field. They are not imported as
a signed-weight theorem or as an automorphism criterion for our map.

The signed-weight argument is independently proved in
[WeightedDegreeBounds.lean](../../General/Normalization/WeightedDegreeBounds.lean)
and [CancellationBudget.lean](Vanishing/CancellationBudget.lean).
It uses sharp finite degrees and the supplied leading-polynomial
relation to obtain $0<rn-k\le D$. The legal target shear gives a
nonnegative decreasing defect; a general power replacement is not
promoted to a Keller pair. The actual initial-residue comparison is now
proved in [BoundaryInitialResidue.lean](Vanishing/BoundaryInitialResidue.lean),
using the same boundary DVR and its residue field. It does not construct
the polynomial leading relation or establish iteration availability.

## Next reduction and the division lemma

[Nguyen Van Chau, *A simple proof of Jung's theorem on polynomial automorphisms of C2* (2003)](https://math.ac.vn/public/uploads/files/0302209.pdf)
states the Division Lemma on p. 209 for polynomial automorphisms. On
p. 213, the reduction step combines that divisibility with the
common-power description of ordinary homogeneous forms with zero
Jacobian. These passages were checked directly. They do not supply
degree divisibility for a map assumed only Keller, nor a signed-weight
division theorem for a boundary valuation.

The local implementation in
[TwoSidedCancellation.lean](Vanishing/TwoSidedCancellation.lean) proves
the step in either orientation once its leading-power relation is
given. [OppositeDegreeExclusion.lean](Vanishing/OppositeDegreeExclusion.lean)
uses signed Euler and the existing derivative-zero criterion to exclude
opposite strict degrees from the zero-leading-Jacobian branch. Neither
imports the automorphism Division Lemma under the Keller hypothesis.

## Ledger maintenance

For a new source, record its version or stable tag, exact passage and
hypotheses, intended role, local object or theorem, and the remaining
comparison. Mark a project inference as such. Promote an entry to
independently checked or formalized only with the argument or declaration
identified; keep build evidence in the existing proof and provenance notes.
