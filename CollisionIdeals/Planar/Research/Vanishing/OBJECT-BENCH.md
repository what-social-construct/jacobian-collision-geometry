# Object bench: contributions to planar vanishing

The benchmark is the [primary proof spine](PROOF-SPINE.md): does an object
help derive \(\operatorname{Obs}(F)=0\) for every planar Keller map?
Being defined, nonzero, or equivalent to another open condition does not by
itself close a step of that proof.

This bench records mathematical roles; the latest verification results are
recorded in the proof spine. Keep the existing Lean implementations; do not
duplicate objects or move files merely to classify them here.

## Core and active route

| Object / source | Established contribution | Remaining use or test |
| --- | --- | --- |
| Canonical finite normalized cover in [General/Keller/Normalization.lean](../../../General/Keller/Normalization.lean) | Constructed from the Keller condition; suffices for the direct conditional endpoint in [Ramification.lean](Ramification.lean). | Prove no height-one ramification. The larger collision-model constructor is not needed for this endpoint. |
| Global source-divisor visibility in [General/Keller/DivisorVisibility.lean](../../../General/Keller/DivisorVisibility.lean) | Uses constant polynomial units, factorization, and Keller flatness to produce a visible unramified source divisor over every height-one base prime. | Control the remaining normal-closure sheets. One visible source prime does not mean all inertia is trivial. |
| Visible conjugate center in [General/Normalization/VisibleConjugateCenter.lean](../../../General/Normalization/VisibleConjugateCenter.lean) | Proves center realization by lying-over and Galois transitivity; transports the source divisor into the actual conjugate-center family. With the supplied local-index realization, inertia fixes some sheet. All four declarations passed the targeted build. | Control the other sheets. No center-surjectivity or visibility premise is assumed; the existing diagram/index realization remains explicit in the fixed-sheet corollary. |
| Direct local collision exclusion in [LocalCollision.lean](LocalCollision.lean) and [InertiaCoordinates.lean](InertiaCoordinates.lean) | Residue agreement forces equality of local Keller collision maps. Actual valuation inertia moving a sheet forces some source coordinate outside the valuation ring, without an index realization. | Prove regularity on a moved sheet at each nontrivial-inertia divisor. Neither closure nor regularity of the residual projector supplies this. |
| Monomial support weights in [General/Keller/MonomialWeights.lean](../../../General/Keller/MonomialWeights.lean) | Each source variable occurs linearly in a Keller component; nonnegative integer weights on all supported monomials imply nonnegative coordinate weights, in every dimension over any field. | The mathematical monomial-valuation application uses the no-cancellation rule. General boundary valuations need not satisfy it; their cancellation is not excluded. |
| Shared local inertia and conjugate-index API in [General/Normalization](../../../General/Normalization) and [General/Galois/RamificationIndex.lean](../../../General/Galois/RamificationIndex.lean) | Supplies the actual local rings and ramification/inertia comparisons for the boundary/conjugate-sheet route; ramification implies nontrivial inertia. The characteristic-zero model/index assembly is verified. | Use the constructed model where this route needs it; it is not a prerequisite of the smaller direct endpoint. These comparisons do not prove inertia trivial. |
| Base transversality in [General/Normalization/BaseTransversality.lean](../../../General/Normalization/BaseTransversality.lean) | Proves that every nonzero proper polynomial ideal in characteristic zero contains an element with some coordinate partial outside the ideal. Targeted build and all six axiom audits passed. | Transfer the contracted base prime through the target polynomial presentation and use the corresponding Keller frame. This dimension-independent fact supplies no boundary regularity. |
| Target-polynomial frame identities in [BaseFrame.lean](BaseFrame.lean) | Prove that the existing first and second Keller frames act as target partial derivatives on arbitrary target polynomials, including on each conjugate sheet in the normal closure. Targeted build and all four axiom audits passed. | Use the frame matching the coordinate selected by base transversality. These identities do not restrict a field derivation to a boundary local ring. |
| Derivation denominator criterion in [FrameDenominator.lean](FrameDenominator.lean) | Clearing generator derivatives is equivalent to clearing all of the finite order, by Leibniz. Nonzero denominators for one frame or a pair are proved. Targeted build and all three axiom audits passed. | Establish local membership of those derivatives; finite local clearing then produces a denominator outside the prime. The existing secant family is not automatically a family of normalization-generator derivatives. |
| Regular transverse derivation in [General/Normalization/DerivationCriterion.lean](../../../General/Normalization/DerivationCriterion.lean) | Proves that a base element in the contracted prime with unit derivative under a derivation of the actual local ring forces local index one. Generic and local criteria passed a targeted Lean build. | Exhibit such a derivation from the actual Keller frame at each boundary divisor. Field-level extension does not prove local regularity. |
| Local index/unramifiedness criterion in [General/Normalization/LocalUnramified.lean](../../../General/Normalization/LocalUnramified.lean) | Checked equivalence at a DVR prime with separable residue extension; checked integral residue-characteristic-zero specialization. | Supply the concrete normalization certificates when specializing. This is independent of inertia-index and Galois-action comparisons. |
| Fixed--moving boundary ideal in [Boundary/Separation.lean](../../Boundary/Separation.lean) | `PlanarBoundarySeparation` feeds the no-divisorial-ramification endgame for the supplied model. | Prove separation from the Keller hypothesis; merely renaming the condition is not progress. |
| Actual section ring \(R_C\) in [BoundarySections.lean](../BoundarySections.lean) | Embeds the sections of the fixed--moving open complement into \(N\), as a \(T\)-subalgebra. | Use this actual ring when quantifying over boundary sections, not an arbitrary supplied module. |
| Trace dual and transporter in [PrincipalPartsStrategy.lean](../PrincipalPartsStrategy.lean), specialized in [TraceLanding.lean](../TraceLanding.lean) | Express the required containment for all sections. These are the existing shared objects despite the historical filename. | Prove a nonzero multiplier lands the whole section ring in the trace dual. |
| Trace bound and pole witness in [NormalizationTraceBound.lean](../NormalizationTraceBound.lean) and [BoundaryPoleWitness.lean](../BoundaryPoleWitness.lean) | A uniform nonzero trace multiplier forces \(R_C=T\); a removed height-one fixed--moving prime produces a section violating every such multiplier. | Supplies the contradiction once uniform landing is established; does not supply landing. |
| Extended Keller frames in [KellerFrameExtension.lean](../KellerFrameExtension.lean) | Extend the actual source derivations to \(N\) and preserve conjugate polynomial sheets. | For the local route, prove regularity of a transverse frame at the boundary DVR; for the trace route, control arbitrary boundary sections, including their inertia-invariant poles. |
| Finite secant-frame lattice and denominator in [SecantFrameCandidate.lean](../SecantFrameCandidate.lean), reduced in [SecantReduction.lean](SecantReduction.lean) | Concrete first-jet coefficients and a proved nonzero denominator ideal. The matrix-only lattice and denominator equalities passed a targeted build and all four public axiom audits: adjugate entries and jets add no generators in dimension two. | Uniform containment in the section-ring trace transporter is **open**; finite denominator clearing is insufficient. The original definitions remain intact for API compatibility. |
| Conditional endpoint in [SecantFrameTraceLanding.lean](../SecantFrameTraceLanding.lean) | Landing for prime-order subgroups implies boundary separation and then obstruction vanishing with the model and literature inputs. | Discharge the landing hypothesis rather than adding another equivalent wrapper. |

The section-localization and denominator-clearing leaves support the actual
pole-witness construction: `BoundarySectionLocalization`,
`LocalizationDenominator`, and `HeightOneBoundaryPole`. They need not become
separate conceptual steps in the final exposition.

For the local frame test, a nonzero denominator is insufficient: a denominator
for the chosen transverse frame must avoid the prime in question. A frame
regular at the divisor but tangent to the base divisor does not satisfy the
unit-derivative condition.

### Concrete boundary-regularity test

Let \(t_1,\ldots,t_r\) generate \(T\) as a \(B\)-module, and let \(D\)
be the extended Keller frame chosen transverse to the contracted base prime.
Reuse the existing object

\[
J_D=\texttt{finiteCoefficientDenominatorIdeal}\bigl(D(t_i)\bigr).
\]

Because \(D(B)\subseteq B\), the Leibniz rule makes clearing these generator
derivatives sufficient to clear \(D(T)\); this is now formalized in
[FrameDenominator.lean](FrameDenominator.lean), with the weaker premise
\(D(B)\subseteq T\). The exact local test is
\(J_D\not\subseteq\mathfrak q\), not merely \(J_D\ne0\). Finite generation
and the quotient rule identify this test with
\(D(T_{\mathfrak q})\subseteq T_{\mathfrak q}\).
This equivalence is a mathematical audit, **not yet a packaged Lean theorem**.
The existing `linearOperatorDenominatorIdeal` cannot be substituted: the
Keller frame is not \(B\)-linear.

For the local diagnostic \(s=t^e\), \(e>1\), the extended derivative satisfies
\(\partial_s(t)=1/(e t^{e-1})\). On the module generators
\(1,t,\ldots,t^{e-1}\), its denominator ideal is
\((t^{e-1})\): nonzero but contained in \((t)\). This is a test of the
proposed local inference, not a planar Keller counterexample.

No inspected result compares the secant first-jet family with derivatives of
these normalization-module generators under the global Keller hypothesis.
The comparison is false without that hypothesis, as the diagnostic below
shows. Similarly, the Keller Jacobian determinant is not the monogenic
derivative in the conductor--trace-dual formula.

There is also no automatic normalization shortcut:
[Seidenberg's derivation theorem, §3](https://msp.org/pjm/1966/16-1/pjm-v16-n1-p16-s.pdf)
preserves the integral closure of a Noetherian differential domain **in its
own fraction field** in characteristic zero. Here \(\operatorname{Frac}(B)=K\),
whereas \(T\) is the integral closure in \(N\); applying that theorem to
\(B\) does not control \(T\). Preservation of a conjugate source ring also
does not show that this ring lies in the boundary localization. A usable
application would have to supply an appropriate differential subring there
with fraction field \(N\), not assume such a subring exists.

### Secant comparison audit (2026-09-18)

The following calculation is a mathematical negative control, not a new Lean
theorem and not a Keller counterexample. Set
\(B=\mathbb C[s,y]\), \(T=\mathbb C[t,y]\), \(N=\mathbb C(t,y)\), with
\(s=t^2\). For the polynomial map \((t,y)\mapsto(t^2,y)\), the ordered
secant matrix on the moving pair \((t,y),(-t,y)\) is

\[
M=\begin{pmatrix}0&0\\0&1\end{pmatrix},\qquad
\operatorname{adj}(M)=\begin{pmatrix}1&0\\0&0\end{pmatrix}.
\]

The true target-dual field derivations satisfy
\(D_s(t)=1/(2t)\), \(D_s(y)=0\), \(D_y(t)=0\), \(D_y(y)=1\).
Every first jet of these evaluated matrix entries is zero. Thus the
**evaluated** secant coefficient lattice is just \(T\), and its denominator
ideal is the unit ideal. But \(1,t\) is a \(B\)-basis of \(T\), and the
denominator ideal for its \(D_s\)-derivatives is \((t)\). In particular,
the secant lattice does not contain all generator derivatives, even though
its own denominator already avoids \((t)\).

This uses the supplied-derivation `evaluatedSecantFrameCoefficient` pattern,
not the constant-\(c\) Keller specialization: the Jacobian determinant of
this map is \(2t\), not a nonzero constant. After removing \(t=0\), both
target-dual derivations preserve the source ring and the map is étale, yet
they do not preserve \(T_{(t)}\). Consequently generic separability,
étaleness on retained sheets, and the secant equations cannot alone supply
the missing generator comparison.

There is a positive but weaker comparison in the actual Keller situation.
The algebra generated by all conjugate source rings is an étale normal
component of their iterated fiber product, has fraction field \(N\), and
contains \(T\). This follows from étale base change/composition and
normality; normal components are open and closed here.
See [Stacks, étale ring maps](https://stacks.math.columbia.edu/tag/00U0),
[normality under smooth maps](https://stacks.math.columbia.edu/tag/034F), and
[normal components](https://stacks.math.columbia.edu/tag/0357).
The existing frame-preservation identities therefore put generator
derivatives in that conjugate-source algebra, **not** in the finite secant
lattice or in every \(T_{\mathfrak q}\). This is a mathematical inference,
not a packaged Lean comparison. The containing algebra need not be finite
over \(B\); treating it as a finite order contained in \(T\) reverses the
inclusion and cannot justify a conductor argument.

### What the conductor comparison can supply

The three lemmas in [ConductorComparison.lean](ConductorComparison.lean)
passed a targeted build and axiom audit.

For the existing monogenic order \(U=B[\alpha]\subseteq T\), let
\(\Lambda\subseteq N\) be a \(T\)-submodule. If the derivatives of the
base coefficients and of \(\alpha\) belong to \(\Lambda\), the Leibniz rule
gives \(D(U)\subseteq\Lambda\). For any \(a\in(U:T)\),

\[
aD(t)=D(at)-tD(a)\in\Lambda\qquad(t\in T).
\]

Consequently, if \(s\Lambda\subseteq T\), then \(saD(T)\subseteq T\).
This is an actual comparison using the existing conductor, not an assertion
that \(D(T)\subseteq\Lambda\). To use it at \(\mathfrak q\), one needs
\(s,a\notin\mathfrak q\) and a proved derivative comparison for the chosen
\(\alpha\). No current secant identity supplies those conditions. In the
quadratic diagnostic above, \(U=T\) and its conductor is already the unit
ideal, but \(D_s(t)\) is outside the secant lattice: even a trivial conductor
does not repair the missing generator comparison.

Rescaling the primitive generator illustrates the other failure. Taking
\(\alpha=t^3=st\) gives \(U=\mathbb C[t^2,t^3,y]\), with conductor
\((t^2)\), while \(D_s(\alpha)=3t/2\in T\). The derivative now belongs
to the secant lattice, but the conductor is contained in the boundary prime
\((t)\). Also \(D_s(\alpha)\notin U\), so this order is not a differential
order to which the normalization-preservation theorem could be applied.
These are two presentations of the same diagnostic, not new counterexamples
or Lean results.

### Adapted generator and the exact derivative test

Conductor avoidance and derivative regularity are separate. In the present
finite characteristic-zero normalization setting, conductor avoidance can
be arranged structurally. Fix a height-one prime \(\mathfrak q\subset T\)
and its height-one contraction \(\mathfrak p=\mathfrak q\cap B\).
Put \(R=B_{\mathfrak p}\) and
\(S=T\otimes_B R\). The special fibre of this finite semilocal Dedekind
algebra is a product of principal local Artinian algebras with separable
residue extensions. Over the infinite residue field of \(R\), these admit
a common algebra generator. Lifting it and applying Nakayama gives
\(S=R[\alpha]\). Scaling by a unit of \(R\) puts \(\alpha\) in \(T\);
finite denominator clearing then gives

\[
c\in B\setminus\mathfrak p,\qquad cT\subseteq B[\alpha].
\]

This is a mathematical construction outline, **not yet a Lean constructor**.
It does not say an arbitrary previously chosen primitive generator works.
The conditional cancellation step is now formalized in
[ConductorLocalization.lean](ConductorLocalization.lean): after such a
conductor element becomes a unit, control of \(D(\alpha)\) is equivalent
to control of all \(D(T)\) in the local lattice.

[GeneratorDerivative.lean](GeneratorDerivative.lean) uses Mathlib's
coefficientwise derivation API. For
\(f(X)=\sum_i a_iX^i=\operatorname{minpoly}_B(\alpha)\), it proves

\[
J D(\alpha)=-\nu_D,\qquad
J=f'(\alpha),\qquad \nu_D=\sum_i D(a_i)\alpha^i.
\]

For a torsion-free ambient module and \(J\ne0\), it proves the exact test
\(D(\alpha)\in\Lambda\) iff \(\nu_D\in J\Lambda\), and composes it with
the outside-prime conductor criterion. Base regularity only proves
\(\nu_D\in\Lambda\). With \(\Lambda=T_{\mathfrak q}\), the extra
divisibility is the substantive missing input. In additive DVR notation it
is \(v_{\mathfrak q}(\nu_D)\ge v_{\mathfrak q}(J)\); this valuation
translation is mathematical commentary, not a new Lean theorem here.
Both new files passed a targeted build; all seven lemmas have only
`propext`, `Classical.choice`, and `Quot.sound` in their axiom audits.

The distinction has geometric content: in an adapted monogenic neighborhood,
\(J\) generates the different, by
[Stacks, Example 49.12.5](https://stacks.math.columbia.edu/tag/0BWI).
Thus locally inverting the conductor does not remove possible ramification
from \(J\). In the quadratic diagnostic, \(f(X)=X^2-s\),
\(\nu_{D_s}=-1\), and \(J=2t\). The conductor is the unit ideal, but
\(-1\notin 2tT_{(t)}\). This still is not a Keller counterexample.

For a transverse frame, adapted-generator regularity forces index one by
the existing derivation criterion. Conversely, in residue characteristic
zero, index one gives unramifiedness and makes this local monogenic
Jacobian a unit. The derivative test therefore reformulates the local
ramification problem; it does not solve it using generic algebra alone.

In the original trace route, no outside-prime multiplier is required.
`boundarySeparation_of_secantFrameTraceLanding` uses only a nonzero element
of the secant denominator ideal; the pole witness defeats every such
multiplier. The open input there remains the uniform `hLanding` containment.

### Global source visibility and the localized unit-Jacobian test

The global polynomial input in
[General/Keller/DivisorVisibility.lean](../../../General/Keller/DivisorVisibility.lean)
is stronger than preservation of an arbitrary affine source ring. Every
unit in a polynomial ring over a reduced coefficient ring is a constant,
so inclusion of a coefficient subalgebra reflects units. For a Keller map,
an irreducible factor of a prime base element supplies a source divisor;
flat going-down identifies its contracted prime. Unique factorization in
the coordinate-image base extends this to every height-one base prime.
The resulting source divisor is unramified by Keller étaleness.

This is an unconditional **existence** result under `IsKeller`, not another
supplied-visibility interface. It does not assert that every prime of the
normalization has a visible center. In group terms, a nontrivial inertia
subgroup may fix one sheet and move others; existence of a fixed sheet is
not triviality of the subgroup. The source-divisor theorem itself ends at
a source prime. The transport is now proved separately in
[VisibleConjugateCenter.lean](../../../General/Normalization/VisibleConjugateCenter.lean):
lying-over lifts the intermediate prime and Galois transitivity realizes
it as a conjugate center of the selected normalization prime. Its
fixed-sheet corollary uses a supplied diagram and its existing local-index
realization, not a new no-ramification hypothesis. This targeted build
does not test the older unconditional model/index constructor.
All four transport/fixed-sheet declarations passed the axiom audit with
only `propext`, `Classical.choice`, and `Quot.sound`.
The visibility file passed its targeted build and all three public axiom
audits, with only the standard Lean axioms.

The sharper diagnostic uses the proper open source
\(A'=\mathbb C[t,t^{-1},u]\) and

\[
(s,z)=\left(t^2,\frac{u}{2t}\right),\qquad
\det\frac{\partial(s,z)}{\partial(t,u)}=1.
\]

Its target-dual derivations preserve \(A'\), but the normalization of
\(B=\mathbb C[s,z]\) in \(N=\mathbb C(t,z)\) is
\(T=\mathbb C[t,z]\). The derivative \(D_s(t)=1/(2t)\) is not regular
at \((t)\), where the extension has ramification index two. The new
visibility theorem excludes this example from its hypotheses: \(s=t^2\)
is a nonunit of \(B\) but a unit of \(A'\), so the entire base divisor
\(s=0\) is missed. The second coordinate is rational in \((t,u)\), not
a polynomial on the whole affine plane.

[LocalizedJacobianDiagnostic.lean](LocalizedJacobianDiagnostic.lean)
uses the actual fraction field of `PlanePolynomial`. It proves the four
source-coordinate derivative identities, the determinant-one identity,
the first target-frame identities, and nonmembership of \(D_s(t)\) in
the polynomial ring \(T\). The statements about the open source,
normalization, local nonregularity, and index two above are mathematical
interpretation, not additional Lean conclusions of that file. This is a
negative control for an overly general inference, not a JC counterexample.
Its targeted build and both public axiom audits passed, again with only
`propext`, `Classical.choice`, and `Quot.sound`.

A separate single-sheet shortcut also fails in the nonnormal branch.
If \(\alpha\) lies in a proper conjugate field \(g(L)\subsetneq N\),
then \(B[\alpha]\subseteq g(L)\). A nonzero conductor element \(c\)
would satisfy \(c\in B[\alpha]\) and \(ct\in B[\alpha]\) for every
\(t\in T\), forcing \(T\subseteq g(L)\) and hence
\(N=\operatorname{Frac}(T)\subseteq g(L)\), a contradiction. Thus a
normal-closure generator with usable conductor cannot simply be chosen on
one sheet to inherit source derivative regularity. This is a mathematical
audit of that candidate, not a newly formalized theorem.

### Visible--hidden secant test (2026-09-19)

The current `MovedConjugatePair D C` family pairs `g` with `σg` for
`σ ∈ C`. When `C` is contained in inertia, a sheet fixed by inertia
cannot occur in such a moved pair. A genuinely visible--hidden comparison
uses arbitrary distinct sheets, not an unmentioned member of this family.
The underlying `evaluatedSecantMatrix` already accepts arbitrary group
elements; no new coefficient family has been added without a usable bound.

For visible coordinates \(a\), hidden coordinates \(b\), and the actual
polynomial divided-difference matrix \(M\), the identities are

\[
M(a-b)=0,\qquad
(\delta M)(a-b)+M(\delta a-\delta b)=0.
\]

The matrix is singular for distinct collision points. Its differentiated
entries already involve hidden-sheet derivatives; assuming their local
regularity is not an independent way to establish that regularity.
Degree estimates give bounds for the fixed finite family, not a uniform
bound for arbitrary sections. Thus this attempt supplies neither local
frame preservation nor the open trace-landing containment.

Two complementary mathematical diagnostics delimit this test:

- For the **polynomial but non-Keller** map
  \(F(x,y)=(x,xy^3-y)\), over the generic point of \(x=0\), one root
  \(a\) of \(xy^3-y=u\) is regular and two other roots have poles.
  With the regular sheet first, the mixed matrix is
  \(\left(\begin{smallmatrix}1&0\\a^3&0\end{smallmatrix}\right)\).
  Its entries and their target-frame derivatives are regular, while the
  other sheets remain polar. Its Jacobian is \(3xy^2-1\), not a constant.
  Here the frames are the rational inverse-Jacobian target derivations,
  not the constant-Jacobian Keller specialization: their values on \(a\)
  have denominator \(3xa^2-1\), a unit at the visible center.
- For the **unit-Jacobian but rational** map on a proper open source,
  \[
  (s,z)=\left(t^3-3t,\frac{u}{q(t)}\right),\qquad q(t)=3t^2-3,
  \]
  every complex target point has a preimage with \(q(t)\ne0\).
  At \(s=-2\), the factorization
  \(t^3-3t+2=(t-1)^2(t+2)\) exhibits a deleted ramified root \(1\)
  and a surviving simple root \(-2\). Yet
  \(\partial_s t=1/q(t)\) has a pole at the deleted root.
  This source ring contains \(q(t)^{-1}\): the root is deleted even though
  \(t\) and \(u\) themselves remain finite. That is a concrete difference
  from a missing center for the full polynomial source \(\mathbb A^2\).

For the second diagnostic, let \(r\) be the root approaching \(-2\),
with \(u=q(t)z\) and \(v=q(r)z\). The **rational**, hidden--visible
ordered secant matrix is

\[
M=\begin{pmatrix}
0&0\\
-3z(t+r)/q(r)&1/q(r)
\end{pmatrix}.
\]

Its entries are regular at this mixed pair, but \(\partial_s M\) has
a pole at the generic point of \(s=-2\), where \(z\ne0\). The leading pole terms in
\((\partial_sM)(t-r,u-v)\) and
\(M\partial_s(t-r,u-v)\) cancel. These rational divided differences
are **not** an instance of the polynomial `ExplicitSecant` construction.
This example therefore rules out an inference from visibility and local
unit-Jacobian identities alone, not an argument using the full polynomial
Keller hypothesis. Neither diagnostic is a Jacobian-conjecture
counterexample, and their complementary hypotheses cannot be combined
into one.

The cubic variant in
[LocalizedJacobianDiagnostic.lean](LocalizedJacobianDiagnostic.lean)
checks three precise claims: point-surjectivity on its stated domain,
source/target frame identities with determinant one, and nonmembership of
the target derivative in \(\mathbb C[t,z]\). Its targeted build passed.
All three cubic declarations passed the same standard-axiom audit; the
two earlier quadratic diagnostic declarations were rechecked as well.
The mixed matrices, local pole interpretation, and normal-closure geometry
in this audit are mathematical calculations, not additional conclusions of
that Lean file.

The next substantive target must use a global polynomial constraint that
these tests do not share. Merely enlarging the finite secant family does
not supply one. Keep the existing denominator and generator criteria on
the bench until such a comparison is proved.

### Local collision and closure audit (2026-09-19)

The direct argument now uses the polynomial secant determinant:
if two collision maps into a local ring have equal coordinate residues,
their evaluated determinant is congruent to the nonzero Keller constant.
It is a unit and annihilates the coordinate differences, so the maps agree.
[LocalCollision.lean](LocalCollision.lean) proves both statements over an
arbitrary commutative local \(\mathbb C\)-algebra, not just a domain.
[InertiaCoordinates.lean](InertiaCoordinates.lean) applies this to actual
valuation inertia and the existing conjugate-source maps. A moved sheet
has a nonregular coordinate; no conjugate-index realization is assumed.
The compatible inclusion of \(\mathbb C\) in the valuation ring is explicit.

This proves the local contradiction **if the source coordinates are regular**.
It does not prove that regularity. At a boundary divisor, extending just
the off-diagonal projector proves nothing: its field value is already
\(1\). To specialize the pair to the diagonal requires a homomorphism
from the whole collision algebra into the local ring, hence regularity of
both source-coordinate tuples.

Normalization does not reverse this requirement. For a conjugate source
\(A_g=gA\), let \(S_g=\operatorname{IntCl}_B(gL)\) be the finite
normalization of the target ring in that source function field.
Normality of the polynomial source gives

\[
S_g\subseteq A_g,
\]

not \(A_g\subseteq S_g\). Enlarging the space by adding its boundary need
not extend affine coordinate functions. For example, the graph \(tx=1\)
is already closed in \(\mathbb A^1_t\times\mathbb A^1_x\) and has no point
over \(t=0\); its projective closure adds a point where \(x\) has a pole.
This is an elementary closure diagnostic, not a Keller example.

Local monic equations for each source coordinate over \(B_{\mathfrak p}\)
would suffice, since \(T_{\mathfrak q}\) is integrally closed. Finite generic
degree supplies algebraicity over \(K\), not these monic local equations.
Clearing their coefficients after inverting a nonzero base element leaves
the same unresolved question: does that element avoid the chosen prime?

### Global polynomial pole-order test (2026-09-19; not formalized)

There is a genuine constraint beyond the proper-open diagnostics, but it
does not yet exclude poles in arbitrary degree. Let
\(d=\max(\deg P,\deg Q)\) be **total polynomial degree**, not generic degree.
At a height-one prime \(\mathfrak q\) over \(\mathfrak p=(b)\), normalize
the additive valuation by \(v(\pi)=1\) and write \(e=v(b)\). Choose an
actual target partial \(D=\partial_P\) with \(Db\notin\mathfrak p\),
or interchange \(P,Q\). On a conjugate source sheet put
\(M=\max(0,-v(x),-v(y))\).

For \(M>0\), a coordinate \(z\) with \(v(z)=-M\) satisfies

\[
v(Dz)=-M-e.
\]

The completion argument matters. Transversality makes
\(\kappa(\mathfrak p)\) finite separable over \(\mathbb C(Q)\);
\(\kappa(\mathfrak q)\) is also finite over that field
([Stacks, Tag 09E5](https://stacks.math.columbia.edu/tag/09E5)).
Lift a primitive residue generator by
[Hensel's lemma](https://stacks.math.columbia.edu/tag/04GE) to obtain a
coefficient field \(E\) containing \(\mathbb C(Q)\). The completed local
ring is \(E[[\pi]]\)
([Stacks, Lemma 10.160.10](https://stacks.math.columbia.edu/tag/0323)).
In its Laurent series field, write \(b'=d b/d\pi\). The derivation
\((Db/b')\,d/d\pi\) agrees with \(\partial_P\) on \(P,Q\), hence with
its extension to \(N\) by separability. Since characteristic is zero,
\(v(b')=e-1\) and a pole of order \(M\) differentiates to order \(M+1\).
This proves the displayed valuation formula. It neither assumes regularity
of \(D\) on the local ring nor silently drops the derivative of the unit
in \(b=\pi^e u\).

The actual polynomial inverse-Jacobian frame has coefficients of degree
at most \(d-1\). Constants have valuation zero, so

\[
-M-e=v(Dz)\ge -(d-1)M,
\qquad\text{hence}\qquad e\le(d-2)M.
\]

Thus total polynomial degree at most two excludes such coordinate poles,
even when \(e=1\). This is **not** the generic-degree-two result. For
\(d\ge3\) the inequality is compatible with a pole. Repeating the same
derivative gives \(v(D^r z)=-M-re\) and polynomial degree at most
\(1+r(d-2)\), hence only the same bound. Iteration alone cannot close
the argument. The formal-series calculation and degree estimate are
mathematical audits, not conclusions of `InertiaCoordinates.lean` or of
the existing supplied `CompletedTameRamificationData`.

### Original-extension pole test (2026-09-19)

The smaller geometric target uses \(S=\operatorname{IntCl}_B(L)\subseteq A\).
If \(x,y\) are regular at every height-one prime of \(S\), then
\(S=\bigcap_{\operatorname{ht}\mathfrak p=1}S_{\mathfrak p}\) gives
\(A=S\), hence finiteness of the original map
([Stacks, Tag 031T](https://stacks.math.columbia.edu/tag/031T)).
The existing source open immersion and polynomial frame do not prove this
regularity at the omitted primes. This height-one reduction is not yet a
packaged Lean theorem in the development.

There is a positive exclusion for **genuinely monomial valuations in
polynomial source coordinates**, in every dimension and degree. The
Jacobian matrix at the source origin is invertible, so each coordinate
\(x_i\) occurs with nonzero linear coefficient in at least one target
polynomial \(F_j\). For a monomial valuation, a regular polynomial has
nonnegative value on every supported monomial. Since \(F_j\) is regular
at any prime above the affine target, it follows that \(v(x_i)\ge0\).
Thus such a valuation cannot be a source-coordinate pole. This uses only
the nonsingular linear part, not a degree bound or a Galois hypothesis.

[General/Keller/MonomialWeights.lean](../../../General/Keller/MonomialWeights.lean)
formalizes the two algebraic statements as
`exists_linearCoeff_ne_zero_of_isKeller` and
`nonneg_weights_of_isKeller`. The latter uses Mathlib's existing
`Finsupp.weight` and explicitly assumes nonnegative weights on every
supported monomial of each component. It does not construct a valuation
or infer the support hypothesis from general valuation regularity.

The exact obstruction beyond this subcase is cancellation. In
\(\mathbb C(t,u)=\mathbb C(x,z)\), set

\[
x=t^{-1},\qquad z=t+t^2u.
\]

For the \(t\)-adic valuation, \(v(x)=-1\), \(v(z)=1\), but
\(xz-1=tu\) has positive value and
\(x^2z-x=u\) is regular although both displayed monomials have value
\(-1\). Thus regularity of \(F_j\) does not generally imply regularity
of each term in its polynomial support. Monomialization on a birational
chart is not a polynomial change of coordinates on the original source;
one cannot transfer the preceding argument without checking that distinction.

This gives a concrete **non-Keller** polynomial diagnostic:

\[
(P,Q)=(z,x^2z-x),\qquad
S=\mathbb C[P,Q,\alpha]/(\alpha^2-\alpha-PQ),\quad \alpha=Px.
\]

The model \(S\) is smooth, finite over \(\mathbb C[P,Q]\), and has the
same fraction field as \(A=\mathbb C[x,z]\). Its height-one prime
\((P,\alpha-1)\) is omitted by the source open immersion and \(x\) has
a pole there; the companion prime \((P,\alpha)\) is visible. On the
hidden chart the Jacobian is \(1-2xz=-1-2tu\), a local unit, but it is
**not a constant polynomial**. The hidden prime is unramified. Hence a
coordinate pole does not conversely imply nontrivial inertia, and local
Jacobian invertibility there does not rule out the pole.

The two-form shortcut also fails: here \(dx\wedge dz=-dt\wedge du\)
is regular despite the coordinate pole. More generally
\(x=t^{-1}\), \(y=t^{-1}+t^m u\), with \(m\ge2\), give
\(dx\wedge dy=-t^{m-2}dt\wedge du\); its order can be arbitrarily
positive. These are valuation diagnostics, not Keller counterexamples.

Finally, unit reflection does not make every missing divisor principal.
For a Noetherian normal domain \(S\) with dense source open
\(\operatorname{Spec}A\subseteq\operatorname{Spec}S\), the
divisor restriction sequence and \(A^*=S^*=\mathbb C^*\),
\(\operatorname{Cl}(A)=0\), identify \(\operatorname{Cl}(S)\) with the
free group on the missing prime divisors. This follows from the
[Weil-divisor presentation](https://stacks.math.columbia.edu/tag/0BE0).
The diagnostic above has one missing divisor and class group \(\mathbb Z\).
Finiteness over the polynomial target therefore does not imply the torsion
class-group premise that would remove that boundary.

The remaining substantive target is to exclude the nonmonomial
cancellations for an actual polynomial Keller pair, or to find another
global argument forcing regularity. Neither the class-group calculation
nor the local two-form equality supplies that exclusion. The geometric
diagnostics and valuation applications in this section are mathematical
audits, separate from the formal weighted-support calculation.

## Marked-field Galois descent (2026-09-19)

The explicit research target in [GaloisDescent.lean](GaloisDescent.lean) is
that every \(g\in\operatorname{Gal}(N/K)\) sends both marked source
coordinates into \(\iota(L)\). Equivalently, for each \(g\) there should
be rational functions \(r_g,s_g\in\mathbb C(x,y)\) such that
\(g(\iota(x))=\iota(r_g)\) and \(g(\iota(y))=\iota(s_g)\).
These rational functions are not constructed by the target definition.

The shared field-theoretic bridge proves that coordinate membership is
equivalent to preservation of the entire marked field. Since \(N\) is the
actual normal closure, this preservation forces \(\iota(L)=N\), hence
normality of \(L/K\). It does **not** by itself force \(L=K\).
The explicit `ComplexKellerGaloisRigidity 2` input supplies the subsequent
polynomial-invertibility conclusion; the existing collision API then
gives \(\operatorname{Obs}(F)=0\).

The target is rational descent, not regularity on a source sheet or in a
valuation ring, and it does not ask that \(g\) fix the coordinates
pointwise. Neither a single inertia-fixed sheet nor normality of the
closure implies it. The target is defined, and its conditional consequences
are proved; it is not assumed as an axiom or proved for all Keller maps.
With the accepted rigidity input it is as strong as full complex \(JC(2)\).
Its promotion criterion is an actual Keller-specific proof of this
membership, not another equivalent formulation of normality.

## Descent witness and frame audit (2026-09-19)

The first concrete test of marked-field descent uses the existing fixed
field of \(H\), not another normality predicate. The shared lemma
`NormalClosureData.exists_fixingSubgroup_move_of_not_mem` proves

\[
z\notin\iota(L)\quad\Longrightarrow\quad
\exists h\in H:\ h(z)\ne z.
\]

It uses the existing perfect-base-field hypothesis of the fixed-field API.
The polynomial specialization
`polynomialSource_exists_moved_conjugate_coordinate_of_not_normal` supplies
such a witness on a conjugate source coordinate whenever \(L/K\) is
nonnormal. It is dimension-independent; over the complex base the
perfectness hypothesis is automatic.

For the planar map, the existing `polynomialGaloisCollisionPair D g h`
then gives two distinct equal-image tuples. The existing secant theorem
evaluates their secant determinant to zero, and the Keller specialization
factors through `OffDiagonalRing F`. The element \(h\) fixes the original
sheet, which is not either of these two moving tuples. It need not be an
inertia element at any supplied valuation. Consequently, this construction
does not provide the common local center or equal residue tuples required
by [LocalCollision.lean](LocalCollision.lean). If actual inertia is supplied,
the existing [InertiaCoordinates.lean](InertiaCoordinates.lean) instead
forces a coordinate pole; exclusion of that pole remains open.

The differential test also does not establish descent.
[KellerFrameExtension.lean](../KellerFrameExtension.lean) already proves
that both extended Keller derivations preserve every conjugate polynomial
sheet separately. Unique extension to a finite separable field is the
formally étale mechanism (see
[Stacks, Lemma 10.158.1](https://stacks.math.columbia.edu/tag/090W)). Uniqueness
also makes the extended target derivations commute with the Galois group;
it does not identify the conjugate fields.

The existing proper-open cubic diagnostic makes this distinction concrete.
Write

\[
K=\mathbb C(s,z),\qquad L=\mathbb C(t,z),\qquad s=t^3-3t.
\]

The target derivatives extend with
\(D_s(t)=(3t^2-3)^{-1}\) and \(D_z(t)=0\). They commute, and their
extensions to the normal closure commute with its Galois group. But another
root \(r\) satisfies

\[
r^2+tr+t^2-3=0,
\]

whose discriminant \(12-3t^2\) is nonsquare in \(L\): it has simple
zeros at \(t=2\) and \(t=-2\). Thus \(r\notin L\), and descent
fails. With \(q(r)=3r^2-3\) and \(v=q(r)z\), each localized conjugate
source ring \(\mathbb C[r,v,q(r)^{-1}]\) remains stable under the two
target derivatives. The source is a proper open, not the full polynomial
plane; this is not a polynomial Keller counterexample.

The discriminant and normal-closure calculation here is a mathematical
audit, not an additional Lean theorem in
[LocalizedJacobianDiagnostic.lean](LocalizedJacobianDiagnostic.lean).
The diagnostic rules out an argument using only field-level frame
compatibility. A successful descent argument must supply additional global
polynomial information; no new universal target wrapper is introduced for
that missing information.

## Common-center and all-conjugate-ring test (2026-09-19)

Let \(a,b:A\to R\) be distinct Keller collision maps into a domain,
and put \(J=(a(x)-b(x),a(y)-b(y))\). If \(s\) is the evaluated
secant determinant and \(c\in\mathbb C^\times\) is the constant
Jacobian, the existing secant identities give

\[
s=0,\qquad s-c\in J,\qquad\text{hence}\quad J=R.
\]

This applies to the actual subalgebra generated by both tuples, not only
to the ambient field (where a nonzero coordinate difference is already
invertible). Consequently no proper ideal in the simultaneous regularity
domain contains both differences. Prime selection or Krull height cannot
produce a common residue center. Even two nonunits can generate the unit
ideal: \((x,xy-1)=\mathbb C[x,y]\).

This is the image of the existing
`diagonal_sup_collisionOffDiagonalIdeal_eq_top` and the moved-pair
factorization in [ConjugateSecantEvaluation.lean](../../ConjugateSecantEvaluation.lean).
Two temporary Lean lemmas verified the secant-zero statement for arbitrary
commutative complex algebras and its distinct-pair domain specialization;
their axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`.
No duplicate public API or new universal target was added.

For the global ring test, identify \(A\) with its marked image and write
\(E=B[g(A):g\in G]\subset N\). This is temporary notation for the
mathematical audit, not a new Lean object or a replacement for the finite
normalization \(T\). The finite tensor product of the conjugate étale
source algebras maps to \(N\); the corresponding regular connected
component has coordinate ring \(E\). Thus \(E/B\) is étale and
\(\operatorname{Frac}(E)=N\).

The nonidentity elements of \(G\) act without geometric fixed points
on \(\operatorname{Spec}E\): the equalizer with the identity is open
by unramifiedness and closed by separatedness, hence empty on this connected
component. This uses the
[open diagonal of an unramified map](https://stacks.math.columbia.edu/tag/02GE).
The [finite free-action quotient](https://stacks.math.columbia.edu/tag/07S7)
is a finite étale torsor. Étale descent and birationality then make
\(\operatorname{Spec}(E^G)\) an affine open of \(\operatorname{Spec}B\).
Its complement has pure codimension one; factoriality of the polynomial
image algebra \(B=\mathbb C[P,Q]\) makes it principal (see
[complements of affine opens](https://stacks.math.columbia.edu/tag/0BCQ)).
Therefore, for some \(0\ne d\in B\),

\[
E^G=B[1/d],\qquad E^H=A[1/d].
\]

For the second equality, \(E^H\) contains \(A[1/d]\), is integral
over it because \(E\) is finite over \(B[1/d]\), and lies in
\(L\). Normality of \(A[1/d]\) gives the reverse containment.
This does not prove \(E^H=A\): it describes the possible deleted
divisor. The nonconstant units of \(A[1/d]\) need not be units of
\(A\); flatness of localization does not supply faithful flatness.

Frame preservation gives no further restriction here. Every derivation
of \(A\) preserves \(A[1/d]\), with
\(D(d^{-1})=-D(d)d^{-2}\), by
[localization of derivations](https://stacks.math.columbia.edu/tag/07PE).
It does not follow that the boundary ideal is preserved. A single
nonzero multiplier clearing the *whole* overring would force equality by
`subalgebra_eq_bot_of_nonzero_mul_mem_base` in
[MonogenicLanding.lean](../MonogenicLanding.lean), but obtaining that bound
is precisely the earlier uniform-denominator gap, not a new consequence.

The proper-open cubic diagnostic illustrates the deletion explicitly:
\(A_0=\mathbb C[t,z,(t^2-1)^{-1}]\), \(s=t^3-3t\), and
\(B=\mathbb C[s,z]\). Adjoining all conjugate source rings inverts
\(s^2-4=(t^2-1)^2(t^2-4)\), giving
\(E^H=A_0[(t^2-4)^{-1}]\supsetneq A_0\). The visible original
points \(t=\pm2\) disappear because other sheets are missing there.
This is not a polynomial Keller map on the whole plane.

The quotient-ring calculation and this diagnostic are mathematical audits,
not Lean theorems added in this step. The tested common-center shortcut
does not close descent. A new global argument must exclude the deleted
divisor or otherwise prove descent; none is supplied by the construction.

## Reduced boundary and simple-pole test (2026-09-19)

For the preceding all-conjugate open \(U=D(d)\subset\operatorname{Spec}B\),
use its reduced boundary ideal
\(\mathfrak b=\sqrt{(d)}=(s)\), with \(s\ne0\) squarefree.
This ideal depends only on \(U\), not on its chosen equation. It is a
base ideal in \(B\), not the intermediate boundary ideal in \(S\),
the ramification ideal, or the finite secant denominator in \(T\).
The all-conjugate-open construction remains a mathematical audit rather
than an instantiated Lean object.

[SimplePole.lean](../../../General/Normalization/SimplePole.lean) proves,
for a derivation \(D\) on a domain and its extension to the fraction field,

\[
D(s^{-1}B)\subseteq s^{-1}B
\quad\Longleftrightarrow\quad D(1/s)\in s^{-1}B
\quad\Longleftrightarrow\quad D(s)\in(s).
\]

Thus the two target partials preserve simple poles precisely when they
preserve \(\mathfrak b\); base transversality then forces
\(\mathfrak b=B\). The finite defect is
\((\partial_Ps\bmod s,\partial_Qs\bmod s)\). For \(b\in B\),
the identity
\(s^2D(b/s)\equiv-bD(s)\pmod{s}\) displays the possible new pole.
Preserving the entire localization is automatic by the
[derivation localization formula](https://stacks.math.columbia.edu/tag/07PE);
preserving this bounded-pole module is not.

The active comparison stops at first order: the original module has one
generator \(1/s\), and adjoining \(D_P(1/s),D_Q(1/s)\) gives a
module with at most three generators. Its quotient by \(s^{-1}B\)
has at most two generators and vanishes exactly when the two tests pass.
No higher jets or whole-overring transporter are needed to formulate this
finite target. This is finite generation over \(B\), not over
\(\mathbb C\); choosing the finite stage does not establish its equality
with the original module. Existing spans suffice, without a new universal
predicate or a duplicate boundary-object definition.

Geometrically, the same two classes are the value on the generator of the
standard conormal map
\(\mathfrak b/\mathfrak b^2\to
\Omega_{B/\mathbb C}\otimes_B B/\mathfrak b\),
\(s\bmod s^2\mapsto ds\bmod s\); see the
[conormal exact sequence](https://stacks.math.columbia.edu/tag/00RU).
This attaches the finite test to the actual reduced boundary rather than
to an arbitrary truncation of the section ring. It is an interpretation
of the same test, not an additional Lean object or an established
Keller-specific vanishing statement.

The actual first-jet construction does not prove that preservation.
If \(\Lambda_0=T+\sum_iTa_i\) is the matrix-coefficient lattice and
\(\Lambda_1=\Lambda_0+\sum_iT D_Pa_i+\sum_iT D_Qa_i\), their
denominator ideals satisfy \(I_1\subseteq I_0\). Including derivatives
allows a larger denominator; it supplies no pole-cancellation assertion.
Even the weaker implication \(D_j(I_1)\subseteq I_0\) by Leibniz
requires \(D_j(T)\subseteq T\), which is not established at the boundary.
[SecantReduction.lean](SecantReduction.lean) removes the adjugate
redundancy but does not remove these derivatives.

The existing proper-open diagnostic makes the distinction explicit. In
its notation,

\[
P=t^2,\quad Q=z,\quad u=2tz,\qquad
A_0=\mathbb C[t,u,t^{-1}],\quad T=\mathbb C[t,z].
\]

The rational map \((t,u)\mapsto(t^2,u/(2t))\) has determinant one
on \(t\ne0\). Its conjugate pair \((t,u),(-t,-u)\) has ordered
telescoping secant matrix and first target derivative

\[
M=\begin{pmatrix}0&0\\ z/t&-1/(2t)\end{pmatrix},\qquad
D_PM=\begin{pmatrix}0&0\\-z/(2t^3)&1/(4t^3)\end{pmatrix}.
\]

Here \(D_QM\) has sole nonzero entry \(1/t\), so
\(I_0=(t)\) and \(I_1=(t^3)\). The reduced base boundary has equation
\(s=P\), and \(D_P(1/P)=-1/P^2\) is not a simple pole.
The first-jet denominator also fails the uniform trace test:
\(t^{-5}\in A_0\), but
\(\operatorname{Tr}_{L/K}(t^3t^{-5})=2/P\notin B\).
These matrix, denominator-ideal and trace calculations are mathematical
audits, using the rational extension of the telescoping formula, not a
specialization of the polynomial `ExplicitSecant` implementation.
[LocalizedJacobianDiagnostic.lean](LocalizedJacobianDiagnostic.lean)
verifies the target-frame inverse derivative and its failure to remain
in the simple-pole span.

This source is a proper open with nonconstant units, not the full
polynomial plane; it is not a Keller counterexample. The test excludes
an inference from only the local Jacobian, secant and conjugate-frame
identities. A successful proof must use additional global polynomial
information. In particular, the actual secant denominator has not been
identified with the reduced base-boundary ideal, and its first jets have
not been shown to kill the displayed defect.

## Finite conormal realization and Galois--secant comparison (2026-09-19)

[ConormalDerivation.lean](../../../General/Normalization/ConormalDerivation.lean)
now constructs a derivation's component
\(I/I^2\to B/I\), \([f]\mapsto[D(f)]\), using Mathlib's
`Ideal.Cotangent`. Its evaluation and zero-map criteria are proved.
For \(I=(s)\), vanishing is exactly \(D(s)\in(s)\); for a nonzero
ideal in a characteristic-zero polynomial ring, all coordinate components
vanish exactly when \(I=B\). Existing finite-generation instances over
both \(B\) and \(B/I\) were verified over a Noetherian base. This
does not instantiate the actual Keller boundary or prove its preservation.

The finite simple-pole quotient and the conormal map should not be
identified as modules. Multiplication by \(s^2\) identifies the former
\(M_1/M_0\) with the ideal generated by
\(\partial_Ps,\partial_Qs\) in \(B/(s)\); the conormal map instead
sends \(1\) to that pair in \((B/(s))^2\). For reduced \(s\),
both detect every boundary component: at each irreducible factor of
\(s\), some coordinate partial is nonzero modulo that factor.
These quotient/support comparisons are mathematical audits, not new Lean
theorems. Their common vanishing criterion does not identify their images.

Galois symmetry supplies the secant relation before coordinate descent.
For \(a=g(\iota(x))\), \(b=h(\iota(x))\), both automorphisms fix
\(K\), so \(F(a)=F(b)\) and \(M_F(a,b)(a-b)=0\).
For distinct tuples the secant determinant vanishes. The relevant APIs
are the existing `PolynomialCollisionPair` and
[ConjugateSecantEvaluation.lean](../../ConjugateSecantEvaluation.lean).
Coordinate descent places these rational identities inside the marked
\(L\), but is not needed to obtain them. Once descent is proved,
Keller--Galois rigidity already gives invertibility. It must not be
assumed while claiming to prove the still-missing boundary comparison.

The useful direction remains failure of descent, then a finite moved
coordinate/secant witness, then a new boundary comparison. Fixing the
original field does not make the moving element inertia or furnish a
common residue center. No existing relation kills the two actual
conormal classes. The new manuscript section records this gap, and
pruning remains deferred until a comparison has identified its dependencies.

## Galois--secant boundary comparison audit (2026-09-19)

The proper-open diagnostic also tests the proposed Galois shortcut itself.
In source coordinates put
\[
A_0=\mathbb C[t,u,t^{-1}],\qquad
P=t^2,\quad Q=u/(2t),\qquad B=\mathbb C[P,Q].
\]
Then \(L=\mathbb C(t,Q)\) is Galois of degree two over
\(K=\mathbb C(P,Q)\). Its nonidentity automorphism sends
\((t,u)\) to \((-t,-u)\), preserves \(A_0\), and commutes with the
extended target derivatives. The all-conjugate algebra is \(E=A_0\),
with \(E^G=B[1/P]\). Nevertheless its reduced base boundary is
\((P)\), and \(\partial_P P=1\notin(P)\).

Thus even regular Galois descent on this open source, the unit Jacobian,
and the collision/secant identities do not force boundary preservation.
This is **not** a full-plane polynomial Keller map and does not challenge
Keller--Galois rigidity. Any proposed comparison must use the full source
\(A=\mathbb C[x_1,x_2]\) at an identifiable step.

The finite secant test is sharper than merely checking that denominators
can be cleared. For the rational secant entry \(m=-1/(2t)\),
\[
4m^2=1/P,\qquad D_Pm=1/(4t^3),\qquad
8mD_Pm=-1/P^2\notin P^{-1}B.
\]
So even a finite invariant polynomial in secant entries representing the
boundary reciprocal does not supply its required first-derivative bound.
The normalized traces of \(m,D_Pm,D_Qm\) vanish in this example;
their linear trace span does not capture \(1/P\), while a product does.
These Galois/invariant-ring and rational-secant calculations are a
mathematical audit, not additional claims about what the existing
polynomial secant implementation formalizes.

Moreover, \(G\) acts trivially on \((B/(s))^2\). Averaging fixes the
two conormal classes rather than annihilating them. A useful next lemma
must connect those classes to an actually vanishing expression and prove
the needed pole bound; neither a new finite denominator nor a Galois
average is enough. No such connection is assumed in the proof spine.

## Alternative routes and presentations

| Object / source | Role | Promotion criterion |
| --- | --- | --- |
| \(\Omega_{T/B}\) and `PlanarRamificationRigidity` in [Rigidity/Statements.lean](../../Rigidity/Statements.lean) | Finite length is a sufficient divisorial criterion; the support bridge is an explicit input. | Prove the finite-length or height-one-vanishing assertion from the Keller condition, and supply the formal bridge. Finite generation is not enough. |
| `PlanarBoundaryCoherence` in the same file | Alternative global-boundary route using local cohomology. | Establish its Keller-specific premise and the explicit boundary-coherence bridge; do not infer either from normalization finiteness. |
| `MonogenicOrder`, `MonogenicTraceDual`, `TateReconstruction`, [MonogenicLanding.lean](../MonogenicLanding.lean), [ConductorComparison.lean](ConductorComparison.lean), [ConductorLocalization.lean](ConductorLocalization.lean), and [GeneratorDerivative.lean](GeneratorDerivative.lean) | Give the monogenic/conductor trace presentation, cancel a supplied local-unit conductor, and isolate the exact coefficientwise divisibility needed for generator derivatives. The bounded-overring lemma still supports the concrete trace-bound route. | Prove that the actual Keller frame satisfies this divisibility for a locally adapted generator. The local generator constructor is separate formalization work; do not treat its existence as the missing Keller theorem. Retain shared lemmas without promoting an unused presentation into the spine. |
| `FixedMovingBoundaryPrincipalParts`, `FinitePrincipalPartsControl`, `UnboundedPrincipalParts` | An alternative principal-parts formulation. The actual-section pole witness no longer requires a local-cohomology comparison. | Supply a new bound or contradiction not already assumed by the endpoint; otherwise keep separate from the primary argument. |
| [Keller--Galois rigidity](../../../General/Automorphism/GaloisRigidity.lean) and [GaloisDescent.lean](GaloisDescent.lean) | Settle the quadratic special case; the coordinate-descent target is equivalent to normality of \(L/K\), with a conditional vanishing endpoint. | Prove descent for arbitrary planar Keller maps, not merely normality of the already-constructed closure. |

## Negative controls to retain

- [FiniteDenominatorCounterexample.lean](../FiniteDenominatorCounterexample.lean)
  proves that a nonzero finite coefficient denominator can coexist with a zero
  whole-overring transporter. Use it to reject finite-clearing arguments that
  claim uniform landing without an additional input.
- [LogarithmicInertia.lean](../LogarithmicInertia.lean) and
  [CompletedTameRamification.lean](../CompletedTameRamification.lean) retain
  inertia-invariant poles at multiples of the ramification index. An eigenvalue
  identity does not remove these poles. The completed local data still supplies
  its derivation; it is not automatically identified with the actual Keller
  frames.

These are tests of proposed implications, not counterexamples to planar
vanishing. They belong on the bench even if the final proof never imports them.

## Maintenance rule

For each new object or proposed lemma, record:

1. The exact missing implication it is meant to establish.
2. Its hypotheses, especially any equivalent form of the desired vanishing.
3. Its downstream consumer in the spine, or the negative test it provides.
4. Whether it is a definition, proved conditional lemma, open candidate, or
   verified specialization; record the relevant build when promoting it.

Promote an object when it removes a premise or gives a necessary comparison.
Keep alternative presentations and useful falsification tests on the bench.
Archive only after checking actual imports and theorem uses; do not delete
shared infrastructure merely because one research route stops using it.
