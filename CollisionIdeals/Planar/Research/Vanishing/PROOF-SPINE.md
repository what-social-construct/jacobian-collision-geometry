# Primary proof spine: planar vanishing

## Endpoint and notation

For a planar Keller map $F=(P,Q)$, the endpoint is
$\mathrm{Obs}(F)=0$, not vanishing of the diagonal ideal itself.
Use the existing declarations:

- `PlanarVanishing` in [Statements/Vanishing.lean](../../Statements/Vanishing.lean).
- `planarVanishing_iff_forall_collisionIdeal_eq_diagonalIdeal` in
  [Equivalences/Vanishing.lean](../../Equivalences/Vanishing.lean): the same goal
  is $I_R(F)=I_\Delta$.
- `planarJacobianConjecture_iff_planarVanishing` in
  [Equivalences/JacobianConjecture.lean](../../Equivalences/JacobianConjecture.lean):
  the equivalence with polynomial invertibility takes Ax--Grothendieck explicitly.

Write $A=\mathbb C[x,y]$, $B=\mathbb C[P,Q]$,
$K=\mathrm{Frac}(B)$, $L=\mathrm{Frac}(A)$,
$N$ for the marked normal closure of $L/K$, and $T$ for the integral
closure of $B$ in $N$. These are the shared objects, not new planar copies.

## Coherent derivation exclusion

[DerivationAnnihilator.lean](../../../General/Normalization/DerivationAnnihilator.lean)
formalizes the first coherent-analogy checkpoint. An additive operator
satisfying a base derivation's Leibniz rule preserves the module
annihilator under that derivation. For an algebra isomorphic to a
characteristic-zero polynomial ring, compatible operators for all target
partials give

```math
\mathrm{Ann}_B(M)\ne0\quad\Longrightarrow\quad M=0.
```

The main result needs neither finite generation nor commuting operators.
Its finite-torsion corollary obtains the nonzero annihilator from
Mathlib's existing theorem. The index type of the polynomial variables is
arbitrary, and no new connection structure or quotient is introduced.

This supplies an exclusion mechanism for a given action, not an action or
finiteness theorem for the actual boundary module. The section-side
construction and actual quotient action below provide the setting in
which to test preserved finite stages. The normalization field action is not
assumed to descend to $N/T$.

Verification (2026-11-08, Lean 4.28.0): the targeted module builds, and a
separate importing client checks the transported and finite-torsion
endpoints, infinite and empty coordinate families, and the zero-annihilator
regular-module control. The generic annihilator lemma uses only
`propext` and `Quot.sound`; the two characteristic-zero endpoints
also use `Classical.choice`, with no custom mathematical axioms.
The broader `CollisionIdeals.Planar.Research` build was stopped during a
slow dependency rebuild, after 3799 of 3812 jobs and without reported
errors; umbrella verification is not recorded as complete.

## Actual target sections modulo the base

[ConjugateInvariantSections.lean](../../../General/Keller/ConjugateInvariantSections.lean)
identifies the existing fixed algebra over the original base with sections
on its actual target open:

```math
E^G\simeq_B\Gamma(U_F,\mathcal O),\qquad
E^G/B\simeq_B\Gamma(U_F,\mathcal O)/B.
```

Both quotients are standard module quotients by the image of
`Algebra.linearMap`, not quotient rings or new quotient structures.
This target-section quotient is not a redefinition of
$\mathrm{Obs}(F)\subseteq C_F$.
The section equivalence respects the original restriction map, using the
generic [affine-open section comparison](../../../General/Normalization/AffineOpenSections.lean).
The same module detects the actual boundary:

```math
E^G/B=0\quad\Longleftrightarrow\quad\mathfrak b_F=B.
```

Its torsion theorem needs only the existing separable normal-closure data,
not the Keller condition. The target-field embedding clears a denominator
for each class, by the generic
[fractional quotient lemma](../../../General/Normalization/FractionalQuotient.lean).
It supplies no uniform annihilator or finite generation.

This completes the section-side bridge, not the comparison with
`BoundaryPrincipalParts`. That comparison requires an adapter between
Mathlib's filtered-Ext functor and the newer AXIOM derived/Čech model,
including the Ext transition maps. It need not block the direct quotient
route: the actual target-partial action is constructed below, while
preservation of a finite stage containing the boundary class under study
remains to be proved.

Verification (2026-11-08, Lean 4.28.0): all three new leaves pass the
focused build (2950 jobs). A separate importing client checks base-map
compatibility, quotient representatives and round trips, fractional
torsion, and the actual-map specialization. All seven audited
declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
The generic section leaf has one unused-simp-argument warning; there are
no build errors. The full research umbrella was not rerun for this
checkpoint.

## Actual quotient Leibniz action

[InvariantFrame.lean](../InvariantFrame.lean) restricts the existing
normal-closure Keller frames to the same fixed algebra. Adjoin induction
proves preservation of $E$ from the conjugate-polynomial identities.
Differentiating fractions proves preservation of the embedded $K$.
Characteristic-zero separability then identifies their intersection with
$E^G$; no normality assumption on $L/K$ is added.

[InvariantQuotientAction.lean](../InvariantQuotientAction.lean) descends
these additive operators through the original base image, using the
generic [quotient operator](../../../General/Normalization/DerivationQuotient.lean).
For $q\in E^G/B$, the constructed operators satisfy

```math
\nabla_i([z])=[\delta_i(z)],\qquad
\nabla_i(bq)=\partial_i(b)q+b\nabla_i(q),\qquad i=0,1,
```

where $\delta_0,\delta_1$ are the existing first and second normal-closure
Keller frames and $\partial_i$ is the existing transported target partial.
The existence theorem
`planarKellerInvariantQuotient_exists_leibniz` takes only marked
normal-closure data and the Keller condition. Operator existence and
fixed-algebra preservation are proved, not supplied.

The remaining finite-stage target is a finite $B$-submodule of this
quotient containing the class under study and preserved by both actual
operators. Elementwise torsion does not give that preservation or a
uniform annihilator of the whole quotient. No action on $N/T$,
normalization boundary regularity, or filtered-Ext comparison is asserted.

Verification (2026-11-08, Lean 4.28.0): all four new leaves build without
warnings; the focused quotient-action target passes 2942 jobs. A separate
client imports both the section comparison and quotient action, checks
the original quotient type, representatives, both normal-closure frame
identities, base representatives mapping to zero, all four target-coordinate
Leibniz rules, and existence from Keller. All thirteen audited declarations
use only `propext`, `Classical.choice`, and `Quot.sound`.
The full research umbrella was not rerun for this checkpoint.

## Concrete finite-stage tests

The first candidate is the standard finite cyclic stage $Bq\subseteq E^G/B$.
[CyclicStage.lean](CyclicStage.lean), using the generic
[cyclic escape lemma](../../../General/Normalization/DerivationCyclicStage.lean),
proves

```math
q\ne0\quad\Longrightarrow\quad
\exists i\in\{0,1\},\quad \nabla_i(q)\notin Bq.
```

The proof uses an annihilator $a$ of $q$ transverse to a target partial:
$a\nabla_i(q)=-\partial_i(a)q\ne0$, whereas $a$ kills every element of $Bq$.
Finiteness of this concrete span is automatic; preservation fails for a
nonzero class. The theorem does not assert that such a class exists.

The old trace-integral stage is a different candidate.
[TraceStageAudit.lean](../TraceStageAudit.lean) tests an element already
in the embedded target field against $1\in T$:

```math
\iota(r)\in T^\dagger
\quad\Longrightarrow\quad
\mathrm{Tr}_{N/K}(\iota(r))=[N:K]\,r\in B.
```

If $[N:K]$ is a unit in $B$, then $r\in B$. The characteristic-zero
field-algebra corollary proves this unit condition internally. Thus an
element of $E^G$ whose normal-closure value is trace-integral has zero
class in $E^G/B$. The degree here is $[N:K]$, not $[L:K]$.
This tests the fixed-field part only; it does not invalidate the original
$N/T$ trace strategy or prove that the entire target quotient vanishes.

Neither candidate supplies the missing finite control. The existing
evaluated secant lattice is a $T$-span in $N$, not already a stage of
$E^G/B$. The ambient comparisons below place the old and new quotients
in $N/T$; using the lattice still requires a map on the relevant
section domain and detection of the boundary class under study.
Finite denominator clearing supplies neither that detection nor
derivative closure.

Verification (2026-11-08, Lean 4.28.0): the generic cyclic leaf and both
research specializations build; the combined actual/trace target passes
2993 jobs. The new leaves have no warnings; an older unused-simp warning
is replayed from `AffineOpenSections`. A separate client checks the
actual cyclic escape, finiteness of its standard span, the zero-class
control, both trace hypotheses, and zero image for an actual trace-integral
invariant element using the existing normalization ring. All six audited
declarations use only `propext`, `Classical.choice`, and `Quot.sound`
(the single-operator escape lemma does not need choice).
No full research-umbrella build was run for this checkpoint.

## Differential orbit and finite jet denominator test

The coherent-subsheaf route can be tested on the existing module
$M=E^G/B$, without choosing a new sheaf or local-cohomology model.
For a class $q$, [DerivationOrbit.lean](../../../General/Normalization/DerivationOrbit.lean)
uses finite words in the existing frame operators and their standard
$B$-module span:

```math
\nabla_{i::w}q=\nabla_i(\nabla_w q),\qquad
M_q=B\langle\nabla_wq:w\text{ a finite word}\rangle.
```

Leibniz makes this span invariant. A single nonzero scalar annihilating
all words is therefore equivalent to $q=0$, by the existing annihilator
theorem. Coherence of a preserved stage would supply such a scalar, but
neither coherence nor that scalar is assumed to exist.

[DerivationJetTest.lean](../../../General/Normalization/DerivationJetTest.lean)
sharpens the test to a finite order. Write a proposed denominator as
$s=f(P,Q)$, using the existing injective target-polynomial presentation
of $B$. If $f\ne0$ and

```math
s\nabla_wq=0\quad\text{for every }|w|\le r,
\qquad \deg f\le r,
```

then $q=0$. Here $\deg f$ is total degree in the target variables, not
generic map degree or a source-weighted degree. The proof is strong
degree induction: Leibniz transfers a jet test for $f$ to one for a
nonzero partial derivative of smaller degree; a nonzero constant
annihilator is a unit. No commutation hypothesis on the module
operators is needed.

[DifferentialOrbit.lean](DifferentialOrbit.lean) applies both tests to
the actual quotient and its constructed Keller-frame operators. In
particular, a hypothetical nonzero class defeats any proposed
denominator $f(P,Q)$ by a word of length at most $\deg f$. This does not
assert that such a class exists.

The automatic finite-order estimate is weaker.
[DerivationOrbitStages.lean](../../../General/Normalization/DerivationOrbitStages.lean)
proves, using only Leibniz,

```math
aq=0\quad\Longrightarrow\quad
a^{r+1}\nabla_wq=0\quad (|w|\le r).
```

The actual torsion theorem supplies one initial $a\ne0$. Its powers
give denominators at every finite order, not one denominator for all
orders. If $a=g(P,Q)$ has positive total target degree $d$, the supplied
denominator has degree $(r+1)d>r$, so it does not meet the finite jet
criterion. A constant nonzero $a$ already implies $q=0$.

A separate importing client verifies sharpness in the ordinary rational
quotient $\mathbb C(x,y)/\mathbb C[x,y]$. The class $q=[1/x]$ is nonzero,
and $x^{r+1}$ kills every word through order $r$, while $x^r$ fails on a
word of exactly length $r$. This is a generic simple-pole control, not
the actual Keller invariant quotient or a counterexample.

The remaining Keller-specific estimate is to find a denominator
clearing a jet at least as long as its own target degree, or to give a
uniform annihilator by another geometric argument. The one-step
weighted target-shear budget does not bound iterated frame derivatives
and is not promoted to this estimate.

One concrete stage construction is the
[all-conjugate polynomial-degree filtration](OBJECT-BENCH.md#coherent-stage-from-total-polynomial-degree).
The low-total-degree case is formalized below. In higher total degree
the same ordinary degree calculation permits growth.

Verification (2026-11-09, Lean 4.28.0): all four new leaves pass focused
builds; the actual-quotient target passes 2965 jobs. The new leaves have
no warnings; the older unused-simp warning in `AffineOpenSections` is
replayed. Two independent importing clients pass without warnings and
check finite-order bounds without a commuting-operator assumption,
two-operator words, unit annihilators, the zero-class uniform test,
the finite jet criterion and degree-bounded escape, and the numerical
gap $r<(r+1)d$ for $d\ge1$, together with the concrete simple-pole
nonvanishing and sharp-order failure. All nineteen audited declarations use only
`propext`, `Classical.choice`, and `Quot.sound`.
The full research umbrella was not rebuilt for this checkpoint.

## Constructed finite stages in low total degree

[ConjugatePolynomialPresentation.lean](../../../General/Galois/ConjugatePolynomialPresentation.lean)
presents the existing all-conjugate algebra over the ground field, not
only as a $B$-algebra. Write $\xi_{g,j}=\varphi_g(x_j)$ and let $\Phi_D$
evaluate polynomials in this finite coordinate family. Its range is
exactly the original $E$ restricted to $\mathbb C$. No extra generators
for $B$ are needed: base coefficients are already polynomials on the
marked source sheet.

[FilteredPolynomialDerivation.lean](../../../General/Normalization/FilteredPolynomialDerivation.lean)
uses Mathlib's standard bounded-total-degree submodule to define

```math
E_{\le m}=\Phi_D\bigl(\mathbb C[Z_{g,j}]_{\le m}\bigr)\subseteq N.
```

Every stage is finite-dimensional over $\mathbb C$, even when the
coordinate generators have relations. The stages exhaust $E$. A
derivation whose generator values have affine-linear polynomial
representatives preserves each stage; this is proved by an explicit
polynomial lift and the partial-derivative degree bound.

[LowTotalDegreeFrame.lean](LowTotalDegreeFrame.lean) derives those
affine representatives for the actual normal-closure Keller frames
when both $F_0,F_1$ have total polynomial degree at most two. The
inverse-Jacobian coefficients are scalar multiples of their partials,
so they have degree at most one. The representatives on a conjugate
sheet are the renamed source-frame polynomials, using the already
proved normal-closure compatibility.

For a chosen invariant representative, pull a suitable stage back
through the original inclusion $E^G\hookrightarrow N$, then map it to
$M=E^G/B$. Its quotient image is a finite-dimensional coefficient-field
subspace preserved by both operators. Its standard $B$-span is finite
over $B$ and preserved by Leibniz.
[DerivationFiniteStage.lean](../../../General/Normalization/DerivationFiniteStage.lean)
then applies the existing finite-torsion annihilator theorem. A
different stage may be chosen for each representative; no coherence
or finite generation of the whole quotient is assumed.

The actual endpoint in [TotalDegreeTwoStage.lean](TotalDegreeTwoStage.lean)
therefore proves

```math
J(F)=c\ne0,\quad \deg F_j\le2\ (j=0,1)
\quad\Longrightarrow\quad E^G/B=0.
```

This is a bound on **total coordinate-polynomial degree**, not generic
degree. The construction takes marked normal-closure data and derives
finite-stage preservation internally. It uses no purity, finite-étale
rigidity, supplied uniform denominator, or local-cohomology comparison.
The already available boundary and vanishing endpoints remain separate.

On the Noetherian affine base, the finite $B$-stage has the usual
coherent-sheaf interpretation ([Stacks, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)).
The new implementation works with that module, without constructing a
new sheaf model or importing a coherence premise.

For higher total degree the ordinary filtration need not be preserved.
The triangular Keller control $F=(x,y-x^3/3)$ has first frame sending
$y$ to $x^2$, outside the ordinary degree-one source stage. This tests
the particular ambient filtration, not nonvanishing of the actual
quotient or impossibility of an adapted stage. The general degree-shift
estimate remains the separate mathematical audit on the bench.
Similarly, the signed boundary weights from the earlier residue
comparison cannot be substituted into this finite-dimensional argument
without checking finiteness: nonpositive weights may give infinite
bounded-weight spaces.

Verification (2026-11-09, Lean 4.28.0): all five new leaves pass their
focused builds; the final target completes its 2965-job dependency
graph. The new leaves emit no warnings; an existing unused-simp warning
in `AffineOpenSections.lean` is replayed. Two independent clients also
pass: they check finite pullback and quotient images, zero stages, the
original-algebra presentation, translation and Euler frames, dependent
coordinate generators, the actual quotient endpoint, and nonlinear and
cubic Keller controls. Their 21 axiom checks cover 20 distinct
declarations and report only `propext`, `Classical.choice`, and
`Quot.sound`. The full research umbrella was not rebuilt.

## Source restriction and normalization comparison

The inclusion problem can be located on the original schemes without
assuming a bounded orbit. Write $A=\mathbb C[x,y]$, $Y=\mathrm{Spec}B$,
$Z=\mathrm{Spec}T$, and $U_F=\mathrm{Spec}(E^G)$ with its existing open
immersion into $Y$.

[ConjugateSourceBaseChange.lean](../../../General/Keller/ConjugateSourceBaseChange.lean)
constructs the canonical map

```math
E^G\otimes_B A\longrightarrow E,\qquad c\otimes a\longmapsto c\,\iota(a).
```

It is injective: Keller flatness preserves the injection $E^G\hookrightarrow K$
after tensoring with $A$, and the existing generic-source map embeds the
result into $L\hookrightarrow N$. Since $E$ is finite over the Noetherian
ring $E^G$, the source of this map is finite over $E^G$. Its étaleness is
the base change of the original Keller étaleness. Thus the original map
is finite étale over this particular invariant target open. The proof is
dimension-independent and retains the same separable-normal-closure
hypothesis as the target-open construction. It does not yet identify
$U_F$ as the maximal finite locus.

[ConjugateNormalizationOpen.lean](ConjugateNormalizationOpen.lean) gives
the planar comparison with the original finite model. The open immersion
$U_F\hookrightarrow Y$ identifies its local rings with localizations of
the normal base; this proves normality of $E^G$. The existing delta frame
then reconstructs every $z\in N$ from finitely many field traces. If $z$
is integral over $E^G$, those trace coefficients are integral and lie in
$K$, hence belong to $E^G$. Reconstruction puts $z$ in $E$. Integral
transitivity proves normality of $E$ as well.

In particular the original normalization has a canonical inclusion
$T\hookrightarrow E$. Birational quasi-finite Zariski main constructs
the induced open immersion, commuting with the maps to the original
target:

```math
\begin{array}{ccc}
\mathrm{Spec}E & \hookrightarrow & Z=\mathrm{Spec}T\\
\downarrow && \downarrow\\
U_F & \hookrightarrow & Y=\mathrm{Spec}B.
\end{array}
```

The left vertical map is finite étale over $U_F$; the right vertical map
is finite over $Y$. No normality or orbit-containment premise is added.
The Cartesian comparison and the pointwise common-regularity criterion
are treated in the next section.

The direction of the ring inclusion matters: $T\subseteq E$ does not
bound poles of $E$ at $Z\setminus\mathrm{Spec}E$. The existing
[divisor-visibility theorem](../../../General/Keller/DivisorVisibility.lean)
gives one visible unramified source divisor over each target divisor,
not simultaneous regularity of all conjugate source coordinates. Likewise
the existing source-intersection criterion makes regularity of every
fixed element on the marked source equivalent to $E^G=B$; it cannot be
assumed to transfer regularity across the boundary.

The requested inclusion still requires one fixed fractional
normalization stage containing the lifted orbit of the class under
study. These scheme comparisons locate that remaining extension problem
without proving it.

Verification (2026-11-09, Lean 4.28.0): both new leaves pass their focused
builds without warnings (2846 and 2943 jobs), and their combined target
passes 2944 jobs. Eleven audited public endpoints use only `propext`,
`Classical.choice`, and `Quot.sound`. Both independent importing clients
pass without warnings. They check étaleness without a normal-extension
separability premise, the marked pure-tensor formula, injectivity and
finiteness with separability, both normality statements, actual
normalization membership, coefficient compatibility of the canonical
ring map, and the open immersion. The full research umbrella was not
rebuilt.

## Constructed target divisor and common regularity

A hypothetical nonzero class $q\in E^G/B$ now supplies its own target
boundary divisor. [TargetPoleWitness.lean](../../../General/Normalization/TargetPoleWitness.lean)
starts with a rational function outside a Noetherian UFD. A prime factor
of its reduced denominator constructs a height-one prime $p$ and
coefficients $a,b$ with $a\notin p$, $b\in p$, $b\ne0$, and $a=br$.
Cross multiplication excludes membership in the actual local ring
$B_p\subset K$.

[ConjugateInvariantPole.lean](../../../General/Keller/ConjugateInvariantPole.lean)
applies this to an invariant representative $z$ of the original quotient
class. Its canonical coefficient identity holds already in $E^G$:

```math
[z]=q,\qquad a=bz,\qquad
\mathrm{ht}(p)=1,\quad a\notin p,\quad b\in p.
```

If a prime of $E^G$ lay over $p$, that identity would put $a$ in it
because $b$ is in it, contradicting contraction to $p$. Thus $p\notin U_F$.
The same construction proves that $B_p$ is a DVR and the embedded
representative is not in $B_p$. The divisor and polar representative are
derived from $q\ne0$, not supplied as additional assumptions. The result
is dimension-independent under the existing normal-extension separability
hypothesis; it does not assert that a nonzero class exists.

[InvariantNormalizationBaseChange.lean](InvariantNormalizationBaseChange.lean)
constructs the canonical Cartesian comparison

```math
W=\mathrm{Spec}E\simeq Z\times_Y U_F.
```

Both projection identities are proved, as is
$W=\pi^{-1}(U_F)$ for the existing finite normalization map $\pi:Z\to Y$.
The proof uses the previously constructed open immersions and finite map
$W\to U_F$: the comparison is finite and open, so its image is nonempty
and clopen in the integral pullback, hence is all of it. No new open or
normalization model is chosen.

[ConjugateCommonOpen.lean](ConjugateCommonOpen.lean) tests an actual point
$Q\in Z$ in its original local ring, embedded in $N$:

```math
Q\in W\quad\Longleftrightarrow\quad
\varphi_g(x_i)\in\mathcal O_{Z,Q}\quad\hbox{for every }g,i.
```

The local ring is Mathlib's existing localization subalgebra. The forward
direction uses the stalk isomorphism of the open immersion; the reverse
direction uses generation of $E$ by these same coordinates. Consequently
$Q\notin W$ produces a conjugate coordinate nonregular at that same point;
at a divisorial $Q$, this is a pole. A separate generation-only lemma
derives a nonregular coordinate from any nonregular element of $E$,
without a Keller or ramification premise.

Combining the comparisons, every normalization center over the extracted
$p$ is outside $W$ and has a nonregular conjugate coordinate. This does not make
$p$, or a center above it, a ramification divisor; no inertia conclusion is
drawn. The remaining polynomial-geometric task is a bound on the selected
orbit across this actual boundary. The target DVR and its polar class no
longer have to be supplied independently.

Verification (2026-11-09, Lean 4.28.0): all four new leaves pass their
focused builds (2014, 2989, 2950, and 2944 jobs); the combined target
passes 3015 jobs. The new leaves have no warnings; the combined build
replays an older unused-simp warning in `AffineOpenSections.lean`.
Four independent importing clients pass, and all fourteen audited public
declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
The Cartesian client pins the canonical base scalar actions explicitly.
The full research umbrella was not rebuilt.

## Fractional normalization and local pole growth

The general construction already uses schemes.
[Keller/Normalization.lean](../../../General/Keller/Normalization.lean)
constructs $X=\mathbb A^2\hookrightarrow\bar X\to Y$, where
$\bar X$ is the intermediate normalization finite over $Y$, and the
finite normal-closure model $Z\to\bar X\to Y$. The source is an open
in the finite model, not already finite over $Y$. Likewise the
[all-conjugate finite étale cover](../ConjugateCover.lean) is finite over
$U_F$, not yet over all of $Y$. A module structure alone does not supply
module-finiteness over the target base.

The fixed-lattice candidate uses the original normalization
$T=\overline B^{\,N}$, not a second section ring.
[FractionalNormalization.lean](../../../General/Normalization/FractionalNormalization.lean)
constructs its scalar image as a standard linear-map range. For a fixed
nonzero $s\in N$ and $m\ge0$, write this image as

```math
\Lambda_{s,m}=s^{-m}T\subset N.
```

It is finite over $B$ by the already proved normalization finiteness.
Membership is exactly $s^m z$ integral over $B$. No derivative-orbit
containment is a premise of this construction or a conclusion of it.

[ValuationFiniteStage.lean](../../../General/Normalization/ValuationFiniteStage.lean)
proves that every finite $B$-submodule of $N$ has one common bound at a
valuation with $v(B)\le1$. The bound still holds after arbitrary additions
from $B$. Thus passage to classes modulo $B$ cannot hide an unbounded pole
tower. The fractional-normalization specialization constructs the finite
candidate before applying this bound.

The opposite side of the contradiction is constructive.
[TransversePoleStep.lean](../../../General/Normalization/TransversePoleStep.lean)
works in a local algebra $R$ over a characteristic-zero field. Suppose
$f$ lies in its maximal ideal, $d(f)$ is a unit, and $d_K$ extends $d$
to a field containing $R$. For a unit $u$ and $m>0$, it produces

```math
d_K(u/f^m)=u'/f^{m+1},\qquad
u'=f\,d(u)-m\,u\,d(f)\in R^\times.
```

Iteration constructs a unit numerator for every exponent $m+n$.
If $R$ is a target boundary DVR and $f$ its uniformizer, this is exact
pole growth without completion or a supplied orbit sequence. The
coefficient-field hypothesis makes every positive integer a unit;
characteristic zero of $R$ alone would not suffice. The preceding
quotient construction now extracts a target boundary DVR and polar
invariant representative from $q\ne0$. Instantiating the transverse
derivative and unit-numerator presentation there is a separate step,
as is the Keller-specific uniform bound. These target-field statements
remain distinct from inertia-moved coordinates at a ramified
normalization divisor.

[DerivationFractionalStage.lean](../../../General/Normalization/DerivationFractionalStage.lean)
tests the direct preservation argument through the exact identity

```math
s^{m+1}\delta(s^{-m}t)
   =s\,\delta(t)-m\,\delta(s)t.
```

One-step clearing of $\delta(T)$ therefore gives a next-exponent bound,
not a bound uniform in derivative order. If the whole shifted lattice
were preserved, testing $t=1$ would force
$m\,\delta(s)/s\in T$. For $s\in B$, positive $m$, and the complex
coefficient field, $T\cap K=B$ would then force $s\mid\delta(s)$.
A transverse target partial violates that condition. Enlarging a
positive power shift does not repair this preservation test.

The remaining target is weaker: contain the chosen Keller orbit in one
finite lattice, without requiring that entire lattice to be preserved.
Its orbit submodule would then be finite by Noetherianity and already
stable by Leibniz. Scaling a transverse derivative by a vanishing
denominator is not a substitute: it loses the target-partial action used
by the annihilator argument.

Verification (2026-11-09, Lean 4.28.0): all four new leaves pass focused
builds without warnings. The actual fractional-normalization target
completes 2580 jobs; the valuation, fractional-derivation, and transverse
pole targets complete 1309, 1325, and 1420 jobs respectively. All sixteen
public declarations have axiom audits using only `propext`,
`Classical.choice`, and `Quot.sound`. Four independent clients pass and
check normalization-image finiteness, zero-exponent and unit-denominator
controls, the zero-stage and modulo-base bound, the quotient-rule and
basic-denominator tests, and successive unit numerators at the same
maximal ideal. The fractional-rule client's redundant zero-exponent
example has two scratch-only linter warnings. The full research umbrella
was not rebuilt.

## Original multiplier comparison in the common ambient quotient

The earlier trace route uses the actual normalization section quotient,
not $E^G/B$. [BoundaryMultiplierComparison.lean](../BoundaryMultiplierComparison.lean)
recovers its conditional map

```math
\lambda_{C,s}:R_C/T\longrightarrow T^\dagger/T,\qquad
[r]\longmapsto[sr],\qquad sR_C\subseteq T^\dagger.
```

Both quotients inject into the same $N/T$. Under these inclusions,
$\lambda_{C,s}$ is multiplication by $s$. The normalization image is
contained in both modules: restriction gives $T\subseteq R_C$, and
Mathlib's `Submodule.one_le_traceDual_one` gives $T\subseteq T^\dagger$
from integrality and normality of $B$. The generic
[multiplier comparison](../../../General/Normalization/MultiplierQuotient.lean)
uses only standard submodule quotients. The multiplier map need not be
injective; its landing condition is still explicit.

[ConjugateInvariantNormalizationQuotient.lean](../../../General/Keller/ConjugateInvariantNormalizationQuotient.lean)
also puts the newer quotient in this ambient space:

```math
E^G/B\hookrightarrow N/T.
```

Injectivity follows from the original embeddings and $K\cap T=B$.
The map is $B$-linear; the old maps are $T$-linear and can be compared
after restricting scalars. This does not identify $E^G/B$ with $R_C/T$
or prove $E^G\subseteq R_C$. A local section-domain adapter may suffice;
global containment is not imposed as a new requirement. The
filtered-Ext identification $R_C/T\simeq H^1_{\mathfrak J_C}(T)$
remains separate.

The collision ring already supplies the actual conjugate pair maps,
their off-diagonal lifts, and
[local collision rigidity](LocalCollision.lean). If an inertia-moved
sheet is regular in the selected valuation ring, inertia gives residue
agreement and the collision relations force the sheets to coincide.
[InertiaCoordinates.lean](InertiaCoordinates.lean) proves the
contrapositive. Thus the local contradiction is available; regularity
at that same divisor is the remaining input. A pair evaluation on
$U_g\cap U_{\sigma g}$ does not yet extend arbitrary sections on
$U_C$ or prove uniform trace landing.

Verification (2026-11-08, Lean 4.28.0): the two generic leaves and the
actual boundary specialization pass their focused builds; the latter
passes 3079 jobs. An independent importing client checks the ambient
inclusions, multiplier representatives and compatibility, the zero
multiplier, the actual invariant-quotient injection, and Mathlib's
scalar-restriction equivalence on representatives and scalar products.
All nine audited declarations use only `propext`, `Classical.choice`,
and `Quot.sound`. The new leaves have no warnings; an existing
unused-section-variable warning in `LocalBaseChange` is replayed.
The full research umbrella was not rebuilt for this checkpoint.

## Full Jacobian constraint on weighted components

[WeightedJacobian.lean](WeightedJacobian.lean) uses the full polynomial
Jacobian identity $J(P,Q)=c\in\mathbb C^\times$ for $F=(P,Q)$.
Let $w=(w_x,w_y)\in\mathbb Z^2$ be maximum-weight
grading weights, and let $m,n$ bound the weights in the supports of
$P,Q$. Write
$P_m=\mathrm{wcomp}_{w,m}(P)$ and
$Q_n=\mathrm{wcomp}_{w,n}(Q)$ for Mathlib's existing weighted components.
Then

```math
J(P_m,Q_n)=
\begin{cases}
c,&m+n=w_x+w_y,\\
0,&m+n\ne w_x+w_y.
\end{cases}
```

The generic [component lemmas](../../../General/Normalization/WeightedComponents.lean)
prove the derivative shift, derivative support bound, and highest-product
component formula for signed integer weights. The
[signed Euler identity](../../../General/Normalization/WeightedEuler.lean)
extends the existing natural-weight statement without imposing positive
coordinate weights.

In the balanced case $m+n=w_x+w_y$, a common zero $z$ of $P_m,Q_n$
must satisfy $(w_i z_i)_{i=0,1}=0$: Euler puts that vector in the kernel
of the leading Jacobian matrix, whose determinant is $c\ne0$.
Thus a common torus zero is impossible if some $w_i\ne0$.
The formal evaluation field can be any field extension of $\mathbb C$,
including the relevant residue-field setting.

This excludes a balanced common-zero configuration, not every pole.
It does not show that a ramified divisor gives balanced weights. The
actual initial-residue comparison below supplies the tuple and its
zero evaluations when the corresponding target degrees are positive.

The strict case $m+n>w_x+w_y$ has a genuine global Keller negative control in
[LeadingFaceDiagnostic.lean](LeadingFaceDiagnostic.lean):

```math
P=x+y^2,\qquad Q=y+P^2,\qquad J(P,Q)=1.
```

This is a polynomial automorphism. At weights $(2,1)$, its leading
components are $P$ and $P^2$, with the common torus zero $(-1,1)$.
Here $m+n=6>3=w_x+w_y$ and the leading Jacobian is zero.
Substituting $y=t^{-1}$, $x=u-t^{-2}$ gives
$P=u$, $Q=t^{-1}+u^2$. In the Laurent interpretation with $t$ a
uniformizer and $u$ regular, both leading components cancel, but a lower
polar term survives. The example is not an inertia model or a pole
above an affine target point. It shows why common leading zeros and the
full Keller identity cannot alone finish the proposed contradiction.

The remaining strict-case task is to control successive lower terms,
keeping the actual valuation and polynomial coordinate changes.
Vanishing of the leading bracket is a necessary relation, not a
termination or regularity theorem.

Verification (2026-11-09, Lean 4.28.0): all four new leaves pass their
focused builds; the weighted-Jacobian target passes 1601 jobs.
The new leaves have no warnings. A separate importing client checks
signed and negative weights, the strict-case formula on the diagnostic,
the balanced criterion over arbitrary field extensions, and the
zero-weight/common-zero control where the radial hypothesis fails.
It also checks the diagnostic's polynomial-automorphism and substitution
endpoints. All twelve audited declarations use only `propext`,
`Classical.choice`, and `Quot.sound`.
The full research umbrella was not rebuilt for this checkpoint.

## Weighted cancellation budget and target shears

[PolynomialSubtraction.lean](PolynomialSubtraction.lean) specializes the
existing second-frame identity in [BaseFrame.lean](BaseFrame.lean):
$\partial_Q=c^{-1}J(P,-)$ differentiates arbitrary target polynomials.
Thus

```math
R=Q^r-\lambda P^s\in B,\qquad
J(P,R)=rQ^{r-1}c.
```

This reuses the earlier frame calculus; it is not a new Jacobian
identity. General power subtraction is proved to lie in the same
original image algebra, without asserting that $(P,R)$ generates $B$.

[CancellationBudget.lean](CancellationBudget.lean) supplies the new
weighted comparison. Use the existing signed weighted degree
`weightedTotalDegree'`, with values in `WithBot ℤ`; finite integer
degrees are sharp maxima, not just support bounds. Suppose
$\deg_w P=m$, $\deg_w Q=n$, $r\ge1$, and

```math
Q_n^r=\lambda P_m^s,\qquad rn=sm,
\qquad \lambda\in\mathbb C.
```

The leading-polynomial relation is an explicit input, not a consequence
of a common residue zero. The Jacobian identity proves $R\ne0$,
then the theorem derives its finite degree $k$ and the bound

```math
0<rn-k\le D,\qquad D=m+n-w_x-w_y.
```

The generic [sharp-degree lemmas](../../../General/Normalization/WeightedDegreeBounds.lean)
identify finite degree with a support bound and a nonzero component,
and prove product and power formulas over a domain. No positivity
restriction on the source weights or on $k$ is imposed.

When $r=1$, the actual target shear
$(u,v)\mapsto(u,v-\lambda u^s)$ has inverse obtained by replacing
$\lambda$ with $-\lambda$. It preserves Keller and the existing
coordinate-image subalgebra inside the original polynomial source.
The new defect satisfies

```math
0\le D'=m+k-w_x-w_y<D.
```

This is one proved descent step. With the same fixed weights $w$, a
continuing sequence of such legal steps has a strictly decreasing
nonnegative integer, but existence of the next leading relation or of
an exponent-one branch is not proved.
For $r>1$, the Jacobian factor $rQ^{r-1}$ is retained and the new pair
is not assumed Keller. Application to the actual moved-sheet pole also
uses the initial-residue comparison below; that comparison supplies
residue vanishing, not the polynomial leading-power relation.

Verification (2026-11-09, Lean 4.28.0): all three new leaves pass their
focused builds without warnings; the cancellation-budget target passes
2641 jobs. An independent importing client passes without warnings and
checks the baseline residual, two successive legal subtractions with
second-coordinate degrees $4\to2\to1$ and defects $3\to1\to0$,
negative residual degree, and a power-subtraction control with $r=2$.
That control has residual degree $5>4$ but virtual drop $8-5=3$,
and retains the factor $2Q$ in its Jacobian. The client also checks the
excluded exponent-zero case, the actual Keller and image-range
endpoints, and the sharp-degree API. All ten audited declarations use
only `propext`, `Classical.choice`, and `Quot.sound`.
The full research umbrella was not rebuilt for this checkpoint.

## Actual boundary weights and initial residues

[BoundaryValuation.lean](BoundaryValuation.lean) separates the geometric
inputs already used by [PolarCancellation.lean](PolarCancellation.lean):
the center map puts ground constants and target values in the actual DVR
$V$, while nontrivial inertia supplies a moved sheet with a source
coordinate outside that same ring. The older finite-support certificate
now reuses these lemmas.

[DivisorialWeights.lean](../../../General/Normalization/DivisorialWeights.lean)
normalizes the value group without changing $V$ or its maximal ideal.
Write $v_{\mathbb Z}(\varphi_g(x_i))=\exp(w_i)$, with a pole corresponding
to $w_i>0$. Evaluated nonzero monomials have exactly their exponent
weights. The valuation of a polynomial sum need not equal its maximum
term value.

[BoundaryInitialResidue.lean](BoundaryInitialResidue.lean) derives finite
sharp degrees $m,n$ for the actual target pair, with at least one of them
positive. If a target component has positive degree $d$, its evaluated
weighted top part has value strictly below $\exp(d)$; division by a
top-valued monomial gives an element of $V$ with zero residue.

Equivalently, choose a uniformizer $\pi$ with value $\exp(-1)$ and put

```math
u_i=\varphi_g(x_i)\pi^{w_i}\in V^\times,
\qquad z_i=\overline{u_i}\ne0.
```

The signed homogeneous-scaling theorem in
[WeightedInitialEvaluation.lean](../../../General/Normalization/WeightedInitialEvaluation.lean)
identifies evaluation at $u$ with multiplication by $\pi^d$.
Reduction takes place in the residue field of the original $V$, and
gives

```math
d=\deg_w F_j>0\quad\Longrightarrow\quad
\mathrm{wcomp}_{w,d}(F_j)(z)=0.
```

This supplies the actual initial tuple required by the leading-Jacobian
test. A zero weighted degree does not meet the positive-degree premise,
and the argument does not assert that both target degrees are positive.
When both degrees are positive, a polar source coordinate supplies a
nonzero weighted radial direction. The actual-divisor wrapper then
rules out $m+n=w_x+w_y$ by the existing balanced common-zero theorem.

## Availability of the next legal reduction

[TwoSidedCancellation.lean](TwoSidedCancellation.lean) allows either
$(P,Q-\lambda P^s)$ or $(P-\lambda Q^s,Q)$. Both preserve the original
Jacobian constant and image algebra. They also preserve regular target
values in the same $V$, leaving the source map $\varphi_g$ and its weights
unchanged. A supplied leading-power relation in the corresponding
orientation therefore gives a genuine decrease of the same defect $D$.
The swapped diagnostic has degrees $(4,2)$: only the first-coordinate
subtraction is available in that orientation.

The remaining task is to derive a relation with an exponent one, or
exclude the state using the full Keller identity. Evaluated residue
vanishing alone is not a polynomial identity. Even zero leading
Jacobian and a common-power relation do not force an elementary shear:
the non-Keller leading-form pair $(H^2,H^3)$ has degrees $(4,6)$ when
$\deg_w H=2$, and neither degree is an integer multiple of the other.
It is a control for the leading-form inference, not a Keller
counterexample or a ramified-divisor example.

[OppositeDegreeExclusion.lean](OppositeDegreeExclusion.lean) narrows one
branch independently. Nonzero weighted-homogeneous polynomials of
strictly opposite signed degrees cannot have zero Jacobian: Euler's
identity would make a positive-power product a nonzero constant. Thus
opposite signs for a constant-Jacobian pair force the balanced degree.
They are not excluded universally; the identity pair at weights
$(1,-1)$ is balanced. This does not settle the nonpositive-degree or
positive-degree branches of the next-reduction problem.

Verification (2026-11-09, Lean 4.28.0): all seven new leaves and the
refactored finite polar-cancellation leaf pass focused builds without
warnings; the combined planar targets pass 2946 jobs. An independent
importing client passes without warnings. It checks the swapped
diagnostic's unavailable second-coordinate balance and legal opposite
shear, Keller and image-range preservation, regularity in the same
valuation ring, signed coordinate normalization and residue vanishing,
the balanced opposite-sign identity control, and the non-Keller
$(H^2,H^3)$ control. All twenty-two audited declarations use only
`propext`, `Classical.choice`, and `Quot.sound`.
All 359 local links in the research notes and parity table resolve.
The full research umbrella was not rebuilt for this checkpoint.

## Construction checkpoint: evaluated projectors and fixed loci

The canonical projector is now evaluated on actual collision pairs in
[`EvaluatedProjector.lean`](../EvaluatedProjector.lean). It takes value zero
on identical sheets and one on distinct sheets in a domain. Its evaluated
coordinate-ideal membership turns the second value into a unit-ideal
certificate, using the supplied nonzero constant Jacobian.

[`ConjugateFixedLocus.lean`](../ConjugateFixedLocus.lean) corestricts the
existing conjugate source maps into the same $E\subset N$. Faithfulness of
the existing action supplies a conjugate sheet moved by any $\sigma\ne1$.
The evaluated projector then proves

```math
(\sigma(z)-z:z\in E)=E.
```

This is an empty scheme-theoretic fixed-locus certificate, also packaged as
a trivial quotient and `Ideal.inertia` equal to the trivial subgroup at
every proper ideal of $E$. It needs Keller and marked normal-closure data,
but no rigidity, purity, or generic-degree restriction.

This is a construction step toward the Galois-cover comparison, not a
vanishing step: it neither fills the target open nor asserts trivial
inertia at primes of the omitted normalization boundary. Setwise prime
stabilizers may be nontrivial. The cover comparison below retains this
boundary; its target has not been identified with the maximal finite locus.

## Finite étale cover and canonical tensor comparison

[`ConjugateCover.lean`](../ConjugateCover.lean) works over the existing
invariant algebra $E^G$, with no new quotient model. For planar Keller
maps it proves

```math
E/E^G\text{ finite étale and faithfully flat},\qquad
E\otimes_{E^G}E\simeq_{E^G}\prod_{g\in G}E,
\quad a\otimes b\longmapsto(g\longmapsto a\,g(b)).
```

The unit difference ideals make the action-graph kernels pairwise
comaximal. Chinese remainders give a tensor mapping to the identity delta
function. Its finite pure-tensor expansion supplies a trace-dual frame,
making $E$ a direct summand of a finite free $E^G$-module. That proves
projectivity and flatness; the existing module-finiteness supplies finite
presentation. Existing Keller formal unramifiedness over $B$ passes to
$E^G$ and yields étaleness. Integral injectivity supplies faithful flatness.
The same frame reconstructs every tensor from its graph values, proving
that the canonical map is an equivalence, not just surjective.

The generic proof leaves are `GaloisTensor`, `GaloisTrace`, and
`GaloisTensorEquiv`, all in the research tree. Neither a trace frame nor
flatness is taken as a new premise in the actual-map endpoints. This
affine algebraic torsor certificate does not introduce a bundled
scheme-level torsor object. No degree, rigidity, purity, or extra
separability premise is added. In particular it does not imply $E^G=B$
or fill the target boundary.

## Planar Galois rigidity from the geometric endgame

[`GaloisRigidity.lean`](GaloisRigidity.lean) packages the implication
`BranchPurityA2 → AffinePlaneFiniteEtaleRigidity → ComplexKellerGaloisRigidity 2`.
The geometric results remain explicit inputs, not new proved literature
theorems or installed axioms.

The proof order is

```math
L/K\text{ normal}\Longrightarrow H=1
\Longrightarrow\text{no height-one ramification of }T/B
\Longrightarrow T/B\text{ finite étale}
\Longrightarrow N=K\Longrightarrow L=K.
```

[`NormalRamification.lean`](NormalRamification.lean) proves the first
ramification bridge: a visible inertia-fixed sheet and $H=1$ force trivial
inertia. Its canonical endpoint constructs all normalization and local-index
data. Only the next two arrows use purity and affine-plane finite-etale
rigidity. [`BirationalAutomorphism.lean`](BirationalAutomorphism.lean) then
uses $A\cap K=B$ to obtain $A=B$ and polynomial invertibility, without
Ax--Grothendieck. The existing flat generic-degree-one theorem gives
$\mathrm{Obs}(F)=0$ as well.

This discharges the *planar* rigidity input relative to those two geometric
theorems, not unconditionally. It does not prove absence of ramification
for a general nonnormal $L/K$ or replace Paper I's dimension-three input.
The independently constructed $E/E^G$ cover is not a prerequisite here.

## Current finding: exact characterizations

Identify the rings with their images in the marked normal closure. The
internally proved source-intersection theorem gives

```math
A\cap K=B,\qquad E^G\cap A=B.
```

[ConjugateInvariantCriterion.lean](../../../General/Keller/ConjugateInvariantCriterion.lean)
packages the resulting boundary characterization:

```math
E^G\subseteq A\quad\Longleftrightarrow\quad E^G=B
\quad\Longleftrightarrow\quad\mathfrak b_F=B
\quad\Longleftrightarrow\quad U_F=\mathrm{Spec}B.
```

Lean uses source-image membership and surjectivity of the existing base
map rather than literal equality of differently presented rings. This
criterion uses Keller and the existing separable normal-closure data,
not characteristic zero, purity, or Keller--Galois rigidity. It asserts
no universal source regularity or empty boundary. The conormal test
below is an equivalent alternative in characteristic zero.

The separate coordinate-descent characterization identifies normality
of $L/K$, after which Keller--Galois rigidity gives automorphy and
$\mathrm{Obs}(F)=0$. Its planar value can now be derived from the two
geometric inputs above. The empty-boundary endpoint
instead uses source finiteness and its explicit geometric inputs.
The boundary ideal $\mathfrak b_F\subset B$ is not the obstruction
ideal $\mathrm{Obs}(F)\subset C_F$.

[BoundaryCriterion.lean](BoundaryCriterion.lean) packages the exact planar
equivalence $\mathrm{Obs}(F)=0\iff\mathfrak b_F=B$, and its
source-regularity and conormal corollaries. Only `BranchPurityA2` and
`AffinePlaneFiniteEtaleRigidity` are passed as geometric inputs, in the
boundary-to-obstruction direction. The shared reverse bridge in
[ConjugateInvariantObstruction.lean](../../../General/Keller/ConjugateInvariantObstruction.lean)
evaluates $I_R=I_\Delta$ at every Galois collision pair. The resulting
coordinate equalities put the all-conjugate algebra inside the marked
source, so the existing source-regularity criterion gives empty boundary.
This uses no Ax--Grothendieck or Keller--Galois rigidity. The first,
source-regularity step needs neither Keller nor separability; those
hypotheses enter only when applying the actual boundary criterion.

These are the findings to present. The historical attempts and their
negative controls below remain available, while the finite derivative
lattice is a [bench proposal](OBJECT-BENCH.md#finite-derivative-lattice-proposal-2026-09-20),
not a claimed next step proving full $JC(2)$.

## Precise Galois-descent characterization

The complementary marked-closure criterion is now explicit:

```math
\mathrm{Obs}(F)=0\quad\Longleftrightarrow\quad L/K\text{ normal}
\quad\Longleftrightarrow\quad N=\iota(L)
\quad\Longleftrightarrow\quad H=1.
```

`planarObstructionIdeal_eq_bot_iff_normal` and
`planarObstructionIdeal_eq_bot_iff_normalClosureEmbedding_surjective`
package the planar equivalences with only Keller--Galois rigidity passed
explicitly, from normality to vanishing. The other direction reuses the
direct coordinate equalities in
[CollisionVanishing.lean](../../../General/Galois/CollisionVanishing.lean),
with no Ax--Grothendieck input. The shared
`NormalClosureData.normal_iff_embedding_surjective` and
`normal_iff_intermediateFixingSubgroup_eq_bot` compare the actual marked
closure and its fixing subgroup (the subgroup theorem uses a perfect base).
The reverse planar characterization does not add an input to the focused
degree-two exclusion. It does not assert that the marked field fills its
normal closure for every Keller map.

Let $\iota:L\hookrightarrow N$ be the existing marked embedding. The
coordinate-descent condition is

```math
\forall g\in\mathrm{Gal}(N/K),\qquad
g(\iota(x)),\ g(\iota(y))\in\iota(L).
```

[GaloisDescent.lean](GaloisDescent.lean) names the universal complex-planar
statement `CollisionIdeals.Planar.PlanarGaloisDescent`, using the canonical
normal closure constructed from the Keller condition. No choice of a
separate model, generic-degree restriction, or normality of $L/K$ is
assumed in its definition.

The shared bridges in
[General/Galois/Descent.lean](../../../General/Galois/Descent.lean) and
[General/Galois/PolynomialDescent.lean](../../../General/Galois/PolynomialDescent.lean)
give the chain

```text
conjugate coordinates descend to the marked L     [condition]
    <-> L/K is normal                            [coordinate-generation bridge]
    -> F is a polynomial automorphism            [Keller--Galois rigidity input]
    -> Obs(F) = 0                                [existing collision API]
```

The normality equivalence and the two conditional endpoints are formalized
as `planarGaloisDescent_iff_forall_normal`,
`planarJacobianConjecture_of_galoisDescent`, and
`planarVanishing_of_galoisDescent`. This route needs neither an
Ax--Grothendieck input nor the ramification route's purity input.

The universal assertion of descent remains open. Constructing the normal closure
proves normality of $N/K$, not of $L/K$. The target concerns rational
membership in the original field, not polynomial or valuation-ring
regularity. With the accepted rigidity input, proving it for every complex
planar Keller map would settle full $JC(2)$; this is not a proved weaker
compatibility lemma. The earlier ramification and pole routes remain
separate approaches to the same vanishing endpoint.

The first attempt at a contradiction now has a concrete field-theoretic
witness. If descent fails, a conjugate coordinate $z=g(\iota(X_i))$
lies outside $\iota(L)$. The fixed-field theorem supplies
$h\in H=\mathrm{Gal}(N/\iota(L))$ with $h(z)\ne z$.
This is packaged in `NormalClosureData.exists_fixingSubgroup_move_of_not_mem`
and `polynomialSource_exists_moved_conjugate_coordinate_of_not_normal`.
The existing Galois collision pair $(g,hg)$ is therefore off diagonal,
and its planar secant determinant evaluates to zero.

That zero is not a contradiction: $h\in H$ fixes the original field,
not the conjugate sheet, and it gives no residue agreement or inertia
condition. The local rigidity theorem would exclude the pair if both
tuples could be realized in a local ring with identical residues, compatibly
with their distinct generic values. The common-center test is now sharper:
the two coordinate differences generate the unit ideal in any domain
containing both tuples as a collision pair. No prime in that simultaneous
regularity domain can supply the required center. This follows from the
existing diagonal/off-diagonal comaximality, not a new vanishing theorem.
Nor does preservation of each sheet by the extended Keller frame imply
descent. The precise tests are recorded in the
[descent audit](OBJECT-BENCH.md#descent-witness-and-frame-audit-2026-09-19).

Adjoining all conjugate source rings does not repair the problem. The
[common-center audit](OBJECT-BENCH.md#common-center-and-all-conjugate-ring-test-2026-09-19)
identifies a possible deleted base divisor: the resulting ring's
$H$-invariants have the form $A[1/d]$, with $0\ne d\in B$.
The underlying algebra $E$ is now constructed in
[ConjugateAlgebra.lean](../../../General/Galois/ConjugateAlgebra.lean),
with conjugate-polynomial membership, Galois stability, and finite type.
The $G$-invariant target open is now constructed in
[ConjugateInvariantOpen.lean](../../../General/Keller/ConjugateInvariantOpen.lean).
The principal localization presentation and the $H$-invariant comparison
above are not yet packaged in Lean. Equality with $A$, or a uniform
denominator bound forcing that equality, remains unproved. Thus the proposed
shortcut returns to the global boundary gap;
it does not bypass it through Galois symmetry or prime selection.

### Reduced-boundary invariant

For the all-conjugate open $U=D(d)$ in that mathematical audit, retain
the canonical ideal $\mathfrak b=I(\mathrm{Spec}B\setminus U)=\sqrt{(d)}=(s)$,
with $s\ne0$ squarefree. It is independent of
the equation chosen for the same open. The shared
[simple-pole criterion](../../../General/Normalization/SimplePole.lean)
and base transversality give

```math
\partial_P(s^{-1}B),\partial_Q(s^{-1}B)\subseteq s^{-1}B
\quad\Longleftrightarrow\quad
\partial_Ps,\partial_Qs\in(s)
\quad\Longleftrightarrow\quad s\in B^\times.
```

Keep this target explicitly finite: $s^{-1}B$ is a free rank-one
$B$-module, and Leibniz reduces its preservation to the two tests on
$1/s$. Equivalently, compare it with the module generated by
$1/s,D_P(1/s),D_Q(1/s)$; no higher-jet sequence or whole pole tower
is part of this target. Finite means finitely generated over $B$, not
finite-dimensional over $\mathbb C$. The finite defect is
$(\partial_Ps\bmod s,\partial_Qs\bmod s)$.
The actual all-conjugate open and its canonical reduced boundary ideal are
now constructed. The characteristic-zero conormal criterion is applied to
that same ideal: all target-coordinate components vanish iff the open is
the whole target. This intrinsic criterion does not need a principal
presentation. The latter remains unformalized for the one-generator
simple-pole formulation. The Keller-specific claim that the components
vanish remains open. In particular,
neither preservation of $B[1/s]$ nor adjoining first jets to the
secant coefficient lattice supplies simple-pole preservation. The
[bench test](OBJECT-BENCH.md#reduced-boundary-and-simple-pole-test-2026-09-19)
records an explicit proper-open example where those jets increase the
required denominator. No new universal theorem-target predicate is added.

The conditional finite-boundary endpoint is now packaged in
[FiniteBoundary.lean](FiniteBoundary.lean):

```text
target derivatives of finite boundary generators lie in the boundary ideal [open]
    -> all actual conormal components vanish
    -> U_F = Spec B, hence the base-to-fixed-algebra map is bijective
    -> E is finite over B, hence the embedded polynomial source A is finite
    -> the source fills its intermediate normalization
    -> no hidden inertia, hence no height-one ramification
    -> Obs(F) = 0                         [purity + finite-etale rigidity inputs]
```

The finite tests use a generating set for the same $\mathfrak b_F$,
not a new denominator ideal or a chosen principal equation. The target
boundary and intermediate-normalization boundary are not identified;
source finiteness connects their emptiness by a proved implication.
`BranchPurityA2` and `AffinePlaneFiniteEtaleRigidity` remain explicit theorem
arguments. The new endpoint imports no custom literature axioms. These
are the existing full-planar research inputs, not the single
Keller--Galois rigidity input of the separate degree-two theorem.

The source-specific characterization also uses
[SourceIntersection.lean](../../../General/Keller/SourceIntersection.lean), which
proves $A\cap K=B$ from visible source divisors and factorization.
[ConjugateInvariantSource.lean](../../../General/Keller/ConjugateInvariantSource.lean)
applies it to the existing fixed algebra: a fixed element regular on the
marked source already belongs to $B$. The comparison does not show
that every fixed element is source-regular. Source unit reflection or a
visible center on each separate sheet cannot supply that assertion for
their joint algebra. The new criterion packages that assertion as
equivalent to boundary emptiness, rather than presuming a proof of it.

## Ramification reduction

For the canonical finite normalized cover constructed from the Keller
condition, the conditional endgame is:

```text
Keller condition + missing planar argument
    -> no height-one ramification in Spec(T) -> Spec(B)
    -> finite étale normalization                 [purity input]
    -> N = K, hence L = K                         [finite-étale rigidity input]
    -> Obs(F) = 0                                [Keller flatness + collision API]
```

The direct endpoint is now in [Ramification.lean](Ramification.lean):

- `planarVanishing_of_normalizedCover_noCodimensionOneRamification` takes the
  finite normalized cover, Keller hypothesis, and no-ramification premise.
- `planarVanishing_of_canonicalNoCodimensionOneRamification` constructs that
  cover internally and reduces the existing universal `PlanarVanishing`
  target to no height-one ramification for every planar Keller map.

Both take `BranchPurityA2` and `AffinePlaneFiniteEtaleRigidity` explicitly.
Neither imports the custom literature axioms nor requires the larger
collision model's conjugate centers or inertia-index realization. The older
model-based endpoint in
[Rigidity/Consequences.lean](../../Rigidity/Consequences.lean) remains available
to the boundary/conjugate-sheet route; it is not a dependency of this smaller
spine.

The missing mathematical step is deriving no height-one ramification from the
planar Keller hypothesis. Constructing the model or proving local comparison
lemmas does not establish that step.

## Local formulation of the missing step

For every height-one prime $\mathfrak q$ of $T$, with
$\mathfrak p=\mathfrak q\cap B$, aim to prove

```math
e(\mathfrak q/\mathfrak p)=1.
```

The existing target is `NoCodimensionOneRamification` in
[NormalizationDiagram.lean](../../NormalizationDiagram.lean), defined using
`Algebra.IsUnramifiedAt`, not a newly introduced index-one predicate.
The characteristic-zero residue-field criterion in
[General/Galois/RamificationIndex.lean](../../../General/Galois/RamificationIndex.lean)
relates unramifiedness, index one, and trivial inertia after the appropriate
Dedekind localization. Use the actual localized rings and the existing
`localRamificationIndex` comparisons; do not use global ideal powers in the
two-dimensional normalization.

Here the index is for the **full normal closure over the base**. Index one at
a visible center on one intermediate conjugate sheet is not the same result:
the sheet index is $[I:I\cap gHg^{-1}]$, which can be one while $I\ne1$.
The primes in question lie over the affine base, not over a chosen
compactification's divisors at infinity.

Equivalently, the local differential target is
$(\Omega_{T/B})_{\mathfrak q}=0$ at every height-one prime. The existing
`PlanarRamificationRigidity` asks for finite length of $\Omega_{T/B}$, a
sufficient criterion rather than a replacement goal. Its
`RamificationRigidityBridge` remains an explicit input in
[Rigidity/Interfaces.lean](../../Rigidity/Interfaces.lean).

## Original-extension pole route

One can instead work in $L$, before forming its normal closure. Put
$S=\mathrm{IntCl}_B(L)$. The constructed source open immersion
comes from $S\subseteq A$; $S$ is finite over $B$. It would suffice
to prove

```math
x,y\in S_{\mathfrak p}\quad
\text{for every height-one prime }\mathfrak p\subset S.
```

The normal-Noetherian height-one intersection theorem then gives
$A=S$, so the original map is finite. Keller étaleness and the stated
finite-étale rigidity input finish. This is a mathematical reduction using
[Stacks, Tag 031T](https://stacks.math.columbia.edu/tag/031T), not a new
Lean endpoint with the regularity hypothesis discharged.

The global source-divisor theorem gives one visible prime over each base
divisor, not regularity at every prime of $S$ above it. The
[original-extension test](OBJECT-BENCH.md#original-extension-pole-test-2026-09-19)
excludes genuinely monomial pole valuations in polynomial source
coordinates. General divisorial valuations can have cancellation between
terms of negative value; no reduction of all boundary valuations to the
monomial case has been proved.

## Direct local collision exclusion

[LocalCollision.lean](LocalCollision.lean) proves that two planar Keller
collision maps into any commutative local $\mathbb C$-algebra which agree
on residue coordinates are equal. The evaluated secant determinant reduces
to the nonzero constant Jacobian, hence is a unit; it annihilates every
coordinate difference. No domain hypothesis or ramification index is used.

[InertiaCoordinates.lean](InertiaCoordinates.lean) applies this directly to
the actual valuation inertia group of the marked normal closure. With the
ground-field constants included compatibly in a valuation ring $V$,

```math
\sigma\in I_V,\quad \sigma gH\ne gH
\quad\Longrightarrow\quad
\exists i\in\{1,2\}:\ g(x_i)\notin V.
```

Indeed, if both coordinates belonged to $V$, inertia would provide a
second local collision map with the same residues, contradicting movement
of the sheet. This argument needs no `ConjugateRamificationRealization`.
At a divisorial valuation, nonmembership means a coordinate pole.

The missing step on this route is to rule out that pole: it would suffice
to produce, at each nontrivial-inertia divisor, a moved sheet whose two
coordinates are regular. The existing visible sheet is inertia-fixed and
does not supply such a witness. Taking closure does not supply it either:
$\mathrm{IntCl}_B(gL)\subseteq gA$, not the reverse inclusion.
Extending the residual projector alone is insufficient; the collision
evaluation must extend on the source-coordinate generators. See the
[closure and pole-order audit](OBJECT-BENCH.md#local-collision-and-closure-audit-2026-09-19).

## Finite polynomial cancellation at a pole

[ValuationCancellation.lean](../../../General/Keller/ValuationCancellation.lean)
derives a necessary condition from the actual polynomial supports.
If a source coordinate is polar, some Keller component has a nonzero
linear occurrence of it. That summand is polar when the valuation is
trivial on the coefficient field. If the whole component is regular,
the maximal monomial value must therefore be attained at least twice.
The generic [finite-sum lemma](../../../General/Normalization/ValuationCancellation.lean)
uses Mathlib's `Valuation.map_sum_eq_of_lt`.

[PolarCancellation.lean](PolarCancellation.lean) applies this at a supplied
ramified divisor of the actual planar normalization diagram. The existing
center map $T\to V$ derives regularity of every target coordinate and
value one for nonzero complex coefficients. Core-freeness supplies an
inertia-moved sheet, and local collision rigidity supplies its coordinate
pole. No source-regularity or no-cancellation premise is added.

Write $\varphi_g$ for the existing conjugate source map and use
Mathlib's multiplicative valuation $v$, where a pole has value greater
than $1$, and put $c_m=\mathrm{coeff}_m(F_j)$.
The conclusion supplies $a\ne b$ in the support of some $F_j$,
on that same moved sheet, with

```math
v\bigl(\varphi_g(c_a x^a)\bigr)
=v\bigl(\varphi_g(c_b x^b)\bigr)
=\max_{m\in\mathrm{supp}(F_j)}
 v\bigl(\varphi_g(c_m x^m)\bigr)>1.
```

The pair witnesses repeated dominance; the cancellation may involve more
than those two terms. Since nonzero coefficients have value one, these
values depend only on the source-coordinate values and the finite
exponent supports. This is the necessary Newton-support resonance,
not an exclusion of all resonant valuations.

The generic polynomial step uses only the nonsingular linear Jacobian
at the origin. The remaining target is to use the full constant-Jacobian
identity to exclude the possible higher-order cancellations. Neither the
finite certificate nor the existing first-jet denominator bound supplies
that argument.

Verification (2026-11-09, Lean 4.28.0): all three new leaves pass their
focused builds; the actual-divisor target passes 2878 jobs with no
warnings. A separate importing client checks a genuine cancelling sum,
the monomial-value product formula, the no-polar-tie contrapositive,
and extraction from the actual diagram theorem without additional
regularity premises. All three audited declarations use only
`propext`, `Classical.choice`, and `Quot.sound`.
The full research umbrella was not rebuilt for this checkpoint.

## First local step: a regular transverse derivation

[General/Normalization/DerivationCriterion.lean](../../../General/Normalization/DerivationCriterion.lean)
now proves a concrete sufficient condition for local index one. In
$T_{\mathfrak q}$, it takes

```math
d:T_{\mathfrak q}\longrightarrow T_{\mathfrak q},\qquad
b\in\mathfrak q\cap B,\qquad d(b)\in T_{\mathfrak q}^{\times},
```

where $d$ is a derivation, and concludes
`localRamificationIndex (R := B) q = 1`. Its proof uses
$d(\mathfrak m^2)\subseteq\mathfrak m$: the extended base ideal cannot lie
in $\mathfrak m^2$ if it contains an element with unit derivative. No
uniformizer choice or principal-generator hypothesis is needed.

The generic criterion, local specialization, and composed unramifiedness
criterion passed targeted Lean builds. The index-one/unramifiedness comparison
is in [General/Normalization/LocalUnramified.lean](../../../General/Normalization/LocalUnramified.lean).
They do **not** assert that an extended Keller frame preserves
$T_{\mathfrak q}$. That is the next hypothesis to investigate at missing
boundary points; regularity on the visible polynomial sheets is not enough.
The base transversality part is now proved in
[General/Normalization/BaseTransversality.lean](../../../General/Normalization/BaseTransversality.lean):
every nonzero proper ideal in a characteristic-zero polynomial ring contains
an element whose derivative in some coordinate lies outside the ideal. The
proof chooses a nonzero element of minimal total degree; it requires neither
a principal generator nor a height-one hypothesis. For a base divisor, use
the polynomial presentation of $B=\mathbb C[P,Q]$. The coordinate selected
by this result can depend on the divisor: regularity of an arbitrary tangent
frame would not suffice.

[BaseFrame.lean](BaseFrame.lean) connects the target partials to the existing
Keller frames, both on the source and on each conjugate sheet in $N$:
$D_P(b(P,Q))=(\partial_u b)(P,Q)$, and similarly for $D_Q$ and
$\partial_v$. In Lean these use `coordinateAlgHom F`.
The partial is taken **before** target evaluation; it is not the ordinary
source partial of $b(P,Q)$. Transporting the base-prime witness and the
derivative to the actual localization remains specialization work, separate
from the missing regularity proof.

This is an alternative local route, not an assumption that the trace-landing
route has already closed. The remaining mathematical input is regularity of
the selected transverse frame in the actual boundary localization. See the
[denominator test on the bench](OBJECT-BENCH.md#concrete-boundary-regularity-test):
the denominator must avoid $\mathfrak q$, not just be nonzero.

## Testing the secant comparison

The finite generator criterion is in [FrameDenominator.lean](FrameDenominator.lean):
if $D(B)\subseteq T$, a multiplier clears the derivatives of a finite
$B$-module generating family of $T$ if and only if it clears all of
$D(T)$. This uses Leibniz, not $B$-linearity. It gives a nonzero
denominator, not one outside a specified prime.

The existing secant family is a different family.
[SecantReduction.lean](SecantReduction.lean) removes its redundant adjugate
entries and jets without changing the lattice or denominator. The matrix
entries and both first-derivative families are retained; the adjugate may
still be useful for other determinant/kernel identities.

The [quadratic diagnostic on the bench](OBJECT-BENCH.md#secant-comparison-audit-2026-09-18)
shows that secant coefficients can all be regular while a transverse
normalization derivative has a pole. It is not a Keller counterexample,
but rules out the proposed comparison based on generic secant identities
and étaleness on retained sheets alone.

[ConductorComparison.lean](ConductorComparison.lean) supplies a precise
alternative comparison with the existing order $U=B[\alpha]$:
$D(U)\subseteq\Lambda$ implies $(U:T)D(T)\subseteq\Lambda$.
Control of the base derivatives and $D(\alpha)$ suffices for its premise.
The local refinement in [ConductorLocalization.lean](ConductorLocalization.lean)
proves that a conductor element outside $\mathfrak q$ makes control of
$D(\alpha)$ equivalent to control of all $D(T)$ in a
$T_{\mathfrak q}$-submodule. This does not construct the adapted generator.
Conductor avoidance can be arranged by a local monogenic construction in
this characteristic-zero finite-normalization setting; it should not be
listed as an independent Keller-specific conjecture. The construction is
outlined on the bench and is not yet packaged in Lean.

[GeneratorDerivative.lean](GeneratorDerivative.lean) isolates the remaining
test using the existing monogenic Jacobian. Write
$f(X)=\sum_i a_iX^i=\mathrm{minpoly}_B(\alpha)$,
$J=f'(\alpha)$, and $\nu_D=\sum_i D(a_i)\alpha^i$. It proves

```math
J D(\alpha)=-\nu_D,\qquad
D(\alpha)\in\Lambda\ \Longleftrightarrow\ \nu_D\in J\Lambda
\quad(J\ne0).
```

Base derivative control gives $\nu_D\in\Lambda$, not membership in
$J\Lambda$. In the local ring the missing test is
$\nu_D\in JT_{\mathfrak q}$. For an adapted generator and a transverse
frame this is an exact reformulation of the ramification issue, not an
independent proof of its vanishing. Both comparisons remain bench tests;
neither is a new mandatory hypothesis of `PlanarVanishing`.

## Global polynomial input: one visible divisor over every base divisor

[General/Keller/DivisorVisibility.lean](../../../General/Keller/DivisorVisibility.lean)
uses the actual polynomial source, not merely a smooth affine open. Its
unit-reflection lemma applies to any subalgebra of a polynomial ring over a
reduced coefficient ring. For a Keller map, it proves

```math
\forall\mathfrak p\in\mathrm{Spec}^{(1)}B,\quad
\exists\mathfrak r\in\mathrm{Spec}^{(1)}A:\quad
\mathfrak r\cap B=\mathfrak p,
\qquad B\longrightarrow A\text{ is unramified at }\mathfrak r.
```

The proof transfers unique factorization to the coordinate-image base,
chooses a prime generator of $\mathfrak p$, and factors its nonunit image
in $A$. Flat going-down identifies the contraction of a source factor;
Keller étaleness gives its unramifiedness. This dimension-independent result
requires no extra visibility hypothesis and no generic-degree restriction.

This is **one visible source divisor**, not every normal-closure divisor.
The source theorem concludes with a prime of `SourceRing`.
[VisibleConjugateCenter.lean](../../../General/Normalization/VisibleConjugateCenter.lean)
now transports that prime into the marked normalization: lying-over and
Galois transitivity prove that the intermediate prime is an actual
conjugate center of any chosen full-normalization prime over the base
prime. This requires no supplied visibility or center-surjectivity premise.

For a supplied normalization diagram and its existing
`ConjugateRamificationRealization`, the checked corollary gives an
inertia-fixed sheet at every ramified divisor. The realization remains
explicit; this check does not verify the older unconditional model/index
assembly. In group terms the conclusion is $I\le gHg^{-1}$ for some
sheet, not $I=1$. In the nonnormal case, inertia can fix one sheet while
moving others. The missing step must control those other sheets; unit
reflection alone does not establish $\nu_D\in JT_{\mathfrak q}$.

[LocalizedJacobianDiagnostic.lean](LocalizedJacobianDiagnostic.lean)
checks a sharper negative test than the nonconstant-Jacobian quadratic
example: the rational map $(t,u)\mapsto(t^2,u/(2t))$ has determinant one
on $t\ne0$, but its target derivative of $t$ is not polynomial in
the normalization coordinates $(t,z)$. The diagnostic is not a global
polynomial Keller map; it misses the whole base divisor $s=0$. Thus it
fails exactly the new visibility conclusion. The bench distinguishes the
Lean-checked identities/non-polynomiality from the local geometric
interpretation.

The cubic variant in the same file checks determinant one and a surviving
preimage for **every complex target point**, while its target derivative
still fails to preserve the polynomial normalization ring. Thus the new
visibility conclusion by itself does not repair the inference. The
[mixed-secant audit](OBJECT-BENCH.md#visible--hidden-secant-test-2026-09-19)
tests the actual polynomial identities separately: their singular matrix
relation does not bound hidden derivatives. No enlarged finite coefficient
family or new landing assumption is promoted into the spine from this test.

## Boundary/trace route into the spine

This is a candidate proof of the missing planar step, not an additional
condition on the final `PlanarVanishing` statement:

```text
uniform secant-frame trace landing                [OPEN]
    -> PlanarBoundarySeparation                   [proved conditional implication]
    -> NoCodimensionOneRamification               [for the supplied model]
    -> Obs(F) = 0                                [endgame above]
```

The actual boundary-section ring $R_C$, secant-frame denominator ideal,
and pole witness are constructed. In
[SecantFrameTraceLanding.lean](../SecantFrameTraceLanding.lean),
`boundarySeparation_of_secantFrameTraceLanding` requires landing for every
nontrivial prime-order subgroup. `boundarySectionSubalgebra_eq_bot_of_secantFrameTraceLanding`
also shows that landing already forces $R_C=T$: here `⊥` denotes the base
$T$-subalgebra, not the zero ring.

What is not proved is a uniform trace bound for **all** sections of $R_C$.
Clearing finitely many secant coefficients is not that bound. The
[object bench](OBJECT-BENCH.md) records the constructions and negative tests.
This trace endgame needs a nonzero multiplier, not one outside the boundary
prime. The pole witness already defeats every nonzero multiplier. Its
outside-prime numerator is constructed in `HeightOneBoundaryPole`; that
choice must not be confused with a regularity denominator for the frame.

## Earlier work order for the local-ramification route

This is retained as a research plan, not the current manuscript proof
spine. The established findings are the characterizations above; the
following steps would pursue the stronger universal vanishing target.

1. Test whether the global polynomial Keller condition supplies
   $\nu_D\in JT_{\mathfrak q}$ for the adapted integral generator and
   the transverse frame, or rules out the coordinate pole forced by the
   direct inertia argument. The local collision contradiction is proved
   without an index realization; source-coordinate regularity is not.
   The [polynomial pole-order test](OBJECT-BENCH.md#global-polynomial-pole-order-test-2026-09-19-not-formalized)
   yields $e\le(d-2)M$, which allows poles when total polynomial degree
   $d\ge3$; iterating the same derivative does not strengthen it.
   The coefficientwise derivative identity is proved;
   the divisibility is not. The source-visibility theorem now supplies an
   unramified source divisor over every base divisor, but does not control
   the remaining normal-closure sheets. The weaker generic secant comparison fails the
   quadratic diagnostic even with unit conductor. Keep the local adapted
   generator construction and transport to the actual localization separate
   from this substantive premise. More equivalent criteria alone do not
   discharge it.
2. Keep the larger conjugate-sheet model/index assembly on the bench for the
   boundary route. Its ramification-to-nontrivial-inertia leaves, local-index
   wrappers, and complete characteristic-zero model assembly are verified.
   They are not prerequisites of the smaller direct conditional endgame.
   Boundary separation/trace landing remains an
   alternative route to the same no-ramification premise.
3. Once one route closes, assemble `PlanarVanishing`, run the complete build
   and axiom audit, and align Paper 2 with the verified argument. Do not require
   every bench route to succeed or import them all into the final proof.

Keller--Galois rigidity remains a separate possible finish if one proves
$L/K$ normal. The normality of $N/K$ does not supply that premise.

## Checked first step (2026-09-18)

Targeted builds passed for `General.Normalization.LocalUnramified`,
`General.Normalization.DerivationCriterion`, and
`Planar.Research.Vanishing.Ramification`. The nine new lemmas were audited:
their only axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Purity, finite-etale rigidity, and no ramification are explicit hypotheses in
the planar reduction, not hidden axioms or discharged conclusions.

This is not a full-repository build or a proof of `PlanarVanishing`. The
normalization-specific index wrapper and older conjugate-index/model assembly
remain separate verification work; the direct endpoint above builds without
them.

## Checked base/frame step (2026-09-18)

Targeted builds passed for `General.Normalization.BaseTransversality` and
`Planar.Research.Vanishing.BaseFrame`. All ten new lemmas were audited and use
only `propext`, `Classical.choice`, and `Quot.sound`. No new predicates,
literature assumptions, or `sorry` proofs were introduced.

This discharges the generic base-transversality argument and identifies the
actual Keller-frame action on target polynomials. It does not prove boundary
regularity, prime avoidance for the frame denominator, or `PlanarVanishing`.
No full-repository build is claimed.

## Checked comparison/pruning step (2026-09-18)

Targeted builds passed for `Vanishing.FrameDenominator`,
`Vanishing.SecantReduction`, and `Vanishing.ConductorComparison`, all under
`CollisionIdeals.Planar.Research`. All ten public lemmas were audited and use
only `propext`, `Classical.choice`, and `Quot.sound`; there are no new axioms,
`sorry` proofs, or object definitions. The original secant definitions were
preserved; matrix-only equality is available without breaking their users.

The quadratic secant/conductor diagnostic and the conjugate-source overring
comparison are mathematical audits recorded on the bench, not Lean results.
They explain which weaker inferences fail and which hypotheses a successful
Keller-specific argument must genuinely use. Boundary regularity and planar
vanishing remain open in this development. No full-repository build or
manuscript change was made in this step.

## Checked local-generator test (2026-09-18)

The targeted build for `Vanishing.GeneratorDerivative` also built
`Vanishing.ConductorLocalization` successfully (1842 jobs). All seven new
lemmas were audited and use only `propext`, `Classical.choice`, and
`Quot.sound`. No new definitions, axioms, or `sorry` proofs were added.

This verifies the local conductor cancellation, the differentiated
minimal-polynomial identity, and the exact lattice-membership criterion.
It does not construct the locally adapted generator in Lean or establish
the required Keller-specific numerator divisibility. No full-repository
build, manuscript change, commit, or submission is claimed.

## Checked global visibility step (2026-09-19)

Targeted builds passed for `General.Keller.DivisorVisibility` (2914 jobs)
and `Planar.Research.Vanishing.LocalizedJacobianDiagnostic` (2626 jobs),
under `CollisionIdeals`. All five new public results were audited; their
only axioms are `propext`, `Classical.choice`, and `Quot.sound`. No new
object definitions, axioms, or `sorry` proofs were added. The diagnostic
build reports only simplifier/tactic-style warnings.

The visibility theorem derives a source prime from `IsKeller` rather than
requiring a visibility witness. The diagnostic verifies identities on the
actual rational function field and a failure of polynomial derivative
regularity, not a counterexample to planar vanishing. The local generator
constructor, the marked-normalization transport of source visibility, and
the Keller-specific derivative divisibility are not proved by this step.
No full-repository build or manuscript change is claimed.

## Checked direct local collision step (2026-09-19)

Targeted builds passed cleanly for `Vanishing.LocalCollision` (1576 jobs)
and `Vanishing.InertiaCoordinates` (2600 jobs), under
`CollisionIdeals.Planar.Research`. All three new lemmas passed a joint
axiom audit and use only `propext`, `Classical.choice`, and `Quot.sound`.
No new object definitions, axioms, or `sorry` proofs were introduced.

This proves local collision rigidity and the coordinate-pole consequence
of actual inertia movement without an index realization. It does not
establish boundary regularity or `PlanarVanishing`. The completion and
pole-order calculations remain mathematical audits on the bench. No
full-repository build, manuscript change, commit, or submission was made.

## Checked monomial-support exclusion (2026-09-19)

The targeted build for `General.Keller.MonomialWeights` passed cleanly
(1543 jobs). Both new lemmas passed a joint axiom audit using only
`propext`, `Classical.choice`, and `Quot.sound`. They use the existing
`IsKeller` and `Finsupp.weight`; no new predicates or axioms were added.

The result concerns integer weights on polynomial supports in arbitrary
dimension over any field. The monomial-valuation consequence and the
nonmonomial cancellation diagnostics are mathematical applications recorded
on the bench, not a formal valuation construction. No general height-one
coordinate-regularity theorem or proof of `PlanarVanishing` was obtained.
The research import graph is acyclic; this is not a full-repository build.
No manuscript change, commit, push, or submission was made.

## Checked Galois-descent target (2026-09-19)

Targeted builds passed cleanly for `General.Galois.Descent` (1890 jobs),
`General.Galois.PolynomialDescent` (2520 jobs), and
`Planar.Research.Vanishing.GaloisDescent` (2629 jobs). All eight new
theorems and the `PlanarGaloisDescent` target definition passed a joint
axiom audit using only `propext`, `Classical.choice`, and `Quot.sound`.
No new axioms or `sorry` proofs were introduced.

The shared normality criterion is dimension-independent and does not
require separability. The open universal target is specifically over
the complex plane, using the existing canonical marked closure. Its
vanishing endpoint takes both descent and Keller--Galois rigidity as
explicit hypotheses; neither is proved by defining the target.

The research entry point imports the new route; its local import graph is
acyclic, and all 99 local documentation links checked exist. This is not
a full-repository build. No manuscript change, commit, push, or submission
was made.

## Checked non-descent witness (2026-09-19)

Targeted builds passed cleanly for the updated `General.Galois.Descent`
(1890 jobs) and `General.Galois.PolynomialDescent` (2520 jobs). Both new
witness lemmas passed the axiom audit using only `propext`,
`Classical.choice`, and `Quot.sound`. A temporary integration theorem also
passed: the witness gives a genuinely moved planar collision coordinate
and a zero value of its secant determinant, using the existing collision
pair and secant APIs. It has the same three standard axioms.

No new object definitions, axioms, or `sorry` proofs were introduced. The
frame/nonnormal-cubic diagnostic remains a mathematical audit, not a new
formalized counterexample. Neither a common local realization of the
moving pair nor the universal descent target was proved. This is not a
full-repository build; no manuscript change, commit, push, or submission
was made.

## Checked common-center test (2026-09-19)

A temporary `lake env lean` audit verified that zero secant evaluation
forces the coordinate-difference ideal to be the unit ideal, and that
distinct Keller collision maps into a domain satisfy this premise. Both
lemmas use only `propext`, `Classical.choice`, and `Quot.sound`; the check
passed without warnings or errors. The result is already encoded by the
existing comaximality API, so no repository Lean module or new target was
added or changed in this step.

The all-conjugate-ring quotient calculation and proper-open cubic test
are recorded separately as mathematical audits. They identify a possible
deleted divisor, not a proof that it is empty. The common-center shortcut
does not establish descent or planar vanishing. All 109 local documentation
links checked exist; there was no full-repository build, manuscript edit,
commit, push, or submission.

## Checked finite simple-pole test (2026-09-19)

Targeted builds passed for `General.Normalization.SimplePole` (1386 jobs)
and the updated `Planar.Research.Vanishing.LocalizedJacobianDiagnostic`
(3318 jobs). The five shared criterion lemmas and two new diagnostic
lemmas passed axiom audits using only the standard `propext`,
`Classical.choice`, and `Quot.sound` axioms (the ideal-only lemma does not
need choice). No new definitions, axioms, or `sorry` proofs were added.
The diagnostic build has tactic-style warnings, including a redundant
`ring` following a closing `field_simp`; the shared criterion builds cleanly.

The polynomial criterion requires neither squarefreeness nor a fixed
number of variables. The diagnostic verifies that a target derivative
raises a simple pole and leaves its cyclic module on a proper open source;
it is not a full-plane polynomial Keller example. Exact secant denominator
ideals and the conormal interpretation remain mathematical audits, not
additional Lean claims.

The active boundary target is now explicitly finite: two generator tests
or two remainders modulo the reduced boundary equation, without an entire
pole tower. Actual Keller-specific preservation and the Lean construction
of the all-conjugate base boundary remain open. All 116 local documentation
links checked exist, and the 118-module local import graph checked is
acyclic. This is not a full-repository build; no manuscript change, commit,
push, or submission was made.

## Checked conormal realization and manuscript synchronization (2026-09-19)

The targeted build of `General.Normalization.ConormalDerivation` passed
(2886 jobs). Its adapter definition and four lemmas passed axiom audits
using only `propext`, `Classical.choice`, and `Quot.sound`. Temporary
examples also verified the existing finite-generation instances for
`Ideal.Cotangent` over both the Noetherian base and its quotient. No
duplicate quotient, universal theorem-target predicate, axiom, or `sorry`
was introduced.

Paper II now records the all-conjugate target open, reduced boundary,
finite simple-pole/conormal criterion, and the Galois origin of the secant
relation in a separate research section. Its degree-two theorem is
unchanged. The actual boundary remains uninstantiated in Lean, and no
Keller-specific vanishing or comparison from secants to its conormal
classes is claimed. The semantic-parity table records these distinctions.
No research object was pruned, archived, committed, or pushed in this step.

## All-conjugate algebra and dependency audit (2026-09-19)

`General.Galois.ConjugateAlgebra` now defines the actual
$E=B[g(\iota(A)):g\in G]\subset N$ as the adjoin of the finite
set of conjugate source coordinates. Conjugate-polynomial membership,
Galois stability in both directions, finite generation, and finite type
are proved. This construction is dimension-independent and needs no
Keller condition beyond the supplied marked finite normal-closure data.
It does not assert that $E$ is module-finite over $B$.

The geometric audit of Paper II confirms the selected regular component,
free scheme-theoretic action, invariant affine open, and reduced principal
boundary argument under its stated Keller hypotheses. The finite-submodule
step uses Noetherianity of $B$; empty boundary then uses classical
finite-etale rigidity of affine space. The actual target open is now
instantiated by the shorter route below, followed by its actual reduced
boundary. The stronger etale/free-action identifications remain separate work.

The construction reuses $E$ rather than introducing a new boundary-model
hypothesis bundle. The 2026-09-20 checkpoint below shortens the route to the
target open:

1. Construct $E$, identify its fraction field with $N$, and construct
   its fixed algebra, over which $E$ is module-finite (proved).
2. Realize $E^G$ inside $K$ with fraction field $K$ under separability,
   and prove $E/B$ unramified under Keller (proved).
3. Descend finite type and quasi-finiteness to $E^G/B$. Use birationality
   and normality of $B$ to identify its spectrum with an affine target
   open (proved). The selected-etale-component and free-action comparisons are not
   prerequisites for this shorter open-immersion route.
4. Form the radical ideal of the actual complement and specialize the
   existing conormal criterion (proved). Its principal reduced presentation
   remains separate work for the one-generator simple-pole formulation;
   it is not needed for the intrinsic conormal criterion.

These are construction tasks. None proves that the resulting conormal
components vanish; that remains the distinct Keller-specific comparison.

The new [comparison diagnostic](OBJECT-BENCH.md#galois--secant-boundary-comparison-audit-2026-09-19)
shows exactly why Galois descent and secants alone are insufficient on a
proper open source. Even a finite invariant secant expression for $1/s$
does not bound its first derivatives. No Keller-specific vanishing is
claimed, and the full polynomial-plane hypothesis must enter any successful
comparison explicitly.

The dependency audit separates this active finite test from the alternative
conductor, trace, and ramification routes. The unchanged elementary lemma
`derivation_mem_ideal_of_mem_sq` was moved to
[DerivationIdeal.lean](../../../General/Normalization/DerivationIdeal.lean),
preserving its name and existing clients. As a result the conormal criterion
has only four local modules in its import closure, down from 24, and no
ramification dependency. No mathematical object, alternative route, or
negative control was deleted. The public planar spine remains isolated.

The accumulated research umbrella requires all of the previously untracked
Lean research modules. Its import changes must be committed together with
those dependencies, not as an incomplete umbrella-only snapshot.

## Integrated research checkpoint (2026-09-19)

The all-conjugate algebra's seven declarations passed their targeted build
and axiom audit. The extracted derivation lemma, simple-pole criterion, and
conormal realization passed targeted builds and a combined nine-declaration
audit; finite-generation instances for the conormal module were checked as
well. These audits use only `propext`, `Classical.choice`, and `Quot.sound`.

Integration exposed elaboration issues in the older divisorial-index route.
The repairs reuse the existing local-base-change algebra instances, scope
the normal-closure base algebra to the actual field rather than a polymorphic
instance that also matches the source field, and remove redundant type
reconstructions. The polynomial wrapper has a local heartbeat allowance;
the theorem statements and mathematical hypotheses are unchanged. The
characteristic-zero diagram and `PolynomialKellerCollisionModel.ofIsKeller`
now compile with the inertia and local-index inputs derived internally.

The combined integration build passed all 3818 jobs:

```sh
lake build CollisionIdeals CollisionIdeals.Planar.Research CollisionIdeals.Palomar.PaperOne.Solution CollisionIdeals.Palomar.PaperTwo.Solution
```

Only the existing local-base-change and diagnostic tactic-style linter
warnings remain. This verifies the public library, the separate research
umbrella, and both solution entry points together; it does not discharge
the open research hypotheses.

A final axiom audit of `integralClosure_localRamificationIndex_eq`,
`polynomialConjugateCenter_localRamificationIndex_eq`, and
`PolynomialKellerCollisionModel.ofIsKeller` passed. Each depends only on
`propext`, `Classical.choice`, and `Quot.sound`; the integration repairs
introduce no new mathematical input.

Paper II was rebuilt and all thirteen rendered pages checked, with no final
LaTeX warnings or layout defects. Paper I and the manuscript archive are
unchanged. The parity queue now distinguishes the verified full
collision-normalization model from the still-uninstantiated invariant-open
boundary. Neither that model nor the finite conormal criterion proves the
Keller-specific vanishing comparison. No submission is made.

## Fraction-field and invariant-ring checkpoint (2026-09-19)

[ConjugateFractionField.lean](../../../General/Galois/ConjugateFractionField.lean)
proves that the existing inclusion $E\subset N$ makes $N$ a fraction
field of $E$. Every conjugate source rational function is a quotient of
conjugate polynomials in $E$, and these generate the supplied normal
closure. The shared lemma `NormalClosureData.eq_top_of_conjugate_mem` now
serves both this proof and the existing descent theorem. No normality of
$L/K$, coordinate descent, Keller condition, or separability premise is
introduced.

[ConjugateInvariants.lean](../../../General/Galois/ConjugateInvariants.lean)
restricts the action via Mathlib's `IsInvariantSubring` and reuses
`FixedPoints.subalgebra` for $E^G$. The fraction-field result makes this
action faithful. Finite-group invariants give integrality over $E^G$,
and the already-proved finite type over $B$ gives module-finiteness over
$E^G$. Neither finiteness over $B$ nor scheme-theoretic freeness is
inferred. Under the explicit additional assumption that $N/K$ is
separable, membership in $E^G$ is equivalent to membership in the embedded
base field $K$.

At this checkpoint the comparison was elementwise. The 2026-09-20
checkpoint below packages the corresponding $B$-subalgebra of $K$ and
its fraction field, using `Subalgebra.comap` along the marked base-field
embedding, not a new abstract quotient or supplied birationality hypothesis.

The geometric route considered at this checkpoint was to identify $E$ with the
selected component of the tensor product of conjugate source algebras and
obtain etaleness from the Keller condition. Scheme-theoretic freeness and
the invariant affine-open realization would then follow; the ordinary
fixed-ring construction alone is not the quotient theorem. The relevant
free-action comparison is [Stacks, Tag 07S7](https://stacks.math.columbia.edu/tag/07S7),
with the affine invariant-ring formulation in
[Tag 03BM](https://stacks.math.columbia.edu/tag/03BM).
Only after identifying this actual open should its reduced complement be
fed into the existing finite conormal criterion. Keller-specific conormal
vanishing remains open. The next checkpoint separates the shorter route
to the target open from these stronger etale/free-action identifications.

The targeted fraction-field build passed all 2521 jobs, and the invariant
module build passed all 2585 jobs. A combined audit of fifteen declarations
uses only `propext`, `Classical.choice`, and `Quot.sound`. Five generic
external-client checks passed: faithful action, module-finiteness,
inference of the fixed algebra's ring structure, integrality, and the
separable fixed-field membership equivalence. The canonical fixed-algebra
ring instance is exported as a specialization of `Subalgebra.toCommRing`;
no parallel ring structure or quotient is introduced.

The combined build of `CollisionIdeals`, `CollisionIdeals.Planar.Research`,
`CollisionIdeals.Palomar.PaperOne.Solution`, and
`CollisionIdeals.Palomar.PaperTwo.Solution` passed all 3820 jobs. Only the
previously known local-base-change and diagnostic linter warnings replayed;
the two new modules have no warnings. No axiom or `sorry` declaration was
added.

The 170-module local import graph is acyclic with no missing imports. The
focused planar closure remains 35 modules, and the separate research closure
is 122; all 134 local documentation-link targets checked exist. No manuscript,
PDF, archive, push, or submission is changed in this step.

## Target-field and unramifiedness checkpoint (2026-09-20)

[ConjugateInvariantField.lean](../../../General/Galois/ConjugateInvariantField.lean)
realizes the existing fixed algebra in the target function field. Pull back
$E\subset N$ along $K\hookrightarrow N$; the resulting
$B$-subalgebra of $K$ has fraction field $K$. Under separability
of $N/K$, the fixed-field theorem gives a canonical $B$-algebra
equivalence with the same $E^G$ already constructed. This gives its
embedding in $K$; fractions from $B$ already suffice to prove
$\mathrm{Frac}(E^G)=K$. The compatibility lemmas preserve both
the original map from $B$ and the inclusion in $N$. No additional
quotient, global competing algebra instance, or birationality hypothesis
is introduced.

[ConjugateUnramified.lean](../../../General/Keller/ConjugateUnramified.lean)
uses the Keller condition on the actual generating source sheets. Two
infinitesimal lifts from $E$ agree on each conjugate source algebra by
Keller etaleness, hence agree on their generated algebra. This proves
formal unramifiedness, and existing finite type gives unramifiedness of
$E/B$. This argument does not first identify a tensor-product component
and does not infer flatness or etaleness of $E/B$.

### Geometric construction planned at this checkpoint

The following was the audited next route. It is implemented in the
target-open checkpoint below:

1. Unramifiedness and finite type make $E/B$ quasi-finite.
2. Since $B$ is Noetherian and $E$ is finite over its fixed subalgebra,
   [Artin–Tate (Stacks, Tag 00IS)](https://stacks.math.columbia.edu/tag/00IS)
   makes $E^G/B$ finite type.
3. The integral inclusion $E^G\hookrightarrow E$ gives a surjection on
   spectra. Thus quasi-finiteness descends to $E^G/B$, as in
   [Stacks, Tag 0GWS](https://stacks.math.columbia.edu/tag/0GWS).
4. Apply the existing
   `isOpenImmersion_integralClosure_of_quasiFinite` from
   [OpenImmersion.lean](../../../General/Normalization/OpenImmersion.lean).
   The fraction-field comparison and normality of $B$ identify the
   relative integral closure with $B$, yielding the desired open
   immersion $\mathrm{Spec}(E^G)\hookrightarrow\mathrm{Spec}B$.

This route needs neither scheme-theoretic freeness nor the stronger
selected-etale-component identification merely to construct the target
open. Those comparisons remain available for the stronger torsor picture.
It also does not require assuming that $E^G$ is normal: normality of
the target $B$, already available from the finite function-field data,
is sufficient here.

The remaining construction after the open immersion is its actual reduced
boundary and principal presentation. Proving the two Keller-specific
conormal components vanish is still a separate open theorem. None of the
new algebraic results identifies $E^G$ with $B$ or proves planar
obstruction vanishing.

The target-field module passed its targeted build (2586 jobs), and the
unramifiedness module passed its targeted build (2809 jobs), both without
warnings. The fraction-field proof uses a theorem-local elaboration budget
and explicit scalar action; this changes no mathematical hypothesis.

The combined axiom audit of thirteen declarations uses only `propext`,
`Classical.choice`, and `Quot.sound`. All ten external-client checks passed,
covering the pullback's canonical structures, the equivalence, the original
fixed algebra's fraction field, both scalar towers, embedding compatibility,
and the two unramifiedness statements. Four examples require a scoped
typeclass-synthesis budget of 80000; the two tower examples also bind the
canonical scalar actions explicitly. These are inference controls, not new
algebra structures or mathematical premises.

The combined build of `CollisionIdeals`, `CollisionIdeals.Planar.Research`,
`CollisionIdeals.Palomar.PaperOne.Solution`, and
`CollisionIdeals.Palomar.PaperTwo.Solution` passed all 3822 jobs. Only the
pre-existing local-base-change and diagnostic linter warnings replayed.
The 172-module local import graph is acyclic with no missing imports; the
focused planar closure remains 35 modules and the separate research closure
is 124. All 141 local documentation-link targets checked exist, and
`git diff --check` passes. No manuscript, PDF, archive, commit, push, or
submission is changed in this checkpoint.

## Invariant target-open checkpoint (2026-09-20)

The preceding fraction-field/unramifiedness checkpoint was committed as
`121fb56`. Those two results now enter the actual open-immersion proof:

1. [ConjugateInvariantFiniteType.lean](../../../General/Galois/ConjugateInvariantFiniteType.lean)
   applies Artin–Tate to the existing $B\subset E^G\subset E$, proving
   finite type of $E^G/B$. Neither Keller nor separability is needed
   for this step.
2. [QuasiFiniteDescent.lean](../../../General/Normalization/QuasiFiniteDescent.lean)
   proves the reusable finite-fiber descent along an integral injective
   extension. Applying it to $E^G\subset E$, Keller unramifiedness of
   $E/B$ gives quasi-finiteness of $E^G/B$.
3. [BirationalOpen.lean](../../../General/Normalization/BirationalOpen.lean)
   identifies the relative integral closure with the normal base for an
   intermediate algebra in its fraction field. The existing affine
   Zariski-main theorem then gives an open immersion. This generic lemma
   assumes neither Noetherianity of the base nor normality of the
   intermediate algebra.
4. [ConjugateInvariantOpen.lean](../../../General/Keller/ConjugateInvariantOpen.lean)
   applies these lemmas to the actual fixed algebra and its proved
   target-field embedding. Under Keller and separability of $N/K$, it
   proves
   ```math
   \mathrm{Spec}(E^G)\hookrightarrow\mathrm{Spec}B.
   ```
   `polynomialConjugateInvariantTargetOpen` is the standard
   `Scheme.Hom.opensRange` of this map, and
   `polynomialConjugateInvariantTargetOpen_isAffineOpen` proves that this
   actual $U_F$ is affine.

The fixed algebra has not been replaced by a second quotient, and no
open-model hypothesis was introduced. Neither flatness of $E/B$ nor
scheme-theoretic freeness is needed for this construction. Its next step
is the actual radical ideal
$\mathfrak b_F=I(\mathrm{Spec}B\setminus U_F)$ and its principal
reduced presentation. The stronger etale/torsor and $H$-invariant
localization comparisons remain separate. Proving the Keller-specific
conormal classes vanish remains the substantive open theorem; the open
immersion does not assert $U_F=\mathrm{Spec}B$.

The generic descent leaf passed 2001 jobs and its default-setting external
client; the birational leaf passed 2678 jobs and two independent clients.
The actual finite-type and target-open build passed all 2923 jobs. These
builds have no warnings. A private generic adapter reuses Mathlib's
unramified-to-quasi-finite instance to avoid inference through the nested
conjugate subalgebra; it adds no mathematical premise.

The combined build of `CollisionIdeals`, `CollisionIdeals.Planar.Research`,
`CollisionIdeals.Palomar.PaperOne.Solution`, and
`CollisionIdeals.Palomar.PaperTwo.Solution` passed all 3826 jobs. The eight
public declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
All seven external-client checks passed: the two generic clients use default
settings, while the five actual-object clients use scoped elaboration and
typeclass-synthesis budgets of 800000 and 80000. These budgets add no
mathematical premises. Only pre-existing local-base-change and diagnostic
linter warnings replayed.

The 176-module local import graph is acyclic with no missing imports. The
focused planar closure remains 35 modules; the research closure is 128.
All 152 local documentation-link targets checked exist, and
`git diff --check` passes. Paper II's Lean-status paragraph now records the
proved invariant open and the still-open reduced-boundary and conormal
steps. Its rebuilt 13-page PDF passed visual review, with no warnings in
the final LaTeX log. Paper I and the manuscript archive are unchanged.
The earlier checkpoint is committed as `121fb56`; this target-open
checkpoint remains uncommitted, with no push or submission.

## Actual reduced-boundary and intrinsic-conormal checkpoint (2026-09-20)

The next construction uses the same target open, without selecting an
equation or supplying a new boundary model:

```math
\mathfrak b_F=I(\mathrm{Spec}B\setminus U_F)\subset B.
```

[AffineOpenBoundary.lean](../../../General/Normalization/AffineOpenBoundary.lean)
reuses Mathlib's `PrimeSpectrum.vanishingIdeal`. It proves radicality, the
exact complement as zero locus, and the unit-ideal/full-open equivalence.
Its nonzero-ideal lemma needs only a nonempty open, not a domain assumption.
[ConjugateInvariantBoundary.lean](../../../General/Keller/ConjugateInvariantBoundary.lean)
applies this API to the actual target open, proves that open nonempty, and
proves $\mathfrak b_F$ nonzero and finitely generated. A nonzero ideal
does not assert a nonempty boundary: the empty boundary has the unit ideal.

[PolynomialConormal.lean](../../../General/Normalization/PolynomialConormal.lean)
transports polynomial-coordinate derivations through an algebra equivalence
and transfers the existing characteristic-zero conormal criterion to any
algebra with that polynomial presentation.
[ConjugateInvariantConormal.lean](../../../General/Keller/ConjugateInvariantConormal.lean)
uses the existing injective target-polynomial presentation of $B$.
`polynomialImageCoordinatePartial_rangeRestrict` verifies that the partial
is taken before target evaluation; it is not the ordinary source partial
of the evaluated polynomial. No new frame, quotient, or obstruction is
introduced.

The actual conormal module $\mathfrak b_F/\mathfrak b_F^2$ is finitely
generated over $B$. In characteristic zero the actual criterion is

```math
\left(\forall i,\ [d_i]:\mathfrak b_F/\mathfrak b_F^2\to B/\mathfrak b_F
\text{ is zero}\right)
\quad\Longleftrightarrow\quad U_F=\mathrm{Spec}B.
```

There are two component maps in the planar specialization. This criterion
does not require the principal presentation $\mathfrak b_F=(s)$, so
that separate formalization no longer blocks stating the actual finite
conormal target. Without selecting a generator, these are two maps on a
finitely generated module, not two chosen element classes or a claim of
cyclicity. The principal reduced presentation remains useful for the
rank-one simple-pole formulation.

The substantive gap is unchanged: prove the actual Keller-specific
component maps vanish (equivalently, preserve $\mathfrak b_F$).
The new equivalence establishes neither side for every Keller map. No
principal-equation assumption, flatness/freeness assertion, or boundary
vanishing hypothesis is introduced into the construction.

The generic boundary leaf passed 1920 build jobs, four theorem-axiom
checks, and five external scheme-open clients. The generic polynomial
conormal leaf passed 1731 jobs, five declaration-axiom checks, and four
external clients at default elaboration settings. The actual boundary and
conormal modules passed the combined 2931-job targeted build without
warnings. A private generic finite-quotient helper avoids an inference
timeout through the nested actual ideal; it changes no premise and needs
no increased elaboration budget. The nonempty-open theorem alone uses a
scoped typeclass-synthesis budget of 80000 for the inherited fixed-ring
structures.

The final combined build of `CollisionIdeals`,
`CollisionIdeals.Planar.Research`,
`CollisionIdeals.Palomar.PaperOne.Solution`, and
`CollisionIdeals.Palomar.PaperTwo.Solution` passed all 3830 jobs. Only the
pre-existing local-base-change and diagnostic linter warnings replayed.
All 21 public declarations use only `propext`, `Classical.choice`, and
`Quot.sound`. All ten final external-client checks passed at default
elaboration settings, including the planar two-component specialization
and a proper-nonzero-ideal negative control. The final audit was rerun
directly after the delegated temporary session became unavailable.

The 180-module local import graph has no missing imports or cycles. The
focused planar closure remains 35 modules; the research closure is 132.
All 162 local documentation-link targets checked exist, and
`git diff --check` passes. The semantic parity queue and Paper II's status
paragraph now distinguish the actual boundary and intrinsic conormal
criterion from the still-unformalized principal presentation and open
Keller-specific vanishing statement. The rebuilt 13-page PDF passed
complete visual review, with no warnings in the final LaTeX log. Paper I
and the manuscript archive are unchanged. This work and the preceding
target-open checkpoint remain uncommitted; no push or submission was made.

## Finite-generator-to-vanishing checkpoint (2026-09-20)

The actual finite test is now connected to the existing planar endpoint:

1. [FiniteConormalTest.lean](../../../General/Normalization/FiniteConormalTest.lean)
   reduces a conormal component to derivatives of any finite ideal
   generating set, by Leibniz and span induction. The actual-boundary
   wrappers supply such a set and identify the successful test with
   $U_F=\mathrm{Spec}B$. No principal equation is required.
2. [FullOpenAlgebra.lean](../../../General/Normalization/FullOpenAlgebra.lean)
   converts a full affine open immersion into a bijective algebra map.
   [ConjugateInvariantFiniteness.lean](../../../General/Keller/ConjugateInvariantFiniteness.lean)
   applies this to $B\to E^G$, then uses finiteness of $E/E^G$
   and the embedded source $A\subset E$ to prove finiteness of
   $E/B$ and $A/B$. Noetherianity of $B$ supplies submodule
   finiteness; source finiteness is derived, not assumed in this bridge.
3. [FiniteSource.lean](../../../General/Normalization/FiniteSource.lean)
   proves that a finite source fills its intermediate normalization.
   [FiniteBoundary.lean](FiniteBoundary.lean) then excludes hidden inertia
   and uses the existing no-ramification endpoint to conclude
   $\mathrm{Obs}(F)=0$. `BranchPurityA2` and
   `AffinePlaneFiniteEtaleRigidity` are explicit inputs. The model is
   constructed from the Keller map; no model-existence premise or custom
   literature-axiom import is added.

The target boundary and intermediate-normalization boundary remain
distinct. Their emptiness is connected through actual source finiteness,
not an identification of their defining objects. The generic leaves and
dimension-independent wrappers stay in `General`; only the final planar
endpoint is in the research tree. The focused degree-two theorem is
unchanged.

The remaining theorem is the generator membership itself:
$\partial_Pf_j,\partial_Qf_j\in\mathfrak b_F$ for generators of
the actual reduced boundary. Neither finite generation nor preservation
after localization proves it. The
[proper-open negative control](OBJECT-BENCH.md#finite-generator-endpoint-audit-2026-09-20)
records this distinction. This checkpoint completes a conditional
connection, not a proof of full planar vanishing.

The targeted actual-boundary endpoint build passed all 3020 jobs. Only
the pre-existing local-base-change linter warning replayed. The shared
source-finiteness proofs use scoped elaboration budgets for the nested
subalgebra structures; no mathematical hypothesis is added by those
settings.

The full build of `CollisionIdeals`, `CollisionIdeals.Planar.Research`,
`CollisionIdeals.Palomar.PaperOne.Solution`, and
`CollisionIdeals.Palomar.PaperTwo.Solution` passed all 3835 jobs. Only the
pre-existing local-base-change and diagnostic linter warnings replayed.
All 20 new public declarations use only `propext`, `Classical.choice`, and
`Quot.sound`. All 14 downstream clients passed at default elaboration
settings, including the universal canonical-conormal premise implying
the existing `PlanarVanishing` target. That client constructs the normal
closure internally and takes only the remaining conormal premise and
the two geometric theorem inputs; no separate model-existence premise
is needed.

The 185-module local import graph has no missing imports or cycles. The
focused planar closure is unchanged at 35 modules; the research closure
is 137. The new endpoint's 82-module closure contains no custom-axiom
module. All 178 local documentation-link targets checked exist, and
`git diff --check` passes. The object bench and semantic parity queue now
record the finite-generator and source-finiteness bridges. No manuscript
or PDF was edited in this checkpoint. This and the preceding two
checkpoints remain uncommitted; no push or submission was made.

## Polynomial-source intersection checkpoint (2026-09-20)

The next source-specific comparison is the classical intersection
property, proved internally rather than added as a literature input:
```math
A\cap K=B\qquad\text{inside }L.
```

[SourceIntersection.lean](../../../General/Keller/SourceIntersection.lean)
first reflects divisibility by a prime $p\in B$, using an existing
visible source divisor contracting to $(p)$. UFD factorization and
cancellation handle arbitrary divisors, including zero and units. A
fraction in $K$ that is polynomial on the source then has its
denominator dividing its numerator already in $B$. Neither
characteristic zero nor separability is required for these three
theorems. The targeted build passed all 2915 jobs without warnings or
increased elaboration budgets.

[ConjugateInvariantSource.lean](../../../General/Keller/ConjugateInvariantSource.lean)
applies this comparison to the existing separable marked normal closure.
For each element of the actual fixed algebra, membership in the marked
polynomial source is equivalent to membership in the image of the base
map. No new intersection ring, source copy, or theorem-target predicate
is defined.

This is useful source information, not a vanishing argument:
$E^G\cap\iota(A)=\iota(B)$ does not imply
$E^G\subseteq\iota(A)$. The generator derivative memberships remain
open. The [object-bench audit](OBJECT-BENCH.md#what-the-full-polynomial-source-does-supply-2026-09-20)
records the classical attribution and explains why unit reflection and
separate visible sheets do not furnish the missing regularity assertion.

The actual fixed-algebra application passed its 2928-job targeted build
without warnings or increased elaboration budgets. The combined build of
`CollisionIdeals`, `CollisionIdeals.Planar.Research`,
`CollisionIdeals.Palomar.PaperOne.Solution`, and
`CollisionIdeals.Palomar.PaperTwo.Solution` passed all 3837 jobs; only the
pre-existing local-base-change and diagnostic linter warnings replayed.
All four new public declarations use only `propext`, `Classical.choice`,
and `Quot.sound`. All twelve external clients passed at default budgets
without warnings. The two canonical-closure clients construct the
separability and base-algebra structures internally and express the
conclusion in the ambient normal closure, coercing the public theorem's
fixed-algebra membership result. This avoids redundant instance search
through the concrete nested fixed ring; no mathematical premise or
source theorem was changed.
The 187-module import
graph has no missing imports or cycles. The focused planar closure
remains 35 modules; the research closure is 139. The new leaf's 29-module
closure contains no custom-axiom module. All 187 local documentation-link
targets checked exist, and `git diff --check` passes.

The shared semantic parity table, object bench, and active proof spine
use the existing rings and embeddings throughout. No manuscript, PDF,
archive, focused degree-two theorem, commit, push, or submission was
changed in this checkpoint. Earlier uncommitted changes are preserved.

## Source-regularity characterization checkpoint (2026-09-20)

[ConjugateInvariantCriterion.lean](../../../General/Keller/ConjugateInvariantCriterion.lean)
combines the pointwise source-intersection theorem with the existing
actual target open and boundary. Its three declarations identify:

1. Regularity on the marked source of every element of $E^G$ with
   surjectivity of the canonical map $B\to E^G$.
2. That surjectivity with $\mathfrak b_F=B$.
3. Source regularity directly with empty target boundary.

The reverse boundary implication uses the same injective base map and
the affine spectrum isomorphism; no equality between incompatible Lean
subtypes is asserted. Together with the earlier intersection theorem,
this formalizes $E^G\subseteq A\iff E^G=B\iff\mathfrak b_F=B$
under the established embeddings.

This checkpoint consolidates exact criteria and their existing
consequences. The Galois-descent consequence still takes classical
Keller--Galois rigidity; the conditional finite-boundary vanishing
endpoint still takes `BranchPurityA2` and `AffinePlaneFiniteEtaleRigidity`.
Neither universal descent nor boundary emptiness is proved. The
finite-lattice proposal remains on the bench, and no historical
research objects have been deleted or duplicated.

The same checkpoint adds the complementary marked-closure criterion in
`General.Galois.Descent` and the map-by-map obstruction characterization
in `Planar.Research.Vanishing.GaloisDescent`. For complex planar Keller
maps, at this checkpoint the latter took Ax--Grothendieck and
Keller--Galois rigidity explicitly; the Ax--Grothendieck input is removed
in the later direct-closure checkpoint below. It characterizes vanishing
by normality of the original
extension, or equivalently by surjectivity of the marked embedding into
its normal closure. The field-theoretic fixing-subgroup criterion reuses
the same $H$ as Paper I; it is not an inertia-group assertion.

Verification: the fixed-algebra criterion passed its 2946-job targeted
build; the closure/vanishing additions passed their 2637-job targeted
build. All seven new declarations use only `propext`, `Classical.choice`,
and `Quot.sound`; all 22 external clients passed at default budgets,
including canonical-closure and complementary nonvanishing examples.
The combined build of `CollisionIdeals`, `CollisionIdeals.Planar.Research`,
and both Palomar solution targets passed all 3838 jobs. Only pre-existing
linter warnings replayed.

The 188-module project import graph has no missing imports or cycles;
the focused planar closure remains 35 modules and the research closure
is 141. All 193 checked local documentation paths and 21 anchors resolve.
Paper II now presents these criteria and their distinct classical inputs;
its 14-page PDF rebuilt without TeX warnings and all rendered pages were
visually reviewed. Wang's intersection theorem is cited while its Lean
proof remains internal. Paper I and the manuscript archive are untouched.
`git diff --check` passes. Changes remain uncommitted; no push or submission
was made.

## Direct collision-to-boundary characterization (2026-09-20)

The reverse implication is now intrinsic to the collision construction,
not an application of Ax--Grothendieck. In
[ConjugateInvariantObstruction.lean](../../../General/Keller/ConjugateInvariantObstruction.lean),
vanishing gives $I_R=I_\Delta$. Every Galois collision pair therefore
annihilates the diagonal generators, so all conjugate source coordinates
equal the marked coordinates. Adjoin generation places $E$, and hence
$E^G$, in the marked polynomial source. This first implication needs
neither Keller nor separability. The second applies the existing actual
boundary criterion, with Keller and separability, to give $\mathfrak b_F=B$.

[BoundaryCriterion.lean](BoundaryCriterion.lean) combines this direct
reverse with the existing finite-boundary endpoint. Its central theorem
and two corollaries package

```math
\mathrm{Obs}(F)=0\iff\mathfrak b_F=B
\iff E^G\subseteq\iota(A)
\iff\text{both target-coordinate conormal components vanish}.
```

Only `BranchPurityA2` and `AffinePlaneFiniteEtaleRigidity` are theorem
inputs, and only from boundary emptiness to obstruction vanishing.
There is no Ax--Grothendieck or Keller--Galois rigidity input on this
route. At this checkpoint the separate normal-closure characterization
retained its two-input signature, subsequently simplified below.
No new rings, quotients, or universal-vanishing assumptions
were added. The unused automorphism-based draft created during this
checkpoint was removed; earlier research files were preserved.

Verification: the shared leaf passed its 2947-job targeted build on the
first attempt, with no warnings or increased elaboration budgets. The
combined repository, research, and two Palomar solution build passed all
3840 jobs; only pre-existing linter warnings replayed. All five new
declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
All 14 external clients passed at default settings, including both
directions, the nonvanishing complements, the hypothesis-free shared
source implication, and canonical-closure instantiations.

The 190-module project graph has no missing imports or cycles. The focused
Planar closure remains 35 modules; the research closure is 143. Neither
new leaf reaches a custom-axiom module. All 202 local documentation paths
checked exist, and `git diff --check` passes. Paper II's direct reverse
proof and Lean-status paragraph are synchronized; its 14-page PDF rebuild
has no TeX warnings, and all rendered pages were visually reviewed.
Paper I and the archive remain untouched. No commit, push, or submission
was made; earlier uncommitted changes are preserved.

## Direct normal-closure criterion and exposition checkpoint (2026-09-20)

`General.Galois.CollisionVanishing` now owns the dimension-independent
conjugate-coordinate equality obtained by evaluating the diagonal
generators at a Galois collision pair. It also proves
`polynomialSource_normal_of_obstructionIdeal_eq_bot`, using the existing
marked normal closure and coordinate-descent criterion. Neither Keller,
separability, nor a literature theorem is needed for this shared step.
`General.Keller.ConjugateInvariantObstruction` reuses the coordinate
equality instead of duplicating that proof.

The two per-map planar normal-closure equivalences consequently drop
their former Ax--Grothendieck parameter. Their only literature input is
`ComplexKellerGaloisRigidity 2`, used from normality to vanishing.
The general vanishing-to-automorphism theorem remains unchanged.
The boundary equivalences likewise retain their distinct purity and
finite-etale inputs only in the boundary-to-obstruction direction.
No universal vanishing assertion or replacement object is introduced.

Paper II follows the direct collision proof, reuses its coordinate
equalities in the boundary argument, and shortens the Lean-status
inventory and conclusion. The current semantic table and research
overview record the reduced inputs; earlier checkpoint records above
remain explicitly historical. Paper I and the archive are untouched.

Verification: the three targeted modules passed their 2957-job build
without new warnings. The full repository, research, and both Palomar
solution targets passed all 3841 jobs, replaying only pre-existing linter
warnings. All 33 refreshed external clients passed at default budgets;
all 11 axiom checks report only `propext`, `Classical.choice`, and
`Quot.sound`.

The 191-module local import graph has 474 edges, no missing imports, and
no cycles. The focused Planar closure remains 35 modules; Research is
143. Neither direct-collision nor boundary-criterion leaf reaches a
custom-axiom module; the broad research umbrella retains its pre-existing
assumptions import. All 205 checked local documentation links resolve.
Paper II rebuilt to 13 pages without TeX warnings, and all pages were
visually reviewed. The complete checkpoint is prepared for the authorized
local commit; no push or submission is included.
