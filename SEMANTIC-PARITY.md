# Two-paper object correspondence

The focused release preserves the shared notation of the full repository.
These tables record the cubic and quadratic proof interfaces; it does not identify distinct
affine and generic residual constructions.

| Manuscript object | Lean declaration | Meaning |
|---|---|---|
| $A$ | `SourceRing` | Source polynomial ring. |
| $S$ | `PairRing` | Polynomial ring of pairs. |
| $I_R(F)$ | `collisionIdeal F` | Collision ideal. |
| $I_\Delta$ | `diagonalIdeal` | Diagonal ideal in $S$. |
| $C_F=S/I_R(F)$ | `CollisionRing F` | Collision coordinate ring. |
| $R_F=\mathrm{Spec} C_F$ | `collisionAffineScheme F` | Collision scheme. |
| $\mathrm{Obs}(F)\cong I_\Delta/I_R(F)$ | `obstructionIdeal F` | Ideal cutting out the diagonal inside the collision scheme. |
| $\bar\mu_F:C_F\to A$ | `barMu F`, `collisionDiagonal F` | Diagonal evaluation; its kernel is the obstruction ideal. |
| $B=\mathbb C[F_1,\ldots,F_n]$ | `polynomialMapImageAlgebra F` | Actual coordinate-image algebra. |
| $K=\mathrm{Frac}(B)$, $L=\mathrm{Frac}(A)$ | `PolynomialBaseFunctionField F`, `PolynomialSourceFunctionField` | Base and source function fields. |
| $K\otimes_B C_F\simeq_K L\otimes_K L$ | `polynomialGenericCollisionEquiv` | Generic collision bridge; the positive-degree endpoint derives its surjectivity input. |
| $L\otimes_K L\simeq_L L\times D_\alpha$ | `primitiveTensorDecomposition` | Marked-root decomposition; multiplication is first projection. |
| $D_\alpha$ | `CubicResidualAlgebra` | Quadratic generic residual algebra under the cubic-degree hypothesis. |
| $N/K$ | `NormalClosureData`, `canonicalNormalClosureData` | Marked normal closure and its canonical construction. |
| $D_\alpha\simeq_L N$ | `cubicResidualEquivNormalClosureOfNotNormal` | Residual-field identification in the nonnormal cubic branch. |
| $G$, $H$ | `NormalClosureData.galoisGroup`, `NormalClosureData.intermediateFixingSubgroup` | Normal-closure Galois group and subgroup fixing the marked source field. |
| $G\cong S_3$ | `NormalClosureData.galoisGroupEquivPermFinThree` | Cubic normal-closure Galois-group identification. |
| Keller--Galois rigidity | `ComplexKellerGaloisRigidity 3` | Explicit literature input, neither an installed axiom nor a proved theorem here. |

Ambient dimension three and generic field degree three are separate
conditions. Generic degree three implies nonautomorphy, not the Keller
condition. Their precise counterexample equivalence is
`complexThree_counterexample_iff_keller_of_finrank_eq_three`.

The canonical endpoint `complexThreeGenericDegreeThreeS3Collision`
constructs the closure and other cubic data internally. The Palomar
declaration `CollisionIdeals.Palomar.PaperOne.genericDegreeThreeS3Collision`
instead accepts a supplied normal closure and derives its finiteness from cubic degree. It proves the Keller
specialization of manuscript Theorem 3.3.

The affine first-colon residual ring, the quadratic generic residual algebra,
and the intrinsic generic annihilator quotient are distinct objects. The
three cosets $G/H$ index embeddings of one fixed cubic field, not a parameter
space of polynomial maps.

The [full source-revision parity table](https://github.com/what-social-construct/jacobian-collision-geometry/blob/b11f8a7691550887360163cecfffec6e59b5afd0/SEMANTIC-PARITY.md)
also records general modules and statements outside this focused proof
closure. The full cubic split/field/connectedness equivalence is packaged by
`cubicResidual_tfae` in `ComplexThree.Cubic.ResidualCriteria`; the split
normal branch is constructed in `ComplexThree.Cubic.NormalBranch`.

## Paper II: focused planar degree two

The symbols $A,S,I_R,I_\Delta,C_F,R_F,\mathrm{Obs}(F),B,K,L$
have exactly the shared meanings above.

| Manuscript object or claim | Lean declaration | Scope |
|---|---|---|
| $\delta_F$ | `Planar.ExplicitSecant.determinant F` | Canonical ordered divided-difference determinant. |
| $p_F=1-c^{-1}q_F(\delta_F)$ | `Planar.ExplicitSecant.collisionProjector F c hc` | Off-diagonal idempotent generating the obstruction; not the quotient map $q_F$. |
| $e_F=1-p_F$ | Complement of the same projector | Diagonal idempotent; no duplicate construction. |
| $[L:K]=2\Rightarrow\mathrm{Obs}(F)\ne0$ | `planarGenericDegreeTwo_obstructionIdeal_ne_bot` | Independent of the Keller condition. |
| No planar Keller map has generic degree two | `quadraticPlanarCollisionRigidity` | Uses the explicit Keller--Galois rigidity input in dimension two. |

The [Paper II Solution](CollisionIdeals/Palomar/PaperTwo/Solution.lean) adapts
the existing projector and quadratic modules. Its independence from the
broader boundary program is part of the statement scope, not an omitted
hypothesis. It does not prove universal planar obstruction vanishing.
