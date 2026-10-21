# Reading the Lean code

Read the [proof guide](Proof.md) first for the argument. This page then tells you where each step is implemented and what the supporting files contribute. All source links below are relative to [`RequestProject/Yau/`](../RequestProject/Yau/), except the entry point.

The library contains the entry point and 59 modules. Its mathematical definitions use the same objects as the paper: the Jacobian ideal, the Milnor algebra, weighted homogeneous components, and homogeneous derivations. Some Lean declaration identifiers contain Chinese characters. They are retained so that the existing declarations, imports, and proofs remain unchanged; all explanatory comments are in English.

## Main theorem

Start at [`Final/ThreeNewLocal.lean`](../RequestProject/Yau/Final/ThreeNewLocal.lean). The exact declaration for the main theorem is **`Yau.«Yau猜想_第三版»`**. It takes the textbook statement as the explicit argument

```lean
hA : ∀ m, 2 ≤ m → Yau.«AGV定理14_8For» m
```

The remaining arguments say that the weights are positive, `f` is weighted homogeneous, the origin is an isolated critical point, and `δ` is a derivation of degree `k < 0`. The conclusion is `δ = 0`.

To follow how this theorem is obtained, use this reading order:

1. [`Basic/Basic.lean`](../RequestProject/Yau/Basic/Basic.lean): identify the algebra and grading in the statement.
2. [`Final/AGV148.lean`](../RequestProject/Yau/Final/AGV148.lean): read the precise textbook hypothesis.
3. [`Final/ThreeNewLocal.lean`](../RequestProject/Yau/Final/ThreeNewLocal.lean): see how it implies the local Lemma 3.4.
4. [`Final/ThreeNew.lean`](../RequestProject/Yau/Final/ThreeNew.lean): follow the application to the square deformation and Corollary 3.5.
5. [`Sec3_Radical/Radical.lean`](../RequestProject/Yau/Sec3_Radical/Radical.lean): see Theorem 3.6 exclude the radical element.
6. [`Sec4_Proof/Core.lean`](../RequestProject/Yau/Sec4_Proof/Core.lean) and [`MainTheorem.lean`](../RequestProject/Yau/Sec4_Proof/MainTheorem.lean): follow the contradiction and the splitting induction.

The rest of this page follows the paper's order rather than the order of imports.

## Introduction: definitions and analytic language

The proof moves between polynomial calculations and analytic local algebras. These files define both settings and establish their basic operations.

| File | Role in the proof |
| --- | --- |
| [Basic/Basic.lean](../RequestProject/Yau/Basic/Basic.lean) | Defines `Poly`, `jacobianIdeal`, `MilnorAlgebra`, `gradedPiece`, `IsDerivationOfDegree`, and `partialIdeal`. Proves weighted-scaling and homogeneous-coefficient facts used throughout the argument. |
| [Basic/PolyDeriv.lean](../RequestProject/Yau/Basic/PolyDeriv.lean) | Constructs `polyDer`, the derivation with coefficients `h_i`. `IsNegHomog` records their degrees. The commutator and iteration estimates give the derivative calculations and local nilpotence needed in Sections 2 and 4. |
| [Basic/PolyCalculus.lean](../RequestProject/Yau/Basic/PolyCalculus.lean) | Identifies formal polynomial partial derivatives with derivatives of polynomial functions. Also proves that a polynomial vanishing on a neighborhood is zero. |
| [Basic/Setup.lean](../RequestProject/Yau/Basic/Setup.lean) | Collects the hypotheses after quadratic-variable removal in `Setup`. Defines `SquareDeformationProperty`, the conclusion of Corollary 3.5 used by the core proof. |
| [Basic/Convergent.lean](../RequestProject/Yau/Basic/Convergent.lean) | Defines `ConvSeries`, the convergent power series ring, through coefficient bounds, and the inclusion `polyToConv` from polynomials. |
| [Analytic/Expansion.lean](../RequestProject/Yau/Analytic/Expansion.lean) | Builds convergent Taylor series from analytic functions and proves their uniqueness, algebraic operations, and recovery from sum functions. This connects the function and power-series formulations. |
| [Analytic/LocalMilnor.lean](../RequestProject/Yau/Analytic/LocalMilnor.lean) | Defines `localJacobianIdeal` and `localMilnorNumber` at arbitrary points. Proves invariance under analytic coordinate changes and agreement with the polynomial formulation at zero. |

## Section 2: remove quadratic variables and select D

The first six files below implement weight-preserving substitutions and the removal of variables. The last file makes the minimum-degree choice that gives $`D^2f=0`$.

| File | Role in the proof |
| --- | --- |
| [Sec2_Splitting/Elementary.lean](../RequestProject/Yau/Sec2_Splitting/Elementary.lean) | Setting a variable to zero, independence of a variable, division by a coordinate, and one-variable quadratic Taylor expansions. These are the elementary operations used in the splitting steps. |
| [Sec2_Splitting/Subst.lean](../RequestProject/Yau/Sec2_Splitting/Subst.lean) | The chain rule for polynomial substitutions, transformation of the Jacobian ideal, and preservation of weighted homogeneity. |
| [Sec2_Splitting/Transfer.lean](../RequestProject/Yau/Sec2_Splitting/Transfer.lean) | Constructs induced Milnor-algebra isomorphisms and conjugates derivations through them, preserving the no-negative-derivation conclusion. |
| [Sec2_Splitting/Reduction.lean](../RequestProject/Yau/Sec2_Splitting/Reduction.lean) | Elementary automorphisms of the form `x_v ↦ a x_v + g` and maps to the polynomial ring with fewer variables. |
| [Sec2_Splitting/Steps.lean](../RequestProject/Yau/Sec2_Splitting/Steps.lean) | Implements the two concrete coordinate-change cases of Lemma 2.1: a square term and a paired-variable term. Isolatedness supplies the necessary nonzero coefficients. |
| [Sec2_Splitting/Splitting.lean](../RequestProject/Yau/Sec2_Splitting/Splitting.lean) | Removes a quadratic variable or pair and relates the resulting Milnor algebras. These steps are assembled by the induction in `Sec4_Proof/MainTheorem.lean`. |
| [Sec2_Splitting/Minimum.lean](../RequestProject/Yau/Sec2_Splitting/Minimum.lean) | Defines `InV`, proves its stability, and implements `Setup.minimum`, selecting the derivation of Proposition 2.4. |

## Section 3: the Hessian, square deformation, and radical theorem

These modules provide the two sides of the small-degree contradiction and the direct large-degree argument. Lemma 3.4, which connects the square deformation to ideal membership, is listed separately just below.

| File | Role in the proof |
| --- | --- |
| [Sec3_Radical/Taylor.lean](../RequestProject/Yau/Sec3_Radical/Taylor.lean) | A second-order Taylor expansion along a direction when the corresponding third derivatives vanish. |
| [Sec3_Radical/LowestOrder.lean](../RequestProject/Yau/Sec3_Radical/LowestOrder.lean) | Extracts a nonzero vector from the lowest-order part of a polynomial quadratic identity, supporting the Hessian argument. |
| [Sec3_Radical/Hessian.lean](../RequestProject/Yau/Sec3_Radical/Hessian.lean) | Proves nondegeneracy of the heavy-variable Hessian block in the polynomial instance of Lemma 3.1 used in the proof. |
| [Sec3_Radical/SquareDeformation.lean](../RequestProject/Yau/Sec3_Radical/SquareDeformation.lean) | Proves that `f+t a²` and `f` have the same Jacobian radical under the hypotheses of Lemma 3.3. Also supplies the homogeneous-component argument used to conclude `q ∈ J`. |
| [Sec3_Radical/MilnorConstancy.lean](../RequestProject/Yau/Sec3_Radical/MilnorConstancy.lean) | Uses homogenization and regular sequences to compute polynomial quotient dimensions under lower-degree perturbations. Combines this with the radical calculation to prove the local Milnor-number constancy required for the square deformation. |
| [Sec3_Radical/Radical.lean](../RequestProject/Yau/Sec3_Radical/Radical.lean) | Proves Lemma 3.2, the large-degree radical case, and Theorem 3.6 using the square-deformation property in the small-degree range. |

### Lemma 3.4 and the textbook input

The formalization proves the first-order consequence through a monomial-basis deformation, invariance of the local Milnor number, and a right-equivalence construction. The following files are its main components.

| File | Role in the proof |
| --- | --- |
| [Final/AGV148.lean](../RequestProject/Yau/Final/AGV148.lean) | Defines `Yau.«AGV定理14_8For»`, the neighborhood form of AGV, Theorem 14.8. Relates the full coordinate description to the stratum inclusion and records the direct zero- and one-variable cases. |
| [Final/ThreeNew.lean](../RequestProject/Yau/Final/ThreeNew.lean) | States the local and global forms of Lemma 3.4, proves the zero- and one-variable cases, and applies the lemma to obtain the square-deformation input of Corollary 3.5. |
| [Final/ThreeNewLocal.lean](../RequestProject/Yau/Final/ThreeNewLocal.lean) | Connects local Milnor-number conditions to the global critical-point formulation, derives Lemma 3.4 from AGV, and assembles the main theorem. Also gives an equivalent polynomial-only formulation of Lemma 3.4. |
| [Sec3_Radical/Corollary35.lean](../RequestProject/Yau/Sec3_Radical/Corollary35.lean) | Defines a monomial basis and its miniversal deformation. Proves the parameter-vanishing, differentiation, and homogeneous-component steps for a general first-order consequence. Its general-versality argument is separate from the specialized construction used by the main theorem. |
| [Versality/Tools.lean](../RequestProject/Yau/Versality/Tools.lean) | Analytic local inverses, algebraic Taylor remainders, and nilpotence bounds used in the construction. |
| [Versality/Jet.lean](../RequestProject/Yau/Versality/Jet.lean) | Solves the finite-jet problem using an analytic coefficient map whose differential is the identity. Produces the parameter curve and its first-order relation. |
| [Versality/Determinacy.lean](../RequestProject/Yau/Versality/Determinacy.lean) | Proves a Tougeron finite-determinacy statement using the analytic inverse function theorem. Converts equality of sufficiently large jets into right equivalence. |
| [Versality/FixedPoint.lean](../RequestProject/Yau/Versality/FixedPoint.lean) | Combines the jet and determinacy arguments for the fixed-origin families needed here. Derives the first-order Jacobian-ideal conclusion from the stratum hypothesis. |

### Supporting modules for the stratum's reverse inclusion

The main argument uses $`\Sigma_\mu\subseteq E`$ from the textbook. The library also proves $`E\subseteq\Sigma_\mu`$ directly. The following modules establish that inclusion and the resulting equivalence of the two hypothesis formulations.

| File | Role |
| --- | --- |
| [Sec3_Radical/WeightFiltration.lean](../RequestProject/Yau/Sec3_Radical/WeightFiltration.lean) | Defines ideals of terms above a weight threshold and proves component, product, derivative, and coordinate-power estimates. |
| [Sec3_Radical/LemmaC1.lean](../RequestProject/Yau/Sec3_Radical/LemmaC1.lean) | Uses Koszul syzygy reduction and approximation to compare truncated Jacobian quotients under higher-weight perturbations. |
| [Sec3_Radical/LemmaC1Local.lean](../RequestProject/Yau/Sec3_Radical/LemmaC1Local.lean) | Turns that comparison into local isolatedness and equality of analytic Milnor numbers. |
| [Sec3_Radical/HilbertFunction.lean](../RequestProject/Yau/Sec3_Radical/HilbertFunction.lean) | Computes homogeneous quotient dimensions and proves that isolated weighted homogeneous polynomials of the same weights and degree have equal Milnor-algebra dimensions. |
| [Sec3_Radical/Openness.lean](../RequestProject/Yau/Sec3_Radical/Openness.lean) | Proves persistence of isolatedness under small same-degree homogeneous perturbations through openness of finite-dimensional surjectivity. |
| [Sec3_Radical/VarchenkoInclusion.lean](../RequestProject/Yau/Sec3_Radical/VarchenkoInclusion.lean) | Combines the preceding results to prove the coordinate-subspace inclusion in the stratum for every number of variables. |
| [Sec3_Radical/VarchenkoOneVar.lean](../RequestProject/Yau/Sec3_Radical/VarchenkoOneVar.lean) | Identifies a one-variable local Milnor number with root multiplicity and proves the stratum theorem directly for zero and one variable. |

## Section 4: the orbit argument and the contradiction

| File | Role in the proof |
| --- | --- |
| [Sec4_Proof/Orbit.lean](../RequestProject/Yau/Sec4_Proof/Orbit.lean) | Implements the orbit polynomials, their weighted degeneration, and the radical-membership conclusion of the instance of Lemma 4.1 used here. |
| [Sec4_Proof/Quotient.lean](../RequestProject/Yau/Sec4_Proof/Quotient.lean) | Implements Lemma 4.3: preservation of `I_r` and the calculations making `D²f_i` vanish modulo that ideal. |
| [Sec4_Proof/Core.lean](../RequestProject/Yau/Sec4_Proof/Core.lean) | Chooses the least-weight variable moved by `D`. Its coefficient contradicts Theorem 3.6. This is the proof after quadratic-variable removal. |
| [Sec4_Proof/MainTheorem.lean](../RequestProject/Yau/Sec4_Proof/MainTheorem.lean) | Inducts over the splitting steps and restores the general polynomial statement from the core proof. |
| [Final/MainResult.lean](../RequestProject/Yau/Final/MainResult.lean) | Connects the first-order and square-deformation inputs to the core theorem and packages the Milnor- and moduli-algebra conclusions. |
| [Final/Rational.lean](../RequestProject/Yau/Final/Rational.lean) | Clears denominators of rational weights and transports the grading and derivation degree. |

## Appendices A–B: local algebras and derivations

| File | Role in the proof |
| --- | --- |
| [Appendix/Isolated.lean](../RequestProject/Yau/Appendix/Isolated.lean) | Uses weighted scaling and the Nullstellensatz to connect isolated critical points, the radical of `J`, and finite-dimensional polynomial Milnor algebras. |
| [Appendix/AnalyticMilnor.lean](../RequestProject/Yau/Appendix/AnalyticMilnor.lean) | Proves the polynomial-to-analytic quotient comparison for ideals containing coordinate powers, by finite Taylor truncation. |
| [Appendix/AnalyticYau.lean](../RequestProject/Yau/Appendix/AnalyticYau.lean) | Specializes the comparison to the Jacobian ideal, giving Lemma A.1 for the Milnor algebra. |
| [Appendix/Syzygy.lean](../RequestProject/Yau/Appendix/Syzygy.lean) | Proves regularity of the full gradient in any order and the low-degree syzygy and uniqueness statements of Lemma B.1. |
| [Appendix/EulerModuli.lean](../RequestProject/Yau/Appendix/EulerModuli.lean) | Euler's identity, the Milnor–Tjurina identification, preservation of the maximal ideal under derivations (Lemma B.2), and polynomiality of weighted homogeneous power series. |
| [Appendix/Lift.lean](../RequestProject/Yau/Appendix/Lift.lean) | Constructs the homogeneous polynomial lift of a negative-degree derivation, used in Lemma B.3 and Section 2. |

The regular-sequence arguments use the following algebraic tools.

| File | Role |
| --- | --- |
| [CommAlg/Depth.lean](../RequestProject/Yau/CommAlg/Depth.lean) | Depth and regular elements over Noetherian local rings, culminating in the Cohen–Macaulay criterion used by the project. |
| [CommAlg/RegularSequence.lean](../RequestProject/Yau/CommAlg/RegularSequence.lean) | Localizes at the origin and uses the grading to prove that homogeneous systems of parameters form regular sequences in the polynomial ring. |
| [CommAlg/Koszul.lean](../RequestProject/Yau/CommAlg/Koszul.lean) | First syzygies of regular sequences are Koszul relations; also controls their homogeneous degrees. |

## Additional consequences

These modules give direct proofs in special cases and criteria that can replace the stratum input in those cases. They are included with the library; the reader can follow the general paper proof above independently of them.

| File | Result or criterion |
| --- | --- |
| [LowDim/LowDim.lean](../RequestProject/Yau/LowDim/LowDim.lean) | The radical statement with at most one heavy variable, and the induction with a bound on the number of variables. |
| [LowDim/ThreeVar.lean](../RequestProject/Yau/LowDim/ThreeVar.lean) | The local Euler argument with one light and two heavy variables, giving Yau's conjecture for at most three variables. |
| [LowDim/Homogeneous.lean](../RequestProject/Yau/LowDim/Homogeneous.lean) | The direct proof when all weights are equal. |
| [LowDim/Restriction.lean](../RequestProject/Yau/LowDim/Restriction.lean) | The radical statement from an isolated heavy-coordinate restriction; includes the Brieskorn–Pham case. |
| [LowDim/SmallWeights.lean](../RequestProject/Yau/LowDim/SmallWeights.lean) | A condition on the weights ensuring that each degree is covered by an elementary radical argument. |
| [LowDim/QuadraticHeavy.lean](../RequestProject/Yau/LowDim/QuadraticHeavy.lean) | A quadratic-heavy-variable criterion, combined with the restriction and single-heavy-variable criteria. |
| [LowDim/LocalCriterion.lean](../RequestProject/Yau/LowDim/LocalCriterion.lean) | Local-to-global membership of squares in selected partial-derivative ideals, and a local Euler criterion with one light variable. |
| [LowDim/LocalLevels.lean](../RequestProject/Yau/LowDim/LocalLevels.lean) | Combines the local criteria with the elementary criteria degree by degree. |
| [LowDim/ThomSebastiani.lean](../RequestProject/Yau/LowDim/ThomSebastiani.lean) | Preserves local Euler relations under sums in disjoint variable sets, giving a Thom–Sebastiani criterion. |

Finally, [`RequestProject/Yau.lean`](../RequestProject/Yau.lean) imports all modules and exposes the collected results.
