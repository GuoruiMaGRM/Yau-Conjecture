# A guide to the proof and its formalization

This guide follows the sections and numbering of the [accompanying paper](../papers/Yau-Conjecture.pdf). Start with the mathematical argument in each section, then follow the linked Lean files for its implementation. The complete chain to the main theorem uses AGV, Theorem 14.8 as the cited textbook hypothesis; its precise role is explained below and in the [textbook guide](AGV.md).

## 1. Introduction: the algebra and the grading

The paper starts with an isolated weighted homogeneous hypersurface singularity. Positive weights imply that its defining convergent power series is a polynomial: only finitely many monomials can have a fixed weight. Clearing denominators makes the positive rational weights integral without changing the sign of a derivation degree.

The polynomial calculations take place in

```math
S=\mathbb C[x_1,\ldots,x_n],\quad \mathfrak m=(x_1,\ldots,x_n),\quad f_i=\partial_if,\quad J=(f_1,\ldots,f_n),\quad A=S/J.
```

The space $`S_r`$ consists of polynomials homogeneous of weighted degree $`r`$. The analytic Milnor algebra is $`M_f=\mathcal O/J\mathcal O`$, where $`\mathcal O=\mathbb C\lbrace x\rbrace`$. Lemma A.1 identifies $`A`$ with $`M_f`$. Euler's identity,

```math
df=\sum_iw_ix_if_i,
```

gives $`f\in J`$ and hence identifies the moduli algebra $`T_f`$ with $`M_f`$. It is therefore enough to rule out negative-degree derivations on the graded polynomial quotient $`A`$.

**In Lean.** [`Basic/Basic.lean`](../RequestProject/Yau/Basic/Basic.lean) defines `jacobianIdeal`, `MilnorAlgebra`, `gradedPiece`, and `IsDerivationOfDegree`. [`Basic/Convergent.lean`](../RequestProject/Yau/Basic/Convergent.lean) defines the convergent power series ring. [`Appendix/AnalyticYau.lean`](../RequestProject/Yau/Appendix/AnalyticYau.lean) supplies the algebra comparison, and [`Appendix/EulerModuli.lean`](../RequestProject/Yau/Appendix/EulerModuli.lean) supplies Euler's identity and the moduli-algebra identification. [`Final/Rational.lean`](../RequestProject/Yau/Final/Rational.lean) formalizes the clearing of denominators.

## 2. Removal of quadratic variables and the choice of D

### Lemma 2.1: simplify f without changing its graded Milnor algebra

The coordinate changes preserve weights. Their Jacobian matrices are invertible, so the chain rule identifies the gradient ideals and gives graded isomorphisms of Milnor algebras.

A variable of weight greater than $`d/2`$ can occur only linearly. Isolatedness supplies a nonzero linear term in its coefficient, allowing a pair of variables to be split off. Variables of weight $`d/2`$ form a nondegenerate quadratic part, which is removed by completing the square. Repeating this leaves either the algebra $`\mathbb C`$ or a polynomial satisfying

```math
f\in\mathfrak m^3,\qquad d\gt2W,\qquad W=\max_iw_i.
```

The origin is still an isolated critical point. This is the standing setup for Sections 3–4. In particular, every partial derivative has degree at least $`d-W\gt W`$.

**In Lean.** [`Sec2_Splitting/Elementary.lean`](../RequestProject/Yau/Sec2_Splitting/Elementary.lean), [`Reduction.lean`](../RequestProject/Yau/Sec2_Splitting/Reduction.lean), [`Steps.lean`](../RequestProject/Yau/Sec2_Splitting/Steps.lean), and [`Splitting.lean`](../RequestProject/Yau/Sec2_Splitting/Splitting.lean) implement the substitutions and variable deletion. [`Subst.lean`](../RequestProject/Yau/Sec2_Splitting/Subst.lean) proves the chain-rule and homogeneity properties. [`Transfer.lean`](../RequestProject/Yau/Sec2_Splitting/Transfer.lean) transports derivations through the graded algebra isomorphisms. The induction that applies these steps is in [`Sec4_Proof/MainTheorem.lean`](../RequestProject/Yau/Sec4_Proof/MainTheorem.lean).

### Lemmas 2.2–2.3 and Proposition 2.4: choose the right derivation

Suppose that $`A`$ has a nonzero homogeneous derivation of negative degree. Appendix B lifts it to a polynomial derivation preserving $`J`$. The paper then considers

```math
\mathcal V=\lbrace g\in J:\partial_ig\in J\text{ for every }i\rbrace.
```

Lemma 2.2 relates homogeneous elements of this space to negative-degree derivations through $`D\mapsto Df`$. Lemma 2.3 shows that a derivation preserving $`J`$ also preserves $`\mathcal V`$. Choose a nonzero element of $`\mathcal V`$ of least positive degree. The associated derivation lowers degree, so its action on this element must vanish. Proposition 2.4 therefore produces

```math
D=\sum_ih_i\partial_i,\qquad \deg D=-s\lt0,\qquad D(J)\subseteq J,\qquad 0\ne Df,\qquad D^2f=0.
```

Every $`h_i`$ belongs to $`\mathfrak m`$. Repeated application of $`D`$ eventually lowers any polynomial below degree zero, so $`D`$ is locally nilpotent. These are precisely the properties needed for the orbit argument in Section 4.

**In Lean.** [`Appendix/Lift.lean`](../RequestProject/Yau/Appendix/Lift.lean) constructs the lift; [`Appendix/Syzygy.lean`](../RequestProject/Yau/Appendix/Syzygy.lean) gives the low-degree uniqueness used in the argument. [`Sec2_Splitting/Minimum.lean`](../RequestProject/Yau/Sec2_Splitting/Minimum.lean) implements the space `InV` and the minimization argument `Setup.minimum`. [`Basic/PolyDeriv.lean`](../RequestProject/Yau/Basic/PolyDeriv.lean) supplies the derivation, degree estimates, and local nilpotence.

## 3. Radicals of ideals generated by selected partial derivatives

For a positive integer $`r`$, split the variables into those of weight at most $`r`$ and those of weight greater than $`r`$. The paper denotes them by $`u`$ and $`y`$, respectively, and sets

```math
I_r=(f_i:w_i\gt r)=(f_y).
```

A polynomial of degree $`r`$ can depend only on $`u`$. The goal is Theorem 3.6: $`\sqrt{I_r}\cap S_r=\lbrace0\rbrace`$. Its proof has two ranges, and the small-degree range is where the textbook theorem enters.

### Lemmas 3.1–3.2: a small-degree square cannot belong to J

Lemma 3.1 treats a polynomial, or analytic germ, that is at most quadratic in a selected group of variables. Isolatedness forces the corresponding Hessian determinant to be nonzero. Consequently a linear combination of the selected partial derivatives, with coefficients independent of those variables, cannot itself be independent of them unless every coefficient vanishes.

Lemma 3.2 applies this to a nonzero $`a\in S_r`$ with $`0\lt3r\lt d`$. If $`a^2\in J`$, taking homogeneous coefficients gives

```math
a^2=\sum_ik_if_i,\qquad k_i\in S_{2r-d+w_i}.
```

Only variables with $`w_i\ge d-2r`$ can contribute. These weights exceed both $`r`$ and $`d/3`$, so $`a`$ and the coefficients are independent of those variables, while $`f`$ is at most quadratic in them. Lemma 3.1 forces every coefficient to vanish, contradicting $`a\ne0`$. Thus $`a^2\notin J`$.

**In Lean.** [`Hessian.lean`](../RequestProject/Yau/Sec3_Radical/Hessian.lean), together with [`Taylor.lean`](../RequestProject/Yau/Sec3_Radical/Taylor.lean) and [`LowestOrder.lean`](../RequestProject/Yau/Sec3_Radical/LowestOrder.lean), proves the Hessian result in the polynomial setting used here. [`Radical.lean`](../RequestProject/Yau/Sec3_Radical/Radical.lean) proves the exclusion of squares and later assembles the two ranges of Theorem 3.6.

### Lemma 3.3: the square deformation has constant Milnor number

Suppose $`a=a(u)\in\sqrt{(f_y)}`$. The paper applies Lemma 3.3 to

```math
f_t=f+ta^2.
```

Its critical point remains isolated at the origin, its critical value is zero, and its local Milnor number is constant. The paper proves this for analytic germs by working in $`\mathcal O/(f_y)`$: the class of $`a`$ is nilpotent, and the parameter ideals for the remaining derivatives have equal multiplicities and lengths.

The Lean implementation proves the weighted homogeneous polynomial instance needed by Corollary 3.5. It separates two tasks. First, a radical calculation shows that the square deformation has the same critical-point set. Second, homogenization and regular sequences show that a lower-degree perturbation preserves the dimension of the polynomial Jacobian quotient. Because the origin is the only critical point in this application, the comparison with the analytic local algebra identifies this dimension with the local Milnor number.

This gives the same input used by the next step, without requiring a formalization of the general analytic multiplicity argument.

**In Lean.** [`SquareDeformation.lean`](../RequestProject/Yau/Sec3_Radical/SquareDeformation.lean) proves the equality of radicals. [`MilnorConstancy.lean`](../RequestProject/Yau/Sec3_Radical/MilnorConstancy.lean) proves the dimension and local Milnor-number conclusions and checks the square family's hypotheses. [`CommAlg/`](../RequestProject/Yau/CommAlg/) supplies the regular-sequence tools.

### Lemma 3.4: extract the first-order consequence of AGV, Theorem 14.8

Let $`q\in S_e`$ with $`e\lt d`$. Assume that, for every sufficiently small $`t`$, the family $`f+tq`$ has an isolated critical point at the origin, value zero there, and local Milnor number $`\mu(f,0)`$. Lemma 3.4 concludes that $`q\in J`$.

For one variable, the paper compares the multiplicities of the zero of the derivative. A nonzero lower-degree monomial would reduce the Milnor number. This direct argument is formalized.

For more variables, choose homogeneous monomial representatives of a basis of $`M_f`$, including $`\varphi_0=1`$, and write

```math
F_s(x)=f(x)+\sum_{j=0}^{\mu-1}s_j\varphi_j(x),\qquad e_j=\deg\varphi_j,\qquad \nu_j=1-\frac{e_j}{d}.
```

The parameter weight $`\nu_j`$ is positive exactly when $`e_j\lt d`$. Let $`\Sigma_\mu`$ be the reduced analytic germ of parameters for which $`F_s`$ has a nearby critical point of value zero and Milnor number $`\mu`$. AGV, Theorem 14.8 gives

```math
\Sigma_\mu=\lbrace s:s_j=0\text{ whenever }e_j\lt d\rbrace.
```

The critical point in this statement is allowed to move. Analytic versality writes the linear family as a right equivalence of functions,

```math
f+tq=F_{\gamma(t)}\circ\Phi_t,\qquad \gamma(0)=0,\qquad \Phi_0=\mathrm{id}.
```

The image $`p(t)=\Phi_t(0)`$ has the required critical value and local Milnor number. Hence $`\gamma(t)\in\Sigma_\mu`$, and all coordinates $`\gamma_j(t)`$ with $`e_j\lt d`$ vanish. Differentiating at zero gives

```math
q=\sum_iv_if_i+\sum_{e_j\ge d}\gamma'_j(0)\varphi_j,\qquad v_i=\partial_t\Phi_i(x,0).
```

Take the weighted homogeneous component of degree $`e`$. The second sum has no component in that degree, leaving

```math
q=\sum_i(v_i)_{e-d+w_i}f_i\in J.
```

Positive weights make each coefficient here a polynomial. This is the precise point at which the textbook stratum theorem yields the polynomial ideal membership needed later.

**In Lean.** [`Final/AGV148.lean`](../RequestProject/Yau/Final/AGV148.lean) records the textbook statement as the hypothesis. [`Final/ThreeNew.lean`](../RequestProject/Yau/Final/ThreeNew.lean) states Lemma 3.4 and proves its zero- and one-variable cases. [`Versality/FixedPoint.lean`](../RequestProject/Yau/Versality/FixedPoint.lean) proves the required versality and first-order relation using finite jets and finite determinacy. [`Analytic/LocalMilnor.lean`](../RequestProject/Yau/Analytic/LocalMilnor.lean) proves invariance under the analytic coordinate changes.

The paper states Lemma 3.4 with local conditions at zero. The formal construction uses a global critical-point condition as an intermediate step. [`Final/ThreeNewLocal.lean`](../RequestProject/Yau/Final/ThreeNewLocal.lean) connects them: for a homogeneous lower-degree perturbation, equality of the local Milnor number with the full polynomial quotient dimension rules out another critical point. It then derives the paper's local statement from AGV's theorem. General versality is therefore not an additional hypothesis of the main theorem.

### Corollary 3.5 and Theorem 3.6: finish the radical argument

If $`a\in S_r\cap\sqrt{I_r}`$ and $`0\lt3r\lt d`$, then $`a`$ depends only on the light variables. Lemma 3.3 applies to $`f+ta^2`$. Since $`\deg a^2=2r\lt d`$, Lemma 3.4 gives $`a^2\in J`$. This is Corollary 3.5. Lemma 3.2 gives the opposite conclusion for nonzero $`a`$, so the small-degree range of Theorem 3.6 follows.

For $`3r\ge d`$, every heavy variable has weight greater than $`d/3`$, and $`f`$ is at most quadratic in those variables:

```math
f(u,y)=\tfrac12y^TH(u)y+L(u)^Ty+c(u).
```

Lemma 3.1 makes $`H`$ invertible over $`K=\mathbb C(u)`$. The equations $`f_y=0`$ therefore give a proper ideal in $`K[y]`$, with quotient isomorphic to $`K`$. But a nonzero $`a(u)\in\sqrt{(f_y)}`$ would become a unit in $`K`$, forcing that ideal to contain a unit. This contradiction proves the large-degree range.

Thus, for every positive integer $`r`$,

```math
\sqrt{I_r}\cap S_r=\lbrace0\rbrace.
```

**In Lean.** The square-family application is connected in [`Final/ThreeNew.lean`](../RequestProject/Yau/Final/ThreeNew.lean) and [`Final/MainResult.lean`](../RequestProject/Yau/Final/MainResult.lean). [`Basic/Setup.lean`](../RequestProject/Yau/Basic/Setup.lean) names this input `SquareDeformationProperty`. [`Sec3_Radical/Radical.lean`](../RequestProject/Yau/Sec3_Radical/Radical.lean) combines it with the Hessian argument to prove Theorem 3.6.

## 4. Proof of the main theorem

### Lemma 4.1: degenerate an additive orbit

A locally nilpotent derivation defines an additive-group action by $`\exp(tD)`$. If the action on the reduced quotient were nontrivial, one of its coordinate polynomials $`P_j(t)`$ would be nonconstant. The paper balances its ordinary degree against the variable weight by choosing

```math
\alpha=\min_{P_j\text{ nonconstant}}\frac{w_j}{\deg_tP_j}=\frac{a}{b},\qquad \gamma_j(\zeta)=\zeta^{bw_j}P_j(\zeta^{-a}).
```

Every $`\gamma_j`$ is a polynomial, and at least one has nonzero value at zero. The equations on which the derivation acts at most affinely have degree greater than $`W`$, so they all vanish at the limiting point $`\gamma(0)`$. Finite dimensionality of their graded quotient forces every coordinate of that point to vanish. This is the contradiction.

**In Lean.** [`Sec4_Proof/Orbit.lean`](../RequestProject/Yau/Sec4_Proof/Orbit.lean) implements the instance of Lemma 4.1 used here directly with polynomial derivations and ideals. Its conclusion is that every coefficient $`D(x_j)`$ belongs to the relevant radical. Thus the implementation reaches the needed reduced-quotient conclusion without constructing a general scheme-theoretic group action.

### Lemma 4.3: apply the orbit argument modulo I_r

Assume $`h_j=0`$ for $`w_j\le r`$. Homogeneity and $`D(J)\subseteq J`$ show that $`D(I_r)\subseteq I_r`$. Differentiating $`D^2f=0`$ gives $`D^2f_i\in I_r`$ for every $`i`$. The remaining partial derivatives have degrees at least $`d-W\gt W`$, and quotienting by all of them gives $`S/J`$, which is finite dimensional. Lemma 4.1 therefore forces the induced derivation on $`(S/I_r)_{\mathrm{red}}`$ to vanish.

**In Lean.** [`Sec4_Proof/Quotient.lean`](../RequestProject/Yau/Sec4_Proof/Quotient.lean) proves preservation of the selected ideal and the required derivative calculations. It supplies the hypotheses of [`Orbit.lean`](../RequestProject/Yau/Sec4_Proof/Orbit.lean).

### The final contradiction

Choose a variable $`x_k`$ of least weight with $`h_k=D(x_k)\ne0`$ and set $`r=w_k-s`$. Appendix B ensures $`h_k\in\mathfrak m`$, so $`r\gt0`$. Minimality makes all coefficients attached to variables of weight at most $`r`$ vanish. Lemma 4.3 applies and gives

```math
0\ne h_k\in\sqrt{I_r}\cap S_r,
```

contrary to Theorem 3.6. The graded isomorphisms from Section 2 restore the original polynomial, and the identifications from the introduction and Appendix A give the statement for the analytic Milnor and moduli algebras.

**In Lean.** [`Sec4_Proof/Core.lean`](../RequestProject/Yau/Sec4_Proof/Core.lean) makes the least-weight choice and obtains the contradiction. [`MainTheorem.lean`](../RequestProject/Yau/Sec4_Proof/MainTheorem.lean) restores the quadratic variables by induction. [`Final/ThreeNewLocal.lean`](../RequestProject/Yau/Final/ThreeNewLocal.lean) assembles the main theorem with AGV, Theorem 14.8 as its explicit input.

## Appendices A–B: the supporting algebra

Appendix A relates isolated critical points to the finite-dimensional local algebra and identifies the polynomial and analytic quotients. The formalization uses weighted scaling, the Nullstellensatz, powers of coordinate variables, and finite Taylor truncation. See [`Appendix/Isolated.lean`](../RequestProject/Yau/Appendix/Isolated.lean), [`AnalyticMilnor.lean`](../RequestProject/Yau/Appendix/AnalyticMilnor.lean), and [`AnalyticYau.lean`](../RequestProject/Yau/Appendix/AnalyticYau.lean).

Appendix B supplies three facts used in Section 2: low-degree syzygies are trivial; derivations preserve the maximal ideal of a finite-dimensional local algebra; and negative-degree derivations have unique homogeneous polynomial lifts and are locally nilpotent. See [`Appendix/Syzygy.lean`](../RequestProject/Yau/Appendix/Syzygy.lean), [`EulerModuli.lean`](../RequestProject/Yau/Appendix/EulerModuli.lean), [`Lift.lean`](../RequestProject/Yau/Appendix/Lift.lean), and [`Basic/PolyDeriv.lean`](../RequestProject/Yau/Basic/PolyDeriv.lean).
