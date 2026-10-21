# The textbook theorem used in Lemma 3.4

The cited source is **V. I. Arnold, S. M. Gusein-Zade, and A. N. Varchenko, *Singularities of Differentiable Maps, Volume 2: Monodromy and Asymptotics of Integrals*, Theorem 14.8, printed p. 415**. The supplied [textbook PDF](../papers/AGV-Volume-2.pdf#page=424) is the Modern Birkhäuser Classics reprint of the 1988 edition. Printed p. 415 is PDF page 424.

The accompanying paper cites this theorem in the proof of **Lemma 3.4**, on pp. 7–8. It cites AGV, Section 3.1, pp. 67–68, for the construction and versality of the deformation. The required versality for the linear families in the formal proof is established in this repository.

## The statement in the paper's notation

Take homogeneous monomials $`\varphi_0=1,\varphi_1,\ldots,\varphi_{\mu-1}`$ whose classes form a basis of $`M_f`$. Let $`e_j=\deg\varphi_j`$. The deformation and parameter weights are

```math
F_s=f+\sum_{j=0}^{\mu-1}s_j\varphi_j,\qquad \nu_j=1-\frac{e_j}{d}.
```

Normalize the variable weights to $`\alpha_i=w_i/d`$, so that $`f`$ has weight one. AGV uses the term **quasihomogeneous** for this normalization of the paper's **weighted homogeneous** polynomial. Its monomial condition $`(\alpha,m)\lt1`$ is exactly $`e_j\lt d`$.

The $`\mu`$-constant stratum here includes the condition that the critical value is zero. A parameter belongs to it if $`F_s`$ has a critical point near the origin with value zero and local Milnor number $`\mu(f,0)`$. This point is allowed to move. Theorem 14.8 identifies this stratum near the parameter origin with the coordinate subspace

```math
E=\lbrace s:s_j=0\text{ whenever }e_j\lt d\rbrace,\qquad \Sigma_\mu=E.
```

The paper calls $`\Sigma_\mu`$ a reduced analytic germ. In this application, the relevant content is that the indicated sets agree in a sufficiently small neighborhood of the parameter origin. The Lean hypothesis records that neighborhood statement using local Milnor numbers; the proof does not require a separate construction of the reduced analytic-space structure.

## How it yields q in the Jacobian ideal

Lemma 3.4 concerns the linear family $`f+tq`$, where $`q`$ is homogeneous of degree $`e\lt d`$. Its critical point stays isolated at zero, its value there is zero, and its local Milnor number is constant.

Versality expresses this family as $`F_{\gamma(t)}\circ\Phi_t`$. Invariance under right equivalence places $`\gamma(t)`$ in $`\Sigma_\mu`$. The direction **$`\Sigma_\mu\subseteq E`$** then makes every low-degree parameter vanish. Differentiate at zero and take the degree-$`e`$ component:

```math
q=\sum_i(v_i)_{e-d+w_i}f_i\in J.
```

Corollary 3.5 uses this only with $`q=a^2`$ and $`0\lt3r\lt d`$, where $`a\in S_r\cap\sqrt{I_r}`$. Lemma 3.3 supplies the deformation conditions. The remainder of the proof uses this polynomial ideal membership in Theorem 3.6 and the final contradiction.

## Its place in the Lean theorem

[`Final/AGV148.lean`](../RequestProject/Yau/Final/AGV148.lean) defines the neighborhood statement for each number of variables. [`Final/ThreeNewLocal.lean`](../RequestProject/Yau/Final/ThreeNewLocal.lean) derives Lemma 3.4 from it and concludes the main theorem. Under this textbook theorem, the complete chain from the hypotheses of the paper to the vanishing of negative-degree derivations is formalized.

More precisely, the main theorem takes the AGV statement for every number of variables at least two. The zero- and one-variable cases are proved directly in the project. The inclusion $`E\subseteq\Sigma_\mu`$ is also proved in [`VarchenkoInclusion.lean`](../RequestProject/Yau/Sec3_Radical/VarchenkoInclusion.lean), so the part supplied by the textbook input is the opposite inclusion in two or more variables. The assumption appears as an argument of the main theorem.

For the exact Lean declarations, see the [main-theorem entry in the code guide](CodeGuide.md#main-theorem).
