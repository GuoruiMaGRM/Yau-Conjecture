import Mathlib

/-!
# Basic definitions for Yau's conjecture

Work in `S = ℂ[x₁,…,xₙ]`, with positive integer weights. Define the Jacobian ideal
`J`, the polynomial Milnor algebra `A = S/J`, its homogeneous components and
homogeneous derivations, and the selected partial-derivative ideal
`I_r = (∂_i f : w_i > r)`. The algebraic isolatedness condition means that `A`
is finite dimensional over `ℂ`.
-/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ}

/-- The polynomial ring `ℂ[x₁,…,xₙ]`. -/
abbrev Poly (n : ℕ) := MvPolynomial (Fin n) ℂ

/-- The Jacobian ideal `J = (∂₁f,…,∂ₙf)`. -/
def jacobianIdeal (f : Poly n) : Ideal (Poly n) :=
  Ideal.span (Set.range fun i => pderiv i f)

/-- The polynomial Milnor algebra `ℂ[x]/J`. For positive-degree weighted homogeneous `f`, Euler's identity identifies it with the Tjurina algebra. -/
abbrev MilnorAlgebra (f : Poly n) := Poly n ⧸ jacobianIdeal f

/-- Algebraic isolatedness: the Milnor algebra is finite dimensional over `ℂ`. -/
def IsIsolatedSingularity (f : Poly n) : Prop :=
  Module.Finite ℂ (MilnorAlgebra f)

/-- The ideal `I_r = (∂_i f : w_i > r)`. -/
def partialIdeal (w : Fin n → ℕ) (f : Poly n) (r : ℕ) : Ideal (Poly n) :=
  Ideal.span ((fun i => pderiv i f) '' {i | r < w i})

/-- The degree-`m` component of the Milnor algebra, obtained from weighted homogeneous polynomials; it is zero for `m < 0`. -/
def gradedPiece (w : Fin n → ℕ) (f : Poly n) (m : ℤ) : Submodule ℂ (MilnorAlgebra f) :=
  if 0 ≤ m then
    (weightedHomogeneousSubmodule ℂ w m.toNat).map
      (Ideal.Quotient.mkₐ ℂ (jacobianIdeal f)).toLinearMap
  else ⊥

/-- A `ℂ`-linear derivation has degree `k` if it maps `A_j` into `A_{j+k}` for every `j`. -/
def IsDerivationOfDegree (w : Fin n → ℕ) (f : Poly n) (k : ℤ)
    (δ : Derivation ℂ (MilnorAlgebra f) (MilnorAlgebra f)) : Prop :=
  ∀ j : ℕ, ∀ a ∈ gradedPiece w f j, δ a ∈ gradedPiece w f (j + k)

/-! ### Homogeneity lemmas -/

lemma pderiv_isWH {w : Fin n → ℕ} {p : Poly n} {m : ℕ}
    (hp : p.IsWeightedHomogeneous w m) (i : Fin n) :
    (pderiv i p).IsWeightedHomogeneous w (m - w i) ∧ (m < w i → pderiv i p = 0) := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simp [isWeightedHomogeneous_zero]
  | add p q hp hq ihp ihq =>
    refine ⟨by rw [map_add]; exact ihp.1.add ihq.1,
      fun h => by rw [map_add, ihp.2 h, ihq.2 h, add_zero]⟩
  | monomial μ r hr =>
    classical
    rw [pderiv_monomial]
    by_cases hμ : μ i = 0
    · simp [hμ, isWeightedHomogeneous_zero]
    · have hle : Finsupp.single i 1 ≤ μ := by
        intro j; by_cases hj : j = i
        · subst hj; simp; omega
        · simp [Ne.symm hj]
      have hdec : μ = (μ - Finsupp.single i 1) + Finsupp.single i 1 :=
        (tsub_add_cancel_of_le hle).symm
      have hw : Finsupp.weight w (μ - Finsupp.single i 1) + w i = m := by
        rw [← hr]; conv_rhs => rw [hdec]
        rw [map_add]; simp [Finsupp.weight_apply, Finsupp.sum_single_index]
      exact ⟨isWeightedHomogeneous_monomial _ _ _ (by omega), fun h => by omega⟩

lemma pderiv_eq_zero_of_lt {w : Fin n → ℕ} {p : Poly n} {m : ℕ}
    (hp : p.IsWeightedHomogeneous w m) (i : Fin n) (h : m < w i) : pderiv i p = 0 :=
  (pderiv_isWH hp i).2 h

/-- Weighted scaling: `p(t^w · x) = t^e p(x)` for `p` homogeneous of weighted degree `e`. -/
lemma eval_scale {w : Fin n → ℕ} {p : Poly n} {e : ℕ}
    (hp : p.IsWeightedHomogeneous w e) (t : ℂ) (x : Fin n → ℂ) :
    eval (fun j => t ^ w j * x j) p = t ^ e * eval x p := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp [ihp, ihq, mul_add]
  | monomial μ r hr =>
    simp only [eval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib, ← pow_mul]
    rw [Finset.prod_pow_eq_pow_sum, ← hr]
    simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
    rw [show ∑ i ∈ μ.support, w i * μ i = ∑ i ∈ μ.support, μ i * w i from
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)]
    ring

lemma eval_zero_of_isWH_pos {w : Fin n → ℕ} {p : Poly n} {e : ℕ}
    (hp : p.IsWeightedHomogeneous w e) (he : 0 < e) : eval 0 p = 0 := by
  have := eval_scale hp 0 0
  simpa [zero_pow he.ne'] using this

lemma pderiv_comm' (i j : Fin n) (p : Poly n) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  have : ⁅pderiv (R := ℂ) (σ := Fin n) i, pderiv (R := ℂ) j⁆ = 0 := by
    apply derivation_ext; intro k
    rw [Derivation.commutator_apply]
    classical
    simp only [pderiv_X, Pi.single_apply]
    split_ifs <;> simp
  have h2 := congrArg (fun D => D p) this
  simp only [Derivation.commutator_apply] at h2
  simpa [sub_eq_zero] using h2

lemma weightedHomogeneousComponent_mul_of_right {w : Fin n → ℕ} (c f : Poly n) (e m : ℕ)
    (hf : f.IsWeightedHomogeneous w e) :
    weightedHomogeneousComponent w m (c * f) =
      if e ≤ m then weightedHomogeneousComponent w (m - e) c * f else 0 := by
  classical
  letI := weightedGradedAlgebra ℂ w
  have key := DirectSum.coe_decompose_mul_of_right_mem
    (𝒜 := weightedHomogeneousSubmodule ℂ w) (a := c) m
    (show f ∈ weightedHomogeneousSubmodule ℂ w e from hf)
  simp only [DirectSum.decompose] at key
  erw [weightedDecomposition.decompose'_apply, weightedDecomposition.decompose'_apply] at key
  exact key

/-- A homogeneous element of an ideal generated by homogeneous elements has an expression with coefficients of the appropriate homogeneous degrees. -/
lemma span_homog_decomp {ι : Type*} [Fintype ι] {w : Fin n → ℕ} (v : ι → Poly n)
    (e : ι → ℕ) (hv : ∀ i, (v i).IsWeightedHomogeneous w (e i)) {g : Poly n}
    (hg : g ∈ Ideal.span (Set.range v)) {q : ℕ} (hgq : g.IsWeightedHomogeneous w q) :
    ∃ h : ι → Poly n, (∀ i, (h i).IsWeightedHomogeneous w (q - e i)) ∧
      (∀ i, q < e i → h i = 0) ∧ g = ∑ i, h i * v i := by
  classical
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hg
  refine ⟨fun i => if e i ≤ q then weightedHomogeneousComponent w (q - e i) (c i) else 0,
    fun i => ?_, fun i hi => by simp [not_le.mpr hi], ?_⟩
  · by_cases h : e i ≤ q
    · simp only [h, if_true]
      exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
    · simp only [h, if_false]
      exact isWeightedHomogeneous_zero _ _ _
  · conv_lhs => rw [← hgq.weightedHomogeneousComponent_same, ← hc]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [weightedHomogeneousComponent_mul_of_right _ _ (e i) q (hv i)]
    by_cases h : e i ≤ q
    · simp only [h, if_true]
    · simp only [h, if_false, zero_mul]

/-! ### Jacobian ideals of weighted homogeneous polynomials -/

section WH

variable {w : Fin n → ℕ} {d : ℕ} {f : Poly n}

lemma pderiv_f_isWH (hf : f.IsWeightedHomogeneous w d) (i : Fin n) :
    (pderiv i f).IsWeightedHomogeneous w (d - w i) :=
  (pderiv_isWH hf i).1

/-- Homogeneous coefficient expressions for elements of the Jacobian ideal. -/
lemma jacobian_homog_decomp (hf : f.IsWeightedHomogeneous w d) {g : Poly n}
    (hg : g ∈ jacobianIdeal f) {q : ℕ} (hgq : g.IsWeightedHomogeneous w q)
    (hwd : ∀ i, w i ≤ d) :
    ∃ h : Fin n → Poly n, (∀ i, (h i).IsWeightedHomogeneous w (q + w i - d)) ∧
      (∀ i, q + w i < d → h i = 0) ∧ g = ∑ i, h i * pderiv i f := by
  obtain ⟨h, h1, h2, h3⟩ := span_homog_decomp (fun i => pderiv i f) (fun i => d - w i)
    (pderiv_f_isWH hf) hg hgq
  refine ⟨h, fun i => ?_, fun i hi => h2 i (by have := hwd i; omega), h3⟩
  have := h1 i
  rwa [show q - (d - w i) = q + w i - d by have := hwd i; omega] at this

end WH

end Yau
