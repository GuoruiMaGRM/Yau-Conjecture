import RequestProject.Yau.Basic.Basic

/-!
# The weight filtration `F^T`

Define `highIdeal w T` as the polynomials whose monomials all have weight at
least `T`. Establish its homogeneous-component, product, and derivative bounds.
For sufficiently large `T`, this ideal lies in any ideal containing powers
of every coordinate variable.
-/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ} {w : Fin n → ℕ}

/-- The weight-filtration ideal of polynomials all of whose monomials have weight at least `T`. -/
def highIdeal (w : Fin n → ℕ) (T : ℕ) : Ideal (Poly n) where
  carrier := {p | ∀ m ∈ p.support, T ≤ Finsupp.weight w m}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq m hm
    classical
    rcases Finset.mem_union.1 (support_add hm) with h | h
    · exact hp m h
    · exact hq m h
  smul_mem' := by
    intro c p hp m hm
    classical
    have hm' := support_mul c p hm
    obtain ⟨a, -, b, hb, rfl⟩ := Finset.mem_add.1 hm'
    rw [map_add]
    exact le_add_left (hp b hb)

lemma mem_highIdeal_iff {T : ℕ} {p : Poly n} :
    p ∈ highIdeal w T ↔ ∀ m ∈ p.support, T ≤ Finsupp.weight w m := Iff.rfl

lemma highIdeal_mono {T T' : ℕ} (h : T ≤ T') : highIdeal w T' ≤ highIdeal w T :=
  fun _ hp m hm => h.trans (hp m hm)

lemma highIdeal_zero : highIdeal w 0 = ⊤ :=
  eq_top_iff.2 fun _ _ _ _ => Nat.zero_le _

lemma weightedHomogeneousComponent_eq_zero_of_mem_highIdeal {T v : ℕ} {p : Poly n}
    (hp : p ∈ highIdeal w T) (hv : v < T) : weightedHomogeneousComponent w v p = 0 := by
  classical
  ext m
  rw [coeff_weightedHomogeneousComponent, coeff_zero]
  split_ifs with h
  · by_contra hc
    have := hp m (mem_support_iff.2 hc)
    omega
  · rfl

lemma mem_highIdeal_of_weightedHomogeneousComponent {T : ℕ} {p : Poly n}
    (h : ∀ v < T, weightedHomogeneousComponent w v p = 0) : p ∈ highIdeal w T := by
  classical
  intro m hm
  by_contra hlt
  push_neg at hlt
  have := congrArg (coeff m) (h _ hlt)
  rw [coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at this
  exact (mem_support_iff.1 hm) this

lemma mem_highIdeal_iff_comp {T : ℕ} {p : Poly n} :
    p ∈ highIdeal w T ↔ ∀ v < T, weightedHomogeneousComponent w v p = 0 :=
  ⟨fun hp _ hv => weightedHomogeneousComponent_eq_zero_of_mem_highIdeal hp hv,
    mem_highIdeal_of_weightedHomogeneousComponent⟩

lemma mem_highIdeal_succ {v : ℕ} {p : Poly n} (hp : p ∈ highIdeal w v)
    (h : weightedHomogeneousComponent w v p = 0) : p ∈ highIdeal w (v + 1) := by
  rw [mem_highIdeal_iff_comp] at hp ⊢
  intro u hu
  rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
  · exact hp u hu
  · exact h

lemma isWH_mem_highIdeal {T v : ℕ} {p : Poly n} (hp : p.IsWeightedHomogeneous w v)
    (hv : T ≤ v) : p ∈ highIdeal w T := by
  intro m hm
  rw [hp (mem_support_iff.1 hm)]; exact hv

lemma sub_component_mem_highIdeal {v : ℕ} {p : Poly n} (hp : p ∈ highIdeal w v) :
    p - weightedHomogeneousComponent w v p ∈ highIdeal w (v + 1) := by
  refine mem_highIdeal_succ (Ideal.sub_mem _ hp
    (isWH_mem_highIdeal (weightedHomogeneousComponent_isWeightedHomogeneous _ _) le_rfl)) ?_
  rw [map_sub, (weightedHomogeneousComponent_isWeightedHomogeneous v p).weightedHomogeneousComponent_same,
    sub_self]

lemma mul_mem_highIdeal {a b : ℕ} {p q : Poly n} (hp : p ∈ highIdeal w a)
    (hq : q ∈ highIdeal w b) : p * q ∈ highIdeal w (a + b) := by
  classical
  intro m hm
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (support_mul p q hm)
  rw [map_add]
  exact Nat.add_le_add (hp x hx) (hq y hy)

lemma pderiv_mem_highIdeal {T : ℕ} {p : Poly n} (hp : p ∈ highIdeal w T) (i : Fin n) :
    pderiv i p ∈ highIdeal w (T - w i) := by
  classical
  rw [p.as_sum, map_sum]
  refine Ideal.sum_mem _ fun m hm => ?_
  rw [pderiv_monomial]
  by_cases hmi : m i = 0
  · simp [hmi]
  · have hle : Finsupp.single i 1 ≤ m := by
      intro j; by_cases hj : j = i
      · subst hj; simp; omega
      · simp [Ne.symm hj]
    have hwt : Finsupp.weight w (m - Finsupp.single i 1) + w i = Finsupp.weight w m := by
      conv_rhs => rw [← tsub_add_cancel_of_le hle]
      rw [map_add]; simp [Finsupp.weight_apply, Finsupp.sum_single_index]
    intro m' hm'
    have := support_monomial_subset hm'
    rw [Finset.mem_singleton] at this
    subst this
    have := hp m hm
    omega

/-- If `T>N∑w_i`, every monomial of weight at least `T` is divisible by some `x_i^N`. -/
lemma highIdeal_le_span_X_pow (N : ℕ) :
    highIdeal w (N * ∑ i, w i + 1) ≤ Ideal.span (Set.range fun i : Fin n => (X i : Poly n) ^ N) := by
  classical
  intro p hp
  rw [p.as_sum]
  refine Ideal.sum_mem _ fun m hm => ?_
  have hwm := hp m hm
  obtain ⟨i, hi⟩ : ∃ i, N ≤ m i := by
    by_contra h
    push_neg at h
    have : Finsupp.weight w m ≤ N * ∑ i, w i := by
      rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => by
        rw [smul_eq_mul]; exact Nat.mul_le_mul_right _ (h j).le
    omega
  have hle : Finsupp.single i N ≤ m := by
    intro j; by_cases hj : j = i
    · subst hj; simpa using hi
    · simp [Ne.symm hj]
  have : monomial m (coeff m p) = monomial (m - Finsupp.single i N) (coeff m p) * X i ^ N := by
    rw [X_pow_eq_monomial, monomial_mul, mul_one, tsub_add_cancel_of_le hle]
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- An ideal generated by weighted homogeneous elements is closed under homogeneous components. -/
lemma weightedHomogeneousComponent_mem_span {ι : Type*} [Fintype ι] (v : ι → Poly n)
    (e : ι → ℕ) (hv : ∀ i, (v i).IsWeightedHomogeneous w (e i)) {b : Poly n}
    (hb : b ∈ Ideal.span (Set.range v)) (c : ℕ) :
    weightedHomogeneousComponent w c b ∈ Ideal.span (Set.range v) := by
  classical
  obtain ⟨coef, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hb
  rw [map_sum]
  refine Ideal.sum_mem _ fun k _ => ?_
  rw [weightedHomogeneousComponent_mul_of_right _ _ (e k) c (hv k)]
  split_ifs
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)
  · exact Ideal.zero_mem _

/-- The Jacobian ideal of homogeneous `f` is closed under homogeneous components. -/
lemma weightedHomogeneousComponent_mem_jacobianIdeal {d : ℕ} {f : Poly n}
    (hf : f.IsWeightedHomogeneous w d) {b : Poly n} (hb : b ∈ jacobianIdeal f) (c : ℕ) :
    weightedHomogeneousComponent w c b ∈ jacobianIdeal f :=
  weightedHomogeneousComponent_mem_span _ _ (pderiv_f_isWH hf) hb c

/-- If every `x_i^N` belongs to `I`, then `F^T ⊆ I` for sufficiently large `T`. -/
lemma exists_highIdeal_le_of_pow_X_mem {I : Ideal (Poly n)}
    (hI : ∀ i, ∃ N : ℕ, (X i : Poly n) ^ N ∈ I) : ∃ T, highIdeal w T ≤ I := by
  choose N hN using hI
  refine ⟨(∑ i, N i) * ∑ i, w i + 1, (highIdeal_le_span_X_pow _).trans ?_⟩
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  have : N i ≤ ∑ j, N j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  show X i ^ _ ∈ I
  rw [← Nat.sub_add_cancel this, pow_add]
  exact Ideal.mul_mem_left _ _ (hN i)

end Yau
