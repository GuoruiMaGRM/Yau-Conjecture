import RequestProject.Yau.Sec2_Splitting.Subst

/-! # Eliminating variables and elementary automorphisms -/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ}

/-- Substitute zero for `x_v`. -/
def killV (v : Fin n) : Poly n →ₐ[ℂ] Poly n := aeval (Function.update X v 0)

/-- The polynomial is independent of `x_v`. -/
def FreeOf (v : Fin n) (g : Poly n) : Prop := killV v g = g

section kill

variable {v u : Fin n}

@[simp] lemma killV_X_self : killV v (X v) = 0 := by simp [killV]

lemma killV_X_ne {j : Fin n} (h : j ≠ v) : killV v (X j) = X j := by
  simp [killV, Function.update_of_ne h]

lemma killV_comp_killV : (killV v).comp (killV v) = killV v := by
  apply algHom_ext; intro j
  by_cases h : j = v
  · subst h; simp
  · simp [killV_X_ne h]

lemma killV_killV (p : Poly n) : killV v (killV v p) = killV v p :=
  congrArg (fun F : Poly n →ₐ[ℂ] Poly n => F p) (killV_comp_killV (v := v))

lemma freeOf_killV (p : Poly n) : FreeOf v (killV v p) := killV_killV p

lemma killV_comm (p : Poly n) : killV u (killV v p) = killV v (killV u p) := by
  have : (killV u).comp (killV v) = (killV v).comp (killV u) := by
    apply algHom_ext; intro j
    simp only [AlgHom.comp_apply]
    by_cases hu : j = u <;> by_cases hv : j = v
    · subst hu; subst hv; rfl
    · subst hu; simp [killV_X_ne hv]
    · subst hv; simp [killV_X_ne hu]
    · simp [killV_X_ne hu, killV_X_ne hv]
  exact congrArg (fun F : Poly n →ₐ[ℂ] Poly n => F p) this

lemma FreeOf.killV_other {g : Poly n} (h : FreeOf u g) : FreeOf u (killV v g) := by
  unfold FreeOf at *; rw [killV_comm, h]

lemma freeOf_X {j : Fin n} (h : j ≠ v) : FreeOf v (X j) := killV_X_ne h

lemma freeOf_C (c : ℂ) : FreeOf v (C c) := by simp [FreeOf, killV]

lemma FreeOf.add {p q : Poly n} (hp : FreeOf v p) (hq : FreeOf v q) : FreeOf v (p + q) := by
  unfold FreeOf at *; rw [map_add, hp, hq]

lemma FreeOf.sub {p q : Poly n} (hp : FreeOf v p) (hq : FreeOf v q) : FreeOf v (p - q) := by
  unfold FreeOf at *; rw [map_sub, hp, hq]

lemma FreeOf.mul {p q : Poly n} (hp : FreeOf v p) (hq : FreeOf v q) : FreeOf v (p * q) := by
  unfold FreeOf at *; rw [map_mul, hp, hq]

lemma FreeOf.neg {p : Poly n} (hp : FreeOf v p) : FreeOf v (-p) := by
  unfold FreeOf at *; rw [map_neg, hp]

lemma FreeOf.pow {p : Poly n} (hp : FreeOf v p) (k : ℕ) : FreeOf v (p ^ k) := by
  unfold FreeOf at *; rw [map_pow, hp]

/-- A substitution fixing all variables except `x_v` fixes polynomials independent of `x_v`. -/
lemma FreeOf.aeval_eq {g : Poly n} (h : FreeOf v g) (φ : Fin n → Poly n)
    (hφ : ∀ j, j ≠ v → φ j = X j) : aeval φ g = g := by
  have : (aeval φ).comp (killV v) = killV v := by
    apply algHom_ext; intro j
    by_cases hj : j = v
    · subst hj; simp
    · simp [killV_X_ne hj, hφ j hj]
  have h2 := congrArg (fun F : Poly n →ₐ[ℂ] Poly n => F g) this
  simp only [AlgHom.comp_apply] at h2
  unfold FreeOf at h
  rw [h] at h2
  exact h2

lemma FreeOf.pderiv_eq_zero {g : Poly n} (h : FreeOf v g) : pderiv v g = 0 := by
  unfold FreeOf at h
  rw [← h, killV, pderiv_aeval]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : j = v
  · subst hj; simp
  · simp [Function.update_of_ne hj, pderiv_X, Ne.symm hj]

lemma eval_killV (x : Fin n → ℂ) (p : Poly n) :
    eval x (killV v p) = eval (Function.update x v 0) p := by
  have : (eval x).comp (killV v : Poly n →+* Poly n) = eval (Function.update x v 0) := by
    apply ringHom_ext
    · intro c; simp [killV]
    · intro j
      by_cases hj : j = v
      · subst hj; simp
      · simp [killV_X_ne hj, Function.update_of_ne hj]
  exact congrArg (fun F : Poly n →+* ℂ => F p) this

lemma FreeOf.eval_update {g : Poly n} (h : FreeOf v g) (x : Fin n → ℂ) (c : ℂ) :
    eval (Function.update x v c) g = eval (Function.update x v 0) g := by
  unfold FreeOf at h
  rw [← h, eval_killV, eval_killV]
  simp

lemma killV_isWH {w : Fin n → ℕ} {p : Poly n} {e : ℕ} (hp : p.IsWeightedHomogeneous w e) :
    (killV v p).IsWeightedHomogeneous w e := by
  refine aeval_isWH (fun j => ?_) hp
  by_cases hj : j = v
  · subst hj; simp [isWeightedHomogeneous_zero]
  · simp only [Function.update_of_ne hj]; exact isWeightedHomogeneous_X _ _ _

lemma freeOf_monomial {μ : Fin n →₀ ℕ} (hμ : μ v = 0) (c : ℂ) : FreeOf v (monomial μ c) := by
  unfold FreeOf killV
  rw [aeval_monomial, Finsupp.prod, monomial_eq, Finsupp.prod]
  simp only [MvPolynomial.algebraMap_eq]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  have : j ≠ v := by rintro rfl; simp [hμ] at hj
  rw [Function.update_of_ne this]

end kill

/-! ### Second-order Taylor expansion in one variable -/

section taylor

variable {v : Fin n}

lemma finsupp_update_add_single (μ : Fin n →₀ ℕ) (v : Fin n) :
    Finsupp.update μ v 0 + Finsupp.single v (μ v) = μ := by
  ext i
  by_cases h : i = v
  · subst h; simp
  · simp [h]

@[simp] lemma killV_C {v : Fin n} (c : ℂ) : killV v (C c) = C c := freeOf_C c

lemma taylor_monomial (μ : Fin n →₀ ℕ) (c : ℂ) (h : μ v ≤ 2) :
    monomial μ c = killV v (monomial μ c) + X v * killV v (pderiv v (monomial μ c)) +
      X v ^ 2 * C (1 / 2 : ℂ) * killV v (pderiv v (pderiv v (monomial μ c))) := by
  set ν := Finsupp.update μ v 0
  have hν : ν v = 0 := by simp [ν]
  have hm : monomial μ c = monomial ν c * X v ^ (μ v) := by
    rw [← monomial_add_single, finsupp_update_add_single]
  have hf : killV v (monomial ν c) = monomial ν c := freeOf_monomial hν c
  have hd := (freeOf_monomial hν c).pderiv_eq_zero
  have hD : ∀ q, pderiv v (monomial ν c * q) = monomial ν c * pderiv v q := by
    intro q; rw [Derivation.leibniz, hd]; simp
  rw [hm]
  interval_cases hk : μ v
  · simp [hf, hd]
  · simp only [pow_one, hD, pderiv_X_self, mul_one, map_mul, hf, killV_X_self, hd, map_zero,
      mul_zero, add_zero, zero_add]
    ring
  · have h2 : pderiv v (X v ^ 2 : Poly n) = C 2 * X v := by
      rw [Derivation.leibniz_pow]; simp; exact (map_ofNat C 2).symm
    have h22 : pderiv v (C 2 * X v : Poly n) = C 2 := by
      rw [Derivation.leibniz, derivation_C, pderiv_X_self]; simp
    simp only [hD, h2, h22, map_mul, hf, killV_X_self, mul_zero, add_zero, zero_add,
      map_pow, killV_C, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    rw [show (X v ^ 2 * C (1 / 2 : ℂ) * (monomial ν c * C 2) : Poly n) =
      monomial ν c * X v ^ 2 * (C (1 / 2 : ℂ) * C 2) by ring, ← C_mul]
    norm_num

/-- Taylor expansion of a polynomial of degree at most two in `x_v`. -/
lemma taylor2_killV (p : Poly n) (h : ∀ μ ∈ p.support, μ v ≤ 2) :
    p = killV v p + X v * killV v (pderiv v p) +
      X v ^ 2 * C (1 / 2 : ℂ) * killV v (pderiv v (pderiv v p)) := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun μ hμ => taylor_monomial μ _ (h μ hμ)

lemma degree_le_of_isWH {w : Fin n → ℕ} {p : Poly n} {e : ℕ}
    (hp : p.IsWeightedHomogeneous w e) {μ : Fin n →₀ ℕ} (hμ : μ ∈ p.support) :
    μ v * w v ≤ e := by
  have he : Finsupp.weight w μ = e := hp (mem_support_iff.mp hμ)
  rw [← he, Finsupp.weight_apply, Finsupp.sum]
  by_cases hv : v ∈ μ.support
  · exact Finset.single_le_sum (f := fun i => μ i • w i) (fun _ _ => Nat.zero_le _) hv
  · simp [Finsupp.notMem_support_iff.mp hv]

/-- Every polynomial has the form `killV v p + x_v K`. -/
lemma exists_killV_decomp (p : Poly n) : ∃ K : Poly n, p = killV v p + X v * K := by
  have : p - killV v p ∈ Ideal.span {(X v : Poly n)} := by
    induction p using MvPolynomial.induction_on with
    | C a => simp [killV]
    | add p q hp hq =>
      rw [map_add, add_sub_add_comm]; exact Ideal.add_mem _ hp hq
    | mul_X p j hp =>
      rw [map_mul]
      by_cases hj : j = v
      · subst hj
        rw [killV_X_self, mul_zero, sub_zero]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
      · rw [killV_X_ne hj, ← sub_mul]
        exact Ideal.mul_mem_right _ _ hp
  obtain ⟨K, hK⟩ := Ideal.mem_span_singleton.mp this
  exact ⟨K, by rw [← hK]; ring⟩

/-- Divide a weighted homogeneous polynomial by a variable. -/
lemma isWH_of_X_mul {w : Fin n → ℕ} {K : Poly n} {e : ℕ}
    (h : (X v * K).IsWeightedHomogeneous w e) : K.IsWeightedHomogeneous w (e - w v) := by
  intro μ hμ
  have := h (show coeff (μ + Finsupp.single v 1) (X v * K) ≠ 0 by
    rwa [mul_comm, coeff_mul_X])
  have hw : Finsupp.weight w (μ + Finsupp.single v 1) = Finsupp.weight w μ + w v := by
    rw [map_add]; simp [Finsupp.weight_apply]
  omega

/-- A weighted homogeneous polynomial of weight zero is constant. -/
lemma eq_C_of_isWH_zero {w : Fin n → ℕ} (hw : ∀ i, 0 < w i) {q : Poly n}
    (hq : q.IsWeightedHomogeneous w 0) : q = C (eval 0 q) := by
  ext μ
  rw [coeff_C]
  by_cases hμ : μ = 0
  · subst hμ; simp [MvPolynomial.eval_zero, constantCoeff_eq]
  · rw [if_neg (Ne.symm hμ)]
    by_contra hc
    have h0 := hq hc
    apply hμ
    ext i
    have := Finsupp.le_weight w (hw i).ne' μ (s := i)
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    omega

end taylor

end Yau
