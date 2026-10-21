import RequestProject.Yau.CommAlg.RegularSequence
import RequestProject.Yau.Appendix.Isolated
import RequestProject.Yau.Sec3_Radical.SquareDeformation
import RequestProject.Yau.Appendix.AnalyticYau

/-!
# Milnor numbers for lower-degree perturbations

For isolated weighted homogeneous `f` of degree `d` and homogeneous `q` of
degree less than `d`, the polynomial Jacobian quotients for `f+q` and `f`
are finite dimensional with the same dimension. Introduce a homogenizing variable
of weight one, use regular sequences, and transport a monomial complement.
For the square deformation of Lemma 3.3, the radical calculation ensures that
the origin is the only critical point. The polynomial dimension is therefore
the local analytic Milnor number, giving the weighted homogeneous instance
of Lemma 3.3 used in Corollary 3.5.
-/

open MvPolynomial RingTheory.Sequence

noncomputable section

namespace Yau

namespace Homog

variable {n : ℕ}

/-- The homogenizing variable `t=x₀` in `ℂ[t,x₁,…,xₙ]`. -/
abbrev tv : Poly (n + 1) := X 0

/-- The inclusion `ℂ[x] → ℂ[t,x]`, sending `x_i` to `x_{i+1}`. -/
def emb : Poly n →ₐ[ℂ] Poly (n + 1) := rename Fin.succ

/-- Weights on `ℂ[t,x]`, with `t` of weight one. -/
def wt (w : Fin n → ℕ) : Fin (n + 1) → ℕ := Fin.cases 1 w

/-- Substitute `c` for `t`. -/
def evT (c : ℂ) : Poly (n + 1) →ₐ[ℂ] Poly n := aeval (Fin.cases (C c) X)

lemma evT_emb (c : ℂ) (p : Poly n) : evT c (emb p) = p := by
  simp only [evT, emb, aeval_rename]
  have : (Fin.cases (C c) X : Fin (n + 1) → Poly n) ∘ Fin.succ = X := by
    funext i; simp
  rw [this, aeval_X_left_apply]

lemma evT_tv (c : ℂ) : evT c (tv : Poly (n + 1)) = C c := by
  simp [evT]

variable {w : Fin n → ℕ}

lemma isWH_emb {p : Poly n} {m : ℕ} (hp : p.IsWeightedHomogeneous w m) :
    (emb p).IsWeightedHomogeneous (wt w) m := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simp [isWeightedHomogeneous_zero]
  | add p q _ _ ihp ihq => rw [map_add]; exact ihp.add ihq
  | monomial μ r hr =>
    rw [emb, rename_monomial]
    refine isWeightedHomogeneous_monomial _ _ _ ?_
    rw [← hr, Finsupp.weight_apply, Finsupp.weight_apply,
      Finsupp.sum_mapDomain_index (h := fun i c => c • wt w i) (fun _ => zero_smul _ _)
        (fun _ _ _ => add_smul _ _ _)]
    simp [wt]

lemma isWH_tv : (tv : Poly (n + 1)).IsWeightedHomogeneous (wt w) 1 := by
  simpa [wt] using isWeightedHomogeneous_X ℂ (wt w) 0

lemma evT_eq_eval (c : ℂ) (Z : Poly (n + 1)) :
    evT c Z = Polynomial.eval (C c) (finSuccEquiv ℂ n Z) := by
  have : (evT c : Poly (n + 1) →ₐ[ℂ] Poly n) =
      ((Polynomial.aeval (R := Poly n) (C c)).restrictScalars ℂ).comp
        (finSuccEquiv ℂ n).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [evT, finSuccEquiv_X_zero]
    · simp [evT, finSuccEquiv_X_succ]
  rw [this]
  simp [Polynomial.coe_aeval_eq_eval]

lemma weight_cons (i : ℕ) (m : Fin n →₀ ℕ) :
    Finsupp.weight (wt w) (Finsupp.cons i m) = i + Finsupp.weight w m := by
  simp only [Finsupp.weight_apply]
  rw [Finsupp.sum_fintype _ (fun i c => c • wt w i) (fun _ => zero_smul _ _),
    Finsupp.sum_fintype _ (fun i c => c • w i) (fun _ => zero_smul _ _), Fin.sum_univ_succ]
  simp [wt]

/-- A homogeneous polynomial in `ℂ[t,x]` that vanishes upon setting `t=1` is zero. -/
lemma eq_zero_of_evT_one {Z : Poly (n + 1)} {K : ℕ} (hZ : Z.IsWeightedHomogeneous (wt w) K)
    (h : evT 1 Z = 0) : Z = 0 := by
  set P := finSuccEquiv ℂ n Z with hP
  have hcoef : ∀ i (m : Fin n →₀ ℕ), coeff m (P.coeff i) ≠ 0 → i + Finsupp.weight w m = K := by
    intro i m hm
    rw [hP, finSuccEquiv_coeff_coeff] at hm
    rw [← weight_cons]
    exact hZ hm
  have hhom : ∀ i, (P.coeff i).IsWeightedHomogeneous w (K - i) := by
    intro i m hm
    have := hcoef i m hm
    omega
  have hbig : ∀ i, K < i → P.coeff i = 0 := by
    intro i hi
    ext m
    by_contra hm
    have := hcoef i m hm
    omega
  have hsum : ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i = 0 := by
    rw [evT_eq_eval, Polynomial.eval_eq_sum_range] at h
    simpa using h
  have hzero : ∀ i, P.coeff i = 0 := by
    intro i0
    by_cases hi0 : K < i0
    · exact hbig i0 hi0
    by_cases hdeg : P.natDegree < i0
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt hdeg
    have hc := congrArg (weightedHomogeneousComponent w (K - i0)) hsum
    rw [map_sum, map_zero, Finset.sum_eq_single i0] at hc
    · rwa [(hhom i0).weightedHomogeneousComponent_same] at hc
    · intro i _ hi
      by_cases hiK : K < i
      · rw [hbig i hiK, map_zero]
      · rw [weightedHomogeneousComponent_of_mem (hhom i), if_neg (by omega)]
    · intro h; simp at h; omega
  have hP0 : P = 0 := Polynomial.ext fun i => by rw [hzero i, Polynomial.coeff_zero]
  rw [hP] at hP0
  exact (map_eq_zero_iff _ (finSuccEquiv ℂ n).injective).1 hP0

/-- Homogenization to degree `K`: `∑_{k≤K} t^{K-k}p_k`. -/
def homog (w : Fin n → ℕ) (K : ℕ) (p : Poly n) : Poly (n + 1) :=
  ∑ k ∈ Finset.range (K + 1), tv ^ (K - k) * emb (weightedHomogeneousComponent w k p)

lemma homog_isWH (K : ℕ) (p : Poly n) : (homog w K p).IsWeightedHomogeneous (wt w) K := by
  refine IsWeightedHomogeneous.sum _ _ _ fun k hk => ?_
  have h := (isWH_tv (w := w).pow (K - k)).mul
    (isWH_emb (weightedHomogeneousComponent_isWeightedHomogeneous (w := w) k p))
  have e : (K - k) • 1 + k = K := by
    simp only [Finset.mem_range] at hk; simp; omega
  rwa [e] at h

lemma evT_one_homog {K : ℕ} {p : Poly n}
    (h : ∀ k, K < k → weightedHomogeneousComponent w k p = 0) : evT 1 (homog w K p) = p := by
  simp only [homog, map_sum, map_mul, map_pow, evT_tv, evT_emb, C_1, one_pow, one_mul]
  conv_rhs => rw [← sum_weightedHomogeneousComponent w p]
  rw [finsum_eq_sum_of_support_subset]
  intro k hk
  rw [Function.mem_support] at hk
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  exact hk (h k (by omega))

lemma evT_zero_homog (K : ℕ) (p : Poly n) :
    evT 0 (homog w K p) = weightedHomogeneousComponent w K p := by
  simp only [homog, map_sum, map_mul, map_pow, evT_tv, evT_emb, C_0]
  rw [Finset.sum_eq_single K]
  · simp
  · intro k hk hkK
    simp only [Finset.mem_range] at hk
    rw [zero_pow (by omega), zero_mul]
  · intro h; simp at h

lemma homog_eq_mul {K K' : ℕ} (hK : K' ≤ K) {p : Poly n}
    (h : ∀ k, K' < k → weightedHomogeneousComponent w k p = 0) :
    homog w K p = tv ^ (K - K') * homog w K' p := by
  rw [homog, homog, Finset.mul_sum]
  rw [← Finset.sum_subset (Finset.range_subset_range.2 (Nat.succ_le_succ hK))]
  · refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  · intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    rw [h k (by omega), map_zero, mul_zero]

end Homog

open Homog

variable {n : ℕ} {w : Fin n → ℕ} {d s : ℕ} {f q : Poly n}

/-- The homogenized partial derivatives `G_i = ∂_i f + t^{d-s} ∂_i q`. -/
def homogPartial (d s : ℕ) (f q : Poly n) (i : Fin n) : Poly (n + 1) :=
  emb (pderiv i f) + tv ^ (d - s) * emb (pderiv i q)

lemma homogPartial_isWH (hf : f.IsWeightedHomogeneous w d) (hq : q.IsWeightedHomogeneous w s)
    (hs : s < d) (i : Fin n) :
    (homogPartial d s f q i).IsWeightedHomogeneous (wt w) (d - w i) := by
  refine (isWH_emb (pderiv_f_isWH hf i)).add ?_
  by_cases hsw : s < w i
  · rw [pderiv_eq_zero_of_lt hq i hsw, map_zero, mul_zero]
    exact isWeightedHomogeneous_zero _ _ _
  · have h := (isWH_tv (w := w).pow (d - s)).mul (isWH_emb (pderiv_isWH hq i).1)
    have e : (d - s) • 1 + (s - w i) = d - w i := by simp; omega
    rwa [e] at h

lemma evT_homogPartial (c : ℂ) (i : Fin n) :
    evT c (homogPartial d s f q i) = pderiv i f + C c ^ (d - s) * pderiv i q := by
  simp [homogPartial, evT_emb, evT_tv]

/-- The variable `t` is a non-zero-divisor modulo `(G₁,…,Gₙ)`. -/
lemma tv_nzd (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hiso : IsIsolatedSingularity f) (hwd : ∀ i, w i < d)
    (hq : q.IsWeightedHomogeneous w s) (hs : s < d) (b : Poly (n + 1))
    (hb : tv * b ∈ Ideal.span (Set.range (homogPartial d s f q))) :
    b ∈ Ideal.span (Set.range (homogPartial d s f q)) := by
  set L : List (Poly (n + 1)) := (List.finRange n).map (homogPartial d s f q) ++ [tv] with hL
  have htvL : (tv : Poly (n + 1)) ∈ Ideal.ofList L :=
    Ideal.subset_span (by simp [hL])
  have hGL : ∀ i, homogPartial d s f q i ∈ Ideal.ofList L :=
    fun i => Ideal.subset_span (by simp [hL])
  have hJ : (jacobianIdeal f).map (emb : Poly n →ₐ[ℂ] Poly (n + 1)) ≤ Ideal.ofList L := by
    rw [jacobianIdeal, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have : (emb (pderiv i f) : Poly (n + 1)) =
        homogPartial d s f q i - tv * (tv ^ (d - s - 1) * emb (pderiv i q)) := by
      rw [homogPartial, ← mul_assoc, ← pow_succ', Nat.sub_one_add_one (by omega)]
      ring
    rw [SetLike.mem_coe, this]
    exact Ideal.sub_mem _ (hGL i) (Ideal.mul_mem_right _ _ htvL)
  have hfin : Module.Finite ℂ (Poly (n + 1) ⧸ Ideal.ofList L) := by
    refine finite_quotient_of_pow_X_mem _ fun j => ?_
    refine Fin.cases ⟨1, by rw [pow_one]; exact htvL⟩ (fun i => ?_) j
    obtain ⟨N, hN⟩ := exists_pow_X_mem_jac (common_zero_eq_zero hw hf hiso) i
    refine ⟨N, hJ ?_⟩
    have : (X i.succ : Poly (n + 1)) ^ N = emb (X i ^ N) := by simp [emb]
    rw [this]
    exact Ideal.mem_map_of_mem _ hN
  have hreg := isWeaklyRegular_of_finite_quotient (w := wt w)
    (fun j => Fin.cases (by simp [wt]) (fun i => by simpa [wt] using hw i) j) L
    (by simp [hL]) (fun g hg => by
      rw [hL, List.mem_append, List.mem_map] at hg
      rcases hg with ⟨i, -, rfl⟩ | hg
      · exact ⟨d - w i, by have := hwd i; omega, homogPartial_isWH hf hq hs i⟩
      · simp only [List.mem_singleton] at hg
        exact hg ▸ ⟨1, one_pos, isWH_tv⟩) hfin
  rw [isWeaklyRegular_self_iff] at hreg
  have hlen : n < L.length := by simp [hL]
  have htake : L.take n = (List.finRange n).map (homogPartial d s f q) :=
    List.take_left' (by simp)
  have hget : L[n] = tv := by simp [hL]
  have hspan : Ideal.ofList ((List.finRange n).map (homogPartial d s f q)) =
      Ideal.span (Set.range (homogPartial d s f q)) := by
    rw [Ideal.ofList]
    congr 1
    ext r
    simp
  have := hreg n hlen b
  rw [hget, htake, hspan] at this
  exact this hb

/-- Independence: a submodule closed under homogeneous components and disjoint from `J_f` is also disjoint from `J_{f+q}`. -/
theorem eq_zero_of_mem_jacobianIdeal_add (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hiso : IsIsolatedSingularity f) (hwd : ∀ i, w i < d)
    (hq : q.IsWeightedHomogeneous w s) (hs : s < d) (V : Submodule ℂ (Poly n))
    (hV : ∀ p ∈ V, ∀ k, weightedHomogeneousComponent w k p ∈ V)
    (hVJ : ∀ p ∈ V, p ∈ jacobianIdeal f → p = 0) :
    ∀ p ∈ V, p ∈ jacobianIdeal (f + q) → p = 0 := by
  classical
  intro p hpV hpJ
  set IG := Ideal.span (Set.range (homogPartial d s f q)) with hIG
  obtain ⟨h, hh⟩ := Ideal.mem_span_range_iff_exists_fun.1 hpJ
  have hcomp : ∀ (r : Poly n) (k : ℕ), weightedTotalDegree w r < k →
      weightedHomogeneousComponent w k r = 0 :=
    fun r k hk => weightedHomogeneousComponent_eq_zero _ _ hk
  set K := d + ∑ i, weightedTotalDegree w (h i) + weightedTotalDegree w p with hK
  have hhK : ∀ i, weightedTotalDegree w (h i) ≤ ∑ j, weightedTotalDegree w (h j) :=
    fun i => Finset.single_le_sum (f := fun j => weightedTotalDegree w (h j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  set H := ∑ i, homog w (K - (d - w i)) (h i) * homogPartial d s f q i with hH
  have hHmem : H ∈ IG :=
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have hHhom : H.IsWeightedHomogeneous (wt w) K := by
    refine IsWeightedHomogeneous.sum _ _ _ fun i _ => ?_
    have := (homog_isWH (w := w) (K - (d - w i)) (h i)).mul (homogPartial_isWH hf hq hs i)
    rwa [Nat.sub_add_cancel (by omega)] at this
  have hHev : evT 1 H = p := by
    rw [hH, map_sum, ← hh]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, evT_one_homog, evT_homogPartial, C_1, one_pow, one_mul, map_add]
    intro k hk
    exact hcomp _ _ (by have := hhK i; omega)
  have hPhom := homog_isWH (w := w) K p
  have hPev : evT 1 (homog w K p) = p := evT_one_homog fun k hk => hcomp p k (by omega)
  have heq : homog w K p = H := by
    refine sub_eq_zero.1 (eq_zero_of_evT_one (K := K)
      (Submodule.sub_mem (weightedHomogeneousSubmodule ℂ (wt w) K) hPhom hHhom) ?_)
    rw [map_sub, hPev, hHev, sub_self]
  have hex : ∃ K', ∀ k, K' < k → weightedHomogeneousComponent w k p = 0 :=
    ⟨_, fun k hk => hcomp p k hk⟩
  have hK' : ∀ k, Nat.find hex < k → weightedHomogeneousComponent w k p = 0 := Nat.find_spec hex
  have hK'K : Nat.find hex ≤ K := Nat.find_min' hex fun k hk => hcomp p k (by omega)
  have key : ∀ m (b : Poly (n + 1)), tv ^ m * b ∈ IG → b ∈ IG := by
    intro m
    induction m with
    | zero => intro b hb; simpa using hb
    | succ m ih =>
      intro b hb
      apply ih
      apply tv_nzd hw hf hiso hwd hq hs
      rw [← mul_assoc, ← pow_succ']
      exact hb
  have hmem2 : homog w (Nat.find hex) p ∈ IG := by
    refine key (K - Nat.find hex) _ ?_
    rw [← homog_eq_mul hK'K hK', heq]
    exact hHmem
  have hmap : IG.map (evT 0 : Poly (n + 1) →ₐ[ℂ] Poly n) ≤ jacobianIdeal f := by
    rw [hIG, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, evT_homogPartial, C_0, zero_pow (by omega), zero_mul, add_zero]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hJ0 := hmap (Ideal.mem_map_of_mem _ hmem2)
  rw [evT_zero_homog] at hJ0
  have htop : weightedHomogeneousComponent w (Nat.find hex) p = 0 :=
    hVJ _ (hV p hpV _) hJ0
  have hall : ∀ k, Nat.find hex ≤ k → weightedHomogeneousComponent w k p = 0 := by
    intro k hk
    rcases Nat.eq_or_lt_of_le hk with h | h
    · rw [← h]; exact htop
    · exact hK' k h
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [← sum_weightedHomogeneousComponent w p]
    exact finsum_eq_zero_of_forall_eq_zero fun k => hall k (by omega)
  · exact absurd (fun k hk => hall k (by omega)) (Nat.find_min hex (Nat.sub_lt hpos one_pos))

/-- Spanning: if `V+J_f` is the whole ring and `V` is closed under homogeneous components, then `V+J_{f+q}` is also the whole ring. -/
theorem mem_sup_jacobianIdeal_add (hf : f.IsWeightedHomogeneous w d) (hwd : ∀ i, w i < d)
    (hq : q.IsWeightedHomogeneous w s) (hs : s < d) (V : Submodule ℂ (Poly n))
    (hV : ∀ p ∈ V, ∀ k, weightedHomogeneousComponent w k p ∈ V)
    (hVJ : ∀ p, p ∈ V ⊔ (jacobianIdeal f).restrictScalars ℂ) :
    ∀ p, p ∈ V ⊔ (jacobianIdeal (f + q)).restrictScalars ℂ := by
  set W := V ⊔ (jacobianIdeal (f + q)).restrictScalars ℂ with hW
  have hhom : ∀ k, ∀ p : Poly n, p.IsWeightedHomogeneous w k → p ∈ W := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro p hp
    obtain ⟨v, hv, j, hj, hvj⟩ := Submodule.mem_sup.1 (hVJ p)
    have hpk : p = weightedHomogeneousComponent w k v + weightedHomogeneousComponent w k j := by
      rw [← map_add, hvj, hp.weightedHomogeneousComponent_same]
    have hjk : weightedHomogeneousComponent w k j ∈ jacobianIdeal f :=
      weightedHomogeneousComponent_mem_jacobianIdeal hf hj k
    obtain ⟨h, hh1, hh2, hh3⟩ := jacobian_homog_decomp hf hjk
      (weightedHomogeneousComponent_isWeightedHomogeneous k j) (fun i => (hwd i).le)
    have hsplit : weightedHomogeneousComponent w k j =
        ∑ i, h i * pderiv i (f + q) - ∑ i, h i * pderiv i q := by
      rw [hh3, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_add]; ring
    rw [hpk, hsplit]
    refine W.add_mem (Submodule.mem_sup_left (hV v hv k)) (W.sub_mem ?_ ?_)
    · apply Submodule.mem_sup_right
      rw [Submodule.restrictScalars_mem]
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    · refine W.sum_mem fun i _ => ?_
      by_cases h1 : k + w i < d
      · rw [hh2 i h1, zero_mul]; exact W.zero_mem
      by_cases h2 : s < w i
      · rw [pderiv_eq_zero_of_lt hq i h2, mul_zero]; exact W.zero_mem
      exact ih (k + w i - d + (s - w i)) (by omega) _ ((hh1 i).mul (pderiv_isWH hq i).1)
  intro p
  rw [← sum_weightedHomogeneousComponent w p,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp p)]
  exact W.sum_mem fun k _ => hhom k _ (weightedHomogeneousComponent_isWeightedHomogeneous k p)

/-- Every ideal of `ℂ[x]` has a monomial-spanned vector-space complement. -/
theorem exists_monomial_complement (I : Ideal (Poly n)) :
    ∃ B : Set (Fin n →₀ ℕ), (∀ p ∈ restrictSupport ℂ B, p ∈ I → p = 0) ∧
      ∀ p, p ∈ restrictSupport ℂ B ⊔ I.restrictScalars ℂ := by
  classical
  let v : (Fin n →₀ ℕ) → Poly n ⧸ I := fun μ => Ideal.Quotient.mkₐ ℂ I (monomial μ 1)
  have hmono : ∀ (μ : Fin n →₀ ℕ) (c : ℂ),
      Ideal.Quotient.mkₐ ℂ I (monomial μ c) = c • v μ := by
    intro μ c
    rw [← map_smul, smul_monomial, smul_eq_mul, mul_one]
  have hexp : ∀ p : Poly n, Ideal.Quotient.mkₐ ℂ I p = ∑ μ ∈ p.support, coeff μ p • v μ := by
    intro p
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
    exact Finset.sum_congr rfl fun μ _ => hmono μ _
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℂ v
  refine ⟨Set.range a, ?_, ?_⟩
  · intro p hp hpI
    rw [restrictSupport, Finsupp.mem_supported] at hp
    set S := p.support.preimage a ha.injOn with hS
    have hsum : ∑ i ∈ S, coeff (a i) p • (v ∘ a) i = 0 := by
      have h0 : Ideal.Quotient.mkₐ ℂ I p = 0 := by
        rw [Ideal.Quotient.mkₐ_eq_mk]; exact Ideal.Quotient.eq_zero_iff_mem.2 hpI
      rw [hexp] at h0
      rw [← h0, hS]
      exact Finset.sum_preimage a p.support ha.injOn (fun μ => coeff μ p • v μ)
        (fun μ hμ hnot => absurd (hp hμ) hnot)
    have hz := linearIndependent_iff'.1 hli S (fun i => coeff (a i) p) hsum
    ext μ
    by_cases hμ : μ ∈ p.support
    · obtain ⟨i, rfl⟩ := hp hμ
      rw [coeff_zero]
      exact hz i (Finset.mem_preimage.2 hμ)
    · rw [coeff_zero]; simpa using hμ
  · intro p
    have hmem : Ideal.Quotient.mkₐ ℂ I p ∈ Submodule.span ℂ (Set.range (v ∘ a)) := by
      rw [hspan, hexp]
      exact Submodule.sum_mem _ fun μ _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨μ, rfl⟩)
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
    set u : Poly n := c.sum fun i r => monomial (a i) r with hudef
    have hu : u ∈ restrictSupport ℂ (Set.range a) := by
      refine Submodule.finsuppSum_mem _ _ _ _ fun i _ => ?_
      rw [restrictSupport, Finsupp.mem_supported]
      intro μ hμ
      have := support_monomial_subset hμ
      rw [Finset.mem_singleton] at this
      exact ⟨i, this.symm⟩
    have hmk : Ideal.Quotient.mkₐ ℂ I u = Ideal.Quotient.mkₐ ℂ I p := by
      rw [← hc, hudef, Finsupp.sum, map_sum, Finsupp.sum]
      exact Finset.sum_congr rfl fun i _ => hmono _ _
    refine Submodule.mem_sup.2 ⟨u, hu, p - u, ?_, by ring⟩
    rw [Submodule.restrictScalars_mem]
    rw [Ideal.Quotient.mkₐ_eq_mk] at hmk
    exact Ideal.Quotient.eq.1 hmk.symm

/-- For an isolated weighted homogeneous `f` and homogeneous `q` of lower degree, the polynomial Milnor algebras of `f+q` and `f` are finite dimensional with equal dimension. -/
theorem finrank_milnorAlgebra_add (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hiso : IsIsolatedSingularity f) (hwd : ∀ i, w i < d)
    (hq : q.IsWeightedHomogeneous w s) (hs : s < d) :
    IsIsolatedSingularity (f + q) ∧
      Module.finrank ℂ (MilnorAlgebra (f + q)) = Module.finrank ℂ (MilnorAlgebra f) := by
  obtain ⟨B, hB1, hB2⟩ := exists_monomial_complement (jacobianIdeal f)
  set V : Submodule ℂ (Poly n) := restrictSupport ℂ B with hVdef
  have hV : ∀ p ∈ V, ∀ k, weightedHomogeneousComponent w k p ∈ V := by
    intro p hp k
    rw [hVdef, restrictSupport, Finsupp.mem_supported] at hp ⊢
    intro μ hμ
    apply hp
    have h1 := (MvPolynomial.mem_support_iff (p := weightedHomogeneousComponent w k p)
      (m := μ)).1 (by simpa using hμ)
    rw [coeff_weightedHomogeneousComponent] at h1
    rw [Finset.mem_coe]
    exact MvPolynomial.mem_support_iff.2 fun h0 => h1 (by simp [h0])
  have h1 := eq_zero_of_mem_jacobianIdeal_add hw hf hiso hwd hq hs V hV hB1
  have h2 := mem_sup_jacobianIdeal_add hf hwd hq hs V hV hB2
  have hc : ∀ g : Poly n, (∀ p ∈ V, p ∈ jacobianIdeal g → p = 0) →
      (∀ p, p ∈ V ⊔ (jacobianIdeal g).restrictScalars ℂ) →
      IsCompl ((jacobianIdeal g).restrictScalars ℂ) V := by
    intro g hd ht
    constructor
    · rw [Submodule.disjoint_def]
      intro p hp hpV
      exact hd p hpV hp
    · rw [codisjoint_iff, eq_top_iff]
      intro p _
      rw [sup_comm]; exact ht p
  let e : ∀ g : Poly n, (∀ p ∈ V, p ∈ jacobianIdeal g → p = 0) →
      (∀ p, p ∈ V ⊔ (jacobianIdeal g).restrictScalars ℂ) → (MilnorAlgebra g ≃ₗ[ℂ] V) :=
    fun g hd ht => (Submodule.Quotient.restrictScalarsEquiv ℂ (jacobianIdeal g)).symm.trans
      (Submodule.quotientEquivOfIsCompl _ V (hc g hd ht))
  have ef := e f hB1 hB2
  have efq := e (f + q) h1 h2
  haveI : Module.Finite ℂ (MilnorAlgebra f) := hiso
  haveI : Module.Finite ℂ V := Module.Finite.equiv ef
  refine ⟨Module.Finite.equiv efq.symm, ?_⟩
  rw [efq.finrank_eq, ef.finrank_eq]

/-- For homogeneous `a` of weight `r`, with `2r<d`, and any `t`, the polynomial Milnor algebras of `f+t a²` and `f` have equal dimension. -/
theorem finrank_milnorAlgebra_add_sq (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hiso : IsIsolatedSingularity f) (hwd : ∀ i, w i < d) {a : Poly n} {r : ℕ}
    (ha : a.IsWeightedHomogeneous w r) (hr : 2 * r < d) (t : ℂ) :
    IsIsolatedSingularity (f + C t * a ^ 2) ∧
      Module.finrank ℂ (MilnorAlgebra (f + C t * a ^ 2)) = Module.finrank ℂ (MilnorAlgebra f) := by
  have hq : (C t * a ^ 2).IsWeightedHomogeneous w (2 * r) := by
    have h := (ha.pow 2).C_mul t
    rwa [smul_eq_mul] at h
  exact finrank_milnorAlgebra_add hw hf hiso hwd hq hr

/-- The analytic Milnor algebra `ℂ{x}/J_fℂ{x}` of a polynomial `f`. -/
def AnalyticMilnorAlgebra (f : Poly n) : Type := ConvSeries n ⧸ convIdeal (jacobianIdeal f)

instance (f : Poly n) : CommRing (AnalyticMilnorAlgebra f) :=
  inferInstanceAs (CommRing (ConvSeries n ⧸ convIdeal (jacobianIdeal f)))

instance (f : Poly n) : Algebra ℂ (AnalyticMilnorAlgebra f) :=
  inferInstanceAs (Algebra ℂ (ConvSeries n ⧸ convIdeal (jacobianIdeal f)))

/-- The local Milnor number at the origin, `μ(f)=dim_ℂ ℂ{x}/J_fℂ{x}`. -/
noncomputable def milnorNumber (f : Poly n) : ℕ := Module.finrank ℂ (AnalyticMilnorAlgebra f)

/-- The weighted homogeneous instance of Lemma 3.3: if `a` has degree `r`, `2r<d`, is independent of the selected heavy variables and belongs to the radical of their partial derivatives, then `f+t a²` has constant local Milnor number at the origin. -/
theorem milnorNumber_add_sq (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hcrit : HasIsolatedCriticalPoint f) (hwd : ∀ i, w i < d) {a : Poly n} {r : ℕ}
    (ha : a.IsWeightedHomogeneous w r) (hr : 2 * r < d) (Y : Set (Fin n))
    (haY : ∀ i ∈ Y, pderiv i a = 0)
    (haJ : a ∈ (Ideal.span ((fun i => pderiv i f) '' Y)).radical) (t : ℂ) :
    Module.Finite ℂ (AnalyticMilnorAlgebra (f + C t * a ^ 2)) ∧
      milnorNumber (f + C t * a ^ 2) = milnorNumber f := by
  have hiso := isIsolatedSingularity_of_hasIsolatedCriticalPoint hw hf hcrit
  obtain ⟨hfin, hrank⟩ := finrank_milnorAlgebra_add_sq hw hf hiso hwd ha hr t
  obtain ⟨-, ⟨et⟩⟩ := isIsolatedSingularity_add_sq hw hf hcrit a Y haY haJ t
  have et' : MilnorAlgebra (f + C t * a ^ 2) ≃ₐ[ℂ] AnalyticMilnorAlgebra (f + C t * a ^ 2) := et
  have e0 : MilnorAlgebra f ≃ₐ[ℂ] AnalyticMilnorAlgebra f := milnorAlgebraEquivAnalytic hw hf hcrit
  haveI : Module.Finite ℂ (MilnorAlgebra (f + C t * a ^ 2)) := hfin
  refine ⟨Module.Finite.equiv et'.toLinearEquiv, ?_⟩
  rw [milnorNumber, milnorNumber, ← et'.toLinearEquiv.finrank_eq,
    ← e0.toLinearEquiv.finrank_eq, hrank]

section SquareDeformationHyp

variable {n : ℕ} {w : Fin n → ℕ} {d : ℕ} {g : Poly n}

/-- The square deformation used in Theorem 3.6 satisfies the required first-order consequence's hypotheses, by the weighted homogeneous instance of Lemma 3.3. -/
theorem squareDeformation_hyp (H : Setup w d g) {r : ℕ} {a : Poly n}
    (ha : a.IsWeightedHomogeneous w r) (hr : 3 * r < d)
    (haI : a ∈ (partialIdeal w g r).radical) (t : ℂ) :
    HasIsolatedCriticalPoint (g + C t * a ^ 2) ∧ eval 0 (g + C t * a ^ 2) = 0 ∧
      milnorNumber (g + C t * a ^ 2) = milnorNumber g := by
  have hwd : ∀ i, w i < d := fun i => by have := H.big i; have := H.pos i; omega
  have haY : ∀ i ∈ {i | r < w i}, pderiv i a = 0 := fun i hi => pderiv_eq_zero_of_lt ha i hi
  -- The polynomial `a` vanishes at the origin.
  have ha0 : eval 0 a = 0 := by
    obtain ⟨N, hN⟩ := haI
    have hle : partialIdeal w g r ≤ RingHom.ker (eval (0 : Fin n → ℂ)) := by
      rw [partialIdeal, Ideal.span_le]
      rintro _ ⟨i, -, rfl⟩
      exact eval_zero_of_isWH_pos (pderiv_f_isWH H.hom i) (by have := hwd i; omega)
    have := hle hN
    rw [RingHom.mem_ker, map_pow] at this
    exact pow_eq_zero_iff'.1 this |>.1
  -- For every `t`, the origin is the only critical point of `g+t a²`.
  have hcrit : ∀ t : ℂ, HasIsolatedCriticalPoint (g + C t * a ^ 2) := by
    intro t
    refine ⟨fun i => ?_, Set.univ, Filter.univ_mem, fun x _ hx => ?_⟩
    · rw [pderiv_add_sq, map_add, map_mul (eval 0) (C (2 * t)), map_mul (eval 0) a, ha0,
        zero_mul, mul_zero, add_zero]
      exact eval_zero_of_isWH_pos (pderiv_f_isWH H.hom i) (by have := hwd i; omega)
    · have hrad := radical_jacobianIdeal_add_sq g a {i | r < w i} haY haI t
      refine H.common_zero x fun i => ?_
      have hmem : pderiv i g ∈ (jacobianIdeal (g + C t * a ^ 2)).radical := by
        rw [hrad]; exact Ideal.le_radical (Ideal.subset_span ⟨i, rfl⟩)
      obtain ⟨N, hN⟩ := hmem
      have := mem_jac_eval_zero hx hN
      rw [map_pow] at this
      exact pow_eq_zero_iff'.1 this |>.1
  have hcrit0 : HasIsolatedCriticalPoint g := by simpa using hcrit 0
  refine ⟨hcrit t, ?_, ?_⟩
  · rw [map_add, map_mul, map_pow, ha0, eval_zero_of_isWH_pos H.hom (by omega)]
    simp
  · exact (milnorNumber_add_sq H.pos H.hom hcrit0 hwd ha (by omega) {i | r < w i} haY haI t).2

end SquareDeformationHyp

end Yau
