import RequestProject.Yau.CommAlg.Koszul
import RequestProject.Yau.Sec3_Radical.MilnorConstancy
import RequestProject.Yau.Appendix.Syzygy

/-!
# Regular sequences with higher-weight perturbations

Let `g` be isolated and weighted homogeneous of degree `d`, and let every term
of `R` have weight greater than `d`. For `G=g+R`, the lowest-weight relations
among its partial derivatives are controlled by the regular sequence of the
partial derivatives of `g`.
Approximation and Koszul syzygy reduction show that, for sufficiently large `T`,
`dim S/(J_G+F^T) = dim S/J_g`. The analytic local consequence is proved in
`LemmaC1Local.lean`.
-/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ} {w : Fin n → ℕ} {d : ℕ} {g R : Poly n}

/-! ## Natural-number indexing of the partial derivatives -/

/-- The partial derivatives indexed by natural numbers, with zero outside the index range. -/
def partialSeq (g : Poly n) (k : ℕ) : Poly n := if h : k < n then pderiv ⟨k, h⟩ g else 0

lemma partialSeq_image_Iio (g : Poly n) {k : ℕ} (hk : k ≤ n) :
    partialSeq g '' Set.Iio k = (fun i => pderiv i g) '' {i : Fin n | (i : ℕ) < k} := by
  ext y; constructor
  · rintro ⟨i, hi, rfl⟩
    have hin : i < n := lt_of_lt_of_le hi hk
    exact ⟨⟨i, hin⟩, hi, by simp [partialSeq, hin]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by simp [partialSeq, i.2]⟩

lemma partialSeq_reg (hw : ∀ i, 0 < w i) (hg : g.IsWeightedHomogeneous w d)
    (hiso : IsIsolatedSingularity g) (hwd : ∀ i, w i < d) :
    ∀ k < n, ∀ b : Poly n, partialSeq g k * b ∈ Ideal.span (partialSeq g '' Set.Iio k) →
      b ∈ Ideal.span (partialSeq g '' Set.Iio k) := by
  intro k hk b hb
  have hreg := (isWeaklyRegular_self_iff _).1
    (isWeaklyRegular_partials hw hg hiso hwd (List.Perm.refl (partialsList g)))
  have hlen : k < (partialsList g).length := by simpa [partialsList] using hk
  have hget : (partialsList g)[k] = partialSeq g k := by
    simp [partialsList, partialSeq, hk]
  rw [partialSeq_image_Iio g hk.le, ← ofList_partialsList_take] at hb ⊢
  exact hreg k hlen b (by rw [hget]; exact hb)

/-- Koszul relations for the partial derivatives: a homogeneous syzygy has antisymmetric homogeneous coefficients of the corresponding degrees, with negative-degree terms zero. -/
theorem koszul_partials (hw : ∀ i, 0 < w i) (hg : g.IsWeightedHomogeneous w d)
    (hiso : IsIsolatedSingularity g) (hwd : ∀ i, w i < d) (q : ℕ) (b : Fin n → Poly n)
    (hb : ∀ i, (b i).IsWeightedHomogeneous w (q - (d - w i)))
    (hb0 : ∀ i, q < d - w i → b i = 0) (hsum : ∑ i, b i * pderiv i g = 0) :
    ∃ c : Fin n → Fin n → Poly n, (∀ i j, c i j = -c j i) ∧
      (∀ i j, (c i j).IsWeightedHomogeneous w (q - (d - w i) - (d - w j))) ∧
      (∀ i j, q < (d - w i) + (d - w j) → c i j = 0) ∧
      ∀ i, b i = ∑ j, c i j * pderiv j g := by
  classical
  set a : ℕ → ℕ := fun k => if h : k < n then d - w ⟨k, h⟩ else 0 with ha
  set bN : ℕ → Poly n := fun k => if h : k < n then b ⟨k, h⟩ else 0 with hbN
  have hgN : ∀ k, (partialSeq g k).IsWeightedHomogeneous w (a k) := by
    intro k
    by_cases h : k < n
    · simp only [partialSeq, h, dif_pos, ha]; exact pderiv_f_isWH hg _
    · simp only [partialSeq, h, dif_neg, not_false_eq_true]; exact isWeightedHomogeneous_zero _ _ _
  obtain ⟨c, hskew, hhom, hzero, hc⟩ := koszul_syzygy_homog (partialSeq g) a n hgN
    (partialSeq_reg hw hg hiso hwd) q bN
    (fun k => by
      by_cases h : k < n
      · simp only [hbN, ha, h, dif_pos]; exact hb _
      · simp only [hbN, h, dif_neg, not_false_eq_true]; exact isWeightedHomogeneous_zero _ _ _)
    (fun k hk => by
      by_cases h : k < n
      · simp only [hbN, h, dif_pos]; exact hb0 _ (by simpa [ha, h] using hk)
      · simp [hbN, h])
    (by
      rw [← Fin.sum_univ_eq_sum_range (fun k => bN k * partialSeq g k) n]
      simpa [hbN, partialSeq] using hsum)
  refine ⟨fun i j => c i j, fun i j => hskew i j, fun i j => ?_, fun i j h => hzero i j ?_,
    fun i => ?_⟩
  · simpa [ha, i.2, j.2] using hhom i j
  · simpa [ha, i.2, j.2] using h
  · have := hc i i.2
    rw [← Fin.sum_univ_eq_sum_range (fun k => c i k * partialSeq g k) n] at this
    simpa [hbN, partialSeq] using this

/-! ## Approximation -/

lemma pderiv_R_mem (hwd : ∀ i, w i < d) (hR : R ∈ highIdeal w (d + 1)) (i : Fin n) :
    pderiv i R ∈ highIdeal w (d - w i + 1) := by
  have := pderiv_mem_highIdeal hR i
  rwa [show d + 1 - w i = d - w i + 1 by have := hwd i; omega] at this

lemma mul_pderiv_R_mem (hwd : ∀ i, w i < d) (hR : R ∈ highIdeal w (d + 1)) {A : Poly n} {e : ℕ}
    (hA : A ∈ highIdeal w e) (i : Fin n) : A * pderiv i R ∈ highIdeal w (e + (d - w i) + 1) := by
  have := mul_mem_highIdeal hA (pderiv_R_mem hwd hR i)
  rwa [← add_assoc] at this

/-- A degree-`v` homogeneous element of `J_g` differs from an element of `J_{g+R}` by terms of weight at least `v+1`. -/
lemma approx_step (hg : g.IsWeightedHomogeneous w d) (hwd : ∀ i, w i < d)
    (hR : R ∈ highIdeal w (d + 1)) {p : Poly n} {v : ℕ} (hp : p.IsWeightedHomogeneous w v)
    (hpJ : p ∈ jacobianIdeal g) :
    ∃ q ∈ jacobianIdeal (g + R), p - q ∈ highIdeal w (v + 1) := by
  obtain ⟨h, hh, hh0, hsum⟩ := span_homog_decomp (fun i => pderiv i g) (fun i => d - w i)
    (pderiv_f_isWH hg) hpJ hp
  refine ⟨∑ i, h i * pderiv i (g + R),
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩), ?_⟩
  have : p - ∑ i, h i * pderiv i (g + R) = -∑ i, h i * pderiv i R := by
    rw [hsum]; simp only [map_add, mul_add, Finset.sum_add_distrib]; ring
  rw [this]
  refine (Ideal.neg_mem_iff _).2 (Ideal.sum_mem _ fun i _ => ?_)
  by_cases hvi : v < d - w i
  · rw [hh0 i hvi, zero_mul]; exact Ideal.zero_mem _
  · have := mul_pderiv_R_mem hwd hR (isWH_mem_highIdeal (hh i) le_rfl) i
    rwa [show v - (d - w i) + (d - w i) = v by omega] at this

/-- If `F^{T₀} ⊆ J_g`, each element of `F^m`, for `m ≥ T₀`, is congruent to an element of `J_{g+R}` modulo `F^{m+1}`. -/
lemma approx_one (hg : g.IsWeightedHomogeneous w d) (hwd : ∀ i, w i < d)
    (hR : R ∈ highIdeal w (d + 1)) {T₀ : ℕ} (hT₀ : highIdeal w T₀ ≤ jacobianIdeal g)
    {m : ℕ} (hm : T₀ ≤ m) {p : Poly n} (hp : p ∈ highIdeal w m) :
    ∃ q ∈ jacobianIdeal (g + R), p - q ∈ highIdeal w (m + 1) := by
  classical
  have key : ∀ s : Finset ℕ, ∃ q ∈ jacobianIdeal (g + R),
      ∑ v ∈ s, weightedHomogeneousComponent w v p - q ∈ highIdeal w (m + 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, Ideal.zero_mem _, by simp⟩
    | insert v s hv ih =>
      obtain ⟨q, hq, hpq⟩ := ih
      by_cases hvm : v < m
      · refine ⟨q, hq, ?_⟩
        rw [Finset.sum_insert hv, weightedHomogeneousComponent_eq_zero_of_mem_highIdeal hp hvm,
          zero_add]
        exact hpq
      · have hcJ : weightedHomogeneousComponent w v p ∈ jacobianIdeal g :=
          hT₀ (isWH_mem_highIdeal (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
            (by omega))
        obtain ⟨q', hq', hpq'⟩ := approx_step hg hwd hR
          (weightedHomogeneousComponent_isWeightedHomogeneous v p) hcJ
        refine ⟨q' + q, Ideal.add_mem _ hq' hq, ?_⟩
        rw [Finset.sum_insert hv]
        have : weightedHomogeneousComponent w v p + ∑ x ∈ s, weightedHomogeneousComponent w x p -
            (q' + q) = (weightedHomogeneousComponent w v p - q') +
              (∑ x ∈ s, weightedHomogeneousComponent w x p - q) := by ring
        rw [this]
        exact Ideal.add_mem _ (highIdeal_mono (by omega) hpq') hpq
  obtain ⟨q, hq, hpq⟩ := key (weightedHomogeneousComponent_finsupp (w := w) p).toFinset
  refine ⟨q, hq, ?_⟩
  have : p = ∑ v ∈ (weightedHomogeneousComponent_finsupp (w := w) p).toFinset,
      weightedHomogeneousComponent w v p := by
    conv_lhs => rw [← sum_weightedHomogeneousComponent w p]
    exact finsum_eq_sum _ _
  rw [this]; exact hpq

lemma approx (hg : g.IsWeightedHomogeneous w d) (hwd : ∀ i, w i < d)
    (hR : R ∈ highIdeal w (d + 1)) {T₀ : ℕ} (hT₀ : highIdeal w T₀ ≤ jacobianIdeal g) (k : ℕ) :
    ∀ m, T₀ ≤ m → ∀ p ∈ highIdeal w m,
      ∃ q ∈ jacobianIdeal (g + R), p - q ∈ highIdeal w (m + k) := by
  induction k with
  | zero => intro m _ p hp; exact ⟨0, Ideal.zero_mem _, by simpa using hp⟩
  | succ k ih =>
    intro m hm p hp
    obtain ⟨q, hq, hpq⟩ := approx_one hg hwd hR hT₀ hm hp
    obtain ⟨q', hq', hpq'⟩ := ih (m + 1) (by omega) _ hpq
    refine ⟨q + q', Ideal.add_mem _ hq hq', ?_⟩
    rw [show p - (q + q') = p - q - q' by ring, show m + (k + 1) = m + 1 + k by ring]
    exact hpq'

/-! ## Syzygy reduction -/

/-- The quadratic form of an antisymmetric matrix is zero: `∑ c_{ij}x_jx_i=0`. -/
lemma skew_sum_eq_zero {c : Fin n → Fin n → Poly n} (hc : ∀ i j, c i j = -c j i)
    (x : Fin n → Poly n) : ∑ i, ∑ j, c i j * x j * x i = 0 := by
  have h : ∑ i, ∑ j, c i j * x j * x i = -∑ i, ∑ j, c i j * x j * x i := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc j i]; ring
  have h2 : (2 : Poly n) * ∑ i, ∑ j, c i j * x j * x i = 0 := by linear_combination h
  exact (mul_eq_zero.1 h2).resolve_left two_ne_zero

/-- For homogeneous `c` of degree `e`, the degree-`e+a_l` component of `c ∂_l G` is `c ∂_l g`, and no lower-weight term occurs. -/
lemma mul_pderiv_G (hg : g.IsWeightedHomogeneous w d) (hwd : ∀ i, w i < d)
    (hR : R ∈ highIdeal w (d + 1)) {c : Poly n} {e : ℕ} (hc : c.IsWeightedHomogeneous w e)
    (l : Fin n) :
    weightedHomogeneousComponent w (e + (d - w l)) (c * pderiv l (g + R)) = c * pderiv l g ∧
      c * pderiv l (g + R) ∈ highIdeal w (e + (d - w l)) := by
  have h1 : (c * pderiv l g).IsWeightedHomogeneous w (e + (d - w l)) :=
    hc.mul (pderiv_f_isWH hg l)
  have h2 := mul_pderiv_R_mem hwd hR (isWH_mem_highIdeal hc le_rfl) l
  rw [map_add, mul_add]
  refine ⟨?_, Ideal.add_mem _ (isWH_mem_highIdeal h1 le_rfl) (highIdeal_mono (by omega) h2)⟩
  rw [map_add, h1.weightedHomogeneousComponent_same,
    weightedHomogeneousComponent_eq_zero_of_mem_highIdeal h2 (by omega), add_zero]

lemma split_sum_G (A : Fin n → Poly n) (h : Poly n) :
    ∑ j, A j * pderiv j (g + R) + h = ∑ j, A j * pderiv j g + (∑ j, A j * pderiv j R + h) := by
  simp only [map_add, mul_add, Finset.sum_add_distrib]; ring

lemma comp_sum_R_eq_zero (hwd : ∀ i, w i < d) (hR : R ∈ highIdeal w (d + 1)) {u : ℕ}
    {A : Fin n → Poly n} (hA : ∀ j, A j ∈ highIdeal w (u - (d - w j))) :
    weightedHomogeneousComponent w u (∑ j, A j * pderiv j R) = 0 :=
  weightedHomogeneousComponent_eq_zero_of_mem_highIdeal (Ideal.sum_mem _ fun j _ =>
    highIdeal_mono (by omega) (mul_pderiv_R_mem hwd hR (hA j) j)) (Nat.lt_succ_self u)

/-- Syzygy reduction: if `p = ∑ A_j ∂_j G + h`, with `h ∈ F^T`, `p ∈ F^v`, and `v<T`, its degree-`v` component belongs to `J_g`. The induction cancels the lowest coefficient terms using Koszul relations. -/
theorem init_mem (hw : ∀ i, 0 < w i) (hg : g.IsWeightedHomogeneous w d)
    (hiso : IsIsolatedSingularity g) (hwd : ∀ i, w i < d) (hR : R ∈ highIdeal w (d + 1))
    {T : ℕ} (k : ℕ) :
    ∀ (A : Fin n → Poly n) (h : Poly n) (v : ℕ), v < T → h ∈ highIdeal w T →
      (∀ j, A j ∈ highIdeal w (v - k - (d - w j))) →
      ∑ j, A j * pderiv j (g + R) + h ∈ highIdeal w v →
      weightedHomogeneousComponent w v (∑ j, A j * pderiv j (g + R) + h) ∈ jacobianIdeal g := by
  classical
  induction k with
  | zero =>
    intro A h v hvT hh hA _
    rw [split_sum_G, map_add, map_add, comp_sum_R_eq_zero hwd hR (fun j => by simpa using hA j),
      weightedHomogeneousComponent_eq_zero_of_mem_highIdeal hh hvT, add_zero, add_zero]
    exact weightedHomogeneousComponent_mem_jacobianIdeal hg
      (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)) v
  | succ k ih =>
    intro A h v hvT hh hA hp
    by_cases hvk : v ≤ k
    · exact ih A h v hvT hh (fun j => by rw [show v - k - (d - w j) = 0 by omega]; simp
        [highIdeal_zero]) hp
    set q := v - (k + 1) with hq
    set b : Fin n → Poly n := fun j =>
      if d - w j ≤ q then weightedHomogeneousComponent w (q - (d - w j)) (A j) else 0 with hbdef
    have hbhom : ∀ j, (b j).IsWeightedHomogeneous w (q - (d - w j)) := by
      intro j; simp only [hbdef]; split_ifs
      · exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
      · exact isWeightedHomogeneous_zero _ _ _
    have hb0 : ∀ j, q < d - w j → b j = 0 := fun j hj => by
      simp only [hbdef]; rw [if_neg (by omega)]
    have hcompg : ∀ j, weightedHomogeneousComponent w q (A j * pderiv j g) = b j * pderiv j g := by
      intro j
      rw [weightedHomogeneousComponent_mul_of_right _ _ (d - w j) q (pderiv_f_isWH hg j)]
      simp only [hbdef]; split_ifs <;> simp
    have hsum : ∑ j, b j * pderiv j g = 0 := by
      have h0 : weightedHomogeneousComponent w q (∑ j, A j * pderiv j (g + R) + h) = 0 :=
        weightedHomogeneousComponent_eq_zero_of_mem_highIdeal hp (by omega)
      rw [split_sum_G, map_add, map_add, comp_sum_R_eq_zero hwd hR (fun j => by
          have := hA j; rwa [show v - (k + 1) - (d - w j) = q - (d - w j) by omega] at this),
        weightedHomogeneousComponent_eq_zero_of_mem_highIdeal hh (by omega), add_zero, add_zero,
        map_sum] at h0
      rw [← h0]
      exact Finset.sum_congr rfl fun j _ => (hcompg j).symm
    obtain ⟨c, hskew, hchom, hc0, hc⟩ := koszul_partials hw hg hiso hwd q b hbhom hb0 hsum
    set A' : Fin n → Poly n := fun j => A j - ∑ l, c j l * pderiv l (g + R) with hA'def
    have hsame : ∑ j, A' j * pderiv j (g + R) = ∑ j, A j * pderiv j (g + R) := by
      have := skew_sum_eq_zero hskew (fun l => pderiv l (g + R))
      simp only [hA'def, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
      rw [this, sub_zero]
    -- Properties of `c_{jl} ∂_l G`.
    have hcl : ∀ j l, d - w j ≤ q →
        weightedHomogeneousComponent w (q - (d - w j)) (c j l * pderiv l (g + R)) =
            c j l * pderiv l g ∧
          c j l * pderiv l (g + R) ∈ highIdeal w (q - (d - w j)) := by
      intro j l hj
      by_cases hjl : q < (d - w j) + (d - w l)
      · rw [hc0 j l hjl]; simp
      · have := mul_pderiv_G hg hwd hR (hchom j l) l
        rwa [show q - (d - w j) - (d - w l) + (d - w l) = q - (d - w j) by omega] at this
    have hA' : ∀ j, A' j ∈ highIdeal w (v - k - (d - w j)) := by
      intro j
      by_cases hj : d - w j ≤ q
      · have hmem : A' j ∈ highIdeal w (q - (d - w j)) := by
          refine Ideal.sub_mem _ ?_ (Ideal.sum_mem _ fun l _ => (hcl j l hj).2)
          have := hA j; rwa [show v - (k + 1) - (d - w j) = q - (d - w j) by omega] at this
        have := mem_highIdeal_succ hmem (by
          simp only [hA'def, map_sub, map_sum, fun l => (hcl j l hj).1]
          rw [← hc j]; simp only [hbdef]; rw [if_pos hj, sub_self])
        rwa [show q - (d - w j) + 1 = v - k - (d - w j) by omega] at this
      · rw [show v - k - (d - w j) = 0 by omega, highIdeal_zero]; trivial
    have key := ih A' h v hvT hh hA' (by rwa [hsame])
    rwa [hsame] at key

/-! ## Equality of dimensions -/

/-- A vector-space complement `V` of `I` is isomorphic to `ℂ[x]/I`. -/
def quotEquivOfComplement (I : Ideal (Poly n)) (V : Submodule ℂ (Poly n))
    (hd : ∀ p ∈ V, p ∈ I → p = 0) (ht : ∀ p, p ∈ V ⊔ I.restrictScalars ℂ) :
    (Poly n ⧸ I) ≃ₗ[ℂ] V :=
  (Submodule.Quotient.restrictScalarsEquiv ℂ I).symm.trans
    (Submodule.quotientEquivOfIsCompl _ V
      ⟨Submodule.disjoint_def.2 fun p hp hpV => hd p hpV hp,
        codisjoint_iff.2 (eq_top_iff.2 fun p _ => by rw [sup_comm]; exact ht p)⟩)

/-- A monomial-spanned subspace is closed under homogeneous components. -/
lemma restrictSupport_component_mem {B : Set (Fin n →₀ ℕ)} {p : Poly n}
    (hp : p ∈ restrictSupport ℂ B) (k : ℕ) :
    weightedHomogeneousComponent w k p ∈ restrictSupport ℂ B := by
  classical
  rw [restrictSupport, Finsupp.mem_supported] at hp ⊢
  intro μ hμ
  apply hp
  have h1 := (MvPolynomial.mem_support_iff (p := weightedHomogeneousComponent w k p)
    (m := μ)).1 (by simpa using hμ)
  rw [coeff_weightedHomogeneousComponent] at h1
  rw [Finset.mem_coe]
  exact MvPolynomial.mem_support_iff.2 fun h => h1 (by simp [h])

/-- If `F^{T₀} ⊆ J_g` and `T ≥ T₀`, then `ℂ[x]/(J_{g+R}+F^T)` is finite dimensional of dimension `dim ℂ[x]/J_g`. Syzygy reduction gives independence of a monomial complement, and approximation gives spanning. -/
theorem finrank_quot_high (hw : ∀ i, 0 < w i) (hg : g.IsWeightedHomogeneous w d)
    (hiso : IsIsolatedSingularity g) (hwd : ∀ i, w i < d) (hR : R ∈ highIdeal w (d + 1))
    {T₀ : ℕ} (hT₀ : highIdeal w T₀ ≤ jacobianIdeal g) {T : ℕ} (hT : T₀ ≤ T) :
    Module.Finite ℂ (Poly n ⧸ (jacobianIdeal (g + R) ⊔ highIdeal w T)) ∧
      Module.finrank ℂ (Poly n ⧸ (jacobianIdeal (g + R) ⊔ highIdeal w T)) =
        Module.finrank ℂ (MilnorAlgebra g) := by
  classical
  obtain ⟨B, hB1, hB2⟩ := exists_monomial_complement (jacobianIdeal g)
  set V : Submodule ℂ (Poly n) := restrictSupport ℂ B with hVdef
  set I : Ideal (Poly n) := jacobianIdeal (g + R) ⊔ highIdeal w T with hIdef
  have hV : ∀ p ∈ V, ∀ k, weightedHomogeneousComponent w k p ∈ V :=
    fun p hp k => restrictSupport_component_mem hp k
  -- `V ∩ I = 0`
  have hdisj : ∀ p ∈ V, p ∈ I → p = 0 := by
    have key : ∀ k, ∀ p ∈ V, p ∈ I → p ∈ highIdeal w (T₀ - k) → p = 0 := by
      intro k
      induction k with
      | zero => intro p hp _ hh; exact hB1 p hp (hT₀ (by simpa using hh))
      | succ k ih =>
        intro p hpV hpI hh
        by_cases hk : T₀ ≤ k
        · exact ih p hpV hpI (by rwa [show T₀ - k = T₀ - (k + 1) by omega])
        set v := T₀ - (k + 1) with hv
        obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hpI
        obtain ⟨A, hA⟩ := Ideal.mem_span_range_iff_exists_fun.1 hy
        have hcomp := init_mem hw hg hiso hwd hR v A z v (by omega) hz
          (fun j => by rw [show v - v - (d - w j) = 0 by omega, highIdeal_zero]; trivial)
          (by rw [hA, hyz]; exact hh)
        rw [hA, hyz] at hcomp
        have h0 : weightedHomogeneousComponent w v p = 0 := hB1 _ (hV _ hpV v) hcomp
        have := mem_highIdeal_succ hh h0
        exact ih p hpV hpI (by rwa [show v + 1 = T₀ - k by omega] at this)
    intro p hp hI
    exact key T₀ p hp hI (by rw [Nat.sub_self, highIdeal_zero]; trivial)
  -- `V + I = ℂ[x]`
  have hspan : ∀ p, p ∈ V ⊔ I.restrictScalars ℂ := by
    have key : ∀ k, ∀ p ∈ highIdeal w (T₀ - k), p ∈ V ⊔ I.restrictScalars ℂ := by
      intro k
      induction k with
      | zero =>
        intro p hp
        obtain ⟨q, hq, hpq⟩ := approx hg hwd hR hT₀ T T₀ le_rfl p (by simpa using hp)
        refine Submodule.mem_sup_right ?_
        show p ∈ I
        rw [show p = q + (p - q) by ring]
        exact Ideal.add_mem _ (Ideal.mem_sup_left hq)
          (Ideal.mem_sup_right (highIdeal_mono (by omega) hpq))
      | succ k ih =>
        intro p hp
        by_cases hk : T₀ ≤ k
        · exact ih p (by rwa [show T₀ - k = T₀ - (k + 1) by omega])
        set v := T₀ - (k + 1) with hv
        obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hB2 (weightedHomogeneousComponent w v p))
        have hcv : weightedHomogeneousComponent w v p =
            weightedHomogeneousComponent w v a + weightedHomogeneousComponent w v b := by
          rw [← map_add, hab]
          exact ((weightedHomogeneousComponent_isWeightedHomogeneous v p).weightedHomogeneousComponent_same).symm
        have hbJ : weightedHomogeneousComponent w v b ∈ jacobianIdeal g :=
          weightedHomogeneousComponent_mem_jacobianIdeal hg hb v
        obtain ⟨q, hq, hbq⟩ := approx_step hg hwd hR
          (weightedHomogeneousComponent_isWeightedHomogeneous v b) hbJ
        have hrest : (weightedHomogeneousComponent w v b - q) +
            (p - weightedHomogeneousComponent w v p) ∈ highIdeal w (T₀ - k) := by
          rw [show T₀ - k = v + 1 by omega]
          exact Ideal.add_mem _ hbq (sub_component_mem_highIdeal hp)
        have hdecomp : p = weightedHomogeneousComponent w v a + q +
            ((weightedHomogeneousComponent w v b - q) +
              (p - weightedHomogeneousComponent w v p)) := by
          rw [hcv]; ring
        rw [hdecomp]
        refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.mem_sup_left (hV a ha v))
          (Submodule.mem_sup_right (Ideal.mem_sup_left hq))) (ih _ hrest)
    intro p
    exact key T₀ p (by rw [Nat.sub_self, highIdeal_zero]; trivial)
  have e1 := quotEquivOfComplement I V hdisj hspan
  have e2 := quotEquivOfComplement (jacobianIdeal g) V hB1 hB2
  haveI : Module.Finite ℂ (MilnorAlgebra g) := hiso
  haveI : Module.Finite ℂ V := Module.Finite.equiv e2
  exact ⟨Module.Finite.equiv e1.symm, by rw [e1.finrank_eq, e2.finrank_eq]⟩

end Yau
