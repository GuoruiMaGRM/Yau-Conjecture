import RequestProject.Yau.LowDim.SmallWeights

/-!
# Quadratic dependence on the heavy variables

The large-degree argument of Theorem 3.6 uses only that `f` is quadratic in
the variables of weight greater than `r`. The predicate `QuadraticIn` records
the vanishing of all third partial derivatives in those variables.
The Hessian argument then proves the radical conclusion for any such `r`.
Combining it with the restriction and single-heavy-variable criteria gives
a degree-by-degree criterion for the main theorem.
-/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ} {w : Fin n → ℕ} {d : ℕ} {f : Poly n}

/-- The polynomial is at most quadratic in the variables in `Y`: all third partial derivatives in those directions vanish. -/
def QuadraticIn (Y : Finset (Fin n)) (f : Poly n) : Prop :=
  ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, pderiv a (pderiv b (pderiv c f)) = 0

/-- A degree-`d` weighted homogeneous polynomial is at most quadratic in variables of weight greater than `d/3`. -/
lemma quadraticIn_of_gt_third (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (Y : Finset (Fin n)) (hY : ∀ i ∈ Y, d < 3 * w i) : QuadraticIn Y f := by
  intro a ha b hb c hc
  have := hY a ha; have := hY b hb; have := hY c hc
  exact pderiv3_zero hf a b c (by omega) (hw a)

/-- The first-order expansion of `∂_a f` along `Y`, using the Hessian matrix, for a polynomial quadratic in `Y`. -/
lemma pderiv_expand_of_quadratic (Y : Finset (Fin n)) (hQ : QuadraticIn Y f)
    (x0 y : Fin n → ℂ) (hy : ∀ b, y b ≠ 0 → b ∈ Y) {a : Fin n} (ha : a ∈ Y) :
    eval (x0 + y) (pderiv a f) =
      eval x0 (pderiv a f) + ∑ c, ((hessY Y f).map (eval x0)) a c * y c := by
  rw [taylor1 _ x0 y (fun b c hb hc => by
    rw [pderiv_comm' c a]
    exact hQ b (hy b hb) a ha c (hy c hc))]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : y c = 0
  · simp [hc]
  · simp [hessY, ha, hy c hc, mul_comm]

/-- The Hessian block has nonzero determinant when `f` is at most quadratic in `Y`, extending Lemma 3.1. -/
lemma Setup.hessY_det_ne_zero_of_quadratic (H : Setup w d f) (Y : Finset (Fin n))
    (hQ : QuadraticIn Y f) : (hessY Y f).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨k, hk0, hk⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set Hm := hessY Y f with hHm
  have hkrow : ∀ a, ∑ b, Hm a b * k b = 0 := fun a => by
    have := congrFun hk a; simpa [Matrix.mulVec, dotProduct] using this
  have hkY : ∀ a, a ∉ Y → k a = 0 := by
    intro a ha; have := hkrow a; simpa [hHm, hessY, ha] using this
  have hid : ∀ j, ∑ a, ∑ b, k a * pderiv j (Hm a b) * k b = 0 := by
    intro j
    have h1 : ∀ a, ∑ b, (pderiv j (Hm a b) * k b + Hm a b * pderiv j (k b)) = 0 := by
      intro a
      have := congrArg (pderiv j) (hkrow a)
      rw [map_sum, map_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
    have h3 : ∑ a, k a * ∑ b, Hm a b * pderiv j (k b) = 0 := by
      have : ∑ a, k a * ∑ b, Hm a b * pderiv j (k b) =
          ∑ b, (∑ a, Hm b a * k a) * pderiv j (k b) := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
        rw [show Hm a b = Hm b a from hessY_symm Y f a b]; ring
      rw [this]; exact Finset.sum_eq_zero fun b _ => by rw [hkrow b, zero_mul]
    have h2 : ∑ a, k a * ∑ b, (pderiv j (Hm a b) * k b + Hm a b * pderiv j (k b)) = 0 := by
      exact Finset.sum_eq_zero fun a _ => by rw [h1 a, mul_zero]
    simp_rw [Finset.mul_sum, mul_add, Finset.sum_add_distrib] at h2
    simp_rw [Finset.mul_sum] at h3
    rw [h3, add_zero] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  obtain ⟨v, hv0, hvk, hvq⟩ := lowest_order_quadratic k (fun j a b => pderiv j (Hm a b)) hk0 hid
  have hvY : ∀ a, v a ≠ 0 → a ∈ Y := by
    intro a ha; by_contra hc; exact ha (hvk a (hkY a hc))
  apply hv0
  apply H.common_zero
  intro i
  have hfi := pderiv_f_isWH H.hom i
  have hbig := H.big
  have key := taylor2 (pderiv i f) 0 v (fun a b c ha hb hc => by
    rw [pderiv_comm' c i, pderiv_comm' b i, pderiv_comm' a i,
      hQ a (hvY a ha) b (hvY b hb) c (hvY c hc), map_zero])
  rw [zero_add] at key
  rw [key]
  have e0 : eval 0 (pderiv i f) = 0 :=
    eval_zero_of_isWH_pos hfi (by have := hbig i; omega)
  have e1 : ∀ c, eval 0 (pderiv c (pderiv i f)) = 0 := fun c =>
    eval_zero_of_isWH_pos (pderiv_isWH hfi c).1 (by have := hbig i; have := hbig c; omega)
  have e2 : ∑ c, ∑ b, v c * v b * eval 0 (pderiv b (pderiv c (pderiv i f))) = 0 := by
    rw [← hvq i]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases hc : v c = 0
    · simp [hc]
    by_cases hb : v b = 0
    · simp [hb]
    have hcY := hvY c hc; have hbY := hvY b hb
    simp only [hHm, hessY, hcY, hbY, and_self, if_true]
    rw [pderiv_comm' c i, pderiv_comm' b i]
    ring
  rw [e0, e2, Finset.sum_eq_zero (fun c _ => by rw [e1 c, mul_zero])]; ring

/-- Theorem 3.6 holds whenever `f` is at most quadratic in the variables of weight greater than `r`, without the stratum theorem. -/
theorem Setup.radical_of_quadratic (H : Setup w d f) (r : ℕ)
    (hQ : QuadraticIn (Finset.univ.filter fun i => r < w i) f) (a : Poly n)
    (ha : a.IsWeightedHomogeneous w r) (hrad : a ∈ (partialIdeal w f r).radical) : a = 0 := by
  classical
  by_contra ha0
  set Y := Finset.univ.filter fun i => r < w i
  have hdet := H.hessY_det_ne_zero_of_quadratic Y hQ
  obtain ⟨x0, hx0⟩ := exists_eval_ne_zero (mul_ne_zero hdet ha0)
  rw [map_mul] at hx0
  set M := (hessY Y f).map (eval x0)
  have hM : M.det ≠ 0 := by
    rw [show M.det = eval x0 (hessY Y f).det from (RingHom.map_det _ _).symm]
    exact left_ne_zero_of_mul hx0
  set F : Fin n → ℂ := fun i => if i ∈ Y then eval x0 (pderiv i f) else 0
  set y := M⁻¹.mulVec (-F)
  have hMy : M.mulVec y = -F := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM),
      Matrix.one_mulVec]
  have hy : ∀ b, y b ≠ 0 → b ∈ Y := by
    intro b hb
    by_contra hbY
    apply hb
    have := congrFun hMy b
    simp only [Matrix.mulVec, dotProduct, M, Matrix.map_apply, hessY, hbY, false_and,
      if_false, F, Pi.neg_apply, neg_zero] at this
    simpa [apply_ite (eval x0)] using this
  have hzero : ∀ i, r < w i → eval (x0 + y) (pderiv i f) = 0 := by
    intro i hi
    have hiY : i ∈ Y := by simp [Y, hi]
    rw [pderiv_expand_of_quadratic Y hQ x0 y hy hiY]
    have := congrFun hMy i
    simp only [Matrix.mulVec, dotProduct, Pi.neg_apply, F, hiY, if_true] at this
    rw [this]; ring
  have haval : eval (x0 + y) a = eval x0 a := by
    apply taylor0
    intro c hc
    have := hy c hc
    simp only [Y, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact pderiv1_zero ha c this
  obtain ⟨N, hN⟩ := hrad
  have := eval_eq_zero_of_mem_partialIdeal hzero hN
  rw [map_pow, haval] at this
  exact right_ne_zero_of_mul hx0 (pow_eq_zero_iff'.mp this).1

/-- The degree-by-degree criteria give the square-deformation property directly. -/
theorem Setup.squareDeformationProperty_of_levels (H : Setup w d f)
    (hlev : ∀ r, 0 < r → 3 * r < d →
      (∀ i j, r < w i → r < w j → i = j) ∨ HeavyRestrictionIsolated w f r ∨
        QuadraticIn (Finset.univ.filter fun i => r < w i) f) :
    SquareDeformationProperty w d f := by
  intro r a ha h3 hrad
  suffices a = 0 by rw [this]; simp
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; exact H.radical_zero a ha hrad
  rcases hlev r hr h3 with hY | hfin | hQ
  · exact H.radical_of_heavy_subsingleton r hY a ha hrad
  · exact H.radical_of_heavyRestrictionIsolated r hfin a ha hrad
  · exact H.radical_of_quadratic r hQ a ha hrad

/-- The main theorem for `2w_i < d` when each degree `0 < 3r < d` has at most one heavy variable, an isolated heavy-coordinate restriction, or quadratic dependence on the heavy variables. -/
theorem yau_conjecture_levelwise (w : Fin n → ℕ) (d : ℕ) (f : Poly n)
    (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hbig : ∀ i, 2 * w i < d) (hcrit : HasIsolatedCriticalPoint f)
    (hlev : ∀ r, 0 < r → 3 * r < d →
      (∀ i j, r < w i → r < w j → i = j) ∨ HeavyRestrictionIsolated w f r ∨
        QuadraticIn (Finset.univ.filter fun i => r < w i) f)
    (k : ℤ) (hk : k < 0) (δ : Derivation ℂ (MilnorAlgebra f) (MilnorAlgebra f))
    (hδ : IsDerivationOfDegree w f k δ) : δ = 0 :=
  have H : Setup w d f :=
    ⟨hw, hf, hbig, isIsolatedSingularity_of_hasIsolatedCriticalPoint hw hf hcrit⟩
  H.no_neg_derivation (H.squareDeformationProperty_of_levels hlev) k hk δ hδ

end Yau
