import RequestProject.Yau.Sec3_Radical.Hessian

/-! # The radical of `I_r`: Lemma 3.2 and Theorem 3.6 -/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ} {w : Fin n → ℕ} {d : ℕ} {f : Poly n}

lemma eval_eq_zero_of_mem_partialIdeal {r : ℕ} {x : Fin n → ℂ}
    (hx : ∀ i, r < w i → eval x (pderiv i f) = 0) {p : Poly n}
    (hp : p ∈ partialIdeal w f r) : eval x p = 0 := by
  have : partialIdeal w f r ≤ RingHom.ker (eval x) := by
    rw [partialIdeal, Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩; exact hx i hi
  exact this hp

lemma exists_eval_ne_zero {p : Poly n} (hp : p ≠ 0) : ∃ x : Fin n → ℂ, eval x p ≠ 0 := by
  by_contra h
  push_neg at h
  exact hp (MvPolynomial.funext fun x => by rw [map_zero]; exact h x)

/-- First-order expansion of `∂_a f` in the selected variables, using the Hessian matrix. -/
lemma Setup.pderiv_expand (H : Setup w d f) (Y : Finset (Fin n))
    (hY : ∀ i ∈ Y, d < 3 * w i) (x0 y : Fin n → ℂ) (hy : ∀ b, y b ≠ 0 → b ∈ Y)
    {a : Fin n} (ha : a ∈ Y) :
    eval (x0 + y) (pderiv a f) =
      eval x0 (pderiv a f) + ∑ c, ((hessY Y f).map (eval x0)) a c * y c := by
  rw [taylor1 _ x0 y (fun b c hb hc => by
    have := hY a ha; have := hY b (hy b hb); have := hY c (hy c hc)
    exact pderiv2_zero (pderiv_f_isWH H.hom a) b c (by omega) (H.pos b))]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : y c = 0
  · simp [hc]
  · simp [hessY, ha, hy c hc, mul_comm]

/-- The large-degree case of Theorem 3.6. -/
lemma Setup.radical_large (H : Setup w d f) (r : ℕ) (hr : d ≤ 3 * r) (a : Poly n)
    (ha : a.IsWeightedHomogeneous w r) (hrad : a ∈ (partialIdeal w f r).radical) : a = 0 := by
  classical
  by_contra ha0
  set Y := Finset.univ.filter fun i => r < w i
  have hY : ∀ i ∈ Y, d < 3 * w i := by
    intro i hi; simp only [Y, Finset.mem_filter, Finset.mem_univ, true_and] at hi; omega
  have hdet := H.hessY_det_ne_zero Y hY
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
    rw [H.pderiv_expand Y hY x0 y hy hiY]
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

/-- Lemma 3.2: if `0<3r<d` and `a∈S_r` is nonzero, then `a²∉J`. -/
lemma Setup.square (H : Setup w d f) (r : ℕ) (h3r : 3 * r < d) (a : Poly n)
    (ha : a.IsWeightedHomogeneous w r) (hsq : a ^ 2 ∈ jacobianIdeal f) : a = 0 := by
  classical
  obtain ⟨k, hk1, hk2, hk3⟩ := jacobian_homog_decomp H.hom hsq (ha.pow 2) H.wd
  simp only [smul_eq_mul] at hk1 hk2
  set Y := Finset.univ.filter fun i => d ≤ 2 * r + w i
  have hY : ∀ i ∈ Y, d < 3 * w i := by
    intro i hi; simp only [Y, Finset.mem_filter, Finset.mem_univ, true_and] at hi; omega
  have hkY : ∀ i, i ∉ Y → k i = 0 := by
    intro i hi; apply hk2; simp only [Y, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    omega
  by_contra ha0
  by_cases hk0 : ∀ i, k i = 0
  · apply ha0
    have : a ^ 2 = 0 := by rw [hk3]; simp [hk0]
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  push_neg at hk0
  obtain ⟨i0, hi0⟩ := hk0
  have hdet := H.hessY_det_ne_zero Y hY
  obtain ⟨x0, hx0⟩ := exists_eval_ne_zero (mul_ne_zero hdet hi0)
  rw [map_mul] at hx0
  set M := (hessY Y f).map (eval x0)
  have hM : M.det ≠ 0 := by
    rw [show M.det = eval x0 (hessY Y f).det from (RingHom.map_det _ _).symm]
    exact left_ne_zero_of_mul hx0
  set κ : Fin n → ℂ := fun i => eval x0 (k i)
  have hκ : κ ≠ 0 := fun h => right_ne_zero_of_mul hx0 (congrFun h i0)
  apply hM
  rw [← Matrix.exists_vecMul_eq_zero_iff]
  refine ⟨κ, hκ, funext fun b => ?_⟩
  simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
  by_cases hbY : b ∈ Y
  · -- Move along the `b`-coordinate axis.
    set y : Fin n → ℂ := Pi.single b 1
    have hy : ∀ c, y c ≠ 0 → c ∈ Y := by
      intro c hc
      by_cases hcb : c = b
      · rw [hcb]; exact hbY
      · simp [y, hcb] at hc
    have hbw : d ≤ 2 * r + w b := by
      simpa only [Y, Finset.mem_filter, Finset.mem_univ, true_and] using hbY
    have haval : eval (x0 + y) a = eval x0 a := by
      apply taylor0; intro c hc
      have := hy c hc
      simp only [Y, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact pderiv1_zero ha c (by omega)
    have hkval : ∀ i, eval (x0 + y) (k i) = eval x0 (k i) := by
      intro i
      by_cases hiY : i ∈ Y
      · apply taylor0; intro c hc
        have := hy c hc
        simp only [Y, Finset.mem_filter, Finset.mem_univ, true_and] at this hiY
        have := H.big i
        exact pderiv1_zero (hk1 i) c (by omega)
      · rw [hkY i hiY]; simp
    have e1 := congrArg (eval (x0 + y)) hk3
    have e0 := congrArg (eval x0) hk3
    simp only [map_pow, map_sum, map_mul, haval, hkval] at e1
    simp only [map_pow, map_sum, map_mul] at e0
    rw [e0] at e1
    have : ∑ i, eval x0 (k i) * (eval (x0 + y) (pderiv i f) - eval x0 (pderiv i f)) = 0 := by
      rw [Finset.sum_congr rfl fun i _ => mul_sub _ _ _, Finset.sum_sub_distrib, e1, sub_self]
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hiY : i ∈ Y
    · rw [H.pderiv_expand Y hY x0 y hy hiY]
      simp [y, κ, Pi.single_apply, M]
    · simp [κ, hkY i hiY]
  · refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hiY : i ∈ Y
    · have hib : i ≠ b := fun h => hbY (h ▸ hiY)
      simp [M, hessY, hbY, hib]
    · simp [κ, hkY i hiY]

/-- The degree-zero boundary calculation accompanying Theorem 3.6. -/
lemma Setup.radical_zero (H : Setup w d f) (a : Poly n) (ha : a.IsWeightedHomogeneous w 0)
    (hrad : a ∈ (partialIdeal w f 0).radical) : a = 0 := by
  obtain ⟨N, hN⟩ := hrad
  have h0 : eval 0 a = 0 := by
    have := eval_eq_zero_of_mem_partialIdeal (x := 0) (fun i _ =>
      eval_zero_of_isWH_pos (pderiv_f_isWH H.hom i) (by have := H.big i; omega)) hN
    rw [map_pow] at this
    exact pow_eq_zero_iff'.mp this |>.1
  apply MvPolynomial.funext
  intro x
  have := eval_scale ha 0 x
  simp only [pow_zero, one_mul] at this
  have hx : (fun j => (0 : ℂ) ^ w j * x j) = 0 := by
    funext j; simp [zero_pow (H.pos j).ne']
  rw [map_zero, ← this, hx, h0]

/-- Theorem 3.6: `√I_r ∩ S_r = 0`; the small-degree case uses the square-deformation property. -/
lemma Setup.radical (H : Setup w d f) (hV : SquareDeformationProperty w d f)
    (r : ℕ) (a : Poly n) (ha : a.IsWeightedHomogeneous w r)
    (hrad : a ∈ (partialIdeal w f r).radical) : a = 0 := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; exact H.radical_zero a ha hrad
  by_cases h3 : d ≤ 3 * r
  · exact H.radical_large r h3 a ha hrad
  · exact H.square r (by omega) a ha (hV r a ha (by omega) hrad)

end Yau
