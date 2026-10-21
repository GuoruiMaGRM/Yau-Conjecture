import RequestProject.Yau.LowDim.Homogeneous

/-!
# A criterion depending only on the weights

The Hessian argument works whenever every variable of weight greater than `r`
has weight greater than `d/3`. Combine this with the cases of no light variable
and at most one heavy variable. The resulting condition is:
if `j ≠ k`, `w_i < w_j`, and `w_i < w_k`, then `3w_j > d`.
It is preserved by deleting variables, so the main theorem follows directly
for these weights. Equal weights are one example.
-/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ}

/-- For each variable, there is at most one strictly heavier variable, or every strictly heavier variable has weight greater than `d/3`. -/
def SmallWeightCondition (w : Fin n → ℕ) (d : ℕ) : Prop :=
  ∀ i j k, j ≠ k → w i < w j → w i < w k → d < 3 * w j

/-- The weight condition is preserved when variables are deleted via an injection. -/
lemma SmallWeightCondition.comp {m : ℕ} {w : Fin n → ℕ} {d : ℕ} (h : SmallWeightCondition w d)
    (g : Fin m → Fin n) (hg : Function.Injective g) : SmallWeightCondition (w ∘ g) d :=
  fun i j k hjk hij hik => h (g i) (g j) (g k) (fun e => hjk (hg e)) hij hik

variable {w : Fin n → ℕ} {d : ℕ} {f : Poly n}

/-- The radical conclusion holds if every variable of weight greater than `r` has weight greater than `d/3`. This contains the `3r ≥ d` case of Theorem 3.6. -/
theorem Setup.radical_of_heavy_gt_third (H : Setup w d f) (r : ℕ)
    (hY3 : ∀ i, r < w i → d < 3 * w i) (a : Poly n)
    (ha : a.IsWeightedHomogeneous w r) (hrad : a ∈ (partialIdeal w f r).radical) : a = 0 := by
  classical
  by_contra ha0
  set Y := Finset.univ.filter fun i => r < w i
  have hY : ∀ i ∈ Y, d < 3 * w i := by
    intro i hi; simp only [Y, Finset.mem_filter, Finset.mem_univ, true_and] at hi; exact hY3 i hi
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

/-- At a positive degree `r`, the radical conclusion follows if there is no light variable, at most one heavy variable, or all heavy weights exceed `d/3`. -/
theorem Setup.radical_of_level (H : Setup w d f) (r : ℕ)
    (hlev : (∀ i, r < w i) ∨ (∀ i j, r < w i → r < w j → i = j) ∨ (∀ i, r < w i → d < 3 * w i))
    (a : Poly n) (ha : a.IsWeightedHomogeneous w r) (hrad : a ∈ (partialIdeal w f r).radical) :
    a = 0 := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; exact H.radical_zero a ha hrad
  rcases hlev with hall | hY | hY3
  · exact eq_zero_of_all_heavy hr ha hall
  · exact H.radical_of_heavy_subsingleton r hY a ha hrad
  · exact H.radical_of_heavy_gt_third r hY3 a ha hrad

/-- The weight condition ensures the preceding criterion at every degree. -/
lemma SmallWeightCondition.level (hC : SmallWeightCondition w d) (r : ℕ) :
    (∀ i, r < w i) ∨ (∀ i j, r < w i → r < w j → i = j) ∨ (∀ i, r < w i → d < 3 * w i) := by
  by_cases hall : ∀ i, r < w i
  · exact Or.inl hall
  push_neg at hall
  obtain ⟨i, hi⟩ := hall
  by_cases hY : ∀ j k, r < w j → r < w k → j = k
  · exact Or.inr (Or.inl hY)
  push_neg at hY
  obtain ⟨j, k, hj, hk, hjk⟩ := hY
  refine Or.inr (Or.inr fun l hl => ?_)
  by_cases hlj : l = j
  · subst hlj; exact hC i l k hjk (by omega) (by omega)
  · exact hC i l j hlj (by omega) (by omega)

/-- The square-deformation property holds under the weight condition. -/
theorem Setup.squareDeformationProperty_of_smallWeight (H : Setup w d f)
    (hC : SmallWeightCondition w d) : SquareDeformationProperty w d f := by
  intro r a ha _ hrad
  rw [H.radical_of_level r (hC.level r) a ha hrad]
  simp

/-- The induction uses the square-deformation property only where the weight condition holds. -/
theorem noNegDer_of_isolated_of_smallWeight :
    ∀ (n : ℕ) (w : Fin n → ℕ) (d : ℕ) (f : Poly n), SmallWeightCondition w d → (∀ i, 0 < w i) →
      f.IsWeightedHomogeneous w d → IsIsolatedSingularity f → NoNegDer w f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w d f hC hw hf hiso
  by_cases hJ : jacobianIdeal f = ⊤
  · exact noNegDer_of_jac_eq_top hJ
  by_cases hbig : ∀ i, 2 * w i < d
  · have H : Setup w d f := ⟨hw, hf, hbig, hiso⟩
    intro k hk δ hδ
    exact H.no_neg_derivation (H.squareDeformationProperty_of_smallWeight hC) k hk δ hδ
  push_neg at hbig
  obtain ⟨u, hu⟩ := hbig
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := u.pos; omega⟩
  by_cases hc : eval 0 (pderiv u (pderiv u f)) ≠ 0
  · have hd : 2 * w u = d := by
      by_contra hne
      apply hc
      rw [pderiv_eq_zero_of_lt (pderiv_isWH hf u).1 u (by omega), map_zero]
    obtain ⟨F, hFw, hFi, hFn⟩ := single_step hw hf u hd hc
    exact hFn (ih n' (by omega) _ d F (hC.comp _ (Fin.succAbove_right_injective))
      (fun i => hw _) hFw (hFi hiso))
  · push_neg at hc
    have hdeg : ∀ μ ∈ f.support, μ u ≤ 2 := by
      intro μ hμ
      have h1 := degree_le_of_isWH hf hμ (v := u)
      have h2 := hw u
      by_contra h3
      have : 3 * w u ≤ μ u * w u := Nat.mul_le_mul_right _ (by omega)
      omega
    have htay := taylor2_killV f hdeg
    have hQ : killV u (pderiv u (pderiv u f)) = 0 := by
      by_cases hd : 2 * w u = d
      · have hQw := killV_isWH (v := u) (pderiv_isWH (pderiv_isWH hf u).1 u).1
        rw [show d - w u - w u = 0 by omega] at hQw
        rw [eq_C_of_isWH_zero hw hQw, eval_killV,
          show Function.update (0 : Fin (n' + 1) → ℂ) u 0 = 0 by simp, hc, map_zero]
      · rw [pderiv_eq_zero_of_lt (pderiv_isWH hf u).1 u (by omega), map_zero]
    set A := killV u f
    set B := killV u (pderiv u f)
    have hfAB : f = A + X u * B := by
      conv_lhs => rw [htay]
      rw [hQ, mul_zero, add_zero]
    have hA : FreeOf u A := freeOf_killV f
    have hB : FreeOf u B := freeOf_killV _
    obtain ⟨v, hv⟩ := exists_v_of_linear hw hf hiso hJ u hfAB hA hB
    have hvu : v ≠ u := by
      rintro rfl; apply hv; rw [hB.pderiv_eq_zero, map_zero]
    obtain ⟨v', rfl⟩ := Fin.exists_succAbove_eq hvu
    obtain ⟨n'', rfl⟩ : ∃ n'', n' = n'' + 1 := ⟨n' - 1, by have := v'.pos; omega⟩
    have hBw0 : B.IsWeightedHomogeneous w (d - w u) := killV_isWH (pderiv_isWH hf u).1
    have h1 : w (Fin.succAbove u v') ≤ d - w u := by
      by_contra hlt
      apply hv
      rw [pderiv_eq_zero_of_lt hBw0 _ (by omega), map_zero]
    have h2 : d - w u - w (Fin.succAbove u v') = 0 := by
      by_contra hpos
      exact hv (eval_zero_of_isWH_pos (pderiv_isWH hBw0 _).1 (by omega))
    have hwv := hw (Fin.succAbove u v')
    have hd : w u + w (Fin.succAbove u v') = d := by omega
    have hBw : B.IsWeightedHomogeneous w (w (Fin.succAbove u v')) := by
      rwa [show d - w u = w (Fin.succAbove u v') by omega] at hBw0
    obtain ⟨F, hFw, hFi, hFn⟩ := pair_step hw hf u v' hfAB hA hB hBw hd hv
    exact hFn (ih n'' (by omega) _ d F (hC.comp _
      (Fin.succAbove_right_injective.comp Fin.succAbove_right_injective))
      (fun i => hw _) hFw (hFi hiso))

/-- The main theorem under `SmallWeightCondition`, without the stratum hypothesis. -/
theorem «Yau猜想_小权条件» (w : Fin n → ℕ) (d : ℕ) (f : Poly n)
    (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hC : ∀ i j k, j ≠ k → w i < w j → w i < w k → d < 3 * w j)
    (hcrit : HasIsolatedCriticalPoint f) (k : ℤ) (hk : k < 0)
    (δ : Derivation ℂ (MilnorAlgebra f) (MilnorAlgebra f))
    (hδ : IsDerivationOfDegree w f k δ) : δ = 0 :=
  noNegDer_of_isolated_of_smallWeight n w d f hC hw hf
    (isIsolatedSingularity_of_hasIsolatedCriticalPoint hw hf hcrit) k hk δ hδ

end Yau
