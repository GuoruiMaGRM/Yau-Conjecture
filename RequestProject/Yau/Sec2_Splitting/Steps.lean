import RequestProject.Yau.Sec2_Splitting.Splitting

/-! # The two coordinate-change steps in Lemma 2.1 -/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ}

lemma isWH_sub {w : Fin n → ℕ} {p q : Poly n} {e : ℕ} (hp : p.IsWeightedHomogeneous w e)
    (hq : q.IsWeightedHomogeneous w e) : (p - q).IsWeightedHomogeneous w e := by
  have := (isWeightedHomogeneous_C w (-1 : ℂ)).mul hq
  rw [zero_add] at this
  rw [sub_eq_add_neg, show -q = C (-1 : ℂ) * q by simp]
  exact hp.add this

lemma isWH_C_mul {w : Fin n → ℕ} {p : Poly n} {e : ℕ} (hp : p.IsWeightedHomogeneous w e)
    (c : ℂ) : (C c * p).IsWeightedHomogeneous w e := by
  have := (isWeightedHomogeneous_C w c).mul hp
  rwa [zero_add] at this

/-- If the Jacobian ideal is proper, all partial derivatives vanish at the origin. -/
lemma eval_zero_pderiv {w : Fin n → ℕ} {d : ℕ} {f : Poly n} (hw : ∀ i, 0 < w i)
    (hf : f.IsWeightedHomogeneous w d) (hJ : jacobianIdeal f ≠ ⊤) (i : Fin n) :
    eval 0 (pderiv i f) = 0 := by
  have hq := (pderiv_isWH hf i).1
  by_cases hlt : d < w i
  · rw [pderiv_eq_zero_of_lt hf i hlt, map_zero]
  by_cases hpos : 0 < d - w i
  · exact eval_zero_of_isWH_pos hq hpos
  have h0 : d - w i = 0 := by omega
  rw [h0] at hq
  by_contra hne
  apply hJ
  apply Ideal.eq_top_of_isUnit_mem _ (pderiv_mem_jac i)
  rw [eq_C_of_isWH_zero hw hq]
  exact (Ne.isUnit hne).map C

/-- If `f=A+x_u B`, with `A,B` independent of `x_u`, isolatedness forces `B` to have a linear term. -/
lemma exists_v_of_linear {w : Fin n → ℕ} {d : ℕ} {f : Poly n} (hw : ∀ i, 0 < w i)
    (hf : f.IsWeightedHomogeneous w d) (hiso : IsIsolatedSingularity f)
    (hJ : jacobianIdeal f ≠ ⊤) (u : Fin n) {A B : Poly n} (hfAB : f = A + X u * B)
    (hA : FreeOf u A) (hB : FreeOf u B) : ∃ v, eval 0 (pderiv v B) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  set x : Fin n → ℂ := Function.update 0 u 1
  have hx0 : ∀ q : Poly n, FreeOf u q → eval x q = eval 0 q := by
    intro q hq
    rw [hq.eval_update]; simp
  have hcz := common_zero_eq_zero hw hf hiso x (fun i => ?_)
  · have := congrFun hcz u
    simp [x] at this
  by_cases hi : i = u
  · subst hi
    have hdu : pderiv i f = B := by
      rw [hfAB, map_add, hA.pderiv_eq_zero, Derivation.leibniz, hB.pderiv_eq_zero,
        pderiv_X_self]; simp
    rw [hdu, hx0 B hB, ← hdu]
    exact eval_zero_pderiv hw hf hJ i
  · have hdi : pderiv i f = pderiv i A + X u * pderiv i B := by
      rw [hfAB, map_add, Derivation.leibniz, pderiv_X_of_ne hi]; simp
    have h1 := eval_zero_pderiv hw hf hJ i
    rw [hdi] at h1 ⊢
    simp only [map_add, map_mul, eval_X] at h1 ⊢
    rw [hx0 _ (hA.pderiv_of_ne hi), hx0 _ (hB.pderiv_of_ne hi), hcon i]
    simp only [Pi.zero_apply, zero_mul, add_zero, mul_zero] at h1 ⊢
    exact h1

/-- The step for a variable of weight `d/2` with a nonzero square coefficient. -/
lemma single_step {w : Fin (n + 1) → ℕ} {d : ℕ} {f : Poly (n + 1)} (hw : ∀ i, 0 < w i)
    (hf : f.IsWeightedHomogeneous w d) (u : Fin (n + 1)) (hd : 2 * w u = d)
    (hc : eval 0 (pderiv u (pderiv u f)) ≠ 0) :
    ∃ F : Poly n, F.IsWeightedHomogeneous (w ∘ Fin.succAbove u) d ∧
      (IsIsolatedSingularity f → IsIsolatedSingularity F) ∧
      (NoNegDer (w ∘ Fin.succAbove u) F → NoNegDer w f) := by
  set c := eval 0 (pderiv u (pderiv u f)) with hc_def
  have hdeg : ∀ μ ∈ f.support, μ u ≤ 2 := by
    intro μ hμ
    have h1 := degree_le_of_isWH hf hμ (v := u)
    have h2 := hw u
    by_contra h3
    have : 3 * w u ≤ μ u * w u := Nat.mul_le_mul_right _ (by omega)
    omega
  have htay := taylor2_killV f hdeg
  set A := killV u f
  set B := killV u (pderiv u f)
  set Q := killV u (pderiv u (pderiv u f))
  have hBw : B.IsWeightedHomogeneous w (w u) := by
    have := killV_isWH (v := u) (pderiv_isWH hf u).1
    rwa [show d - w u = w u by omega] at this
  have hQw : Q.IsWeightedHomogeneous w 0 := by
    have := killV_isWH (v := u) (pderiv_isWH (pderiv_isWH hf u).1 u).1
    rwa [show d - w u - w u = 0 by omega] at this
  have hQ : Q = C c := by
    rw [eq_C_of_isWH_zero hw hQw]; congr 1
    simp only [Q]; rw [eval_killV]; simp [c]
  have hA : FreeOf u A := freeOf_killV f
  have hB : FreeOf u B := freeOf_killV _
  set g : Poly (n + 1) := -(C c⁻¹ * B) with hg_def
  have hg' : g = C (-c⁻¹) * B := by rw [hg_def, C_neg, neg_mul]
  have hg : FreeOf u g := ((freeOf_C _).mul hB).neg
  have hgw : g.IsWeightedHomogeneous w (w u) := by rw [hg']; exact isWH_C_mul hBw _
  obtain ⟨hiso1, hnn1⟩ := elem_transfer (f := f) (one_ne_zero) hg hgw
  set G : Poly (n + 1) := A - C (1 / 2 : ℂ) * C c⁻¹ * B ^ 2
  have hG : FreeOf u G := hA.sub (((freeOf_C _).mul (freeOf_C _)).mul (hB.pow 2))
  have hσ : elem u 1 g f = C (c / 2) * X u ^ 2 + G := by
    conv_lhs => rw [htay]
    rw [hQ]
    simp only [map_add, map_mul, map_pow, elem_X_self, hA.elem_eq, hB.elem_eq,
      (freeOf_C (v := u) _).elem_eq, C_1, one_mul]
    have he : (C c : Poly (n + 1)) * C c⁻¹ = 1 := by rw [← C_mul, mul_inv_cancel₀ hc, C_1]
    have hh : (C (1 / 2 : ℂ) : Poly (n + 1)) * 2 = 1 := by
      rw [show (2 : Poly (n + 1)) = C 2 from (map_ofNat C 2).symm, ← C_mul]; norm_num
    rw [show (C (c / 2) : Poly (n + 1)) = C c * C (1 / 2) by rw [← C_mul]; ring_nf]
    simp only [hg_def, G]
    linear_combination (-2 * C (1 / 2 : ℂ) * X u * B + C (1 / 2 : ℂ) * C c⁻¹ * B ^ 2) * he +
      (-X u * B + C c⁻¹ * B ^ 2) * hh
  set F := psiU u G
  have hGF : G = sU u F := hG.eq_sU_psiU u
  obtain ⟨hiso2, hnn2⟩ := single_removal (w := w) (show c / 2 ≠ 0 by simpa using hc)
    (hσ.trans (by rw [← hGF]))
  refine ⟨F, ?_, fun h => hiso2.mp (hiso1.mp h), fun h => hnn1 (hnn2 h)⟩
  have hFeq : psiU u (elem u 1 g f) = F := by
    rw [hσ, map_add, map_mul, map_pow, psiU_X_self, hGF, psiU_sU]; simp
  rw [← hFeq]; exact psiU_isWH u (elem_isWH' hgw hf)

/-- The paired-variable step: `f=A+x_u B`, with a nonzero linear `x_v` term in `B`. -/
lemma pair_step {w : Fin (n + 2) → ℕ} {d : ℕ} {f : Poly (n + 2)} (hw : ∀ i, 0 < w i)
    (hf : f.IsWeightedHomogeneous w d) (u : Fin (n + 2)) (v' : Fin (n + 1))
    {A B : Poly (n + 2)} (hfAB : f = A + X u * B) (hA : FreeOf u A) (hB : FreeOf u B)
    (hBw : B.IsWeightedHomogeneous w (w (Fin.succAbove u v')))
    (hd : w u + w (Fin.succAbove u v') = d)
    (hc : eval 0 (pderiv (Fin.succAbove u v') B) ≠ 0) :
    ∃ F : Poly n, F.IsWeightedHomogeneous (w ∘ Fin.succAbove u ∘ Fin.succAbove v') d ∧
      (IsIsolatedSingularity f → IsIsolatedSingularity F) ∧
      (NoNegDer (w ∘ Fin.succAbove u ∘ Fin.succAbove v') F → NoNegDer w f) := by
  set v := Fin.succAbove u v' with hv_def
  have huv : u ≠ v := (Fin.succAbove_ne u v').symm
  set c := eval 0 (pderiv v B) with hc_def
  have hdegB : ∀ μ ∈ B.support, μ v ≤ 2 := by
    intro μ hμ
    have h1 := degree_le_of_isWH hBw hμ (v := v)
    have h2 := hw v
    by_contra h3
    have : 3 * w v ≤ μ v * w v := Nat.mul_le_mul_right _ (by omega)
    omega
  have htB := taylor2_killV B hdegB
  have hdB0 : (pderiv v B).IsWeightedHomogeneous w 0 := by
    have := (pderiv_isWH hBw v).1; rwa [Nat.sub_self] at this
  have hB2 : pderiv v (pderiv v B) = 0 := pderiv_eq_zero_of_lt hdB0 v (hw v)
  set R := killV v B
  have hM : killV v (pderiv v B) = C c := by
    rw [eq_C_of_isWH_zero hw (killV_isWH hdB0)]; congr 1
    rw [eval_killV]; simp [c]
  have hBRM : B = R + X v * C c := by
    conv_lhs => rw [htB]
    rw [hB2, map_zero, mul_zero, add_zero, hM]
  have hRv : FreeOf v R := freeOf_killV B
  have hRu : FreeOf u R := hB.killV_other
  have hRw : R.IsWeightedHomogeneous w (w v) := killV_isWH hBw
  -- First substitution: `x_v ↦ c⁻¹(x_v-R)`.
  set g1 : Poly (n + 2) := -(C c⁻¹ * R) with hg1_def
  have hg1' : g1 = C (-c⁻¹) * R := by rw [hg1_def, C_neg, neg_mul]
  have hg1v : FreeOf v g1 := ((freeOf_C _).mul hRv).neg
  have hg1u : FreeOf u g1 := ((freeOf_C _).mul hRu).neg
  have hg1w : g1.IsWeightedHomogeneous w (w v) := by rw [hg1']; exact isWH_C_mul hRw _
  obtain ⟨hiso1, hnn1⟩ := elem_transfer (f := f) (inv_ne_zero hc) hg1v hg1w
  set A1 := elem v c⁻¹ g1 A
  have hτB : elem v c⁻¹ g1 B = X v := by
    rw [hBRM, map_add, map_mul, hRv.elem_eq, elem_X_self, (freeOf_C c).elem_eq, hg1_def]
    have he : (C c⁻¹ : Poly (n + 2)) * C c = 1 := by rw [← C_mul, inv_mul_cancel₀ hc, C_1]
    linear_combination (X v - R) * he
  have hf1 : elem v c⁻¹ g1 f = X u * X v + A1 := by
    rw [hfAB, map_add, map_mul, elem_X_ne huv, hτB]; ring
  have hA1u : FreeOf u A1 := FreeOf.elem_other huv hg1u hA
  have hf1w := elem_isWH' (a := c⁻¹) hg1w hf
  have hXuv : (X u * X v : Poly (n + 2)).IsWeightedHomogeneous w d := by
    have := (isWeightedHomogeneous_X ℂ w u).mul (isWeightedHomogeneous_X ℂ w v)
    rwa [hd] at this
  have hA1w : A1.IsWeightedHomogeneous w d := by
    have := isWH_sub hf1w hXuv
    rwa [hf1, add_sub_cancel_left] at this
  -- Decompose `A1 = A2 + x_v K`.
  obtain ⟨K, hK⟩ := exists_killV_decomp (v := v) A1
  set A2 := killV v A1
  have hA2v : FreeOf v A2 := freeOf_killV _
  have hA2u : FreeOf u A2 := hA1u.killV_other
  have hA2w : A2.IsWeightedHomogeneous w d := killV_isWH hA1w
  have hXK : X v * K = A1 - A2 := by linear_combination -hK
  have hKw : K.IsWeightedHomogeneous w (w u) := by
    have := isWH_of_X_mul (hXK ▸ isWH_sub hA1w hA2w)
    rwa [show d - w v = w u by omega] at this
  have hKu : FreeOf u K := by
    have h1 : killV u (X v * K) = X v * K := by
      rw [hXK, map_sub]; unfold FreeOf at hA1u hA2u; rw [hA1u, hA2u]
    rw [map_mul, killV_X_ne huv.symm] at h1
    exact mul_left_cancel₀ (X_ne_zero v) h1
  -- Second substitution: `x_u ↦ x_u-K`.
  have hnKw : (-K).IsWeightedHomogeneous w (w u) := by
    rw [show -K = C (-1 : ℂ) * K by simp]; exact isWH_C_mul hKw _
  obtain ⟨hiso2, hnn2⟩ := elem_transfer (f := elem v c⁻¹ g1 f) one_ne_zero hKu.neg hnKw
  have hf2 : elem u 1 (-K) (elem v c⁻¹ g1 f) = X u * X v + A2 := by
    rw [hf1, hK, map_add, map_add, map_mul, map_mul, elem_X_self, elem_X_ne huv.symm,
      hA2u.elem_eq, hKu.elem_eq, C_1]
    ring
  -- Remove the two variables.
  set F := psiU v' (psiU u A2)
  have hA2eq : A2 = sU u (sU v' F) := by
    have h2 : FreeOf v' (psiU u A2) := by
      unfold FreeOf; rw [← psiU_killV_succAbove]; unfold FreeOf at hA2v; rw [hA2v]
    rw [← h2.eq_sU_psiU v']
    exact hA2u.eq_sU_psiU u
  obtain ⟨hiso3, hnn3⟩ := pair_removal (w := w) (u := u) (v' := v') (hf2.trans (by rw [← hA2eq]))
  exact ⟨F, psiU_isWH v' (psiU_isWH u hA2w), fun h => hiso3.mp (hiso2.mp (hiso1.mp h)),
    fun h => hnn1 (hnn2 (hnn3 h))⟩

end Yau
