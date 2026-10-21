import RequestProject.Yau.LowDim.ThreeVar

/-!
# Local criteria for Theorem 3.6

For a light variable `u`, the partial derivative `∂_u f` is regular modulo `I_r`.
If `a²` belongs locally to `I_r` at every nonzero common zero of `I_r`, the
Nullstellensatz and this regularity give `a² ∈ J`; Lemma 3.2 then gives `a=0`.
With one light variable, a local Euler relation for `f|_{u=0}` supplies this
condition. This includes restrictions involving at most two variables.
-/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ} {w : Fin n → ℕ} {d : ℕ} {f : Poly n}

/-- The ideal quotient `(I:b)`. -/
def colonBy (I : Ideal (Poly n)) (b : Poly n) : Ideal (Poly n) where
  carrier := {s | s * b ∈ I}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq, add_mul] at *; exact I.add_mem hx hy
  zero_mem' := by simp
  smul_mem' c s hs := by
    simp only [Set.mem_setOf_eq, smul_eq_mul] at *
    rw [mul_assoc]; exact I.mul_mem_left c hs

/-- For a light variable `u` with `w_u ≤ r`, the partial derivative `∂_u f` is a non-zero-divisor modulo `I_r`. -/
theorem Setup.pderiv_mul_mem_partialIdeal (H : Setup w d f) {r : ℕ} {u : Fin n} (hu : w u ≤ r)
    (b : Poly n) (hb : pderiv u f * b ∈ partialIdeal w f r) : b ∈ partialIdeal w f r := by
  classical
  set L := (List.finRange n).filter (fun i => decide (w i ≤ r)) with hL
  set F := ((List.finRange n).filter (fun i => !decide (w i ≤ r))).map (fun j => pderiv j f)
    with hFdef
  have hFI : Ideal.ofList F = partialIdeal w f r := by
    rw [Ideal.ofList, partialIdeal]
    congr 1
    ext g
    simp [hFdef, List.mem_map, List.mem_filter, not_le]
  have huL : u ∈ L := by simp [hL, hu]
  set gs := F ++ (pderiv u f :: (L.erase u).map (fun j => pderiv j f)) with hgs
  have hperm : (L.map (fun j => pderiv j f)).Perm
      (pderiv u f :: (L.erase u).map (fun j => pderiv j f)) := by
    have := (List.perm_cons_erase huL).map (fun j => pderiv j f)
    simpa using this
  have hideal : Ideal.ofList gs = jacobianIdeal f := by
    rw [hgs, Ideal.ofList_append, jacobianIdeal]
    apply le_antisymm
    · refine sup_le ?_ ?_
      · rw [Ideal.ofList, Ideal.span_le]
        intro g hg
        simp only [hFdef, Set.mem_setOf_eq, List.mem_map] at hg
        obtain ⟨j, -, rfl⟩ := hg
        exact Ideal.subset_span ⟨j, rfl⟩
      · rw [Ideal.ofList, Ideal.span_le]
        intro g hg
        simp only [Set.mem_setOf_eq] at hg
        rw [← hperm.mem_iff] at hg
        simp only [List.mem_map] at hg
        obtain ⟨j, -, rfl⟩ := hg
        exact Ideal.subset_span ⟨j, rfl⟩
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      by_cases hj : w j ≤ r
      · apply Ideal.mem_sup_right
        apply Ideal.subset_span
        show pderiv j f ∈ {r | r ∈ _}
        rw [Set.mem_setOf_eq, ← hperm.mem_iff]
        exact List.mem_map_of_mem (by simp [hL, hj])
      · apply Ideal.mem_sup_left
        apply Ideal.subset_span
        show pderiv j f ∈ {r | r ∈ F}
        simp only [hFdef, Set.mem_setOf_eq, List.mem_map, List.mem_filter, List.mem_finRange,
          true_and]
        exact ⟨j, by simpa using hj, rfl⟩
  have hlen : gs.length ≤ n := by
    have h1 := List.length_eq_length_filter_add (l := List.finRange n) (fun i => decide (w i ≤ r))
    simp only [List.length_finRange] at h1
    have h2 : 0 < L.length := List.length_pos_of_mem huL
    simp only [hgs, hFdef, List.length_append, List.length_cons, List.length_map,
      List.length_erase_of_mem huL]
    simp only [hL] at h2 ⊢
    omega
  have hhom : ∀ g ∈ gs, ∃ e, 0 < e ∧ g.IsWeightedHomogeneous w e := by
    intro g hg
    have : ∃ j, g = pderiv j f := by
      simp only [hgs, hFdef, List.mem_append, List.mem_cons, List.mem_map] at hg
      rcases hg with ⟨j, -, rfl⟩ | rfl | ⟨j, -, rfl⟩
      · exact ⟨j, rfl⟩
      · exact ⟨u, rfl⟩
      · exact ⟨j, rfl⟩
    obtain ⟨j, rfl⟩ := this
    exact ⟨d - w j, by have := H.big j; omega, pderiv_f_isWH H.hom j⟩
  have hfin : Module.Finite ℂ (Poly n ⧸ Ideal.ofList gs) := by
    rw [hideal]; exact H.iso
  have hreg := isWeaklyRegular_of_finite_quotient H.pos gs hlen hhom hfin
  rw [isWeaklyRegular_self_iff] at hreg
  have := hreg F.length (by simp [hgs]) b
  have h1 : gs[F.length]'(by simp [hgs]) = pderiv u f := by simp [hgs]
  have h2 : gs.take F.length = F := by simp [hgs]
  rw [h1, h2, hFI] at this
  exact this hb

/-- Local-to-global criterion: if `0 < 3r < d`, `a ∈ S_r`, and for every nonzero common zero `x` of `I_r` there is `s` with `s(x) ≠ 0` and `s a² ∈ I_r`, then `a=0`. -/
theorem Setup.radical_of_local_sq (H : Setup w d f) {r : ℕ} (hr : 0 < r) (h3r : 3 * r < d)
    (a : Poly n) (ha : a.IsWeightedHomogeneous w r)
    (hloc : ∀ x : Fin n → ℂ, x ≠ 0 → (∀ i, r < w i → eval x (pderiv i f) = 0) →
      ∃ s, eval x s ≠ 0 ∧ s * a ^ 2 ∈ partialIdeal w f r) : a = 0 := by
  classical
  by_cases hall : ∀ i, r < w i
  · exact eq_zero_of_all_heavy hr ha hall
  push_neg at hall
  obtain ⟨u, hu⟩ := hall
  set I := partialIdeal w f r with hIdef
  set K := colonBy I (a ^ 2)
  have hIK : I ≤ K := fun p hp => I.mul_mem_right _ hp
  have hzero : ∀ x ∈ zeroLocus ℂ K, x = 0 := by
    intro x hx
    rw [mem_zeroLocus_iff] at hx
    by_contra hx0
    have hxI : ∀ i, r < w i → eval x (pderiv i f) = 0 := fun i hi => by
      simpa using hx _ (hIK (Ideal.subset_span ⟨i, hi, rfl⟩))
    obtain ⟨s, hs, hsK⟩ := hloc x hx0 hxI
    exact hs (by simpa using hx s hsK)
  have hfuK : pderiv u f ∈ K.radical := by
    have hmem : pderiv u f ∈ vanishingIdeal ℂ (zeroLocus ℂ K) := by
      rw [mem_vanishingIdeal_iff]
      intro x hx
      rw [hzero x hx]
      exact eval_zero_of_isWH_pos (pderiv_f_isWH H.hom u) (by have := H.big u; omega)
    rwa [vanishingIdeal_zeroLocus_eq_radical] at hmem
  obtain ⟨N, hN⟩ := hfuK
  have key : ∀ m, pderiv u f ^ m * a ^ 2 ∈ I → a ^ 2 ∈ I := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro h
      apply ih
      apply H.pderiv_mul_mem_partialIdeal hu
      rw [pow_succ] at h
      rw [show pderiv u f * (pderiv u f ^ m * a ^ 2) = pderiv u f ^ m * pderiv u f * a ^ 2 by
        ring]
      exact h
  have haI : a ^ 2 ∈ I := key N hN
  have hIJ : I ≤ jacobianIdeal f := by
    rw [hIdef, partialIdeal, jacobianIdeal, Ideal.span_le]
    rintro _ ⟨i, -, rfl⟩
    exact Ideal.subset_span ⟨i, rfl⟩
  exact H.square r h3r a ha (hIJ haI)

/-! ### One light variable and any number of heavy variables -/

/-- A local Euler relation at `x`: `e g = ∑ c_k ∂_k g`, with `e(x) ≠ 0` and all `c_k(x)=0`; equivalently, `g ∈ 𝔪_x J_g` in the local ring. -/
def LocalEulerAt (g : Poly n) (x : Fin n → ℂ) : Prop :=
  ∃ (e : Poly n) (c : Fin n → Poly n), eval x e ≠ 0 ∧ (∀ k, eval x (c k) = 0) ∧
    e * g = ∑ k, c k * pderiv k g

/-- Theorem 3.6 at degree `r`, with one light variable, follows if `g=f|_{x_u=0}` satisfies the local Euler relation at every nonzero critical point with `x_u=0`. -/
theorem Setup.radical_of_one_light_localEuler (H : Setup w d f) {r : ℕ} (hr : 0 < r)
    (h3r : 3 * r < d) {u : Fin n} (hheavy : ∀ l, l ≠ u → r < w l)
    (hE : ∀ x : Fin n → ℂ, x ≠ 0 → x u = 0 → (∀ k, eval x (pderiv k (killV u f)) = 0) →
      LocalEulerAt (killV u f) x)
    (a : Poly n) (ha : a.IsWeightedHomogeneous w r) (hrad : a ∈ (partialIdeal w f r).radical) :
    a = 0 := by
  classical
  have hfree : ∀ k, k ≠ u → FreeOf k a := fun k hk =>
    freeOf_of_pderiv_eq_zero (pderiv_eq_zero_of_lt ha _ (hheavy k hk))
  obtain ⟨c, e, hce, hcr⟩ := eq_C_mul_X_pow_of_freeOf ha u (H.pos u) hfree
  by_cases hc : c = 0
  · rw [hce, hc]; simp
  have he1 : 1 ≤ e := by
    have := hcr hc
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h, zero_mul] at this; omega
    · exact h
  set I := partialIdeal w f r with hIdef
  have hlight : ∀ l, l ≠ u → pderiv l f ∈ I := fun l hl =>
    Ideal.subset_span ⟨l, hheavy l hl, rfl⟩
  obtain ⟨F, hF⟩ := exists_killV_decomp (v := u) f
  set g := killV u f with hgdef
  have hgl : ∀ l, l ≠ u → pderiv l g = pderiv l f - X u * pderiv l F := by
    intro l hl
    have : pderiv l f = pderiv l g + X u * pderiv l F := by
      have h0 : pderiv l (X u : Poly n) = 0 := pderiv_X_of_ne hl
      conv_lhs => rw [hF]
      rw [map_add, Derivation.leibniz, h0]
      simp only [smul_eq_mul, mul_zero, add_zero]
    rw [this]; ring
  have hgu : pderiv u g = 0 := (freeOf_killV f).pderiv_eq_zero
  have hfu : pderiv u f = F + X u * pderiv u F := by
    conv_lhs => rw [hF]
    rw [map_add, Derivation.leibniz, pderiv_X_self, hgu]
    simp only [smul_eq_mul, mul_one, zero_add]
    ring
  -- Euler's identity.
  have hEuler : C (d : ℂ) * g + X u * (C (d : ℂ) * F - C (w u : ℂ) * pderiv u f) ∈ I := by
    have he := euler_identity H.hom
    have hsplit : (∑ l, (w l : ℂ) • (X l * pderiv l f)) =
        (w u : ℂ) • (X u * pderiv u f) +
          ∑ l ∈ Finset.univ.erase u, (w l : ℂ) • (X l * pderiv l f) :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ u)).symm
    have hrest : ∑ l ∈ Finset.univ.erase u, (w l : ℂ) • (X l * pderiv l f) ∈ I := by
      refine Ideal.sum_mem _ fun l hl => ?_
      rw [smul_eq_C_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (hlight l (Finset.ne_of_mem_erase hl)))
    have : C (d : ℂ) * g + X u * (C (d : ℂ) * F - C (w u : ℂ) * pderiv u f) =
        ∑ l ∈ Finset.univ.erase u, (w l : ℂ) • (X l * pderiv l f) := by
      have h2 : C (d : ℂ) * f = (w u : ℂ) • (X u * pderiv u f) +
          ∑ l ∈ Finset.univ.erase u, (w l : ℂ) • (X l * pderiv l f) := by
        rw [← hsplit, ← he, smul_eq_C_mul]
      rw [smul_eq_C_mul] at h2
      linear_combination h2 - C (d : ℂ) * hF
    rw [this]; exact hrest
  refine H.radical_of_local_sq hr h3r a ha fun x hx0 hxI => ?_
  have hxu : x u = 0 := by
    obtain ⟨N, hN⟩ := hrad
    have := eval_eq_zero_of_mem_partialIdeal hxI hN
    rw [hce] at this
    simp only [map_pow, map_mul, eval_C, eval_X, pow_eq_zero_iff', mul_eq_zero, ne_eq] at this
    tauto
  have hcrit : ∀ k, eval x (pderiv k g) = 0 := by
    intro k
    by_cases hk : k = u
    · rw [hk, hgu, map_zero]
    · rw [hgl k hk, map_sub, map_mul, eval_X, hxu, zero_mul, sub_zero]
      exact hxI k (hheavy k hk)
  obtain ⟨E, cc, hE0, hcc, hEq⟩ := hE x hx0 hxu hcrit
  set T : Fin n → Poly n := fun k => if k = u then 0 else pderiv k F with hT
  have hfux : eval x (pderiv u f) ≠ 0 := by
    intro h3
    apply hx0
    apply H.common_zero x
    intro l
    by_cases hl : l = u
    · rw [hl]; exact h3
    · exact hxI l (hheavy l hl)
  refine ⟨E * (C (d : ℂ) * F - C (w u : ℂ) * pderiv u f) - C (d : ℂ) * ∑ k, cc k * T k, ?_, ?_⟩
  · have hFx : eval x F = eval x (pderiv u f) := by rw [hfu]; simp [hxu]
    have hdu : (d : ℂ) - w u ≠ 0 := by
      have := H.big u
      rw [sub_ne_zero]; exact_mod_cast (by omega : d ≠ w u)
    have hsum : eval x (∑ k, cc k * T k) = 0 := by
      rw [map_sum]
      exact Finset.sum_eq_zero fun k _ => by rw [map_mul, hcc k, zero_mul]
    rw [map_sub, map_mul, map_mul, hsum, mul_zero, sub_zero, map_sub, map_mul, map_mul, eval_C,
      eval_C, hFx, ← sub_mul]
    exact mul_ne_zero hE0 (mul_ne_zero hdu hfux)
  · -- `X_u · s ∈ I`
    have hTk : ∀ k, pderiv k g + X u * T k ∈ I := by
      intro k
      by_cases hk : k = u
      · simp [hT, hk, hgu]
      · simp only [hT, hk, if_false]
        rw [hgl k hk]; ring_nf; exact hlight k hk
    have hXs : X u * (E * (C (d : ℂ) * F - C (w u : ℂ) * pderiv u f) -
        C (d : ℂ) * ∑ k, cc k * T k) ∈ I := by
      have heq : X u * (E * (C (d : ℂ) * F - C (w u : ℂ) * pderiv u f) -
          C (d : ℂ) * ∑ k, cc k * T k) =
          E * (C (d : ℂ) * g + X u * (C (d : ℂ) * F - C (w u : ℂ) * pderiv u f)) -
          C (d : ℂ) * ∑ k, cc k * (pderiv k g + X u * T k) := by
        have hs : ∑ k, cc k * (pderiv k g + X u * T k) =
            ∑ k, cc k * pderiv k g + X u * ∑ k, cc k * T k := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [hs, ← hEq]; ring
      rw [heq]
      exact I.sub_mem (I.mul_mem_left _ hEuler)
        (I.mul_mem_left _ (Ideal.sum_mem _ fun k _ => I.mul_mem_left _ (hTk k)))
    have : (E * (C (d : ℂ) * F - C (w u : ℂ) * pderiv u f) - C (d : ℂ) * ∑ k, cc k * T k) *
        a ^ 2 = (C (c ^ 2) * X u ^ (2 * e - 1)) * (X u * (E * (C (d : ℂ) * F -
          C (w u : ℂ) * pderiv u f) - C (d : ℂ) * ∑ k, cc k * T k)) := by
      have ha2 : a ^ 2 = C (c ^ 2) * X u ^ (2 * e - 1) * X u := by
        rw [hce, mul_pow, ← pow_mul, map_pow, mul_assoc, ← pow_succ,
          show 2 * e - 1 + 1 = e * 2 by omega]
      rw [ha2]
      ring
    rw [this]
    exact I.mul_mem_left _ hXs

/-- Theorem 3.6 with one light variable when `f|_{u=0}` involves at most two variables; the number of heavy variables is unrestricted. -/
theorem Setup.radical_of_one_light_free2 (H : Setup w d f) {r : ℕ} (hr : 0 < r)
    (h3r : 3 * r < d) {u i j : Fin n} (hij : i ≠ j)
    (hheavy : ∀ l, l ≠ u → r < w l) (hfree : Free2 i j (killV u f))
    (a : Poly n) (ha : a.IsWeightedHomogeneous w r) (hrad : a ∈ (partialIdeal w f r).radical) :
    a = 0 := by
  classical
  have hd : 0 < d := by omega
  have hgw : (killV u f).IsWeightedHomogeneous w d := killV_isWH H.hom
  refine H.radical_of_one_light_localEuler hr h3r hheavy (fun x hx0 hxu hcrit => ?_) a ha hrad
  by_cases hxij : x i ≠ 0 ∨ x j ≠ 0
  · obtain ⟨e, a1, b1, he, ha1, hb1, hab⟩ :=
      exists_local_quotient H.pos hij hgw hd hfree x hxij (hcrit i) (hcrit j)
    refine ⟨e, fun k => if k = i then a1 else if k = j then b1 else 0, he, fun k => ?_, ?_⟩
    · by_cases hki : k = i
      · simp [hki, ha1]
      · by_cases hkj : k = j
        · simp [hkj, hb1, Ne.symm hij]
        · simp [hki, hkj]
    · rw [hab, Finset.sum_eq_add (a := i) (b := j) hij]
      · simp [Ne.symm hij]
      · intro k _ hk
        simp [hk.1, hk.2]
      · simp
      · simp
  · push_neg at hxij
    refine ⟨C (d : ℂ), fun k => if k = i ∨ k = j then C (w k : ℂ) * X k else 0, ?_, ?_, ?_⟩
    · simpa using (show (d : ℂ) ≠ 0 by exact_mod_cast hd.ne')
    · intro k
      by_cases hk : k = i ∨ k = j
      · rcases hk with rfl | rfl <;> simp [hxij.1, hxij.2]
      · simp [hk]
    · have he := euler_identity hgw
      rw [← smul_eq_C_mul, he]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : k = i ∨ k = j
      · simp only [hk, if_true, smul_eq_C_mul]; ring
      · push_neg at hk
        rw [(hfree k hk.1 hk.2).pderiv_eq_zero]
        simp

end Yau
