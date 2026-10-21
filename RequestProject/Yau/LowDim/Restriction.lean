import RequestProject.Yau.LowDim.LowDim
import RequestProject.Yau.CommAlg.RegularSequence

/-!
# Theorem 3.6 from an isolated coordinate restriction

Let `u` be the variables of weight at most `r` and `y` those of weight greater
than `r`. If the restriction `f|_{u=0}` has an isolated critical point, then
`f_y` together with `u` form a homogeneous system of parameters, regular in
any order. No nonzero polynomial in `u` can lie in `√(f_y)`. This proves the
degree-`r` radical statement without the stratum theorem.
-/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ}

lemma sub_killV_mem (s : Fin n) (g : Poly n) : g - killV s g ∈ Ideal.span {X s} := by
  induction g using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    rw [map_add, show p + q - (killV s p + killV s q) = (p - killV s p) + (q - killV s q) by ring]
    exact Ideal.add_mem _ hp hq
  | mul_X p i hp =>
    rw [map_mul]
    by_cases hi : i = s
    · subst hi
      rw [killV_X_self, mul_zero, sub_zero]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · rw [killV_X_ne hi, ← sub_mul]
      exact Ideal.mul_mem_right _ _ hp

lemma exists_X_mul_of_killV_eq_zero {s : Fin n} {g : Poly n} (h : killV s g = 0) :
    ∃ b, g = X s * b := by
  have := sub_killV_mem s g
  rw [h, sub_zero, Ideal.mem_span_singleton'] at this
  obtain ⟨b, hb⟩ := this
  exact ⟨b, by rw [← hb, mul_comm]⟩

lemma freeOf_of_pderiv_eq_zero {j : Fin n} {p : Poly n} (h : pderiv j p = 0) : FreeOf j p := by
  apply MvPolynomial.funext
  intro x
  rw [eval_killV, ← eval_update_of_pderiv_eq_zero h x (x j), Function.update_eq_self]

lemma FreeOf.of_X_mul {i s : Fin n} (his : i ≠ s) {b : Poly n} (h : FreeOf i (X s * b)) :
    FreeOf i b := by
  unfold FreeOf at h ⊢
  rw [map_mul, killV_X_ne (Ne.symm his)] at h
  exact mul_left_cancel₀ (X_ne_zero s) h

/-- A polynomial independent of the variables in `T` is unaffected by changing those coordinates. -/
lemma eval_eq_of_freeOf {h : Poly n} (T : Finset (Fin n)) (hT : ∀ i ∈ T, FreeOf i h)
    (x : Fin n → ℂ) : eval x h = eval (fun i => if i ∈ T then 0 else x i) h := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T haT ih =>
    rw [ih (fun i hi => hT i (Finset.mem_insert_of_mem hi))]
    have e := (hT a (Finset.mem_insert_self a T)).eval_update
      (fun i => if i ∈ T then 0 else x i) (if a ∈ T then 0 else x a)
    rw [Function.update_eq_self] at e
    rw [e]
    have hfun : Function.update (fun i => if i ∈ T then 0 else x i) a 0 =
        fun i => if i ∈ insert a T then 0 else x i := by
      funext i
      by_cases hia : i = a
      · subst hia; simp
      · simp [hia]
    rw [hfun]

variable {w : Fin n → ℕ}

/-- If `F` and the variables in `L` form a homogeneous system of parameters, each `x_s` with `s ∈ L` is regular modulo `(F)`. -/
lemma X_mul_mem_ofList (hw : ∀ i, 0 < w i) (F : List (Poly n))
    (hF : ∀ g ∈ F, ∃ e, 0 < e ∧ g.IsWeightedHomogeneous w e) (L : List (Fin n))
    (hlen : F.length + L.length ≤ n)
    (hfin : Module.Finite ℂ (Poly n ⧸ (Ideal.ofList F ⊔ Ideal.ofList (L.map X))))
    {s : Fin n} (hs : s ∈ L) (b : Poly n) (hb : X s * b ∈ Ideal.ofList F) :
    b ∈ Ideal.ofList F := by
  classical
  set gs := F ++ (X s :: (L.erase s).map X) with hgs
  have hperm : (L.map (X : Fin n → Poly n)).Perm (X s :: (L.erase s).map X) := by
    have := (List.perm_cons_erase hs).map (X : Fin n → Poly n)
    simpa using this
  have hideal : Ideal.ofList gs = Ideal.ofList F ⊔ Ideal.ofList (L.map X) := by
    rw [hgs, Ideal.ofList_append]
    congr 1
    unfold Ideal.ofList
    congr 1
    ext r
    exact hperm.mem_iff.symm
  have hlen' : gs.length ≤ n := by
    simp only [hgs, List.length_append, List.length_cons, List.length_map,
      List.length_erase_of_mem hs]
    have : 0 < L.length := List.length_pos_of_mem hs
    omega
  have hgs' : ∀ g ∈ gs, ∃ e, 0 < e ∧ g.IsWeightedHomogeneous w e := by
    intro g hg
    simp only [hgs, List.mem_append, List.mem_cons, List.mem_map] at hg
    rcases hg with hg | rfl | ⟨i, -, rfl⟩
    · exact hF g hg
    · exact ⟨w s, hw s, isWeightedHomogeneous_X _ _ _⟩
    · exact ⟨w i, hw i, isWeightedHomogeneous_X _ _ _⟩
  have hreg := isWeaklyRegular_of_finite_quotient hw gs hlen' hgs' (hideal ▸ hfin)
  rw [isWeaklyRegular_self_iff] at hreg
  have := hreg F.length (by simp [hgs]) b
  have h1 : gs[F.length]'(by simp [hgs]) = X s := by simp [hgs]
  have h2 : gs.take F.length = F := by simp [hgs]
  rw [h1, h2] at this
  exact this hb

lemma ofList_map_killV_sup (F : List (Poly n)) (L : List (Fin n)) {s : Fin n} (hs : s ∈ L) :
    Ideal.ofList (F.map (killV s : Poly n →+* Poly n)) ⊔ Ideal.ofList (L.map X) =
      Ideal.ofList F ⊔ Ideal.ofList (L.map X) := by
  have hXs : Ideal.span {(X s : Poly n)} ≤ Ideal.ofList (L.map X) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span (List.mem_map_of_mem hs)
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    rw [Ideal.ofList, Ideal.span_le]
    intro g hg
    simp only [Set.mem_setOf_eq, List.mem_map] at hg
    obtain ⟨g, hg, rfl⟩ := hg
    have : (killV s : Poly n →+* Poly n) g = g - (g - killV s g) := by simp
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.subset_span hg))
      (Ideal.mem_sup_right (hXs (sub_killV_mem s g)))
  · refine sup_le ?_ le_sup_right
    rw [Ideal.ofList, Ideal.span_le]
    intro g hg
    have : g = (killV s : Poly n →+* Poly n) g + (g - killV s g) := by simp
    rw [SetLike.mem_coe, this]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.subset_span (List.mem_map_of_mem hg)))
      (Ideal.mem_sup_right (hXs (sub_killV_mem s g)))

/-- If `F` and the variables in `L` form a homogeneous system of parameters, no nonzero polynomial in the `L` variables belongs to `√(F)`. -/
theorem eq_zero_of_mem_radical_ofList (hw : ∀ i, 0 < w i) (L : List (Fin n)) :
    ∀ (S : Finset (Fin n)), (∀ s ∈ S, s ∈ L) → ∀ (F : List (Poly n)),
      (∀ g ∈ F, ∃ e, 0 < e ∧ g.IsWeightedHomogeneous w e) → F.length + L.length ≤ n →
      Module.Finite ℂ (Poly n ⧸ (Ideal.ofList F ⊔ Ideal.ofList (L.map X))) →
      ∀ h : Poly n, (∀ i ∉ S, FreeOf i h) → h ∈ (Ideal.ofList F).radical → h = 0 := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ F hF _ _ h hfree hrad
    obtain ⟨N, hN⟩ := hrad
    have h0 : eval 0 h = 0 := by
      have hle : Ideal.ofList F ≤ RingHom.ker (eval (0 : Fin n → ℂ)) := by
        rw [Ideal.ofList, Ideal.span_le]
        intro g hg
        obtain ⟨e, he, hge⟩ := hF g hg
        exact eval_zero_of_isWH_pos hge he
      have := hle hN
      rw [RingHom.mem_ker, map_pow] at this
      exact (pow_eq_zero_iff'.mp this).1
    apply MvPolynomial.funext
    intro x
    rw [eval_eq_of_freeOf Finset.univ (fun i _ => hfree i (Finset.notMem_empty i)) x, map_zero]
    convert h0
    simp
  | insert s S hsS ih =>
    intro hSL F hF hlen hfin h
    have hsL : s ∈ L := hSL s (Finset.mem_insert_self s S)
    induction hd : h.totalDegree using Nat.strong_induction_on generalizing h with
    | _ k ihk =>
    intro hfree hrad
    by_contra hne
    by_cases hks : killV s h = 0
    · obtain ⟨b, rfl⟩ := exists_X_mul_of_killV_eq_zero hks
      have hb0 : b ≠ 0 := by rintro rfl; exact hne (mul_zero _)
      have hbfree : ∀ i ∉ insert s S, FreeOf i b := by
        intro i hi
        exact (hfree i hi).of_X_mul (fun his => hi (by rw [his]; exact Finset.mem_insert_self s S))
      have hbrad : b ∈ (Ideal.ofList F).radical := by
        obtain ⟨N, hN⟩ := hrad
        refine ⟨N, ?_⟩
        rw [mul_pow] at hN
        have strip : ∀ M (c : Poly n), X s ^ M * c ∈ Ideal.ofList F → c ∈ Ideal.ofList F := by
          intro M
          induction M with
          | zero => intro c hc; simpa using hc
          | succ M ihM =>
            intro c hc
            rw [pow_succ', mul_assoc] at hc
            exact ihM c (X_mul_mem_ofList hw F hF L hlen hfin hsL _ hc)
        exact strip N _ hN
      have hlt : b.totalDegree < k := by
        rw [← hd, totalDegree_mul_of_isDomain (X_ne_zero s) hb0, totalDegree_X]
        omega
      exact hb0 (ihk _ hlt b rfl hbfree hbrad)
    · apply hks
      refine ih (fun t ht => hSL t (Finset.mem_insert_of_mem ht))
        (F.map (killV s : Poly n →+* Poly n)) ?_ (by simpa using hlen) ?_ _ ?_ ?_
      · intro g hg
        simp only [List.mem_map] at hg
        obtain ⟨g, hg, rfl⟩ := hg
        obtain ⟨e, he, hge⟩ := hF g hg
        exact ⟨e, he, killV_isWH hge⟩
      · rwa [ofList_map_killV_sup F L hsL]
      · intro i hi
        by_cases his : i = s
        · subst his; exact freeOf_killV h
        · exact (hfree i (by simp [his, hi])).killV_other
      · obtain ⟨N, hN⟩ := hrad
        refine ⟨N, ?_⟩
        have := Ideal.mem_map_of_mem (killV s : Poly n →+* Poly n) hN
        rwa [Ideal.map_ofList, map_pow] at this

variable {d : ℕ} {f : Poly n}

/-- The restriction condition at degree `r`: `ℂ[x]/(I_r+(x_i:w_i≤r))` is finite dimensional, expressing isolatedness on the heavy coordinate subspace. -/
def HeavyRestrictionIsolated (w : Fin n → ℕ) (f : Poly n) (r : ℕ) : Prop :=
  Module.Finite ℂ (Poly n ⧸ (partialIdeal w f r ⊔ Ideal.span ((X : Fin n → Poly n) '' {i | w i ≤ r})))

/-- Theorem 3.6 under the restriction condition, without the stratum theorem. -/
theorem Setup.radical_of_heavyRestrictionIsolated (H : Setup w d f) (r : ℕ)
    (hfin : HeavyRestrictionIsolated w f r) (a : Poly n) (ha : a.IsWeightedHomogeneous w r)
    (hrad : a ∈ (partialIdeal w f r).radical) : a = 0 := by
  classical
  set L := (List.finRange n).filter (fun i => decide (w i ≤ r)) with hL
  set F := ((List.finRange n).filter (fun i => !decide (w i ≤ r))).map (fun j => pderiv j f)
    with hFdef
  have hFI : Ideal.ofList F = partialIdeal w f r := by
    rw [Ideal.ofList, partialIdeal]
    congr 1
    ext g
    simp [hFdef, List.mem_map, List.mem_filter, not_le]
  have hLI : Ideal.ofList (L.map X) = Ideal.span ((X : Fin n → Poly n) '' {i | w i ≤ r}) := by
    rw [Ideal.ofList]
    congr 1
    ext g
    simp [hL, List.mem_map, List.mem_filter]
  have hlen : F.length + L.length ≤ n := by
    have := List.length_eq_length_filter_add (l := List.finRange n) (fun i => decide (w i ≤ r))
    simp only [List.length_finRange] at this
    simp only [hFdef, hL, List.length_map]
    omega
  refine eq_zero_of_mem_radical_ofList H.pos L (Finset.univ.filter fun i => w i ≤ r)
    (fun s hs => by simpa [hL] using hs) F ?_ hlen ?_ a ?_ (hFI ▸ hrad)
  · intro g hg
    simp only [hFdef, List.mem_map, List.mem_filter, List.mem_finRange, true_and] at hg
    obtain ⟨j, -, rfl⟩ := hg
    exact ⟨d - w j, by have := H.big j; omega, pderiv_f_isWH H.hom j⟩
  · rw [hFI, hLI]; exact hfin
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi
    exact freeOf_of_pderiv_eq_zero (pderiv_eq_zero_of_lt ha i hi)

/-- The square-deformation property follows if each degree `0 < 3r < d` has at most one heavy variable or satisfies the restriction condition. -/
theorem Setup.squareDeformationProperty_of_restrictions (H : Setup w d f)
    (hres : ∀ r, 0 < r → 3 * r < d →
      (∀ i j, r < w i → r < w j → i = j) ∨ HeavyRestrictionIsolated w f r) :
    SquareDeformationProperty w d f := by
  intro r a ha h3 hrad
  suffices a = 0 by rw [this]; simp
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; exact H.radical_zero a ha hrad
  rcases hres r hr h3 with hY | hfin
  · exact H.radical_of_heavy_subsingleton r hY a ha hrad
  · exact H.radical_of_heavyRestrictionIsolated r hfin a ha hrad

/-- The main theorem for `2w_i < d` under the preceding restriction-or-single-heavy-variable condition at every degree `0 < 3r < d`. -/
theorem yau_conjecture_of_restrictions (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hbig : ∀ i, 2 * w i < d) (hiso : IsIsolatedSingularity f)
    (hres : ∀ r, 0 < r → 3 * r < d →
      (∀ i j, r < w i → r < w j → i = j) ∨ HeavyRestrictionIsolated w f r)
    (k : ℤ) (hk : k < 0) (δ : Derivation ℂ (MilnorAlgebra f) (MilnorAlgebra f))
    (hδ : IsDerivationOfDegree w f k δ) : δ = 0 :=
  have H : Setup w d f := ⟨hw, hf, hbig, hiso⟩
  H.no_neg_derivation (H.squareDeformationProperty_of_restrictions hres) k hk δ hδ

/-- The Brieskorn–Pham polynomial `∑ c_i x_i^{a_i}`. -/
def brieskornPham (c : Fin n → ℂ) (a : Fin n → ℕ) : Poly n :=
  ∑ i, C (c i) * X i ^ a i

lemma pderiv_brieskornPham (c : Fin n → ℂ) (a : Fin n → ℕ) (i : Fin n) :
    pderiv i (brieskornPham c a) = C (c i * a i) * X i ^ (a i - 1) := by
  classical
  rw [brieskornPham, map_sum, Finset.sum_eq_single i]
  · rw [Derivation.leibniz, Derivation.leibniz_pow, pderiv_X_self, pderiv_C]
    simp only [smul_eq_mul, mul_zero, add_zero, nsmul_eq_mul, map_mul, map_natCast]
    ring
  · intro j _ hj
    rw [Derivation.leibniz, Derivation.leibniz_pow, pderiv_X_of_ne (Ne.symm hj), pderiv_C]
    simp
  · simp

lemma brieskornPham_isWH (c : Fin n → ℂ) (a : Fin n → ℕ) (hwd : ∀ i, a i * w i = d) :
    (brieskornPham c a).IsWeightedHomogeneous w d := by
  rw [brieskornPham]
  refine IsWeightedHomogeneous.sum _ _ _ fun i _ => ?_
  have h := (isWeightedHomogeneous_C w (c i)).mul ((isWeightedHomogeneous_X ℂ w i).pow (a i))
  rwa [zero_add, smul_eq_mul, hwd i] at h

lemma pow_X_mem_of_pderiv_brieskornPham {c : Fin n → ℂ} {a : Fin n → ℕ} (hc : ∀ i, c i ≠ 0)
    (ha : ∀ i, 1 ≤ a i) (I : Ideal (Poly n)) (i : Fin n)
    (hI : pderiv i (brieskornPham c a) ∈ I) : X i ^ (a i - 1) ∈ I := by
  rw [pderiv_brieskornPham] at hI
  have hne : c i * a i ≠ 0 := mul_ne_zero (hc i) (by have := ha i; exact_mod_cast (by omega))
  have := I.mul_mem_left (C (c i * a i)⁻¹) hI
  rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hne, map_one, one_mul] at this

/-- The main theorem for Brieskorn–Pham polynomials with `c_i ≠ 0`, `a_i ≥ 3`, and positive weights satisfying `a_i w_i=d`, without the stratum hypothesis. -/
theorem yau_conjecture_brieskornPham (c : Fin n → ℂ) (a : Fin n → ℕ) (hc : ∀ i, c i ≠ 0)
    (ha : ∀ i, 3 ≤ a i) (hw : ∀ i, 0 < w i) (hwd : ∀ i, a i * w i = d)
    (k : ℤ) (hk : k < 0)
    (δ : Derivation ℂ (MilnorAlgebra (brieskornPham c a)) (MilnorAlgebra (brieskornPham c a)))
    (hδ : IsDerivationOfDegree w (brieskornPham c a) k δ) : δ = 0 := by
  have ha1 : ∀ i, 1 ≤ a i := fun i => by have := ha i; omega
  refine yau_conjecture_of_restrictions hw (brieskornPham_isWH c a hwd) ?_ ?_ ?_ k hk δ hδ
  · intro i
    have := hwd i; have := ha i; have := hw i
    nlinarith
  · exact finite_quotient_of_pow_X_mem _ fun i =>
      ⟨a i - 1, pow_X_mem_of_pderiv_brieskornPham hc ha1 _ i (pderiv_mem_jac i)⟩
  · intro r _ _
    right
    refine finite_quotient_of_pow_X_mem _ fun i => ?_
    by_cases hi : w i ≤ r
    · exact ⟨1, by
        rw [pow_one]
        exact Ideal.mem_sup_right (Ideal.subset_span ⟨i, hi, rfl⟩)⟩
    · exact ⟨a i - 1, pow_X_mem_of_pderiv_brieskornPham hc ha1 _ i
        (Ideal.mem_sup_left (Ideal.subset_span ⟨i, not_le.mp hi, rfl⟩))⟩

end Yau
