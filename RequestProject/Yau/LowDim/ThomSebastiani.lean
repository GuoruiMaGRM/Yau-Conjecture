import RequestProject.Yau.LowDim.LocalLevels

/-!
# Thom–Sebastiani sums and local Euler relations

Local Euler relations are preserved by sums in disjoint sets of variables.
The property holds for weighted homogeneous polynomials involving at most two
variables and for polynomials whose only critical point in their own variables
is the origin. Thus restrictions that are sums of such disjoint blocks give
another degree-by-degree criterion for the main theorem.
-/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ} {w : Fin n → ℕ} {d : ℕ} {f : Poly n}

/-- The variable sets of `g` and `h` are disjoint: for each `k`, either `∂_k g=0` or `∂_k h=0`. -/
def DisjointVars (g h : Poly n) : Prop := ∀ k, pderiv k g = 0 ∨ pderiv k h = 0

/-- The polynomial satisfies `LocalEulerAt` at every critical point. -/
def EulerGood (g : Poly n) : Prop :=
  ∀ x : Fin n → ℂ, (∀ k, eval x (pderiv k g) = 0) → LocalEulerAt g x

/-- Every critical point has zero coordinates in the variables on which the polynomial actually depends. -/
def OwnIsolated (g : Poly n) : Prop :=
  ∀ x : Fin n → ℂ, (∀ k, eval x (pderiv k g) = 0) → ∀ k, pderiv k g ≠ 0 → x k = 0

lemma DisjointVars.symm {g h : Poly n} (hd : DisjointVars g h) : DisjointVars h g :=
  fun k => (hd k).symm

/-- The local Euler relation for a Thom–Sebastiani sum. -/
lemma LocalEulerAt.add {g h : Poly n} (hd : DisjointVars g h) {x : Fin n → ℂ}
    (hg : LocalEulerAt g x) (hh : LocalEulerAt h x) : LocalEulerAt (g + h) x := by
  classical
  obtain ⟨e1, c1, he1, hc1, h1⟩ := hg
  obtain ⟨e2, c2, he2, hc2, h2⟩ := hh
  refine ⟨e1 * e2, fun k => if pderiv k h = 0 then e2 * c1 k else e1 * c2 k,
    by simp [he1, he2], fun k => by dsimp only; split_ifs <;> simp [hc1, hc2], ?_⟩
  have hk : ∀ k, (if pderiv k h = 0 then e2 * c1 k else e1 * c2 k) * pderiv k (g + h) =
      e2 * (c1 k * pderiv k g) + e1 * (c2 k * pderiv k h) := by
    intro k
    split_ifs with hk
    · simp only [map_add, hk]; ring
    · have h0 := (hd k).resolve_right hk
      simp only [map_add, h0]; ring
  rw [Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← h1, ← h2]
  ring

lemma crit_left_of_disjoint {g h : Poly n} (hd : DisjointVars g h) {x : Fin n → ℂ}
    (hx : ∀ k, eval x (pderiv k (g + h)) = 0) (k : Fin n) : eval x (pderiv k g) = 0 := by
  rcases hd k with h0 | h0
  · simp [h0]
  · simpa [h0] using hx k

lemma EulerGood.add {g h : Poly n} (hd : DisjointVars g h) (hg : EulerGood g)
    (hh : EulerGood h) : EulerGood (g + h) := fun x hx =>
  (hg x (crit_left_of_disjoint hd hx)).add hd
    (hh x (crit_left_of_disjoint hd.symm (by simpa [add_comm] using hx)))

lemma eulerGood_zero : EulerGood (0 : Poly n) :=
  fun _ _ => ⟨1, 0, by simp, by simp, by simp⟩

lemma DisjointVars.sum_right {ι : Type*} {g : Poly n} (s : Finset ι) (gs : ι → Poly n)
    (h : ∀ b ∈ s, DisjointVars g (gs b)) : DisjointVars g (∑ b ∈ s, gs b) := by
  intro k
  by_cases hk : pderiv k g = 0
  · exact Or.inl hk
  · right
    rw [map_sum]
    exact Finset.sum_eq_zero fun b hb => (h b hb k).resolve_left hk

/-- The property `EulerGood` is preserved by finite sums in pairwise disjoint sets of variables. -/
lemma EulerGood.sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (gs : ι → Poly n)
    (hd : (s : Set ι).Pairwise fun a b => DisjointVars (gs a) (gs b))
    (hg : ∀ a ∈ s, EulerGood (gs a)) : EulerGood (∑ a ∈ s, gs a) := by
  induction s using Finset.induction_on with
  | empty => simpa using eulerGood_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine EulerGood.add (DisjointVars.sum_right s gs fun b hb => ?_)
      (hg a (Finset.mem_insert_self a s))
      (ih (hd.mono (by simp)) fun b hb => hg b (Finset.mem_insert_of_mem hb))
    exact hd (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hb)
      (fun hab => ha (hab ▸ hb))

/-- A positive-degree weighted homogeneous polynomial involving at most two variables satisfies the local Euler relation at every critical point. -/
lemma eulerGood_of_free2 (hw : ∀ i, 0 < w i) {i j : Fin n} (hij : i ≠ j) {g : Poly n} {D : ℕ}
    (hg : g.IsWeightedHomogeneous w D) (hD : 0 < D) (hfree : Free2 i j g) : EulerGood g := by
  classical
  intro x hcrit
  by_cases hxij : x i ≠ 0 ∨ x j ≠ 0
  · obtain ⟨e, a1, b1, he, ha1, hb1, hab⟩ :=
      exists_local_quotient hw hij hg hD hfree x hxij (hcrit i) (hcrit j)
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
    refine ⟨C (D : ℂ), fun k => if k = i ∨ k = j then C (w k : ℂ) * X k else 0, ?_, ?_, ?_⟩
    · simpa using (show (D : ℂ) ≠ 0 by exact_mod_cast hD.ne')
    · intro k
      by_cases hk : k = i ∨ k = j
      · rcases hk with rfl | rfl <;> simp [hxij.1, hxij.2]
      · simp [hk]
    · have he := euler_identity hg
      rw [← smul_eq_C_mul, he]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : k = i ∨ k = j
      · simp only [hk, if_true, smul_eq_C_mul]; ring
      · push_neg at hk
        rw [(hfree k hk.1 hk.2).pderiv_eq_zero]
        simp

/-- A positive-degree weighted homogeneous polynomial isolated in its own variables satisfies the local Euler relation at every critical point, by Euler's identity. -/
lemma eulerGood_of_ownIsolated {g : Poly n} {D : ℕ} (hg : g.IsWeightedHomogeneous w D)
    (hD : 0 < D) (hiso : OwnIsolated g) : EulerGood g := by
  classical
  intro x hcrit
  refine ⟨C (D : ℂ), fun k => if pderiv k g = 0 then 0 else C (w k : ℂ) * X k, ?_, ?_, ?_⟩
  · simpa using (show (D : ℂ) ≠ 0 by exact_mod_cast hD.ne')
  · intro k
    by_cases hk : pderiv k g = 0
    · simp [hk]
    · simp [hk, hiso x hcrit k hk]
  · rw [← smul_eq_C_mul, euler_identity hg]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : pderiv k g = 0
    · simp [hk]
    · simp only [hk, if_false, smul_eq_C_mul]; ring

/-- A homogeneous block that involves at most two variables or is isolated in its own variables. -/
def GoodBlock (w : Fin n → ℕ) (d : ℕ) (g : Poly n) : Prop :=
  g.IsWeightedHomogeneous w d ∧ ((∃ i j, i ≠ j ∧ Free2 i j g) ∨ OwnIsolated g)

/-- The Thom–Sebastiani criterion at degree `r`: one light variable `u`, and `f|_{u=0}` is a finite sum of pairwise variable-disjoint good blocks. -/
def OneLightThomSebastiani (w : Fin n → ℕ) (d : ℕ) (f : Poly n) (r : ℕ) : Prop :=
  ∃ u : Fin n, (∀ l, l ≠ u → r < w l) ∧
    ∃ (m : ℕ) (gs : Fin m → Poly n), killV u f = ∑ a, gs a ∧
      (∀ a b, a ≠ b → DisjointVars (gs a) (gs b)) ∧ ∀ a, GoodBlock w d (gs a)

lemma GoodBlock.eulerGood (hw : ∀ i, 0 < w i) (hd : 0 < d) {g : Poly n} (hB : GoodBlock w d g) :
    EulerGood g := by
  obtain ⟨hg, ⟨i, j, hij, hfree⟩ | hiso⟩ := hB
  · exact eulerGood_of_free2 hw hij hg hd hfree
  · exact eulerGood_of_ownIsolated hg hd hiso

/-- The Thom–Sebastiani criterion implies `OneLightLocalEuler`. -/
lemma oneLightLocalEuler_of_thomSebastiani (hw : ∀ i, 0 < w i) (hd : 0 < d) {r : ℕ}
    (hTS : OneLightThomSebastiani w d f r) : OneLightLocalEuler w f r := by
  obtain ⟨u, hheavy, m, gs, hsum, hdisj, hgood⟩ := hTS
  refine ⟨u, hheavy, fun x _ _ hcrit => ?_⟩
  have : EulerGood (killV u f) := by
    rw [hsum]
    exact EulerGood.sum Finset.univ gs (fun a _ b _ hab => hdisj a b hab)
      fun a _ => (hgood a).eulerGood hw hd
  exact this x hcrit

/-- Theorem 3.6 with one light variable and a Thom–Sebastiani restriction. -/
theorem Setup.radical_of_one_light_thomSebastiani (H : Setup w d f) {r : ℕ} (hr : 0 < r)
    (h3r : 3 * r < d) (hTS : OneLightThomSebastiani w d f r)
    (a : Poly n) (ha : a.IsWeightedHomogeneous w r) (hrad : a ∈ (partialIdeal w f r).radical) :
    a = 0 := by
  obtain ⟨u, hheavy, hE⟩ := oneLightLocalEuler_of_thomSebastiani H.pos (by omega) hTS
  exact H.radical_of_one_light_localEuler hr h3r hheavy
    (fun x hx0 hxu hcrit => hE x hx0 hxu hcrit) a ha hrad

/-- The main theorem for `2w_i < d` if each degree `0 < 3r < d` satisfies one of the five local or elementary criteria, or the Thom–Sebastiani criterion. -/
theorem yau_conjecture_thom_sebastiani_levelwise (w : Fin n → ℕ) (d : ℕ) (f : Poly n)
    (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hbig : ∀ i, 2 * w i < d) (hcrit : HasIsolatedCriticalPoint f)
    (hlev : ∀ r, 0 < r → 3 * r < d →
      (∀ i j, r < w i → r < w j → i = j) ∨ HeavyRestrictionIsolated w f r ∨
        QuadraticIn (Finset.univ.filter fun i => r < w i) f ∨
        OneLightLocalEuler w f r ∨ LocalSquareCondition w f r ∨
        OneLightThomSebastiani w d f r)
    (k : ℤ) (hk : k < 0) (δ : Derivation ℂ (MilnorAlgebra f) (MilnorAlgebra f))
    (hδ : IsDerivationOfDegree w f k δ) : δ = 0 := by
  refine yau_conjecture_local_levelwise w d f hw hf hbig hcrit (fun r hr h3 => ?_) k hk δ hδ
  have hd : 0 < d := by omega
  rcases hlev r hr h3 with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (oneLightLocalEuler_of_thomSebastiani hw hd h))))

end Yau
