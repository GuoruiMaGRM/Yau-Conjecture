import RequestProject.Yau.LowDim.Restriction
import RequestProject.Yau.Appendix.Isolated
import RequestProject.Yau.Appendix.Syzygy
import RequestProject.Yau.Appendix.EulerModuli

/-!
# One light variable and two heavy variables

An elementary argument proves `x_u ∉ √(f_{y₁},f_{y₂})` when `u` is the only
light variable. A binary weighted homogeneous form satisfies a local Euler
relation at every nonzero critical point. Combine this with Euler's identity
for `f`, apply the Nullstellensatz to the ideal quotient, and use regularity of
the partial derivatives to obtain a contradiction in degree.
Together with the single-heavy-variable case this proves the main theorem
for at most three variables without the stratum hypothesis.
-/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ} {w : Fin n → ℕ}

/-! ### Polynomials involving few variables -/

lemma killV_monomial (k : Fin n) (ν : Fin n →₀ ℕ) (c : ℂ) :
    killV k (monomial ν c) = if ν k = 0 then monomial ν c else 0 := by
  classical
  split_ifs with h
  · exact freeOf_monomial h c
  · rw [killV, aeval_monomial, Finsupp.prod, Finset.prod_eq_zero (i := k)]
    · simp
    · simpa using h
    · simp [zero_pow h]

lemma coeff_eq_zero_of_freeOf {k : Fin n} {p : Poly n} (hp : FreeOf k p)
    {μ : Fin n →₀ ℕ} (hμ : μ k ≠ 0) : coeff μ p = 0 := by
  classical
  rw [← hp, p.as_sum, map_sum, coeff_sum]
  refine Finset.sum_eq_zero fun ν _ => ?_
  rw [killV_monomial]
  split_ifs with h
  · rw [coeff_monomial, if_neg]; rintro rfl; exact hμ h
  · simp

/-- The polynomial involves at most `x_i,x_j`. -/
def Free2 (i j : Fin n) (p : Poly n) : Prop := ∀ k, k ≠ i → k ≠ j → FreeOf k p

/-- A weighted homogeneous polynomial in `x_j` alone is a monomial. -/
lemma weight_single (j : Fin n) (m : ℕ) :
    Finsupp.weight w (Finsupp.single j m) = m * w j := by
  simp [Finsupp.weight_apply, Finsupp.sum_single_index]

lemma eq_C_mul_X_pow_of_freeOf {p : Poly n} {D : ℕ} (hp : p.IsWeightedHomogeneous w D)
    (j : Fin n) (hwj : 0 < w j) (hfree : ∀ k, k ≠ j → FreeOf k p) :
    ∃ c : ℂ, ∃ e : ℕ, p = C c * X j ^ e ∧ (c ≠ 0 → e * w j = D) := by
  classical
  refine ⟨coeff (Finsupp.single j (D / w j)) p, D / w j, ?_, fun hc => ?_⟩
  · ext μ
    rw [coeff_C_mul, coeff_X_pow]
    split_ifs with hμ
    · subst hμ; simp
    · rw [mul_zero]
      by_contra hne
      apply hμ
      have hk : ∀ k, k ≠ j → μ k = 0 := fun k hk => by
        by_contra h; exact hne (coeff_eq_zero_of_freeOf (hfree k hk) h)
      have hμj : μ = Finsupp.single j (μ j) := by
        ext k
        by_cases hkj : k = j
        · subst hkj; simp
        · simp [Ne.symm hkj, hk k hkj]
      have hwt := hp hne
      rw [hμj, weight_single] at hwt
      rw [hμj, ← hwt, Nat.mul_div_cancel _ hwj]
  · have := hp hc
    rwa [weight_single] at this

/-- The quotient of weighted homogeneous polynomials is weighted homogeneous. -/
lemma isWH_of_mul_eq {g h q : Poly n} {D L : ℕ} (hg : g.IsWeightedHomogeneous w D)
    (hh : h.IsWeightedHomogeneous w L) (hh0 : h ≠ 0) (hg0 : g ≠ 0) (hgq : g = h * q) :
    L ≤ D ∧ q.IsWeightedHomogeneous w (D - L) := by
  classical
  have hcomp := weightedHomogeneousComponent_mul_of_right q h L D hh
  rw [mul_comm h q] at hgq
  rw [← hgq, hg.weightedHomogeneousComponent_same] at hcomp
  split_ifs at hcomp with hLD
  · refine ⟨hLD, ?_⟩
    have : q = weightedHomogeneousComponent w (D - L) q := by
      have h2 : (q - weightedHomogeneousComponent w (D - L) q) * h = 0 := by
        rw [sub_mul, ← hcomp, hgq, sub_self]
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact sub_eq_zero.mp h3
      · exact absurd h3 hh0
    rw [this]
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  · exact absurd hcomp hg0

lemma freeOf_of_mul_eq {k : Fin n} {g h q : Poly n} (hg : FreeOf k g) (hh : FreeOf k h)
    (hh0 : h ≠ 0) (hgq : g = h * q) : FreeOf k q := by
  unfold FreeOf at *
  apply mul_left_cancel₀ hh0
  calc h * killV k q = killV k h * killV k q := by rw [hh]
    _ = killV k (h * q) := (map_mul _ _ _).symm
    _ = killV k g := by rw [hgq]
    _ = g := hg
    _ = h * q := hgq

lemma Free2.of_mul_eq {i j : Fin n} {g h q : Poly n} (hg : Free2 i j g) (hh : Free2 i j h)
    (hh0 : h ≠ 0) (hgq : g = h * q) : Free2 i j q :=
  fun k hki hkj => freeOf_of_mul_eq (hg k hki hkj) (hh k hki hkj) hh0 hgq

/-- Extract the highest power of `h` dividing `g`. -/
lemma exists_pow_mul_not_dvd {i j : Fin n} {h : Poly n} {L : ℕ}
    (hh : h.IsWeightedHomogeneous w L) (hL : 0 < L) (hh0 : h ≠ 0) (hhf : Free2 i j h) :
    ∀ (D : ℕ) (g : Poly n), g.IsWeightedHomogeneous w D → g ≠ 0 → Free2 i j g →
      ∃ (m : ℕ) (v : Poly n) (D' : ℕ), g = h ^ m * v ∧ ¬ h ∣ v ∧ Free2 i j v ∧
        v.IsWeightedHomogeneous w D' := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
  intro g hg hg0 hgf
  by_cases hdvd : h ∣ g
  · obtain ⟨q, hq⟩ := hdvd
    obtain ⟨hLD, hqw⟩ := isWH_of_mul_eq hg hh hh0 hg0 hq
    have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; exact hg0 hq
    obtain ⟨m, v, D', hv, hnd, hvf, hvw⟩ :=
      ih (D - L) (by omega) q hqw hq0 (hgf.of_mul_eq hhf hh0 hq)
    exact ⟨m + 1, v, D', by rw [hq, hv, pow_succ]; ring, hnd, hvf, hvw⟩
  · exact ⟨0, g, D, by simp, hdvd, hgf, hg⟩

/-- A binary weighted homogeneous form vanishes at its critical points, by Euler's identity. -/
lemma eval_eq_zero_of_crit {i j : Fin n} {g : Poly n} {D : ℕ}
    (hg : g.IsWeightedHomogeneous w D) (hD : 0 < D) (hgf : Free2 i j g) (x : Fin n → ℂ)
    (hxi : eval x (pderiv i g) = 0) (hxj : eval x (pderiv j g) = 0) : eval x g = 0 := by
  have he := congrArg (eval x) (euler_identity hg)
  rw [map_sum, Finset.sum_eq_zero] at he
  · rw [smul_eval] at he
    rcases mul_eq_zero.mp he with h | h
    · exact absurd h (by exact_mod_cast hD.ne')
    · exact h
  · intro l _
    rw [smul_eval]
    by_cases hli : l = i
    · subst hli; simp [hxi]
    by_cases hlj : l = j
    · subst hlj; simp [hxj]
    rw [(hgf l hli hlj).pderiv_eq_zero]; simp

/-- A local division lemma given a suitable equation `h` of the orbit through `x`. -/
theorem exists_local_quotient_of_h {i j : Fin n} {g : Poly n} {D : ℕ}
    (hg : g.IsWeightedHomogeneous w D) (hD : 0 < D) (hgf : Free2 i j g) (x : Fin n → ℂ)
    (hxi : eval x (pderiv i g) = 0) (hxj : eval x (pderiv j g) = 0)
    {h : Poly n} {L : ℕ} (hh : h.IsWeightedHomogeneous w L) (hL : 0 < L) (hhf : Free2 i j h)
    (hhx : eval x h = 0) {k : Fin n} (hk : eval x (pderiv k h) ≠ 0)
    (hP : ∀ (v : Poly n) (D' : ℕ), v.IsWeightedHomogeneous w D' → Free2 i j v →
      eval x v = 0 → h ∣ v) :
    ∃ e a : Poly n, eval x e ≠ 0 ∧ eval x a = 0 ∧ e * g = a * pderiv k g := by
  have hh0 : h ≠ 0 := by rintro rfl; simp at hk
  by_cases hg0 : g = 0
  · exact ⟨1, 0, by simp, by simp, by simp [hg0]⟩
  obtain ⟨m, v, D', hgv, hnd, hvf, hvw⟩ := exists_pow_mul_not_dvd hh hL hh0 hhf D g hg hg0 hgf
  have hvx : eval x v ≠ 0 := fun h0 => hnd (hP v D' hvw hvf h0)
  have hgx := eval_eq_zero_of_crit hg hD hgf x hxi hxj
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
    rcases m with _ | m'
    · rw [pow_zero, one_mul] at hgv; rw [hgv] at hgx; exact absurd hgx hvx
    · exact ⟨m', rfl⟩
  refine ⟨((m' + 1 : ℕ) : Poly n) * pderiv k h * v + h * pderiv k v, h * v, ?_, ?_, ?_⟩
  · simp only [map_add, map_mul, map_natCast, hhx, zero_mul, add_zero]
    exact mul_ne_zero (mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero m') hk) hvx
  · simp [hhx]
  · rw [hgv, Derivation.leibniz, Derivation.leibniz_pow]
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
    push_cast
    ring

lemma weight_eq_two {i j : Fin n} (hij : i ≠ j) {μ : Fin n →₀ ℕ}
    (hμ : ∀ k, k ≠ i → k ≠ j → μ k = 0) :
    Finsupp.weight w μ = μ i * w i + μ j * w j := by
  have : μ = Finsupp.single i (μ i) + Finsupp.single j (μ j) := by
    ext k
    by_cases hki : k = i
    · subst hki; simp [hij]
    by_cases hkj : k = j
    · subst hkj; simp [Ne.symm hij]
    simp [Ne.symm hki, Ne.symm hkj, hμ k hki hkj]
  conv_lhs => rw [this]
  rw [map_add, weight_single, weight_single]

lemma Free2.swap {i j : Fin n} {p : Poly n} (hp : Free2 i j p) : Free2 j i p :=
  fun k hkj hki => hp k hki hkj

lemma Free2.C {i j : Fin n} (c : ℂ) : Free2 i j (C c : Poly n) := fun _ _ _ => freeOf_C c

lemma Free2.X_left {i j : Fin n} : Free2 i j (X i : Poly n) :=
  fun _ hki _ => freeOf_X (Ne.symm hki)

lemma Free2.X_right {i j : Fin n} : Free2 i j (X j : Poly n) :=
  fun _ _ hkj => freeOf_X (Ne.symm hkj)

lemma Free2.add {i j : Fin n} {p q : Poly n} (hp : Free2 i j p) (hq : Free2 i j q) :
    Free2 i j (p + q) := fun k hki hkj => (hp k hki hkj).add (hq k hki hkj)

lemma Free2.sub {i j : Fin n} {p q : Poly n} (hp : Free2 i j p) (hq : Free2 i j q) :
    Free2 i j (p - q) := fun k hki hkj => (hp k hki hkj).sub (hq k hki hkj)

lemma Free2.mul {i j : Fin n} {p q : Poly n} (hp : Free2 i j p) (hq : Free2 i j q) :
    Free2 i j (p * q) := fun k hki hkj => (hp k hki hkj).mul (hq k hki hkj)

lemma Free2.pow {i j : Fin n} {p : Poly n} (hp : Free2 i j p) (m : ℕ) :
    Free2 i j (p ^ m) := fun k hki hkj => (hp k hki hkj).pow m

/-- Divisibility by a coordinate. -/
lemma dvd_of_eval_axis (hw : ∀ i, 0 < w i) {i j : Fin n} {v : Poly n} {D : ℕ}
    (hv : v.IsWeightedHomogeneous w D) (hvf : Free2 i j v) (x : Fin n → ℂ) (hxi : x i = 0)
    (hxj : x j ≠ 0) (h0 : eval x v = 0) : X i ∣ v := by
  obtain ⟨c, e, hce, -⟩ := eq_C_mul_X_pow_of_freeOf (killV_isWH (v := i) hv) j (hw j)
    (fun k hkj => by
      by_cases hki : k = i
      · subst hki; exact freeOf_killV v
      · exact (hvf k hki hkj).killV_other)
  have hx' : eval x (killV i v) = 0 := by
    rw [eval_killV, show Function.update x i 0 = x by rw [← hxi, Function.update_eq_self]]
    exact h0
  rw [hce] at hx'
  simp only [map_mul, eval_C, map_pow, eval_X, mul_eq_zero, pow_eq_zero_iff', hxj,
    false_and, or_false] at hx'
  have : killV i v = 0 := by rw [hce, hx']; simp
  exact exists_X_mul_of_killV_eq_zero this

/-- Divisibility by the equation of a general orbit. -/
lemma dvd_of_eval_generic (hw : ∀ i, 0 < w i) {i j : Fin n} (hij : i ≠ j) {α β : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hcop : Nat.Coprime α β) (hαβ : α * w j = β * w i)
    (x : Fin n → ℂ) (hxi : x i ≠ 0) (hxj : x j ≠ 0) :
    ∀ (D : ℕ) (v : Poly n), v.IsWeightedHomogeneous w D → Free2 i j v → eval x v = 0 →
      (C (x j ^ α) * X i ^ β - C (x i ^ β) * X j ^ α) ∣ v := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
  intro v hv hvf h0
  obtain ⟨K, hK⟩ := exists_killV_decomp (v := i) v
  obtain ⟨c, e, hce, hcD⟩ := eq_C_mul_X_pow_of_freeOf (killV_isWH (v := i) hv) j (hw j)
    (fun k hkj => by
      by_cases hki : k = i
      · subst hki; exact freeOf_killV v
      · exact (hvf k hki hkj).killV_other)
  have hXKe : X i * K = v - killV i v := by
    rw [eq_sub_iff_add_eq, add_comm]; exact hK.symm
  have hXK : (X i * K).IsWeightedHomogeneous w D := by
    rw [hXKe]; exact isWH_sub hv (killV_isWH hv)
  have hKw : K.IsWeightedHomogeneous w (D - w i) := isWH_of_X_mul hXK
  have hKf : Free2 i j K := fun k hki hkj => FreeOf.of_X_mul hki (by
    rw [hXKe]
    exact (hvf k hki hkj).sub ((hvf k hki hkj).killV_other))
  have hvce : v = C c * X j ^ e + X i * K := by rw [hK, hce]
  by_cases hK0 : K = 0
  · have hc : c = 0 := by
      rw [hvce, hK0] at h0
      simpa [hxj] using h0
    rw [hvce, hK0, hc]; simp
  have hDi : w i ≤ D := by
    obtain ⟨μ, hμ⟩ : ∃ μ, coeff μ K ≠ 0 := by
      by_contra h; push_neg at h; exact hK0 (MvPolynomial.ext _ _ h)
    have hmem : μ + Finsupp.single i 1 ∈ (X i * K).support := by
      rw [mem_support_iff, mul_comm, coeff_mul_X]; exact hμ
    have := degree_le_of_isWH hXK hmem (v := i)
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at this
    nlinarith
  have hlt : D - w i < D := by have := hw i; omega
  by_cases hc : c = 0
  · have hvK : v = X i * K := by rw [hvce, hc]; simp
    have hKx : eval x K = 0 := by
      rw [hvK, map_mul, eval_X] at h0
      exact (mul_eq_zero.mp h0).resolve_left hxi
    obtain ⟨q, hq⟩ := ih _ hlt K hKw hKf hKx
    exact ⟨X i * q, by rw [hvK, hq]; ring⟩
  have heD := hcD hc
  by_cases heα : α ≤ e
  · obtain ⟨β', rfl⟩ : ∃ β', β = β' + 1 := ⟨β - 1, by omega⟩
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + α := ⟨e - α, by omega⟩
    set K' := K + C (c * x j ^ α / x i ^ (β' + 1)) * X i ^ β' * X j ^ e' with hK'
    have hxβ : x i ^ (β' + 1) ≠ 0 := pow_ne_zero _ hxi
    have hid : v + C (c / x i ^ (β' + 1)) * X j ^ e' *
        (C (x j ^ α) * X i ^ (β' + 1) - C (x i ^ (β' + 1)) * X j ^ α) = X i * K' := by
      rw [hvce, hK']
      have h1 : C (c / x i ^ (β' + 1)) * C (x i ^ (β' + 1)) = (C c : Poly n) := by
        rw [← map_mul, div_mul_cancel₀ _ hxβ]
      have h2 : C (c / x i ^ (β' + 1)) * C (x j ^ α) =
          (C (c * x j ^ α / x i ^ (β' + 1)) : Poly n) := by
        rw [← map_mul]; congr 1; ring
      linear_combination (X j ^ (e' + α) : Poly n) * (-h1) +
        (X i ^ (β' + 1) * X j ^ e' : Poly n) * h2
    have hdeg : β' * w i + e' * w j = D - w i := by
      have : β' * w i + e' * w j + w i = D := by nlinarith
      omega
    have hK'w : K'.IsWeightedHomogeneous w (D - w i) := by
      refine hKw.add ?_
      have hm := ((isWeightedHomogeneous_C w (c * x j ^ α / x i ^ (β' + 1))).mul
        ((isWeightedHomogeneous_X ℂ w i).pow β')).mul ((isWeightedHomogeneous_X ℂ w j).pow e')
      rwa [smul_eq_mul, smul_eq_mul, zero_add, hdeg] at hm
    have hK'f : Free2 i j K' :=
      hKf.add (((Free2.C _).mul (Free2.X_left.pow _)).mul (Free2.X_right.pow _))
    have hK'x : eval x K' = 0 := by
      have := congrArg (eval x) hid
      have hhx : eval x (C (x j ^ α) * X i ^ (β' + 1) - C (x i ^ (β' + 1)) * X j ^ α) = 0 := by
        simp; ring
      simp only [map_add, map_mul, hhx, mul_zero, add_zero, h0, eval_X] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hxi
    obtain ⟨q, hq⟩ := ih _ hlt K' hK'w hK'f hK'x
    refine ⟨X i * q - C (c / x i ^ (β' + 1)) * X j ^ e', ?_⟩
    have hv' : v = X i * K' - C (c / x i ^ (β' + 1)) * X j ^ e' *
        (C (x j ^ α) * X i ^ (β' + 1) - C (x i ^ (β' + 1)) * X j ^ α) := by
      rw [← hid]; ring
    rw [hv', hq]; ring
  · exfalso
    apply hK0
    ext μ
    rw [coeff_zero]
    by_contra hμ
    have hwt := hKw hμ
    have hμ0 : ∀ k, k ≠ i → k ≠ j → μ k = 0 := fun k hki hkj => by
      by_contra h; exact hμ (coeff_eq_zero_of_freeOf (hKf k hki hkj) h)
    rw [weight_eq_two hij hμ0] at hwt
    have hsum : (μ i + 1) * w i + μ j * w j = e * w j := by
      rw [heD, add_mul, one_mul]
      have := Nat.sub_add_cancel hDi
      generalize μ i * w i = A at *
      generalize μ j * w j = B at *
      omega
    obtain ⟨t, rfl⟩ : ∃ t, e = μ j + t := by
      refine ⟨e - μ j, ?_⟩
      by_contra hne
      have hle : e ≤ μ j := by omega
      have := Nat.mul_le_mul_right (w j) hle
      have := hw i
      nlinarith
    have h1 : (μ i + 1) * w i = t * w j := by nlinarith
    have h2 : (μ i + 1) * α * w i = t * β * w i := by
      calc (μ i + 1) * α * w i = α * ((μ i + 1) * w i) := by ring
        _ = t * (α * w j) := by rw [h1]; ring
        _ = t * β * w i := by rw [hαβ]; ring
    have h3 : (μ i + 1) * α = t * β := Nat.eq_of_mul_eq_mul_right (hw i) h2
    have h4 : α ∣ t := (Nat.Coprime.dvd_of_dvd_mul_right hcop ⟨μ i + 1, by rw [← h3]; ring⟩)
    have ht0 : 0 < t := by
      rcases Nat.eq_zero_or_pos t with ht | ht
      · rw [ht, zero_mul] at h1; have := hw i; nlinarith
      · exact ht
    have := Nat.le_of_dvd ht0 h4
    omega

/-- Local division: at a nonzero critical point of a binary weighted homogeneous form, `e g = a ∂_i g + b ∂_j g`, with `e(x) ≠ 0` and `a(x)=b(x)=0`. -/
theorem exists_local_quotient (hw : ∀ i, 0 < w i) {i j : Fin n} (hij : i ≠ j) {g : Poly n}
    {D : ℕ} (hg : g.IsWeightedHomogeneous w D) (hD : 0 < D) (hgf : Free2 i j g)
    (x : Fin n → ℂ) (hx : x i ≠ 0 ∨ x j ≠ 0)
    (hxi : eval x (pderiv i g) = 0) (hxj : eval x (pderiv j g) = 0) :
    ∃ e a b : Poly n, eval x e ≠ 0 ∧ eval x a = 0 ∧ eval x b = 0 ∧
      e * g = a * pderiv i g + b * pderiv j g := by
  by_cases hxi0 : x i = 0
  · have hxj0 : x j ≠ 0 := hx.resolve_left (not_not.mpr hxi0)
    obtain ⟨e, a, he, ha, hea⟩ := exists_local_quotient_of_h hg hD hgf x hxi hxj
      (isWeightedHomogeneous_X ℂ w i) (hw i) Free2.X_left (by simp [hxi0]) (k := i) (by simp)
      (fun v D' hv hvf hv0 => dvd_of_eval_axis hw hv hvf x hxi0 hxj0 hv0)
    exact ⟨e, a, 0, he, ha, by simp, by rw [hea]; ring⟩
  by_cases hxj0 : x j = 0
  · obtain ⟨e, b, he, hb, heb⟩ := exists_local_quotient_of_h hg hD hgf x hxi hxj
      (isWeightedHomogeneous_X ℂ w j) (hw j) Free2.X_right (by simp [hxj0]) (k := j) (by simp)
      (fun v D' hv hvf hv0 => dvd_of_eval_axis hw (i := j) (j := i) hv hvf.swap x hxj0 hxi0 hv0)
    exact ⟨e, 0, b, he, by simp, hb, by rw [heb]; ring⟩
  set g0 := Nat.gcd (w i) (w j) with hg0def
  have hg0 : 0 < g0 := Nat.gcd_pos_of_pos_left _ (hw i)
  obtain ⟨α, hαdef⟩ : ∃ α, w i = α * g0 := ⟨w i / g0, (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm⟩
  obtain ⟨β, hβdef⟩ : ∃ β, w j = β * g0 := ⟨w j / g0, (Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)).symm⟩
  have hα : 0 < α := by
    rcases Nat.eq_zero_or_pos α with h | h
    · have := hw i; rw [hαdef, h, zero_mul] at this; omega
    · exact h
  have hβ : 0 < β := by
    rcases Nat.eq_zero_or_pos β with h | h
    · have := hw j; rw [hβdef, h, zero_mul] at this; omega
    · exact h
  have hcop : Nat.Coprime α β := by
    have := Nat.coprime_div_gcd_div_gcd (m := w i) (n := w j) hg0
    rwa [← hg0def, hαdef, hβdef, Nat.mul_div_cancel _ hg0, Nat.mul_div_cancel _ hg0] at this
  have hαβ : α * w j = β * w i := by rw [hαdef, hβdef]; ring
  have hhw : (C (x j ^ α) * X i ^ β - C (x i ^ β) * X j ^ α : Poly n).IsWeightedHomogeneous w
      (β * w i) := by
    refine isWH_sub ?_ ?_
    · have := (isWeightedHomogeneous_C w (x j ^ α)).mul ((isWeightedHomogeneous_X ℂ w i).pow β)
      rwa [zero_add, smul_eq_mul] at this
    · have := (isWeightedHomogeneous_C w (x i ^ β)).mul ((isWeightedHomogeneous_X ℂ w j).pow α)
      rwa [zero_add, smul_eq_mul, hαβ] at this
  obtain ⟨e, a, he, ha, hea⟩ := exists_local_quotient_of_h hg hD hgf x hxi hxj hhw
    (Nat.mul_pos hβ (hw i)) (((Free2.C _).mul (Free2.X_left.pow _)).sub
      ((Free2.C _).mul (Free2.X_right.pow _))) (by simp; ring) (k := i) (by
      obtain ⟨β', rfl⟩ : ∃ β', β = β' + 1 := ⟨β - 1, by omega⟩
      simp [Derivation.leibniz_pow, Pi.single_eq_of_ne hij.symm, hxi0, hxj0,
        Nat.cast_add_one_ne_zero])
    (fun v D' hv hvf hv0 => dvd_of_eval_generic hw hij hα hβ hcop hαβ x hxi0 hxj0 D' v hv hvf hv0)
  exact ⟨e, a, 0, he, ha, by simp, by rw [hea]; ring⟩

/-! ### One light variable and two heavy variables -/

variable {d : ℕ} {f : Poly n}

/-- The ideal quotient `(I:x_u)`. -/
def colonX (I : Ideal (Poly n)) (u : Fin n) : Ideal (Poly n) where
  carrier := {s | X u * s ∈ I}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, mul_add] at *; exact I.add_mem ha hb
  zero_mem' := by simp
  smul_mem' c s hs := by
    simp only [Set.mem_setOf_eq, smul_eq_mul] at *
    rw [mul_left_comm]; exact I.mul_mem_left c hs

/-- With one light and two heavy variables, `x_u ∉ √I_r`. -/
theorem Setup.X_not_mem_radical_of_one_light (H : Setup w d f) {r : ℕ} {u i j : Fin n}
    (hui : u ≠ i) (huj : u ≠ j) (hij : i ≠ j) (hall : ∀ l, l = u ∨ l = i ∨ l = j)
    (hu : w u ≤ r) (hi : r < w i) (hj : r < w j) :
    X u ∉ (partialIdeal w f r).radical := by
  classical
  intro hX
  set I := partialIdeal w f r with hIdef
  have hlight : ∀ l, r < w l → l = i ∨ l = j := by
    intro l hl
    rcases hall l with rfl | rfl | rfl
    · omega
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hIlist : I = Ideal.ofList [pderiv i f, pderiv j f] := by
    rw [hIdef, partialIdeal, Ideal.ofList]
    congr 1
    ext p
    simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_cons,
      List.not_mem_nil, or_false]
    constructor
    · rintro ⟨l, hl, rfl⟩
      rcases hlight l hl with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨i, hi, rfl⟩
      · exact ⟨j, hj, rfl⟩
  have hfi : pderiv i f ∈ I := Ideal.subset_span ⟨i, hi, rfl⟩
  have hfj : pderiv j f ∈ I := Ideal.subset_span ⟨j, hj, rfl⟩
  have hIle : ∀ x : Fin n → ℂ, eval x (pderiv i f) = 0 → eval x (pderiv j f) = 0 →
      ∀ p ∈ I, eval x p = 0 := by
    intro x h1 h2 p hp
    have : I ≤ RingHom.ker (eval x) := by
      rw [hIdef, partialIdeal, Ideal.span_le]
      rintro _ ⟨l, hl, rfl⟩
      rcases hlight l hl with rfl | rfl
      · exact h1
      · exact h2
    exact this hp
  obtain ⟨N0, hN0⟩ := hX
  have hd : 0 < d := by have := H.big i; omega
  obtain ⟨F, hF⟩ := exists_killV_decomp (v := u) f
  set g := killV u f with hgdef
  have hgw : g.IsWeightedHomogeneous w d := killV_isWH H.hom
  have hgf : Free2 i j g := fun k hki hkj => by
    rcases hall k with rfl | rfl | rfl
    · exact freeOf_killV f
    · exact absurd rfl hki
    · exact absurd rfl hkj
  have hgl : ∀ l, l ≠ u → pderiv l g = pderiv l f - X u * pderiv l F := by
    intro l hl
    have : pderiv l f = pderiv l g + X u * pderiv l F := by
      have h0 : pderiv l (X u : Poly n) = 0 := pderiv_X_of_ne hl
      conv_lhs => rw [hF]
      rw [map_add, Derivation.leibniz, h0]
      simp only [smul_eq_mul, mul_zero, add_zero]
    rw [this]; ring
  have hfu : pderiv u f = F + X u * pderiv u F := by
    conv_lhs => rw [hF]
    rw [map_add, Derivation.leibniz, pderiv_X_self, (freeOf_killV f).pderiv_eq_zero]
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
      have hlu : l ≠ u := Finset.ne_of_mem_erase hl
      rw [smul_eq_C_mul]
      refine Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ?_)
      rcases hall l with rfl | rfl | rfl
      · exact absurd rfl hlu
      · exact hfi
      · exact hfj
    have : C (d : ℂ) * g + X u * (C (d : ℂ) * F - C (w u : ℂ) * pderiv u f) =
        ∑ l ∈ Finset.univ.erase u, (w l : ℂ) • (X l * pderiv l f) := by
      have h2 : C (d : ℂ) * f = (w u : ℂ) • (X u * pderiv u f) +
          ∑ l ∈ Finset.univ.erase u, (w l : ℂ) • (X l * pderiv l f) := by
        rw [← hsplit, ← he, smul_eq_C_mul]
      rw [smul_eq_C_mul] at h2
      linear_combination h2 - C (d : ℂ) * hF
    rw [this]; exact hrest
  -- The local step.
  have hloc : ∀ x : Fin n → ℂ, x ≠ 0 → eval x (pderiv i f) = 0 → eval x (pderiv j f) = 0 →
      ∃ s, eval x s ≠ 0 ∧ X u * s ∈ I := by
    intro x hx0 h1 h2
    have hxu : x u = 0 := by
      have := hIle x h1 h2 _ hN0
      simp only [map_pow, eval_X, pow_eq_zero_iff', ne_eq] at this
      exact this.1
    have hgi : eval x (pderiv i g) = 0 := by rw [hgl i hui.symm]; simp [h1, hxu]
    have hgj : eval x (pderiv j g) = 0 := by rw [hgl j huj.symm]; simp [h2, hxu]
    have hxij : x i ≠ 0 ∨ x j ≠ 0 := by
      by_contra h
      push_neg at h
      apply hx0
      funext l
      rcases hall l with rfl | rfl | rfl
      · simp [hxu]
      · simp [h.1]
      · simp [h.2]
    obtain ⟨e, a, b, he, ha, hb, hab⟩ := exists_local_quotient H.pos hij hgw hd hgf x hxij hgi hgj
    have hfux : eval x (pderiv u f) ≠ 0 := by
      intro h3
      apply hx0
      apply H.common_zero x
      intro l
      rcases hall l with rfl | rfl | rfl
      · exact h3
      · exact h1
      · exact h2
    refine ⟨e * (C (d : ℂ) * F - C (w u : ℂ) * pderiv u f) -
      C (d : ℂ) * (a * pderiv i F + b * pderiv j F), ?_, ?_⟩
    · have hFx : eval x F = eval x (pderiv u f) := by rw [hfu]; simp [hxu]
      have hdu : (d : ℂ) - w u ≠ 0 := by
        have := H.big u
        rw [sub_ne_zero]; exact_mod_cast (by omega : d ≠ w u)
      simp only [map_sub, map_mul, map_add, eval_C, ha, hb, zero_mul, add_zero, mul_zero,
        sub_zero, hFx]
      rw [← sub_mul]
      exact mul_ne_zero he (mul_ne_zero hdu hfux)
    · have hgli := hgl i hui.symm
      have hglj := hgl j huj.symm
      have heq : X u * (e * (C (d : ℂ) * F - C (w u : ℂ) * pderiv u f) -
          C (d : ℂ) * (a * pderiv i F + b * pderiv j F)) =
          e * (C (d : ℂ) * g + X u * (C (d : ℂ) * F - C (w u : ℂ) * pderiv u f)) -
          C (d : ℂ) * (a * pderiv i f + b * pderiv j f) := by
        linear_combination (-C (d : ℂ) * a) * hgli + (-C (d : ℂ) * b) * hglj +
          (-C (d : ℂ)) * hab
      rw [heq]
      exact I.sub_mem (I.mul_mem_left _ hEuler)
        (I.mul_mem_left _ (I.add_mem (I.mul_mem_left _ hfi) (I.mul_mem_left _ hfj)))
  -- Apply the Nullstellensatz to the ideal quotient.
  set K := colonX I u
  have hIK : I ≤ K := fun p hp => I.mul_mem_left _ hp
  have hzero : ∀ x ∈ zeroLocus ℂ K, x = 0 := by
    intro x hx
    rw [mem_zeroLocus_iff] at hx
    by_contra hx0
    have h1 : eval x (pderiv i f) = 0 := by simpa using hx _ (hIK hfi)
    have h2 : eval x (pderiv j f) = 0 := by simpa using hx _ (hIK hfj)
    obtain ⟨s, hs, hsK⟩ := hloc x hx0 h1 h2
    exact hs (by simpa using hx s hsK)
  have hfuK : pderiv u f ∈ K.radical := by
    have hmem : pderiv u f ∈ vanishingIdeal ℂ (zeroLocus ℂ K) := by
      rw [mem_vanishingIdeal_iff]
      intro x hx
      rw [hzero x hx]
      exact eval_zero_of_isWH_pos (pderiv_f_isWH H.hom u) (by have := H.big u; omega)
    rwa [vanishingIdeal_zeroLocus_eq_radical] at hmem
  obtain ⟨N, hN⟩ := hfuK
  -- Regularity of `f_u` modulo `(f_i,f_j)`.
  have h3n : [pderiv i f, pderiv j f, pderiv u f].length ≤ n := by
    have := Fin.val_ne_of_ne hui
    have := Fin.val_ne_of_ne huj
    have := Fin.val_ne_of_ne hij
    have := u.isLt; have := i.isLt; have := j.isLt
    simp only [List.length_cons, List.length_nil]
    omega
  have hhom : ∀ g ∈ [pderiv i f, pderiv j f, pderiv u f],
      ∃ e, 0 < e ∧ g.IsWeightedHomogeneous w e := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact ⟨d - w i, by have := H.big i; omega, pderiv_f_isWH H.hom i⟩
    · exact ⟨d - w j, by have := H.big j; omega, pderiv_f_isWH H.hom j⟩
    · exact ⟨d - w u, by have := H.big u; omega, pderiv_f_isWH H.hom u⟩
  have hfin : Module.Finite ℂ (Poly n ⧸ Ideal.ofList [pderiv i f, pderiv j f, pderiv u f]) := by
    have hle : jacobianIdeal f ≤ Ideal.ofList [pderiv i f, pderiv j f, pderiv u f] := by
      rw [jacobianIdeal, Ideal.span_le]
      rintro _ ⟨l, rfl⟩
      apply Ideal.subset_span
      rcases hall l with rfl | rfl | rfl <;> simp
    haveI : Module.Finite ℂ (MilnorAlgebra f) := H.iso
    exact Module.Finite.of_surjective (Ideal.Quotient.factorₐ ℂ hle).toLinearMap
      (Ideal.Quotient.factor_surjective hle)
  have hreg := isWeaklyRegular_of_finite_quotient H.pos _ h3n hhom hfin
  rw [isWeaklyRegular_self_iff] at hreg
  have hreg' : ∀ b, pderiv u f * b ∈ I → b ∈ I := by
    intro b hb
    have := hreg 2 (by simp) b
    simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.take_succ_cons,
      List.take_zero] at this
    rw [hIlist] at hb ⊢
    exact this hb
  have hXI : X u ∈ I := by
    have key : ∀ m, X u * pderiv u f ^ m ∈ I → X u ∈ I := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        intro h
        apply ih
        apply hreg'
        rw [pow_succ] at h
        rw [show pderiv u f * (X u * pderiv u f ^ m) = X u * (pderiv u f ^ m * pderiv u f) by
          ring]
        exact h
    exact key N hN
  rw [hIlist] at hXI
  have := le_degree_of_mem_ofList (c := min (d - w i) (d - w j))
    [pderiv i f, pderiv j f] (by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact ⟨d - w i, min_le_left _ _, pderiv_f_isWH H.hom i⟩
      · exact ⟨d - w j, min_le_right _ _, pderiv_f_isWH H.hom j⟩)
    (isWeightedHomogeneous_X ℂ w u) (X_ne_zero u) hXI
  have := H.big i
  have := H.big j
  omega

/-- Theorem 3.6 with one light and two heavy variables, without the stratum theorem. -/
theorem Setup.radical_of_one_light (H : Setup w d f) {r : ℕ} {u i j : Fin n}
    (hui : u ≠ i) (huj : u ≠ j) (hij : i ≠ j) (hall : ∀ l, l = u ∨ l = i ∨ l = j)
    (hu : w u ≤ r) (hi : r < w i) (hj : r < w j) (a : Poly n)
    (ha : a.IsWeightedHomogeneous w r) (hrad : a ∈ (partialIdeal w f r).radical) : a = 0 := by
  by_contra ha0
  have hfree : ∀ k, k ≠ u → FreeOf k a := fun k hk => by
    rcases hall k with rfl | rfl | rfl
    · exact absurd rfl hk
    · exact freeOf_of_pderiv_eq_zero (pderiv_eq_zero_of_lt ha _ hi)
    · exact freeOf_of_pderiv_eq_zero (pderiv_eq_zero_of_lt ha _ hj)
  obtain ⟨c, e, hce, hcr⟩ := eq_C_mul_X_pow_of_freeOf ha u (H.pos u) hfree
  have hc : c ≠ 0 := by rintro rfl; apply ha0; rw [hce]; simp
  apply H.X_not_mem_radical_of_one_light hui huj hij hall hu hi hj
  obtain ⟨N, hN⟩ := hrad
  refine ⟨e * N, ?_⟩
  have : X u ^ (e * N) = C (c⁻¹ ^ N) * a ^ N := by
    rw [hce, mul_pow, ← mul_assoc, ← map_pow, ← map_mul, ← mul_pow,
      inv_mul_cancel₀ hc, one_pow, map_one, one_mul, pow_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ hN

/-- The square-deformation property holds for at most three variables. -/
theorem Setup.squareDeformationProperty_of_le_three (H : Setup w d f) (hn : n ≤ 3) :
    SquareDeformationProperty w d f := by
  intro r a ha _ hrad
  suffices a = 0 by rw [this]; simp
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; exact H.radical_zero a ha hrad
  by_cases hY : ∀ i j, r < w i → r < w j → i = j
  · exact H.radical_of_heavy_subsingleton r hY a ha hrad
  push_neg at hY
  obtain ⟨i, j, hi, hj, hij⟩ := hY
  by_cases hall : ∀ k, r < w k
  · exact eq_zero_of_all_heavy hr ha hall
  push_neg at hall
  obtain ⟨u, hu⟩ := hall
  have hui : u ≠ i := by rintro rfl; omega
  have huj : u ≠ j := by rintro rfl; omega
  have hall' : ∀ l, l = u ∨ l = i ∨ l = j := by
    intro l
    by_contra h
    push_neg at h
    have h1 := Fin.val_ne_of_ne h.1
    have h2 := Fin.val_ne_of_ne h.2.1
    have h3 := Fin.val_ne_of_ne h.2.2
    have h4 := Fin.val_ne_of_ne hui
    have h5 := Fin.val_ne_of_ne huj
    have h6 := Fin.val_ne_of_ne hij
    have := l.isLt; have := u.isLt; have := i.isLt; have := j.isLt
    omega
  exact H.radical_of_one_light hui huj hij hall' hu hi hj a ha hrad

/-- The main theorem for at most three variables, without the stratum hypothesis. -/
theorem yau_conjecture_of_le_three {n : ℕ} (hn : n ≤ 3) (w : Fin n → ℕ) (d : ℕ) (f : Poly n)
    (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d) (hiso : IsIsolatedSingularity f)
    (k : ℤ) (hk : k < 0) (δ : Derivation ℂ (MilnorAlgebra f) (MilnorAlgebra f))
    (hδ : IsDerivationOfDegree w f k δ) : δ = 0 :=
  noNegDer_of_isolated_of_le 3 (fun _ hm _ _ _ H => H.squareDeformationProperty_of_le_three hm)
    n hn w d f hw hf hiso k hk δ hδ

/-- The same result with the paper's isolated-critical-point hypothesis. -/
theorem yau_conjecture_of_critical_of_le_three {n : ℕ} (hn : n ≤ 3) (w : Fin n → ℕ) (d : ℕ)
    (f : Poly n) (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hcrit : HasIsolatedCriticalPoint f) (k : ℤ) (hk : k < 0)
    (δ : Derivation ℂ (MilnorAlgebra f) (MilnorAlgebra f))
    (hδ : IsDerivationOfDegree w f k δ) : δ = 0 :=
  yau_conjecture_of_le_three hn w d f hw hf
    (isIsolatedSingularity_of_hasIsolatedCriticalPoint hw hf hcrit) k hk δ hδ

end Yau
