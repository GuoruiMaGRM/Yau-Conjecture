import RequestProject.Yau.Appendix.Isolated

/-!
# Theorem 3.6 with at most one heavy variable

An elementary argument proves `√I_r ∩ S_r = 0` when at most one variable has
weight greater than `r`. For a single heavy variable, a nonzero light-variable
polynomial cannot vanish on the zero set of its partial derivative unless that
derivative is independent of the heavy variable, contradicting isolatedness.
This is one ingredient of the result for at most three variables.
-/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ}

/-- Restrict a polynomial to the line through `x` in the `x_j` direction. -/
def lineRestrict (j : Fin n) (x : Fin n → ℂ) : Poly n →+* Polynomial ℂ :=
  eval₂Hom Polynomial.C (fun i => if i = j then Polynomial.X else Polynomial.C (x i))

lemma lineRestrict_eval (j : Fin n) (x : Fin n → ℂ) (p : Poly n) (z : ℂ) :
    (lineRestrict j x p).eval z = eval (Function.update x j z) p := by
  unfold lineRestrict
  rw [coe_eval₂Hom, ← Polynomial.coe_evalRingHom, MvPolynomial.eval₂_comp_left]
  have : (Polynomial.evalRingHom z).comp Polynomial.C = RingHom.id ℂ := by ext; simp
  rw [this]
  show _ = eval₂ (RingHom.id ℂ) _ p
  congr 1
  funext i
  by_cases hi : i = j
  · subst hi; simp
  · simp [hi]

lemma lineRestrict_derivative (j : Fin n) (x : Fin n → ℂ) (p : Poly n) :
    Polynomial.derivative (lineRestrict j x p) = lineRestrict j x (pderiv j p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [lineRestrict]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.derivative_mul, hp, Derivation.leibniz, pderiv_X]
    by_cases hi : i = j
    · subst hi; simp [lineRestrict]; ring
    · simp [lineRestrict, hi, mul_comm]

/-- A polynomial with zero `x_j` derivative is independent of `x_j`. -/
lemma eval_update_of_pderiv_eq_zero {j : Fin n} {p : Poly n} (h : pderiv j p = 0)
    (x : Fin n → ℂ) (z : ℂ) :
    eval (Function.update x j z) p = eval (Function.update x j 0) p := by
  have hd : Polynomial.derivative (lineRestrict j x p) = 0 := by
    rw [lineRestrict_derivative, h, map_zero]
  rw [← lineRestrict_eval, ← lineRestrict_eval, Polynomial.eq_C_of_derivative_eq_zero hd]
  simp

/-- If the `x_j` derivative is independent of `x_j`, the polynomial is affine in `x_j`. -/
lemma eq_killV_add_of_freeOf_pderiv {j : Fin n} {f : Poly n} (h : FreeOf j (pderiv j f)) :
    f = killV j f + X j * pderiv j f := by
  apply MvPolynomial.funext
  intro x
  set P := pderiv j f
  have hP : Polynomial.derivative (lineRestrict j x P) = 0 := by
    rw [lineRestrict_derivative, h.pderiv_eq_zero, map_zero]
  have hPc := Polynomial.eq_C_of_derivative_eq_zero hP
  have hc : (lineRestrict j x P).coeff 0 = eval x P := by
    rw [Polynomial.coeff_zero_eq_eval_zero, lineRestrict_eval, ← h.eval_update x (x j),
      Function.update_eq_self]
  have hψ : Polynomial.derivative (lineRestrict j x f - Polynomial.C (eval x P) * Polynomial.X)
      = 0 := by
    rw [Polynomial.derivative_sub, lineRestrict_derivative, hPc, hc]; simp
  have hψc := Polynomial.eq_C_of_derivative_eq_zero hψ
  have e1 := congrArg (Polynomial.eval (x j)) hψc
  have e0 := congrArg (Polynomial.eval 0) hψc
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    lineRestrict_eval, Function.update_eq_self, mul_zero, sub_zero] at e1 e0
  rw [map_add, map_mul, eval_X, eval_killV, e0, ← e1]
  ring

variable {w : Fin n → ℕ} {d : ℕ} {f : Poly n}

lemma Setup.jacobianIdeal_ne_top (H : Setup w d f) : jacobianIdeal f ≠ ⊤ := by
  intro h
  have h1 : (1 : Poly n) ∈ jacobianIdeal f := h ▸ Submodule.mem_top
  have := mem_jac_eval_zero (x := 0) (fun i => eval_zero_of_isWH_pos (pderiv_f_isWH H.hom i)
    (by have := H.big i; omega)) h1
  simp at this

/-- Theorem 3.6 when at most one variable has weight greater than `r`, without the stratum theorem. -/
theorem Setup.radical_of_heavy_subsingleton (H : Setup w d f) (r : ℕ)
    (hY : ∀ i j, r < w i → r < w j → i = j) (a : Poly n) (ha : a.IsWeightedHomogeneous w r)
    (hrad : a ∈ (partialIdeal w f r).radical) : a = 0 := by
  classical
  by_contra ha0
  obtain ⟨N, hN⟩ := hrad
  by_cases hex : ∃ j, r < w j
  swap
  · push_neg at hex
    have hI : partialIdeal w f r = ⊥ := by
      rw [partialIdeal, Ideal.span_eq_bot]
      rintro _ ⟨i, hi, rfl⟩
      exact absurd (hex i) (not_le.mpr hi)
    rw [hI, Ideal.mem_bot] at hN
    exact ha0 (pow_eq_zero_iff'.mp hN).1
  obtain ⟨j, hj⟩ := hex
  set P := pderiv j f with hPdef
  have hI : partialIdeal w f r = Ideal.span {P} := by
    rw [partialIdeal]; congr 1
    ext q; constructor
    · rintro ⟨i, hi, rfl⟩; rw [hY i j hi hj]; rfl
    · rintro rfl; exact ⟨j, hj, rfl⟩
  rw [hI, Ideal.mem_span_singleton'] at hN
  obtain ⟨b, hb⟩ := hN
  have haj : pderiv j a = 0 := pderiv_eq_zero_of_lt ha j hj
  have haupd : ∀ x z, eval (Function.update x j z) a = eval x a := by
    intro x z
    rw [eval_update_of_pderiv_eq_zero haj, ← eval_update_of_pderiv_eq_zero haj x (x j),
      Function.update_eq_self]
  have hPx : ∀ x, eval x a ≠ 0 → eval x P = eval x (killV j P) := by
    intro x hx
    have hdeg : (lineRestrict j x P).degree = 0 := by
      by_contra hd
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hd
      rw [Polynomial.IsRoot, lineRestrict_eval] at hz
      have := congrArg (eval (Function.update x j z)) hb
      rw [map_mul, hz, mul_zero, map_pow, haupd] at this
      exact hx (pow_eq_zero_iff'.mp this.symm).1
    have hψ := Polynomial.eq_C_of_degree_eq_zero hdeg
    have e1 := lineRestrict_eval j x P (x j)
    have e0 := lineRestrict_eval j x P 0
    rw [Function.update_eq_self] at e1
    rw [eval_killV, ← e1, ← e0, hψ]; simp
  have hfree : FreeOf j P := by
    have : (P - killV j P) * a = 0 := by
      apply MvPolynomial.funext; intro x
      rw [map_mul, map_sub, map_zero]
      by_cases hx : eval x a = 0
      · rw [hx, mul_zero]
      · rw [hPx x hx, sub_self, zero_mul]
    rcases mul_eq_zero.mp this with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h ha0
  have hfAB := eq_killV_add_of_freeOf_pderiv hfree
  obtain ⟨v, hv⟩ := exists_v_of_linear H.pos H.hom H.iso H.jacobianIdeal_ne_top j hfAB
    (freeOf_killV f) hfree
  have hPw : P.IsWeightedHomogeneous w (d - w j) := pderiv_f_isWH H.hom j
  have h1 : w v ≤ d - w j := by
    by_contra hlt
    apply hv
    rw [pderiv_eq_zero_of_lt hPw _ (by omega), map_zero]
  have := H.big v; have := H.big j
  exact hv (eval_zero_of_isWH_pos (pderiv_isWH hPw v).1 (by omega))

/-- If every variable has weight greater than positive `r`, a homogeneous polynomial of degree `r` is zero. -/
lemma eq_zero_of_all_heavy {r : ℕ} (hr : 0 < r) {a : Poly n} (ha : a.IsWeightedHomogeneous w r)
    (hall : ∀ i, r < w i) : a = 0 := by
  ext μ
  rw [coeff_zero]
  by_contra hμ
  have hwt := ha hμ
  by_cases h0 : μ = 0
  · subst h0; simp at hwt; omega
  · obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
      by_contra h; push_neg at h; exact h0 (Finsupp.ext h)
    have := Finsupp.le_weight_of_ne_zero' w hi
    have := hall i
    omega

/-- A bounded-variable version of the induction: the square-deformation property is needed only for at most `N` variables, since reduction only decreases their number. -/
theorem noNegDer_of_isolated_of_le (N : ℕ)
    (hV : ∀ m ≤ N, ∀ (w : Fin m → ℕ) (d : ℕ) (g : Poly m), Setup w d g →
      SquareDeformationProperty w d g) :
    ∀ (n : ℕ), n ≤ N → ∀ (w : Fin n → ℕ) (d : ℕ) (f : Poly n), (∀ i, 0 < w i) →
      f.IsWeightedHomogeneous w d → IsIsolatedSingularity f → NoNegDer w f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnN w d f hw hf hiso
  by_cases hJ : jacobianIdeal f = ⊤
  · exact noNegDer_of_jac_eq_top hJ
  by_cases hbig : ∀ i, 2 * w i < d
  · have H : Setup w d f := ⟨hw, hf, hbig, hiso⟩
    intro k hk δ hδ
    exact H.no_neg_derivation (hV n hnN w d f H) k hk δ hδ
  push_neg at hbig
  obtain ⟨u, hu⟩ := hbig
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := u.pos; omega⟩
  by_cases hc : eval 0 (pderiv u (pderiv u f)) ≠ 0
  · have hd : 2 * w u = d := by
      by_contra hne
      apply hc
      rw [pderiv_eq_zero_of_lt (pderiv_isWH hf u).1 u (by omega), map_zero]
    obtain ⟨F, hFw, hFi, hFn⟩ := single_step hw hf u hd hc
    exact hFn (ih n' (by omega) (by omega) _ d F (fun i => hw _) hFw (hFi hiso))
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
    exact hFn (ih n'' (by omega) (by omega) _ d F (fun i => hw _) hFw (hFi hiso))

end Yau
