import RequestProject.Yau.Sec4_Proof.Orbit

/-! # Second-order Taylor expansion along a direction -/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ}

/-- The line `t ↦ x+t v`, as polynomial coordinates. -/
abbrev lineCoord (x v : Fin n → ℂ) : Fin n → Polynomial ℂ :=
  fun i => Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X

lemma derivative_aeval_line (x v : Fin n → ℂ) (p : Poly n) :
    Polynomial.derivative (aeval (lineCoord x v) p) =
      ∑ i, Polynomial.C (v i) * aeval (lineCoord x v) (pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p k hp =>
    simp only [map_mul, aeval_X, Polynomial.derivative_mul, hp, Derivation.leibniz, pderiv_X,
      smul_eq_mul, map_add, Pi.single_apply]
    simp [mul_add, Finset.sum_add_distrib, mul_comm]
    rw [add_comm, Finset.mul_sum]; congr 1; exact Finset.sum_congr rfl fun _ _ => by ring

lemma eval_aeval_line (x v : Fin n → ℂ) (p : Poly n) (t : ℂ) :
    (aeval (lineCoord x v) p).eval t = eval (fun i => x i + v i * t) p := by
  rw [polynomial_eval_aeval]; simp

lemma poly_eq_zero_of_deriv3 (ψ : Polynomial ℂ)
    (h3 : Polynomial.derivative (Polynomial.derivative (Polynomial.derivative ψ)) = 0)
    (h0 : ψ.eval 0 = 0) (h1 : (Polynomial.derivative ψ).eval 0 = 0)
    (h2 : (Polynomial.derivative (Polynomial.derivative ψ)).eval 0 = 0) : ψ = 0 := by
  have e2 := Polynomial.eq_C_of_derivative_eq_zero h3
  rw [Polynomial.coeff_zero_eq_eval_zero, h2, map_zero] at e2
  have e1 := Polynomial.eq_C_of_derivative_eq_zero e2
  rw [Polynomial.coeff_zero_eq_eval_zero, h1, map_zero] at e1
  have e0 := Polynomial.eq_C_of_derivative_eq_zero e1
  rwa [Polynomial.coeff_zero_eq_eval_zero, h0, map_zero] at e0

/-- The second-order Taylor formula when all third derivatives in directions supported on `v` vanish. -/
lemma taylor2 (g : Poly n) (x v : Fin n → ℂ)
    (h3 : ∀ a b c, v a ≠ 0 → v b ≠ 0 → v c ≠ 0 → pderiv a (pderiv b (pderiv c g)) = 0) :
    eval (x + v) g = eval x g + ∑ c, v c * eval x (pderiv c g) +
      (1 / 2 : ℂ) * ∑ c, ∑ b, v c * v b * eval x (pderiv b (pderiv c g)) := by
  set Φ := fun p : Poly n => aeval (lineCoord x v) p with hΦ
  have hd1 : ∀ p, Polynomial.derivative (Φ p) = ∑ c, Polynomial.C (v c) * Φ (pderiv c p) :=
    fun p => derivative_aeval_line x v p
  have hd2 : Polynomial.derivative (Polynomial.derivative (Φ g)) =
      ∑ c, ∑ b, Polynomial.C (v c * v b) * Φ (pderiv b (pderiv c g)) := by
    rw [hd1, Polynomial.derivative_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Polynomial.derivative_C_mul, hd1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul]; ring
  have hd3 : Polynomial.derivative (Polynomial.derivative (Polynomial.derivative (Φ g))) = 0 := by
    rw [hd2, Polynomial.derivative_sum]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Polynomial.derivative_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Polynomial.derivative_C_mul, hd1, Finset.mul_sum]
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases hc : v c = 0
    · simp [hc]
    by_cases hb : v b = 0
    · simp [hb]
    by_cases ha : v a = 0
    · simp [ha]
    rw [h3 a b c ha hb hc]; simp [hΦ]
  have hev : ∀ p, (Φ p).eval 0 = eval x p := fun p => by
    rw [hΦ]; simp only; rw [eval_aeval_line]; simp
  set e1 := ∑ c, v c * eval x (pderiv c g)
  set e2 := ∑ c, ∑ b, v c * v b * eval x (pderiv b (pderiv c g))
  set Q : Polynomial ℂ := Polynomial.C (eval x g) + Polynomial.C e1 * Polynomial.X +
    Polynomial.C (e2 / 2) * Polynomial.X ^ 2
  have hψ : Φ g - Q = 0 := by
    apply poly_eq_zero_of_deriv3
    · simp only [Q, map_sub, hd3]; simp
    · simp [Q, hev]
    · rw [Polynomial.derivative_sub, Polynomial.eval_sub, hd1]
      simp [Q, Polynomial.eval_finset_sum, hev, e1]
    · rw [Polynomial.derivative_sub, Polynomial.derivative_sub, Polynomial.eval_sub, hd2]
      simp [Q, Polynomial.eval_finset_sum, hev, e2]
      ring
  have h1 := congrArg (Polynomial.eval 1) (sub_eq_zero.mp hψ)
  have hl : (Φ g).eval 1 = eval (x + v) g := by
    rw [hΦ]; simp only; rw [eval_aeval_line]; congr 2; funext i; simp
  rw [← hl, h1]
  simp [Q]; ring

lemma taylor1 (g : Poly n) (x v : Fin n → ℂ)
    (h2 : ∀ b c, v b ≠ 0 → v c ≠ 0 → pderiv b (pderiv c g) = 0) :
    eval (x + v) g = eval x g + ∑ c, v c * eval x (pderiv c g) := by
  rw [taylor2 g x v (fun a b c _ hb hc => by rw [h2 b c hb hc, map_zero])]
  have : ∑ c, ∑ b, v c * v b * eval x (pderiv b (pderiv c g)) = 0 := by
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun b _ => ?_
    by_cases hc : v c = 0
    · simp [hc]
    by_cases hb : v b = 0
    · simp [hb]
    rw [h2 b c hb hc]; simp
  rw [this]; ring

lemma taylor0 (g : Poly n) (x v : Fin n → ℂ)
    (h1 : ∀ c, v c ≠ 0 → pderiv c g = 0) :
    eval (x + v) g = eval x g := by
  rw [taylor1 g x v (fun b c _ hc => by rw [h1 c hc, map_zero])]
  have : ∑ c, v c * eval x (pderiv c g) = 0 := by
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : v c = 0
    · simp [hc]
    rw [h1 c hc]; simp
  rw [this]; ring

end Yau
