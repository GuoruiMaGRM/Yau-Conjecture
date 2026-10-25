import RequestProject.Yau.Sec3_Radical.Taylor

/-!
# Lowest-order terms in polynomial quadratic identities

If `∑ k_a G_{ab} k_b=0` and `k≠0`, an appropriate evaluation of the lowest-order
part of `k` gives a nonzero vector `v` satisfying `∑ v_a G_{ab}(0)v_b=0`.
-/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ}

/-- The one-variable polynomial `t ↦ p(tc)`, expressed using homogeneous components. -/
def lineSeries (c : Fin n → ℂ) (p : Poly n) : Polynomial ℂ :=
  ∑ e ∈ Finset.range (p.totalDegree + 1),
    Polynomial.C (eval c (homogeneousComponent e p)) * Polynomial.X ^ e

lemma lineSeries_coeff (c : Fin n → ℂ) (p : Poly n) (e : ℕ) :
    (lineSeries c p).coeff e = eval c (homogeneousComponent e p) := by
  classical
  simp only [lineSeries, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [homogeneousComponent_eq_zero _ _ (by simp at h; omega), map_zero]

lemma lineSeries_eval (c : Fin n → ℂ) (p : Poly n) (t : ℂ) :
    (lineSeries c p).eval t = eval (fun i => t * c i) p := by
  conv_rhs => rw [← sum_homogeneousComponent p]
  simp only [lineSeries, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  have := eval_scale (homogeneousComponent_isHomogeneous e p) t c
  simp only [Pi.one_apply, pow_one] at this
  rw [this, mul_comm]

lemma lowest_order_quadratic {ι : Type*} (k : Fin n → Poly n)
    (G : ι → Fin n → Fin n → Poly n) (hk0 : k ≠ 0)
    (hid : ∀ j, ∑ a, ∑ b, k a * G j a b * k b = 0) :
    ∃ v : Fin n → ℂ, v ≠ 0 ∧ (∀ a, k a = 0 → v a = 0) ∧
      ∀ j, ∑ a, ∑ b, v a * eval 0 (G j a b) * v b = 0 := by
  classical
  have hex : ∃ m, ∃ a, homogeneousComponent m (k a) ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hk0; funext a
    rw [← sum_homogeneousComponent (k a)]
    simp [hc]
  set m := Nat.find hex
  obtain ⟨a0, ha0⟩ := Nat.find_spec hex
  have hlow : ∀ e < m, ∀ a, homogeneousComponent e (k a) = 0 := by
    intro e he a
    by_contra hc
    exact Nat.find_min hex he ⟨a, hc⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin n → ℂ, eval c (homogeneousComponent m (k a0)) ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha0 (MvPolynomial.funext fun x => by rw [map_zero]; exact h x)
  set v : Fin n → ℂ := fun a => eval c (homogeneousComponent m (k a))
  refine ⟨v, fun hv => hc (congrFun hv a0), fun a ha => by simp [v, ha], fun j => ?_⟩
  -- Divide the restriction of `k a` along the line by `X^m`.
  have hdvd : ∀ a, Polynomial.X ^ m ∣ lineSeries c (k a) := by
    intro a
    rw [Polynomial.X_pow_dvd_iff]
    intro e he
    rw [lineSeries_coeff, hlow e he a, map_zero]
  choose R hR using hdvd
  have hR0 : ∀ a, (R a).eval 0 = v a := by
    intro a
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    have := lineSeries_coeff c (k a) m
    rw [hR a, Polynomial.coeff_X_pow_mul'] at this
    simpa [v] using this
  have hpoly : ∑ a, ∑ b, lineSeries c (k a) * lineSeries c (G j a b) * lineSeries c (k b) = 0 := by
    apply Polynomial.funext
    intro t
    simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, lineSeries_eval,
      Polynomial.eval_zero]
    have := congrArg (eval fun i => t * c i) (hid j)
    simpa using this
  have hpoly2 : Polynomial.X ^ m * Polynomial.X ^ m *
      ∑ a, ∑ b, R a * lineSeries c (G j a b) * R b = 0 := by
    rw [← hpoly, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hR a, hR b]; ring
  have hX : (Polynomial.X ^ m * Polynomial.X ^ m : Polynomial ℂ) ≠ 0 := by
    simp [Polynomial.X_ne_zero]
  have h3 := (mul_eq_zero.mp hpoly2).resolve_left hX
  have h4 := congrArg (Polynomial.eval 0) h3
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, hR0, lineSeries_eval,
    zero_mul, Polynomial.eval_zero] at h4
  simpa using h4

end Yau
