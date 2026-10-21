import RequestProject.Yau.Sec2_Splitting.Steps

/-!
# The main theorem: Yau's conjecture

Combine the splitting induction of Section 2 with the core contradiction of
Section 4. The input `VarchenkoHypothesis` is the square-deformation conclusion
of Corollary 3.5. The files in `Final/` derive it from the stratum theorem,
including the formulation with AGV, Theorem 14.8 as an explicit hypothesis.
-/

open MvPolynomial

noncomputable section

namespace Yau

/-- The square-deformation input: for isolated weighted homogeneous `g` with `2w_i<d`, homogeneous `a` of degree `r` with `3r<d` and `a∈√I_r` satisfies `a²∈J_g`. -/
def VarchenkoHypothesis : Prop :=
  ∀ (m : ℕ) (w : Fin m → ℕ) (d : ℕ) (g : Poly m), Setup w d g → SquareDeformationProperty w d g

/-- Combine Lemma 2.1 with the core proof, inducting on the number of variables and deleting quadratic variables. -/
theorem noNegDer_of_isolated (hV : VarchenkoHypothesis) :
    ∀ (n : ℕ) (w : Fin n → ℕ) (d : ℕ) (f : Poly n), (∀ i, 0 < w i) →
      f.IsWeightedHomogeneous w d → IsIsolatedSingularity f → NoNegDer w f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w d f hw hf hiso
  by_cases hJ : jacobianIdeal f = ⊤
  · exact noNegDer_of_jac_eq_top hJ
  by_cases hbig : ∀ i, 2 * w i < d
  · have H : Setup w d f := ⟨hw, hf, hbig, hiso⟩
    intro k hk δ hδ
    exact H.no_neg_derivation (hV n w d f H) k hk δ hδ
  push_neg at hbig
  obtain ⟨u, hu⟩ := hbig
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := u.pos; omega⟩
  by_cases hc : eval 0 (pderiv u (pderiv u f)) ≠ 0
  · have hd : 2 * w u = d := by
      by_contra hne
      apply hc
      rw [pderiv_eq_zero_of_lt (pderiv_isWH hf u).1 u (by omega), map_zero]
    obtain ⟨F, hFw, hFi, hFn⟩ := single_step hw hf u hd hc
    exact hFn (ih n' (by omega) _ d F (fun i => hw _) hFw (hFi hiso))
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
    exact hFn (ih n'' (by omega) _ d F (fun i => hw _) hFw (hFi hiso))

/-- Yau's conjecture under `VarchenkoHypothesis`: every negative-degree derivation of the Milnor algebra vanishes. The AGV-based main theorem is in `Final/ThreeNewLocal.lean`. -/
theorem yau_conjecture (hV : VarchenkoHypothesis) {n : ℕ} (w : Fin n → ℕ) (d : ℕ)
    (f : Poly n) (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hiso : IsIsolatedSingularity f) (k : ℤ) (hk : k < 0)
    (δ : Derivation ℂ (MilnorAlgebra f) (MilnorAlgebra f))
    (hδ : IsDerivationOfDegree w f k δ) : δ = 0 :=
  noNegDer_of_isolated hV n w d f hw hf hiso k hk δ hδ

end Yau
