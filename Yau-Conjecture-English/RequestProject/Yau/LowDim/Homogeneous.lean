import RequestProject.Yau.LowDim.ThreeVar

/-!
# The case of equal weights

If all weights equal `W`, then for `r < W` the space `S_r` is zero, while for
`r ≥ W` the ideal `I_r` is zero. Thus Theorem 3.6, and consequently the main
theorem, hold directly without the stratum theorem. Splitting removes variables
without changing the remaining weights, so the equal-weight condition is preserved.
-/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ}

/-- For equal weights, the square-deformation property holds directly. -/
theorem Setup.squareDeformationProperty_of_equal_weights {w : Fin n → ℕ} {d : ℕ} {f : Poly n}
    (H : Setup w d f) (hE : ∀ i j, w i = w j) : SquareDeformationProperty w d f := by
  intro r a ha _ hrad
  suffices a = 0 by rw [this]; simp
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; exact H.radical_zero a ha hrad
  by_cases hall : ∀ i, r < w i
  · exact eq_zero_of_all_heavy hr ha hall
  · push_neg at hall
    obtain ⟨i, hi⟩ := hall
    exact H.radical_of_heavy_subsingleton r
      (fun j _ hj _ => absurd hj (by rw [hE j i]; omega)) a ha hrad

/-- The induction uses the square-deformation property only for equal-weight polynomials, where it is proved directly. -/
theorem noNegDer_of_isolated_of_equal_weights :
    ∀ (n : ℕ) (w : Fin n → ℕ) (d : ℕ) (f : Poly n), (∀ i j, w i = w j) → (∀ i, 0 < w i) →
      f.IsWeightedHomogeneous w d → IsIsolatedSingularity f → NoNegDer w f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w d f hE hw hf hiso
  by_cases hJ : jacobianIdeal f = ⊤
  · exact noNegDer_of_jac_eq_top hJ
  by_cases hbig : ∀ i, 2 * w i < d
  · have H : Setup w d f := ⟨hw, hf, hbig, hiso⟩
    intro k hk δ hδ
    exact H.no_neg_derivation (H.squareDeformationProperty_of_equal_weights hE) k hk δ hδ
  push_neg at hbig
  obtain ⟨u, hu⟩ := hbig
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := u.pos; omega⟩
  by_cases hc : eval 0 (pderiv u (pderiv u f)) ≠ 0
  · have hd : 2 * w u = d := by
      by_contra hne
      apply hc
      rw [pderiv_eq_zero_of_lt (pderiv_isWH hf u).1 u (by omega), map_zero]
    obtain ⟨F, hFw, hFi, hFn⟩ := single_step hw hf u hd hc
    exact hFn (ih n' (by omega) _ d F (fun i j => hE _ _) (fun i => hw _) hFw (hFi hiso))
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
    exact hFn (ih n'' (by omega) _ d F (fun i j => hE _ _) (fun i => hw _) hFw (hFi hiso))

/-- The main theorem for equal positive integer weights, equivalently ordinary homogeneous polynomials, without the stratum hypothesis. -/
theorem «Yau猜想_齐次» {W : ℕ} (hW : 0 < W) (d : ℕ) (f : Poly n)
    (hf : f.IsWeightedHomogeneous (fun _ => W) d) (hcrit : HasIsolatedCriticalPoint f)
    (k : ℤ) (hk : k < 0) (δ : Derivation ℂ (MilnorAlgebra f) (MilnorAlgebra f))
    (hδ : IsDerivationOfDegree (fun _ => W) f k δ) : δ = 0 :=
  noNegDer_of_isolated_of_equal_weights n (fun _ => W) d f (fun _ _ => rfl) (fun _ => hW) hf
    (isIsolatedSingularity_of_hasIsolatedCriticalPoint (fun _ => hW) hf hcrit) k hk δ hδ

end Yau
