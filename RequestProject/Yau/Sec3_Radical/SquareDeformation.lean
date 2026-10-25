import RequestProject.Yau.Appendix.AnalyticYau

/-!
# The square deformation `f+t a²`: the algebraic part of Lemma 3.3

If `a` is independent of the selected variables `y` and belongs to `√(f_y)`,
then `J_{f+t a²}` and `J_f` have the same radical for every `t`.
Consequently the square deformation retains the origin as its only critical
point in the weighted homogeneous setting. The dimension calculation is in
`MilnorConstancy.lean`.
-/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ}

lemma pderiv_add_sq (f a : Poly n) (t : ℂ) (i : Fin n) :
    pderiv i (f + C t * a ^ 2) = pderiv i f + C (2 * t) * (a * pderiv i a) := by
  simp only [map_add, Derivation.leibniz, pderiv_C, smul_eq_mul, Derivation.leibniz_pow]
  simp [map_mul, map_ofNat]; ring

/-- Lemma 3.3, algebraic part: independence of `a` from `Y` and membership in `√(∂_i f:i∈Y)` imply `√J_{f+t a²}=√J_f` for every `t`. -/
theorem radical_jacobianIdeal_add_sq (f a : Poly n) (Y : Set (Fin n))
    (haY : ∀ i ∈ Y, pderiv i a = 0)
    (ha : a ∈ (Ideal.span ((fun i => pderiv i f) '' Y)).radical) (t : ℂ) :
    (jacobianIdeal (f + C t * a ^ 2)).radical = (jacobianIdeal f).radical := by
  have hK : ∀ g : Poly n, (∀ i ∈ Y, pderiv i g = pderiv i f) →
      Ideal.span ((fun i => pderiv i f) '' Y) ≤ jacobianIdeal g := by
    intro g hg
    rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact Ideal.subset_span ⟨i, hg i hi⟩
  have hY : ∀ i ∈ Y, pderiv i (f + C t * a ^ 2) = pderiv i f := by
    intro i hi; rw [pderiv_add_sq, haY i hi]; simp
  have ha1 : a ∈ (jacobianIdeal f).radical :=
    Ideal.radical_mono (hK f fun _ _ => rfl) ha
  have ha2 : a ∈ (jacobianIdeal (f + C t * a ^ 2)).radical :=
    Ideal.radical_mono (hK _ hY) ha
  apply le_antisymm
  · rw [Ideal.radical_le_radical_iff, jacobianIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe]
    show pderiv i (f + C t * a ^ 2) ∈ _
    rw [pderiv_add_sq]
    exact Ideal.add_mem _ (Ideal.le_radical (Ideal.subset_span ⟨i, rfl⟩))
      (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ ha1))
  · rw [Ideal.radical_le_radical_iff, jacobianIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have : pderiv i f = pderiv i (f + C t * a ^ 2) - C (2 * t) * (a * pderiv i a) := by
      rw [pderiv_add_sq]; ring
    rw [SetLike.mem_coe]
    show pderiv i f ∈ _
    rw [this]
    exact Ideal.sub_mem _ (Ideal.le_radical (Ideal.subset_span ⟨i, rfl⟩))
      (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ ha2))

/-- Under the square-deformation hypotheses, if `J_f` contains a power of each variable, so does `J_{f+t a²}`. -/
theorem pow_X_mem_jacobianIdeal_add_sq (f a : Poly n) (Y : Set (Fin n))
    (haY : ∀ i ∈ Y, pderiv i a = 0)
    (ha : a ∈ (Ideal.span ((fun i => pderiv i f) '' Y)).radical) (t : ℂ)
    (hf : ∀ j, ∃ N : ℕ, (X j : Poly n) ^ N ∈ jacobianIdeal f) (j : Fin n) :
    ∃ N : ℕ, (X j : Poly n) ^ N ∈ jacobianIdeal (f + C t * a ^ 2) := by
  obtain ⟨N, hN⟩ := hf j
  have : X j ∈ (jacobianIdeal (f + C t * a ^ 2)).radical := by
    rw [radical_jacobianIdeal_add_sq f a Y haY ha t]; exact ⟨N, hN⟩
  exact this

/-- Lemma 3.3, isolatedness: the square deformation has a finite-dimensional polynomial Milnor algebra, naturally isomorphic to its analytic Milnor algebra. -/
theorem isIsolatedSingularity_add_sq {w : Fin n → ℕ} {d : ℕ} {f : Poly n} (hw : ∀ i, 0 < w i)
    (hf : f.IsWeightedHomogeneous w d) (hcrit : HasIsolatedCriticalPoint f)
    (a : Poly n) (Y : Set (Fin n)) (haY : ∀ i ∈ Y, pderiv i a = 0)
    (ha : a ∈ (Ideal.span ((fun i => pderiv i f) '' Y)).radical) (t : ℂ) :
    IsIsolatedSingularity (f + C t * a ^ 2) ∧
      Nonempty (MilnorAlgebra (f + C t * a ^ 2) ≃ₐ[ℂ]
        ConvSeries n ⧸ convIdeal (jacobianIdeal (f + C t * a ^ 2))) := by
  have h := pow_X_mem_jacobianIdeal_add_sq f a Y haY ha t
    (exists_pow_X_mem_jacobianIdeal hw hf hcrit)
  exact ⟨finite_quotient_of_pow_X_mem _ h, ⟨quotientEquivConv h⟩⟩

/-! ### The homogeneous-component argument in Lemma 3.4 -/

/-- The Jacobian ideal of a weighted homogeneous polynomial is homogeneous. -/
lemma weightedHomogeneousComponent_mem_jacobianIdeal {w : Fin n → ℕ} {d : ℕ} {f : Poly n}
    (hf : f.IsWeightedHomogeneous w d) {g : Poly n} (hg : g ∈ jacobianIdeal f) (m : ℕ) :
    weightedHomogeneousComponent w m g ∈ jacobianIdeal f := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hg
  rw [← hc, map_sum]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [weightedHomogeneousComponent_mul_of_right _ _ (d - w i) m (pderiv_f_isWH hf i)]
  split_ifs
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · exact Ideal.zero_mem _

/-- If homogeneous `q` has degree `e<d` and is congruent modulo `J` to a polynomial with no components of degree less than `d`, then `q∈J`. Apply this to the high-degree parameter terms in Lemma 3.4. -/
theorem mem_jacobianIdeal_of_sub_mem {w : Fin n → ℕ} {d : ℕ} {f : Poly n}
    (hf : f.IsWeightedHomogeneous w d) {q : Poly n} {e : ℕ} (hq : q.IsWeightedHomogeneous w e)
    (he : e < d) {r : Poly n} (hr : ∀ m < d, weightedHomogeneousComponent w m r = 0)
    (h : q - r ∈ jacobianIdeal f) : q ∈ jacobianIdeal f := by
  have := weightedHomogeneousComponent_mem_jacobianIdeal hf h e
  rwa [map_sub, hq.weightedHomogeneousComponent_same, hr e he, sub_zero] at this

end Yau
