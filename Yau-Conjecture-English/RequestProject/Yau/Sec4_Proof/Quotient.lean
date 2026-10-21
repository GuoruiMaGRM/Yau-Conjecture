import RequestProject.Yau.Sec2_Splitting.Minimum

/-! # The induced action modulo `I_r`: Lemma 4.3 -/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ} {w : Fin n → ℕ} {d : ℕ} {f : Poly n}

/-- If a derivation sends the generators of one ideal into another ideal, it sends the generated ideal into that ideal. -/
lemma der_preserves_span_set (D : Derivation ℂ (Poly n) (Poly n)) (S : Set (Poly n))
    (I : Ideal (Poly n)) (hSI : S ⊆ I) (hD : ∀ x ∈ S, D x ∈ I) :
    ∀ p ∈ Ideal.span S, D p ∈ I := by
  intro p hp
  induction hp using Submodule.span_induction with
  | mem x hx => exact hD x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact I.add_mem hx hy
  | smul a x hx ih =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have hxI : x ∈ I := (Ideal.span_le.mpr hSI) hx
    exact I.add_mem (I.mul_mem_left _ ih) (I.mul_mem_right _ hxI)

lemma mem_partialIdeal {r : ℕ} {j : Fin n} (hj : r < w j) :
    pderiv j f ∈ partialIdeal w f r :=
  Ideal.subset_span ⟨j, hj, rfl⟩

lemma Setup.quotient (H : Setup w d f) {s : ℕ} {h : Fin n → Poly n}
    (hh : IsNegHomog w s h) (hJ : ∀ p ∈ jacobianIdeal f, polyDer h p ∈ jacobianIdeal f)
    (h2 : polyDer h (polyDer h f) = 0) (r : ℕ) (hr : ∀ j, w j ≤ r → h j = 0) :
    (∀ p ∈ partialIdeal w f r, polyDer h p ∈ partialIdeal w f r) ∧
      ∀ i, polyDer h (polyDer h (pderiv i f)) ∈ partialIdeal w f r := by
  set I := partialIdeal w f r
  -- The sum weighted by `∂_i h_j` lies in `I` once the heavy-variable components do.
  have hsum : ∀ (i : Fin n) (c : Fin n → Poly n), (∀ j, r < w j → c j ∈ I) →
      ∑ j, pderiv i (h j) * c j ∈ I := by
    intro i c hc
    refine Ideal.sum_mem _ fun j _ => ?_
    by_cases hj : w j ≤ r
    · rw [hr j hj, map_zero, zero_mul]; exact I.zero_mem
    · exact I.mul_mem_left _ (hc j (by omega))
  -- Step 1: for `w_i>r`, one has `D(f_i)∈I`.
  have hDf : ∀ i, r < w i → polyDer h (pderiv i f) ∈ I := by
    intro i hi
    have hdeg := (polyDer_isWH hh (pderiv_f_isWH H.hom i)).1
    obtain ⟨c, hc1, hc2, hc3⟩ :=
      jacobian_homog_decomp H.hom (hJ _ (pderiv_mem_jac i)) hdeg H.wd
    rw [hc3]
    refine Ideal.sum_mem _ fun j _ => ?_
    by_cases hj : d - w i - s + w j < d
    · rw [hc2 j hj, zero_mul]; exact I.zero_mem
    · have := H.big j; have := H.big i
      exact I.mul_mem_left _ (mem_partialIdeal (by omega))
  have hI : ∀ p ∈ I, polyDer h p ∈ I := by
    apply der_preserves_span_set
    · rintro _ ⟨i, hi, rfl⟩; exact mem_partialIdeal hi
    · rintro _ ⟨i, hi, rfl⟩; exact hDf i hi
  refine ⟨hI, fun i => ?_⟩
  set g := polyDer h f
  -- `D(f_i) - ∂_i g ∈ I`
  have hdiff : ∀ i, polyDer h (pderiv i f) - pderiv i g ∈ I := by
    intro i
    have := pderiv_polyDer h i f
    rw [show polyDer h (pderiv i f) - pderiv i g = -∑ j, pderiv i (h j) * pderiv j f by
      rw [this]; ring]
    exact I.neg_mem (hsum i _ fun j hj => mem_partialIdeal hj)
  have hgi : ∀ j, r < w j → pderiv j g ∈ I := by
    intro j hj
    have := I.sub_mem (hDf j hj) (hdiff j)
    simpa using this
  have hDg : polyDer h (pderiv i g) ∈ I := by
    have := pderiv_polyDer h i g
    rw [h2, map_zero] at this
    rw [show polyDer h (pderiv i g) = -∑ j, pderiv i (h j) * pderiv j g by
      rw [eq_neg_iff_add_eq_zero]; exact this.symm]
    exact I.neg_mem (hsum i _ hgi)
  have := I.add_mem (hI _ (hdiff i)) hDg
  simpa [map_sub] using this

end Yau
