import RequestProject.Yau.Appendix.Lift

/-!
# Choosing a derivation with `D²f = 0`

The minimization argument in Lemmas 2.2–2.3 and Proposition 2.4.
-/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ} {w : Fin n → ℕ} {d : ℕ} {f : Poly n}

lemma pderiv_mem_jac (i : Fin n) : pderiv i f ∈ jacobianIdeal f :=
  Ideal.subset_span ⟨i, rfl⟩

/-- A derivation preserving the generators of an ideal preserves the whole ideal. -/
lemma der_preserves_span {ι : Type*} (D : Derivation ℂ (Poly n) (Poly n)) (v : ι → Poly n)
    (I : Ideal (Poly n)) (hvI : ∀ i, v i ∈ I) (hD : ∀ i, D (v i) ∈ I) :
    ∀ p ∈ Ideal.span (Set.range v), D p ∈ I := by
  intro p hp
  induction hp using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hD i
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact I.add_mem hx hy
  | smul a x hx ih =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have hxI : x ∈ I := (Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hvI i)) hx
    exact I.add_mem (I.mul_mem_left _ ih) (I.mul_mem_right _ hxI)

/-- The space `𝒱 = {g ∈ J : ∂_i g ∈ J for every i}`. -/
def InV (f g : Poly n) : Prop := g ∈ jacobianIdeal f ∧ ∀ i, pderiv i g ∈ jacobianIdeal f

lemma polyDer_f_inV (h : Fin n → Poly n)
    (hJ : ∀ p ∈ jacobianIdeal f, polyDer h p ∈ jacobianIdeal f) : InV f (polyDer h f) := by
  refine ⟨?_, fun i => ?_⟩
  · rw [polyDer_apply]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (pderiv_mem_jac j)
  · rw [pderiv_polyDer]
    exact Ideal.add_mem _ (hJ _ (pderiv_mem_jac i))
      (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (pderiv_mem_jac j))

/-- Lemma 2.3: a derivation preserving `J` preserves `𝒱`. -/
lemma polyDer_inV (h : Fin n → Poly n)
    (hJ : ∀ p ∈ jacobianIdeal f, polyDer h p ∈ jacobianIdeal f) {g : Poly n}
    (hg : InV f g) : InV f (polyDer h g) := by
  refine ⟨hJ _ hg.1, fun i => ?_⟩
  rw [pderiv_polyDer]
  exact Ideal.add_mem _ (hJ _ (hg.2 i))
    (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hg.2 j))

lemma Setup.minimum (H : Setup w d f) {s : ℕ} (hs : 0 < s) {h : Fin n → Poly n}
    (hh : IsNegHomog w s h) (hJ : ∀ p ∈ jacobianIdeal f, polyDer h p ∈ jacobianIdeal f)
    (hne : h ≠ 0) :
    ∃ s' : ℕ, 0 < s' ∧ ∃ h' : Fin n → Poly n, IsNegHomog w s' h' ∧ h' ≠ 0 ∧
      (∀ p ∈ jacobianIdeal f, polyDer h' p ∈ jacobianIdeal f) ∧
      polyDer h' (polyDer h' f) = 0 := by
  classical
  by_cases hDf : polyDer h f = 0
  · exact ⟨s, hs, h, hh, hne, hJ, by rw [hDf, map_zero]⟩
  have hq0 := (polyDer_isWH hh H.hom).1
  have hds : s ≤ d := by
    by_contra hc; exact hDf ((polyDer_isWH hh H.hom).2 (by omega))
  have hP : ∃ q, q < d ∧ ∃ g : Poly n, g ≠ 0 ∧ InV f g ∧ g.IsWeightedHomogeneous w q :=
    ⟨d - s, by omega, _, hDf, polyDer_f_inV h hJ, hq0⟩
  set q := Nat.find hP with hq_def
  obtain ⟨hqd, g, hg0, hgV, hgq⟩ := Nat.find_spec hP
  have hmin := fun m (hm : m < q) => Nat.find_min hP hm
  obtain ⟨k, hk1, hk2, hk3⟩ := jacobian_homog_decomp H.hom hgV.1 hgq H.wd
  set s' := d - q
  have hs' : 0 < s' := by omega
  have hk : IsNegHomog w s' k := by
    intro j
    refine ⟨by rw [show w j - s' = q + w j - d by omega]; exact hk1 j, fun hj => hk2 j (by omega)⟩
  have hD'f : polyDer k f = g := by rw [polyDer_apply, hk3]
  have hJ' : ∀ p ∈ jacobianIdeal f, polyDer k p ∈ jacobianIdeal f := by
    apply der_preserves_span _ _ _ pderiv_mem_jac
    intro i
    have := pderiv_polyDer k i f
    rw [hD'f] at this
    have h2 : polyDer k (pderiv i f) = pderiv i g - ∑ j, pderiv i (k j) * pderiv j f := by
      rw [this]; ring
    rw [h2]
    exact Ideal.sub_mem _ (hgV.2 i)
      (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (pderiv_mem_jac j))
  refine ⟨s', hs', k, hk, ?_, hJ', ?_⟩
  · rintro rfl
    apply hg0; rw [← hD'f, polyDer_apply]; simp
  · rw [hD'f]
    by_contra hc
    have hV' := polyDer_inV k hJ' hgV
    have hdeg := polyDer_isWH hk hgq
    have hqs : s' ≤ q := by by_contra h'; exact hc (hdeg.2 (by omega))
    exact hmin (q - s') (by omega) ⟨by omega, _, hc, hV', hdeg.1⟩

end Yau
