import RequestProject.Yau.Sec3_Radical.LowestOrder

/-!
# Nondegeneracy of the heavy-variable Hessian block: Lemma 3.1

Variables of weight greater than `d/3` occur at most quadratically.
The corresponding Hessian block has nonzero determinant. For simpler indexing,
the block is extended by the identity outside the selected variables.
-/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ} {w : Fin n → ℕ} {d : ℕ} {f : Poly n}

/-- The Hessian block in the variables in `Y`, extended by the identity outside `Y`. -/
def hessY (Y : Finset (Fin n)) (f : Poly n) : Matrix (Fin n) (Fin n) (Poly n) :=
  fun a b => if a ∈ Y ∧ b ∈ Y then pderiv b (pderiv a f) else if a = b then 1 else 0

lemma hessY_symm (Y : Finset (Fin n)) (f : Poly n) (a b : Fin n) :
    hessY Y f a b = hessY Y f b a := by
  unfold hessY
  by_cases ha : a ∈ Y <;> by_cases hb : b ∈ Y <;> simp [ha, hb, pderiv_comm', eq_comm]

lemma pderiv1_zero {p : Poly n} {m : ℕ} (hp : p.IsWeightedHomogeneous w m) (c : Fin n)
    (h : m < w c) : pderiv c p = 0 :=
  pderiv_eq_zero_of_lt hp c h

lemma pderiv2_zero {p : Poly n} {m : ℕ} (hp : p.IsWeightedHomogeneous w m) (b c : Fin n)
    (h : m < w b + w c) (hb : 0 < w b) : pderiv b (pderiv c p) = 0 :=
  pderiv_eq_zero_of_lt (pderiv_isWH hp c).1 b (by omega)

lemma pderiv3_zero {p : Poly n} {m : ℕ} (hp : p.IsWeightedHomogeneous w m) (a b c : Fin n)
    (h : m < w a + w b + w c) (ha : 0 < w a) : pderiv a (pderiv b (pderiv c p)) = 0 :=
  pderiv_eq_zero_of_lt (pderiv_isWH (pderiv_isWH hp c).1 b).1 a (by omega)

lemma Setup.hessY_det_ne_zero (H : Setup w d f) (Y : Finset (Fin n))
    (hY : ∀ i ∈ Y, d < 3 * w i) : (hessY Y f).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨k, hk0, hk⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set Hm := hessY Y f with hHm
  have hkrow : ∀ a, ∑ b, Hm a b * k b = 0 := fun a => by
    have := congrFun hk a; simpa [Matrix.mulVec, dotProduct] using this
  have hkY : ∀ a, a ∉ Y → k a = 0 := by
    intro a ha; have := hkrow a; simpa [hHm, hessY, ha] using this
  -- The key identity `kᵀ(∂_j H)k = 0`.
  have hid : ∀ j, ∑ a, ∑ b, k a * pderiv j (Hm a b) * k b = 0 := by
    intro j
    have h1 : ∀ a, ∑ b, (pderiv j (Hm a b) * k b + Hm a b * pderiv j (k b)) = 0 := by
      intro a
      have := congrArg (pderiv j) (hkrow a)
      rw [map_sum, map_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
    have h3 : ∑ a, k a * ∑ b, Hm a b * pderiv j (k b) = 0 := by
      have : ∑ a, k a * ∑ b, Hm a b * pderiv j (k b) =
          ∑ b, (∑ a, Hm b a * k a) * pderiv j (k b) := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
        rw [show Hm a b = Hm b a from hessY_symm Y f a b]; ring
      rw [this]; exact Finset.sum_eq_zero fun b _ => by rw [hkrow b, zero_mul]
    have h2 : ∑ a, k a * ∑ b, (pderiv j (Hm a b) * k b + Hm a b * pderiv j (k b)) = 0 := by
      exact Finset.sum_eq_zero fun a _ => by rw [h1 a, mul_zero]
    simp_rw [Finset.mul_sum, mul_add, Finset.sum_add_distrib] at h2
    simp_rw [Finset.mul_sum] at h3
    rw [h3, add_zero] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  obtain ⟨v, hv0, hvk, hvq⟩ := lowest_order_quadratic k (fun j a b => pderiv j (Hm a b)) hk0 hid
  have hvY : ∀ a, v a ≠ 0 → a ∈ Y := by
    intro a ha; by_contra hc; exact ha (hvk a (hkY a hc))
  -- The vector `v` gives a nonzero critical point.
  apply hv0
  apply H.common_zero
  intro i
  have hfi := pderiv_f_isWH H.hom i
  have hwpos := H.pos
  have hbig := H.big
  have key := taylor2 (pderiv i f) 0 v (fun a b c ha hb hc => by
    have := hY a (hvY a ha); have := hY b (hvY b hb); have := hY c (hvY c hc)
    exact pderiv3_zero hfi a b c (by omega) (hwpos a))
  rw [zero_add] at key
  rw [key]
  have e0 : eval 0 (pderiv i f) = 0 :=
    eval_zero_of_isWH_pos hfi (by have := hbig i; omega)
  have e1 : ∀ c, eval 0 (pderiv c (pderiv i f)) = 0 := fun c =>
    eval_zero_of_isWH_pos (pderiv_isWH hfi c).1 (by have := hbig i; have := hbig c; omega)
  have e2 : ∑ c, ∑ b, v c * v b * eval 0 (pderiv b (pderiv c (pderiv i f))) = 0 := by
    rw [← hvq i]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases hc : v c = 0
    · simp [hc]
    by_cases hb : v b = 0
    · simp [hb]
    have hcY := hvY c hc; have hbY := hvY b hb
    simp only [hHm, hessY, hcY, hbY, and_self, if_true]
    rw [pderiv_comm' c i, pderiv_comm' b i]
    ring
  rw [e0, e2, Finset.sum_eq_zero (fun c _ => by rw [e1 c, mul_zero])]; ring

end Yau
