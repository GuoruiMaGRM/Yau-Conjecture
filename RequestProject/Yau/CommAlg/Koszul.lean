import RequestProject.Yau.Sec3_Radical.WeightFiltration

/-!
# First syzygies of regular sequences are Koszul relations

If `∑ b_i g_i = 0` and the `g_i` form a regular sequence, then
`b_i = ∑_j c_{ij}g_j` with `c_{ij} = -c_{ji}`. For homogeneous data the
coefficients can be chosen homogeneous of the appropriate degrees.
-/

open MvPolynomial

noncomputable section

namespace Yau

section General

variable {R : Type*} [CommRing R]

lemma mem_span_image_Iio_iff (g : ℕ → R) (k : ℕ) (x : R) :
    x ∈ Ideal.span (g '' Set.Iio k) ↔ ∃ d : ℕ → R, x = ∑ i ∈ Finset.range k, d i * g i := by
  have himg : g '' Set.Iio k = Set.range (fun i : Fin k => g i) := by
    ext y; constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨i, i.2, rfl⟩
  rw [himg, Ideal.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun i => if h : i < k then c ⟨i, h⟩ else 0, ?_⟩
    rw [← Fin.sum_univ_eq_sum_range (fun i => (if h : i < k then c ⟨i, h⟩ else 0) * g i)]
    simp
  · rintro ⟨d, rfl⟩
    exact ⟨fun i => d i, by rw [Fin.sum_univ_eq_sum_range (fun i => d i * g i)]⟩

/-- A first syzygy of a regular sequence is a Koszul relation with an antisymmetric coefficient matrix. -/
theorem koszul_syzygy (g : ℕ → R) (n : ℕ)
    (hreg : ∀ k < n, ∀ b : R, g k * b ∈ Ideal.span (g '' Set.Iio k) →
      b ∈ Ideal.span (g '' Set.Iio k)) :
    ∀ k ≤ n, ∀ b : ℕ → R, ∑ i ∈ Finset.range k, b i * g i = 0 →
      ∃ c : ℕ → ℕ → R, (∀ i j, c i j = -c j i) ∧
        ∀ i < k, b i = ∑ j ∈ Finset.range k, c i j * g j := by
  intro k
  induction k with
  | zero =>
    intro _ b _
    exact ⟨fun _ _ => 0, fun _ _ => by simp, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk b hb
    rw [Finset.sum_range_succ] at hb
    have hbk : g k * b k ∈ Ideal.span (g '' Set.Iio k) := by
      rw [mem_span_image_Iio_iff]
      refine ⟨fun i => -b i, ?_⟩
      rw [mul_comm, eq_neg_of_add_eq_zero_right hb, ← Finset.sum_neg_distrib]
      simp
    obtain ⟨d, hd⟩ := (mem_span_image_Iio_iff g k _).1 (hreg k (by omega) _ hbk)
    obtain ⟨c', hc'skew, hc'⟩ := ih (by omega) (fun i => b i + d i * g k) (by
      simp only [add_mul, Finset.sum_add_distrib]
      have : ∑ i ∈ Finset.range k, d i * g k * g i = b k * g k := by
        rw [hd, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this]; exact hb)
    refine ⟨fun i j => if i < k then (if j < k then c' i j else if j = k then -d i else 0)
      else if i = k then (if j < k then d j else 0) else 0, ?_, ?_⟩
    · intro i j
      by_cases hi : i < k <;> by_cases hj : j < k <;> simp only [hi, hj, if_true, if_false]
      · exact hc'skew i j
      · by_cases hjk : j = k
        · simp [hjk]
        · simp [hjk]
      · by_cases hik : i = k
        · simp [hik]
        · simp [hik]
      · by_cases hik : i = k <;> by_cases hjk : j = k <;> simp [hik, hjk]
    · intro i hi
      rw [Finset.sum_range_succ]
      by_cases hik : i < k
      · simp only [hik, if_true, lt_irrefl k, if_false]
        have h1 : ∑ x ∈ Finset.range k, (if x < k then c' i x else if x = k then -d i else 0) * g x
            = ∑ x ∈ Finset.range k, c' i x * g x :=
          Finset.sum_congr rfl fun x hx => by rw [if_pos (Finset.mem_range.1 hx)]
        rw [h1, ← hc' i hik]; ring
      · have : i = k := by omega
        subst this
        simp only [lt_irrefl, ↓reduceIte, zero_mul, add_zero]
        rw [hd]
        exact Finset.sum_congr rfl fun x hx => by rw [if_pos (Finset.mem_range.1 hx)]

end General

section Homog

variable {n : ℕ} {w : Fin n → ℕ}

/-- Homogeneous form: if `g_i` has degree `a_i` and `b_i` has degree `q-a_i`, the antisymmetric coefficients have degree `q-a_i-a_j`; negative-degree coefficients are zero. -/
theorem koszul_syzygy_homog (g : ℕ → Poly n) (a : ℕ → ℕ) (k : ℕ)
    (hg : ∀ i, (g i).IsWeightedHomogeneous w (a i))
    (hreg : ∀ j < k, ∀ b : Poly n, g j * b ∈ Ideal.span (g '' Set.Iio j) →
      b ∈ Ideal.span (g '' Set.Iio j))
    (q : ℕ) (b : ℕ → Poly n) (hb : ∀ i, (b i).IsWeightedHomogeneous w (q - a i))
    (hb0 : ∀ i, q < a i → b i = 0)
    (hsum : ∑ i ∈ Finset.range k, b i * g i = 0) :
    ∃ c : ℕ → ℕ → Poly n, (∀ i j, c i j = -c j i) ∧
      (∀ i j, (c i j).IsWeightedHomogeneous w (q - a i - a j)) ∧
      (∀ i j, q < a i + a j → c i j = 0) ∧
      ∀ i < k, b i = ∑ j ∈ Finset.range k, c i j * g j := by
  classical
  obtain ⟨c, hskew, hc⟩ := koszul_syzygy g k hreg k le_rfl b hsum
  refine ⟨fun i j => if a i + a j ≤ q then weightedHomogeneousComponent w (q - a i - a j) (c i j)
    else 0, ?_, ?_, ?_, ?_⟩
  · intro i j
    simp only [add_comm (a i) (a j), show q - a i - a j = q - a j - a i by omega]
    split_ifs
    · rw [hskew i j, map_neg]
    · simp
  · intro i j
    dsimp only
    split_ifs
    · exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
    · exact isWeightedHomogeneous_zero _ _ _
  · intro i j h
    simp [not_le.2 h]
  · intro i hi
    by_cases hiq : a i ≤ q
    · conv_lhs => rw [← (hb i).weightedHomogeneousComponent_same, hc i hi]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp only
      rw [weightedHomogeneousComponent_mul_of_right _ _ (a j) _ (hg j)]
      by_cases hj : a j ≤ q - a i
      · rw [if_pos hj, if_pos (by omega), show q - a i - a j = q - a i - a j from rfl]
      · rw [if_neg hj, if_neg (by omega), zero_mul]
    · rw [hb0 i (by omega)]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      dsimp only
      rw [if_neg (by omega), zero_mul]

end Homog

end Yau
