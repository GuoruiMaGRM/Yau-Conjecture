import RequestProject.Yau.Basic.Basic

/-! # Polynomial derivations of negative weighted degree -/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ}

/-- The polynomial derivation `D = ∑ h_j ∂/∂x_j`. -/
abbrev polyDer (h : Fin n → Poly n) : Derivation ℂ (Poly n) (Poly n) := mkDerivation ℂ h

lemma polyDer_apply (h : Fin n → Poly n) (p : Poly n) :
    polyDer h p = ∑ j, h j * pderiv j p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [derivation_C]
  | add p q hp hq => simp [hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p k hp =>
    rw [Derivation.leibniz, mkDerivation_X, hp]
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    simp [Pi.single_apply, mul_comm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- The commutator `[∂_i,D] = ∑_j (∂_i h_j)∂_j`. -/
lemma pderiv_polyDer (h : Fin n → Poly n) (i : Fin n) (p : Poly n) :
    pderiv i (polyDer h p) = polyDer h (pderiv i p) + ∑ j, pderiv i (h j) * pderiv j p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [derivation_C]
  | add p q hp hq => simp [hp, hq, mul_add, Finset.sum_add_distrib]; ring
  | mul_X p k hp =>
    simp only [Derivation.leibniz, mkDerivation_X, smul_eq_mul, map_add, hp, pderiv_X]
    simp only [mul_add, Finset.sum_add_distrib, Pi.single_apply]
    have : polyDer h (if k = i then 1 else 0) = 0 := by split_ifs <;> simp
    rw [this]
    simp only [mul_ite, ite_mul, one_mul, zero_mul, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
    rw [show ∑ x, pderiv i (h x) * (X k * pderiv x p) =
        ∑ x, X k * (pderiv i (h x) * pderiv x p) from
      Finset.sum_congr rfl fun _ _ => by ring]
    ring_nf

/-- The coefficients define a derivation of degree `-s`: `h_j` has degree `w_j-s` and is zero if `w_j < s`. -/
def IsNegHomog (w : Fin n → ℕ) (s : ℕ) (h : Fin n → Poly n) : Prop :=
  ∀ j, (h j).IsWeightedHomogeneous w (w j - s) ∧ (w j < s → h j = 0)

lemma polyDer_isWH {w : Fin n → ℕ} {s : ℕ} {h : Fin n → Poly n} (hh : IsNegHomog w s h)
    {p : Poly n} {m : ℕ} (hp : p.IsWeightedHomogeneous w m) :
    (polyDer h p).IsWeightedHomogeneous w (m - s) ∧ (m < s → polyDer h p = 0) := by
  rw [polyDer_apply]
  constructor
  · apply IsWeightedHomogeneous.sum
    intro j _
    by_cases h1 : w j < s
    · rw [(hh j).2 h1, zero_mul]; exact isWeightedHomogeneous_zero _ _ _
    by_cases h2 : m < w j
    · rw [pderiv_eq_zero_of_lt hp j h2, mul_zero]; exact isWeightedHomogeneous_zero _ _ _
    have := (hh j).1.mul (pderiv_isWH hp j).1
    rwa [show w j - s + (m - w j) = m - s by omega] at this
  · intro hm
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases h1 : w j < s
    · rw [(hh j).2 h1, zero_mul]
    · rw [pderiv_eq_zero_of_lt hp j (by omega), mul_zero]

lemma polyDer_iterate_isWH {w : Fin n → ℕ} {s : ℕ} {h : Fin n → Poly n}
    (hh : IsNegHomog w s h) {p : Poly n} {m : ℕ} (hp : p.IsWeightedHomogeneous w m) (ν : ℕ) :
    ((polyDer h)^[ν] p).IsWeightedHomogeneous w (m - ν * s) ∧
      (m < ν * s → (polyDer h)^[ν] p = 0) := by
  induction ν with
  | zero => simpa using hp
  | succ ν ih =>
    rw [Function.iterate_succ_apply']
    have := polyDer_isWH hh ih.1
    have h1 := this.1
    rw [show m - ν * s - s = m - (ν + 1) * s by rw [add_mul]; omega] at h1
    refine ⟨h1, fun hm => ?_⟩
    by_cases hc : m < ν * s
    · rw [ih.2 hc, map_zero]
    · exact this.2 (by rw [add_mul] at hm; omega)

/-- Local nilpotence: if `s > 0`, then `D^ν p = 0` for all sufficiently large `ν`. -/
lemma polyDer_iterate_eq_zero {w : Fin n → ℕ} {s : ℕ} {h : Fin n → Poly n}
    (hh : IsNegHomog w s h) (hs : 0 < s) {p : Poly n} {m : ℕ}
    (hp : p.IsWeightedHomogeneous w m) {ν : ℕ} (hν : m < ν) :
    (polyDer h)^[ν] p = 0 :=
  (polyDer_iterate_isWH hh hp ν).2 (lt_of_lt_of_le hν (Nat.le_mul_of_pos_right ν hs))

end Yau
