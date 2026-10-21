import RequestProject.Yau.Sec4_Proof.Quotient

/-!
# Orbits of locally nilpotent derivations: Lemma 4.1

For a homogeneous derivation of negative degree, the orbit through `p` has
polynomial coordinates `P_l(t)=∑ t^ν(D^νx_l)(p)/ν!`.
A weighted rescaling `ζ^{bw}P(ζ^{-a})` degenerates a nonconstant orbit to a
nonzero common zero of the partial derivatives, giving the contradiction used
in the selected-ideal application of Lemma 4.1.
-/

open MvPolynomial Finset

noncomputable section

namespace Yau

variable {n : ℕ} {w : Fin n → ℕ} {d : ℕ} {f : Poly n}

lemma choose_factorial_inv {i j : ℕ} :
    ((i + j).choose i : ℂ) * ((i + j).factorial : ℂ)⁻¹ =
      (i.factorial : ℂ)⁻¹ * (j.factorial : ℂ)⁻¹ := by
  have h := Nat.add_choose_mul_factorial_mul_factorial i j
  have h' : ((i + j).choose i : ℂ) * i.factorial * j.factorial = (i + j).factorial := by
    exact_mod_cast (by rw [Nat.choose_symm_add]; exact h)
  have h1 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have h2 : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have h3 : ((i + j).choose i : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_right i j)).ne'
  rw [← h']
  field_simp

/-- The iterated Leibniz rule for a derivation. -/
lemma iterate_leibniz {A : Type*} [CommRing A] [Algebra ℂ A] (D : Derivation ℂ A A)
    (a b : A) (k : ℕ) :
    (⇑D)^[k] (a * b) =
      ∑ ij ∈ antidiagonal k, (k.choose ij.1 : A) * ((⇑D)^[ij.1] a * (⇑D)^[ij.2] b) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_sum,
      Finset.sum_antidiagonal_choose_succ_mul (fun i j => ((⇑D)^[i] a * (⇑D)^[j] b))]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Derivation.leibniz, Derivation.leibniz]
    have hc : D (k.choose ij.1 : A) = 0 := by
      rw [show (k.choose ij.1 : A) = algebraMap ℂ A (k.choose ij.1) by simp]
      exact D.map_algebraMap _
    simp only [smul_eq_mul, hc, mul_zero, add_zero, Function.iterate_succ_apply']
    rw [Nat.choose_symm_of_eq_add (Finset.mem_antidiagonal.mp hij).symm]
    ring

/-- Coefficients of the formal orbit `exp(tD)` evaluated at a point. -/
lemma orbit_coeff (D : Derivation ℂ (Poly n) (Poly n)) (x0 : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ)
    (hP : ∀ l k, (P l).coeff k = (k.factorial : ℂ)⁻¹ * eval x0 ((⇑D)^[k] (X l)))
    (p : Poly n) (k : ℕ) :
    (aeval P p).coeff k = (k.factorial : ℂ)⁻¹ * eval x0 ((⇑D)^[k] p) := by
  induction p using MvPolynomial.induction_on generalizing k with
  | C a =>
    rw [aeval_C, Polynomial.algebraMap_apply, Polynomial.coeff_C]
    cases k with
    | zero => simp
    | succ k =>
      simp only [Nat.succ_ne_zero, if_false, Function.iterate_succ_apply, derivation_C]
      rw [Function.iterate_fixed (map_zero D)]; simp
  | add p q hp hq =>
    rw [map_add, Polynomial.coeff_add, hp, hq, iterate_map_add, map_add]; ring
  | mul_X p l hp =>
    rw [map_mul, aeval_X, Polynomial.coeff_mul, iterate_leibniz, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [hp, hP]
    obtain ⟨i, j⟩ := ij
    rw [Finset.mem_antidiagonal] at hij
    subst hij
    simp only [map_mul, map_natCast]
    linear_combination (-(eval x0 ((⇑D)^[i] p) * eval x0 ((⇑D)^[j] (X l)))) *
      (choose_factorial_inv (i := i) (j := j))

lemma polynomial_eval_aeval (P : Fin n → Polynomial ℂ) (g : Poly n) (t : ℂ) :
    (aeval P g).eval t = eval (fun l => (P l).eval t) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p l hp => simp [hp]

lemma poly_eq_of_eval_ne_zero (p q : Polynomial ℂ) (h : ∀ ζ : ℂ, ζ ≠ 0 → p.eval ζ = q.eval ζ) :
    p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono _ (Set.finite_singleton (0 : ℂ)).infinite_compl
  intro ζ hζ
  exact h ζ hζ

lemma iterate_mem {I : Ideal (Poly n)} (D : Derivation ℂ (Poly n) (Poly n))
    (hI : ∀ p ∈ I, D p ∈ I) {p : Poly n} (hp : p ∈ I) (k : ℕ) : (⇑D)^[k] p ∈ I := by
  induction k with
  | zero => simpa
  | succ k ih => rw [Function.iterate_succ_apply']; exact hI _ ih

/-- The form of Lemma 4.1 used in the proof: if `D` preserves `I` and `D²f_i∈I` for every `i`, then every `D(x_j)` belongs to `√I`. -/
lemma Setup.orbit (H : Setup w d f) {s : ℕ} (hs : 0 < s) {h : Fin n → Poly n}
    (hh : IsNegHomog w s h) (I : Ideal (Poly n)) (hI : ∀ p ∈ I, polyDer h p ∈ I)
    (h2 : ∀ i, polyDer h (polyDer h (pderiv i f)) ∈ I) :
    ∀ j, h j ∈ I.radical := by
  classical
  intro j
  by_contra hj
  set D := polyDer h with hD
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ)] at hj
  simp only [mem_vanishingIdeal_iff, not_forall] at hj
  obtain ⟨x0, hx0, hne⟩ := hj
  rw [mem_zeroLocus_iff] at hx0
  have hx0' : ∀ p ∈ I, eval x0 p = 0 := fun p hp => by
    simpa [coe_aeval_eq_eval] using hx0 p hp
  have hne' : eval x0 (h j) ≠ 0 := by simpa [coe_aeval_eq_eval] using hne
  -- The orbit polynomials.
  set P : Fin n → Polynomial ℂ := fun l => ∑ ν ∈ Finset.range (w l + 1),
      Polynomial.C ((ν.factorial : ℂ)⁻¹ * eval x0 ((⇑D)^[ν] (X l))) * Polynomial.X ^ ν
    with hPdef
  have hP : ∀ l k, (P l).coeff k = (k.factorial : ℂ)⁻¹ * eval x0 ((⇑D)^[k] (X l)) := by
    intro l k
    simp only [hPdef, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    split_ifs with hk
    · rfl
    · rw [polyDer_iterate_eq_zero hh hs (isWeightedHomogeneous_X ℂ w l)
        (by simp at hk; omega)]
      simp
  have hcoef := orbit_coeff D x0 P hP
  -- Each partial derivative has an orbit affine in `t`.
  have hfi : ∀ i, aeval P (pderiv i f) = Polynomial.C (eval x0 (pderiv i f)) +
      Polynomial.C (eval x0 (D (pderiv i f))) * Polynomial.X := by
    intro i; ext k
    rw [hcoef]
    rcases k with _ | _ | k
    · simp
    · simp
    · have hmem : (⇑D)^[k + 2] (pderiv i f) ∈ I := by
        rw [Function.iterate_add_apply]
        exact iterate_mem D hI (h2 i) k
      rw [hx0' _ hmem]
      simp
  -- The `j`th coordinate is nonconstant.
  have hPj1 : (P j).coeff 1 ≠ 0 := by
    rw [hP]; simpa [hD, mkDerivation_X] using hne'
  have hPjdeg : 0 < (P j).natDegree := by
    by_contra hc
    exact hPj1 (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
  -- Choose `j0` minimizing `w_l/deg P_l` among nonconstant coordinates.
  set S := Finset.univ.filter fun l => 0 < (P l).natDegree
  obtain ⟨j0, hj0S, hmin⟩ := S.exists_min_image
    (fun l => (w l : ℚ) / (P l).natDegree) ⟨j, by simp [S, hPjdeg]⟩
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj0S hmin
  set a := w j0 with ha
  set b := (P j0).natDegree with hb
  have hapos : 0 < a := H.pos j0
  have hab : ∀ l, ∀ k ≤ (P l).natDegree, a * k ≤ b * w l := by
    intro l k hk
    by_cases hl : (P l).natDegree = 0
    · rw [hl] at hk; have : k = 0 := by omega
      subst this; simp
    · have h1 := hmin l (Nat.pos_of_ne_zero hl)
      rw [div_le_div_iff₀ (by exact_mod_cast hj0S) (by exact_mod_cast Nat.pos_of_ne_zero hl)]
        at h1
      have h2 : a * (P l).natDegree ≤ w l * b := by exact_mod_cast h1
      calc a * k ≤ a * (P l).natDegree := Nat.mul_le_mul_left _ hk
        _ ≤ b * w l := by linarith
  -- The rescaled orbit.
  set γ : Fin n → Polynomial ℂ := fun l => ∑ k ∈ Finset.range ((P l).natDegree + 1),
      Polynomial.C ((P l).coeff k) * Polynomial.X ^ (b * w l - a * k) with hγdef
  have hγ : ∀ ζ : ℂ, ζ ≠ 0 → ∀ l, (γ l).eval ζ = (ζ ^ b) ^ w l * (P l).eval (ζ⁻¹ ^ a) := by
    intro ζ hζ l
    rw [Polynomial.eval_eq_sum_range (p := P l), Finset.mul_sum]
    simp only [hγdef, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : a * k ≤ b * w l := hab l k (by simp at hk; omega)
    rw [pow_sub₀ _ hζ hk']
    simp only [← pow_mul, inv_pow]
    ring
  have hγg : ∀ (g : Poly n) (e : ℕ), g.IsWeightedHomogeneous w e → ∀ ζ : ℂ, ζ ≠ 0 →
      (aeval γ g).eval ζ = (ζ ^ b) ^ e * (aeval P g).eval (ζ⁻¹ ^ a) := by
    intro g e hg ζ hζ
    rw [polynomial_eval_aeval, polynomial_eval_aeval]
    simp_rw [hγ ζ hζ]
    exact eval_scale hg _ _
  -- The limiting point is a common zero of all partial derivatives.
  have hzero : ∀ i, eval (fun l => (γ l).eval 0) (pderiv i f) = 0 := by
    intro i
    set e := d - w i
    have hae : a < e := by have := H.big i; have := H.big j0; omega
    have hbe : e ≤ b * e := Nat.le_mul_of_pos_left e hj0S
    set Q : Polynomial ℂ := Polynomial.C (eval x0 (pderiv i f)) * Polynomial.X ^ (b * e) +
      Polynomial.C (eval x0 (D (pderiv i f))) * Polynomial.X ^ (b * e - a)
    have hQ : aeval γ (pderiv i f) = Q := by
      apply poly_eq_of_eval_ne_zero
      intro ζ hζ
      rw [hγg _ _ (pderiv_f_isWH H.hom i) ζ hζ, hfi]
      simp only [Q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      rw [pow_sub₀ _ hζ (by omega), ← pow_mul, inv_pow]
      ring
    rw [← polynomial_eval_aeval, hQ]
    simp only [Q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    rw [zero_pow (by omega), zero_pow (by omega)]
    ring
  have hpt := H.common_zero _ hzero
  have hj0val := congrFun hpt j0
  simp only [Pi.zero_apply] at hj0val
  -- Its `j0`th coordinate is the nonzero leading coefficient of `P j0`.
  rw [hγdef] at hj0val
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X] at hj0val
  rw [Finset.sum_eq_single b] at hj0val
  · rw [← ha, show b * a - a * b = 0 by rw [mul_comm]; simp, pow_zero, mul_one] at hj0val
    have hP0 : P j0 ≠ 0 := by
      intro h0
      have : (P j0).natDegree = 0 := by rw [h0]; simp
      omega
    exact (Polynomial.leadingCoeff_ne_zero.mpr hP0) hj0val
  · intro k hk hkb
    have hkb' : k < b := by simp at hk; omega
    rw [← ha, zero_pow, mul_zero]
    have : a * k < b * a := by rw [mul_comm b]; exact Nat.mul_lt_mul_of_pos_left hkb' hapos
    omega
  · intro hb'; exfalso; apply hb'; simp [hb]

end Yau
