import RequestProject.Yau.Final.MainResult
import RequestProject.Yau.Sec3_Radical.VarchenkoOneVar

/-!
# Lemma 3.4 and its role in the proof

For `q ∈ S_e`, `e < d`, Lemma 3.4 says that the linear family `f+tq` has
`q ∈ J_f` when the origin remains an isolated critical point of value zero
and its local Milnor number remains constant. The one-variable case is proved
by root multiplicities. For several variables, `ThreeNewLocal.lean` derives
the result from AGV, Theorem 14.8 and the proved versality construction.
This file supplies the local and global formulations, Corollary 3.5, and their
connection to the main theorem.
-/

open MvPolynomial Filter Topology

noncomputable section

namespace Yau

/-- Lemma 3.4 in `n` variables: for homogeneous `q` of degree `e < d`, the local isolated-critical-point, zero-value, and constant-Milnor-number hypotheses for `f+tq` imply `q ∈ J_f`. -/
def «新版引理3_4For» (n : ℕ) : Prop :=
  ∀ (w : Fin n → ℕ) (d : ℕ) (f : Poly n), (∀ i, 0 < w i) →
    f.IsWeightedHomogeneous w d → HasIsolatedCriticalPoint f → eval 0 f = 0 →
    ∀ (q : Poly n) (e : ℕ), q.IsWeightedHomogeneous w e → e < d →
    (∀ᶠ t in 𝓝 (0 : ℂ),
      IsIsolatedCriticalPointAt (fun x => eval x (f + C t * q)) 0 ∧
        eval 0 (f + C t * q) = 0 ∧
        localMilnorNumber (fun x => eval x (f + C t * q)) 0 =
          localMilnorNumber (fun x => eval x f) 0) →
    q ∈ jacobianIdeal f

/-- The global formulation of Lemma 3.4 assumes that the origin is the only critical point of `f+tq`, together with critical value zero and equality of analytic Milnor-algebra dimensions. Square deformations used in the main proof satisfy these conditions. -/
def «新版引理3_4_整体For» (n : ℕ) : Prop :=
  ∀ (w : Fin n → ℕ) (d : ℕ) (f : Poly n), (∀ i, 0 < w i) →
    f.IsWeightedHomogeneous w d → HasIsolatedCriticalPoint f → eval 0 f = 0 →
    ∀ (q : Poly n) (e : ℕ), q.IsWeightedHomogeneous w e → e < d →
    (∀ᶠ t in 𝓝 (0 : ℂ),
      (∀ x : Fin n → ℂ, (∀ i, eval x (pderiv i (f + C t * q)) = 0) ↔ x = 0) ∧
        eval 0 (f + C t * q) = 0 ∧ milnorNumber (f + C t * q) = milnorNumber f) →
    q ∈ jacobianIdeal f

lemma exists_ne_zero_of_eventually_nhds {P : ℂ → Prop} (h : ∀ᶠ t in 𝓝 (0 : ℂ), P t) :
    ∃ t, P t ∧ t ≠ 0 := by
  have h' : ∀ᶠ t in 𝓝[≠] (0 : ℂ), P t := nhdsWithin_le_nhds h
  exact (h'.and self_mem_nhdsWithin).exists

/-- A nonzero weighted homogeneous polynomial in one variable is a monomial `b x^ℓ`. -/
lemma eq_C_mul_X_pow_of_isWH1 {w : Fin 1 → ℕ} {e : ℕ} {q : Poly 1} (hw0 : 0 < w 0)
    (hq : q.IsWeightedHomogeneous w e) (hq0 : q ≠ 0) :
    ∃ (b : ℂ) (ℓ : ℕ), b ≠ 0 ∧ ℓ * w 0 = e ∧
      toPoly1 q = Polynomial.C b * Polynomial.X ^ ℓ := by
  obtain ⟨m₀, hm₀⟩ := MvPolynomial.ne_zero_iff.mp hq0
  set ℓ := m₀ 0
  have hwt : ∀ m, coeff m q ≠ 0 → m 0 * w 0 = e := by
    intro m hm
    have h := hq hm
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
    simpa [mul_comm] using h
  have hsupp : ∀ m, coeff m q ≠ 0 → m = Finsupp.single 0 ℓ := by
    intro m hm
    rw [finsupp_fin1 m]; congr 1
    exact Nat.eq_of_mul_eq_mul_right hw0 ((hwt m hm).trans (hwt m₀ hm₀).symm)
  set b := coeff (Finsupp.single 0 ℓ) q
  have hqeq : q = C b * X 0 ^ ℓ := by
    rw [C_mul_X_pow_eq_monomial]
    ext m
    rw [coeff_monomial]
    split_ifs with h
    · rw [← h]
    · by_contra hm; exact h (hsupp m hm).symm
  have hb : b ≠ 0 := by rintro hb; rw [hb, map_zero, zero_mul] at hqeq; exact hq0 hqeq
  refine ⟨b, ℓ, hb, hwt m₀ hm₀, ?_⟩
  rw [hqeq]; simp

/-- If `Q(0) ≠ 0`, then zero has multiplicity `k` in `X^k Q`. -/
lemma rootMultiplicity_zero_X_pow_mul {k : ℕ} {Q : Polynomial ℂ} (hQ : Q.eval 0 ≠ 0) :
    Polynomial.rootMultiplicity 0 (Polynomial.X ^ k * Q) = k := by
  have hQ' : Q ≠ 0 := fun h => hQ (by rw [h, Polynomial.eval_zero])
  rw [Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hQ'),
    Polynomial.rootMultiplicity_eq_zero hQ]
  have := Polynomial.rootMultiplicity_X_sub_C_pow (0 : ℂ) k
  simpa using this

/-- The local form of Lemma 3.4 implies its global form. -/
theorem «新版引理3_4_整体_of» {n : ℕ} (h : «新版引理3_4For» n) : «新版引理3_4_整体For» n := by
  intro w d f hw hf hcrit hf0 q e hq he hfam
  apply h w d f hw hf hcrit hf0 q e hq he
  filter_upwards [hfam] with t ⟨hz, hval, hμ⟩
  refine ⟨isIsolatedCriticalPointAt_of_hasIsolatedCriticalPoint
    ⟨(hz 0).2 rfl, Set.univ, univ_mem, fun x _ hx => (hz x).1 hx⟩, hval, ?_⟩
  rw [localMilnorNumber_eval_zero, localMilnorNumber_eval_zero, hμ]

/-- The `μ`-constant stratum hypothesis implies the global form of Lemma 3.4. -/
theorem «新版引理3_4_整体_of_varchenko» (hV : VarchenkoTheorem) (n : ℕ) :
    «新版引理3_4_整体For» n :=
  fun _ _ _ hw hf hcrit hf0 _ _ hq he hfam => «推论3_5_原点情形» hV hw hf hcrit hf0 hq he hfam

/-- Lemma 3.4 in zero variables. -/
theorem «新版引理3_4_零元» : «新版引理3_4For» 0 := by
  intro w d f hw hf hcrit hf0 q e hq he hfam
  obtain ⟨t, ⟨-, hval, -⟩, ht0⟩ := exists_ne_zero_of_eventually_nhds hfam
  have hq' := eq_C_of_isEmpty q
  rw [map_add, map_mul, eval_C, hf0, zero_add, hq', eval_C] at hval
  have hb : coeff 0 q = 0 := (mul_eq_zero.mp hval).resolve_left ht0
  rw [hq', hb, map_zero]
  exact zero_mem _

/-- Lemma 3.4 in one variable, by the direct argument in the paper. -/
theorem «新版引理3_4_一元» : «新版引理3_4For» 1 := by
  intro w d f hw hf hcrit hf0 q e hq he hfam
  obtain ⟨c, m, hc, hm, hmd, hfc⟩ := eq_C_mul_X_pow_of_isolated hw hf hcrit hf0
  by_contra hqJ
  have hq0 : q ≠ 0 := by rintro rfl; exact hqJ (zero_mem _)
  obtain ⟨b, ℓ, hb, hℓe, hqc⟩ := eq_C_mul_X_pow_of_isWH1 (hw 0) hq hq0
  have hℓm : ℓ < m := by
    by_contra h; push_neg at h
    have := Nat.mul_le_mul_right (w 0) h
    omega
  obtain ⟨t, ⟨-, hval, hμ⟩, ht0⟩ := exists_ne_zero_of_eventually_nhds hfam
  have hP : toPoly1 (f + C t * q) =
      Polynomial.C c * Polynomial.X ^ m + Polynomial.C (t * b) * Polynomial.X ^ ℓ := by
    rw [map_add, map_mul, hfc, hqc, toPoly1_C, Polynomial.C_mul]; ring
  have htb : t * b ≠ 0 := mul_ne_zero ht0 hb
  rcases Nat.eq_zero_or_pos ℓ with hℓ0 | hℓ0
  · apply htb
    rw [eval_eq_toPoly1_eval, hP, hℓ0] at hval
    simpa [zero_pow (by omega : m ≠ 0)] using hval
  · -- Compare local Milnor numbers: `μ(f_t,0) = ℓ-1 < m-1 = μ(f,0)`.
    set Q : Polynomial ℂ := Polynomial.C (c * m) * Polynomial.X ^ (m - ℓ) +
      Polynomial.C (t * b * ℓ) with hQ
    have hQ0 : Q.eval 0 ≠ 0 := by
      simp only [hQ, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, zero_pow (by omega : m - ℓ ≠ 0), mul_zero,
        zero_add]
      exact mul_ne_zero htb (by exact_mod_cast hℓ0.ne')
    have hDt : Polynomial.derivative (toPoly1 (f + C t * q)) =
        Polynomial.X ^ (ℓ - 1) * Q := by
      rw [hP, Polynomial.derivative_add, Polynomial.derivative_C_mul_X_pow,
        Polynomial.derivative_C_mul_X_pow, hQ, mul_add, mul_left_comm, ← pow_add,
        show ℓ - 1 + (m - ℓ) = m - 1 by omega]
      simp only [Polynomial.C_mul, map_natCast]
      ring
    have hDf : Polynomial.derivative (toPoly1 f) =
        Polynomial.X ^ (m - 1) * Polynomial.C (c * m) := by
      rw [hfc, Polynomial.derivative_C_mul_X_pow, mul_comm]
    have hcm : (Polynomial.C (c * m)).eval 0 ≠ 0 := by
      simp only [Polynomial.eval_C]; exact mul_ne_zero hc (by exact_mod_cast (by omega : m ≠ 0))
    have hpt : pderiv 0 (f + C t * q) ≠ 0 := by
      intro h0
      have := congrArg toPoly1 h0
      rw [toPoly1_pderiv, hDt, map_zero] at this
      exact (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
        (fun h => hQ0 (by rw [h, Polynomial.eval_zero]))) this
    have hpf : pderiv 0 f ≠ 0 := by
      intro h0
      have := congrArg toPoly1 h0
      rw [toPoly1_pderiv, hDf, map_zero] at this
      exact (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
        (fun h => hcm (by rw [h, Polynomial.eval_zero]))) this
    rw [localMilnorNumber_eval_one hpt, localMilnorNumber_eval_one hpf, hDt, hDf] at hμ
    simp only [Pi.zero_apply] at hμ
    rw [rootMultiplicity_zero_X_pow_mul hQ0, rootMultiplicity_zero_X_pow_mul hcm] at hμ
    omega

/-- The global form of Lemma 3.4 yields the square-deformation input `VarchenkoHypothesis`, as in Corollary 3.5. -/
theorem varchenkoHypothesis_of_newLemma34 (h : ∀ m, «新版引理3_4_整体For» m) :
    VarchenkoHypothesis := by
  intro m w d g H r a ha hr haI
  have h2 : (a ^ 2).IsWeightedHomogeneous w (2 * r) := by
    have h := ha.pow 2
    rwa [smul_eq_mul] at h
  have hsq := squareDeformation_hyp H ha hr haI
  have hcrit0 : HasIsolatedCriticalPoint g := by simpa using (hsq 0).1
  have hg0 : eval 0 g = 0 := by simpa using (hsq 0).2.1
  exact h m w d g H.pos H.hom hcrit0 hg0 (a ^ 2) (2 * r) h2 (by omega)
    (Eventually.of_forall fun t =>
      ⟨squareDeformation_critical_iff H ha hr haI t, (hsq t).2.1, (hsq t).2.2⟩)

/-- The main theorem under the global form of Lemma 3.4 for `n ≥ 2`. -/
theorem «Yau猜想_新版_整体» (hL : ∀ m, 2 ≤ m → «新版引理3_4_整体For» m) {n : ℕ}
    (w : Fin n → ℕ) (d : ℕ) (f : Poly n) (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hcrit : HasIsolatedCriticalPoint f) (k : ℤ) (hk : k < 0)
    (δ : Derivation ℂ (MilnorAlgebra f) (MilnorAlgebra f))
    (hδ : IsDerivationOfDegree w f k δ) : δ = 0 := by
  refine yau_conjecture_of_critical (varchenkoHypothesis_of_newLemma34 fun m => ?_)
    w d f hw hf hcrit k hk δ hδ
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · exact «新版引理3_4_整体_of» «新版引理3_4_零元»
    · exact «新版引理3_4_整体_of» «新版引理3_4_一元»
  · exact hL m hm

/-- The main theorem under Lemma 3.4 for `n ≥ 2`; the zero- and one-variable cases of the lemma are proved directly. -/
theorem «Yau猜想_新版» (hL : ∀ m, 2 ≤ m → «新版引理3_4For» m) {n : ℕ}
    (w : Fin n → ℕ) (d : ℕ) (f : Poly n) (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hcrit : HasIsolatedCriticalPoint f) (k : ℤ) (hk : k < 0)
    (δ : Derivation ℂ (MilnorAlgebra f) (MilnorAlgebra f))
    (hδ : IsDerivationOfDegree w f k δ) : δ = 0 :=
  «Yau猜想_新版_整体» (fun m hm => «新版引理3_4_整体_of» (hL m hm)) w d f hw hf hcrit k hk δ hδ

end Yau
