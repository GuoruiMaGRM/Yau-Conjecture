import RequestProject.Yau.Sec3_Radical.LemmaC1Local
import RequestProject.Yau.Sec3_Radical.Openness
import RequestProject.Yau.Sec3_Radical.VarchenkoOneVar

/-!
# The inclusion of the coordinate subspace in the `μ`-constant stratum

If all parameters attached to monomials of degree less than `d` vanish, split
the deformation into its degree-`d` part and its higher-weight remainder.
The homogeneous part stays isolated for small parameters. The higher-weight
perturbation preserves its local Milnor number, while the Hilbert-function
calculation identifies that number with `μ(f)`.
Thus the inclusion `E ⊆ Σ_μ` holds for every number of variables.
Together with the stratum inclusion supplied by AGV, Theorem 14.8, this yields
the coordinate description used in Lemma 3.4.
-/

open MvPolynomial Filter Topology

noncomputable section

namespace Yau

variable {n : ℕ} {w : Fin n → ℕ} {d : ℕ} {f : Poly n}

/-- If homogeneous `p` has degree `e<w_i`, its values at the coordinate unit vector `e_i` and at the origin agree. -/
lemma eval_single_of_isWH (hw : ∀ i, 0 < w i) {p : Poly n} {e : ℕ}
    (hp : p.IsWeightedHomogeneous w e) (i : Fin n) (he : e < w i) :
    eval (Pi.single i 1) p = eval 0 p := by
  classical
  rw [show eval 0 p = coeff 0 p by rw [← constantCoeff_eq, MvPolynomial.eval_zero], eval_eq]
  rw [Finset.sum_eq_single (0 : Fin n →₀ ℕ)]
  · simp
  · intro m hm hm0
    obtain ⟨k, hk⟩ : ∃ k, k ≠ i ∧ m k ≠ 0 := by
      by_contra h
      push_neg at h
      have hmi : m i ≠ 0 := by
        intro h0; apply hm0; ext k
        by_cases hk : k = i
        · subst hk; simpa using h0
        · by_contra hne; exact hne (h k hk) |>.elim
      have hwt := hp (mem_support_iff.1 hm)
      have := Finsupp.le_weight w (hw i).ne' m
      have : w i ≤ Finsupp.weight w m := by
        rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
        exact le_trans (by simpa using Nat.le_mul_of_pos_left (w i) (Nat.pos_of_ne_zero hmi))
          (Finset.single_le_sum (f := fun j => m j • w j) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ i))
      omega
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hk.2) ?_)
    rw [Pi.single_eq_of_ne hk.1, zero_pow hk.2]
  · intro h; rw [notMem_support_iff.1 h, zero_mul]

/-- Isolatedness at the origin forces `w_i<d` for every variable. Otherwise a coordinate unit vector would be a nonzero critical point. -/
theorem w_lt_of_hasIsolatedCriticalPoint (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hcrit : HasIsolatedCriticalPoint f) (i : Fin n) : w i < d := by
  classical
  by_contra hle
  push_neg at hle
  have hz := critical_eq_zero_of_isolated hw hf hcrit.2 (Pi.single i 1) fun j => by
    rw [eval_single_of_isWH hw (pderiv_f_isWH hf j) i (by have := hw j; have := hw i; omega)]
    exact hcrit.1 j
  have := congrFun hz i
  simp at this

set_option synthInstance.maxHeartbeats 200000 in
/-- The local Milnor number of `f` at the origin equals the dimension of its polynomial Milnor algebra. -/
lemma localMilnorNumber_eval_eq_finrank (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hcrit : HasIsolatedCriticalPoint f) :
    localMilnorNumber (fun x => eval x f) 0 = Module.finrank ℂ (MilnorAlgebra f) := by
  have e := (milnorAlgebraEquivAnalytic hw hf hcrit).toLinearEquiv
  rw [localMilnorNumber, localJacobianIdeal_eval_zero]
  exact e.finrank_eq.symm

/-- When the low-degree parameters vanish, split the miniversal polynomial into a degree-`d` homogeneous part `g_s` and a higher-weight part `R_s`. -/
lemma miniversalPoly_split {μ : ℕ} (β : Fin μ → (Fin n →₀ ℕ)) (s : Fin μ → ℂ)
    (hs : ∀ j, Finsupp.weight w (β j) < d → s j = 0) :
    miniversalPoly f β s =
      (f + ∑ k, C (s k) * (if Finsupp.weight w (β k) = d then monomial (β k) 1 else 0)) +
        ∑ k, (if d < Finsupp.weight w (β k) then monomial (β k) (s k) else 0) := by
  rw [miniversalPoly, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases lt_trichotomy (Finsupp.weight w (β k)) d with h | h | h
  · rw [hs k h, if_neg h.ne, if_neg (by omega)]; simp
  · rw [if_pos h, if_neg (by omega), C_mul_monomial, mul_one, add_zero]
  · rw [if_neg h.ne', if_pos h, mul_zero, zero_add]

/-- The inclusion `E ⊆ Σ_μ` for every number of variables: a sufficiently small parameter with vanishing low-degree coordinates gives an isolated critical point at the origin, critical value zero, and local Milnor number `μ(f)`. -/
theorem «定理3_4_反向包含» (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d) (hd : 0 < d)
    (hcrit : HasIsolatedCriticalPoint f) {μ : ℕ} (β : Fin μ → (Fin n →₀ ℕ)) :
    ∃ ε > 0, ∀ s : Fin μ → ℂ, ‖s‖ < ε → (∀ j, Finsupp.weight w (β j) < d → s j = 0) →
      IsIsolatedCriticalPointAt (miniversalDeformation f β s) 0 ∧
        miniversalDeformation f β s 0 = 0 ∧
        localMilnorNumber (miniversalDeformation f β s) 0 =
          localMilnorNumber (fun x => eval x f) 0 := by
  classical
  have hwd := w_lt_of_hasIsolatedCriticalPoint hw hf hcrit
  have hiso := isIsolatedSingularity_of_hasIsolatedCriticalPoint hw hf hcrit
  obtain ⟨T₀, hT₀⟩ := exists_highIdeal_le_of_pow_X_mem (w := w)
    (exists_pow_X_mem_jacobianIdeal hw hf hcrit)
  set φ : Fin μ → Poly n := fun k =>
    if Finsupp.weight w (β k) = d then monomial (β k) 1 else 0 with hφdef
  have hφ : ∀ k, (φ k).IsWeightedHomogeneous w d := by
    intro k; simp only [hφdef]; split_ifs with h
    · exact isWeightedHomogeneous_monomial _ _ _ h
    · exact isWeightedHomogeneous_zero _ _ _
  obtain ⟨ε, hε, H⟩ := eventually_highIdeal_le_jacobian hw hf hwd hT₀ φ hφ
  refine ⟨ε, hε, fun s hs hsE => ?_⟩
  obtain ⟨T, hT⟩ := H s hs
  set g := f + ∑ k, C (s k) * φ k with hgdef
  set R : Poly n := ∑ k, (if d < Finsupp.weight w (β k) then monomial (β k) (s k) else 0) with hRdef
  have hg : g.IsWeightedHomogeneous w d :=
    hf.add (IsWeightedHomogeneous.sum _ _ _ fun k _ => (hφ k).C_mul (s k))
  have hR : R ∈ highIdeal w (d + 1) := by
    refine Ideal.sum_mem _ fun k _ => ?_
    split_ifs with h
    · exact isWH_mem_highIdeal (isWeightedHomogeneous_monomial _ _ _ rfl) h
    · exact Ideal.zero_mem _
  have hgiso : IsIsolatedSingularity g := finite_quotient_of_pow_X_mem _ fun i =>
    ⟨T, hT (by
      have := (isWeightedHomogeneous_X ℂ w i).pow T
      rw [smul_eq_mul] at this
      exact isWH_mem_highIdeal this (Nat.le_mul_of_pos_right T (hw i)))⟩
  have hF : miniversalDeformation f β s = fun x => eval x (g + R) := by
    funext x; rw [miniversalDeformation, miniversalPoly_split β s hsE]
  rw [hF]
  refine ⟨isIsolatedCriticalPointAt_of_hasIsolatedCriticalPoint
      (hasIsolatedCriticalPoint_add_high hw hg hwd hR hT), ?_, ?_⟩
  · show eval 0 (g + R) = 0
    rw [map_add, eval_zero_of_isWH_pos hg hd, eval_zero_of_mem_highIdeal (by omega) hR, add_zero]
  · rw [localMilnorNumber_add_high hw hg hgiso hwd hR hT,
      localMilnorNumber_eval_eq_finrank hw hf hcrit,
      finrank_milnorAlgebra_eq_of_isWH hw hf hg hiso hgiso hwd]

/-- The stratum inclusion `Σ_μ ⊆ E` together with the proved reverse inclusion gives the full neighborhood equivalence; for the reverse inclusion the critical point can be taken to be the origin. -/
theorem «定理3_4_完整_由反向包含» (hV : VarchenkoTheoremFor n) (hw : ∀ i, 0 < w i)
    (hf : f.IsWeightedHomogeneous w d) (hd : 0 < d) (hcrit : HasIsolatedCriticalPoint f)
    {μ : ℕ} {β : Fin μ → (Fin n →₀ ℕ)} (hβ : IsMonomialBasis f β) :
    ∃ ε > 0, ∀ s : Fin μ → ℂ, ‖s‖ < ε →
      ((∃ p : Fin n → ℂ, ‖p‖ < ε ∧
          IsIsolatedCriticalPointAt (miniversalDeformation f β s) p ∧
          miniversalDeformation f β s p = 0 ∧
          localMilnorNumber (miniversalDeformation f β s) p =
            localMilnorNumber (fun x => eval x f) 0) ↔
        ∀ j, Finsupp.weight w (β j) < d → s j = 0) := by
  obtain ⟨ε₁, hε₁, H₁⟩ := hV w d f hw hf hcrit (eval_zero_of_isWH_pos hf hd) μ β hβ
  obtain ⟨ε₂, hε₂, H₂⟩ := «定理3_4_反向包含» hw hf hd hcrit β
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun s hs => ⟨fun ⟨p, hp, h1, h2, h3⟩ =>
    H₁ s p (lt_of_lt_of_le hs (min_le_left _ _)) (lt_of_lt_of_le hp (min_le_left _ _)) h1 h2 h3,
    fun hsE => ?_⟩⟩
  obtain ⟨h1, h2, h3⟩ := H₂ s (lt_of_lt_of_le hs (min_le_right _ _)) hsE
  exact ⟨0, by simpa using lt_min hε₁ hε₂, h1, h2, h3⟩

end Yau
