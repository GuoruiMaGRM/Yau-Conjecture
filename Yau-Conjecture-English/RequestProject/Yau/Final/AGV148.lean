import RequestProject.Yau.Final.ThreeNew
import RequestProject.Yau.Sec3_Radical.VarchenkoInclusion

/-!
# AGV, Theorem 14.8: the `μ`-constant stratum

The external input for Lemma 3.4 is Theorem 14.8 in Arnold–Gusein-Zade–Varchenko,
*Singularities of Differentiable Maps, Volume 2*, p. 415. In the monomial-basis
versal deformation, the `μ`-constant stratum with critical value zero is the
coordinate subspace on which parameters of positive parameter weight vanish.
Normalizing the variable weights gives `α_i = w_i/d`, so a monomial has
normalized weight less than one exactly when its weighted degree is less than `d`.

The proposition below records the corresponding neighborhood statement for
polynomials and local Milnor numbers. The critical point is allowed to move.
The reverse inclusion is proved in `VarchenkoInclusion.lean`; this identifies
the proposition with `VarchenkoTheoremFor`. The cases of zero and one variable
are proved directly. The main theorem takes the result for `n ≥ 2` as a hypothesis.
-/

open MvPolynomial Filter Topology

noncomputable section

namespace Yau

/-- AGV, Theorem 14.8 in `n` variables, as a neighborhood statement. For a positive-degree weighted homogeneous `f` and a monomial basis of its Milnor algebra, a small parameter lies in the zero-critical-value `μ`-constant stratum if and only if every parameter attached to a monomial of degree less than `d` vanishes. The nearby isolated critical point may move. -/
def «AGV定理14_8For» (n : ℕ) : Prop :=
  ∀ (w : Fin n → ℕ) (d : ℕ) (f : Poly n), (∀ i, 0 < w i) → 0 < d →
    f.IsWeightedHomogeneous w d → HasIsolatedCriticalPoint f → eval 0 f = 0 →
    ∀ (μ : ℕ) (β : Fin μ → (Fin n →₀ ℕ)), IsMonomialBasis f β →
    ∃ ε > 0, ∀ s : Fin μ → ℂ, ‖s‖ < ε →
      ((∃ p : Fin n → ℂ, ‖p‖ < ε ∧
          IsIsolatedCriticalPointAt (miniversalDeformation f β s) p ∧
          miniversalDeformation f β s p = 0 ∧
          localMilnorNumber (miniversalDeformation f β s) p =
            localMilnorNumber (fun x => eval x f) 0) ↔
        ∀ j, Finsupp.weight w (β j) < d → s j = 0)

/-- AGV, Theorem 14.8 implies `VarchenkoTheoremFor n`, the inclusion of the stratum in the coordinate subspace. For `d = 0` the degree condition is empty. -/
theorem varchenkoTheoremFor_of_AGV {n : ℕ} (h : «AGV定理14_8For» n) : VarchenkoTheoremFor n := by
  intro w d f hw hf hcrit hf0 μ β hβ
  rcases Nat.eq_zero_or_pos d with hd | hd
  · exact ⟨1, one_pos, fun _ _ _ _ _ _ _ j hj => absurd hj (by omega)⟩
  obtain ⟨ε, hε, H⟩ := h w d f hw hd hf hcrit hf0 μ β hβ
  exact ⟨ε, hε, fun s p hs hp h1 h2 h3 => (H s hs).1 ⟨p, hp, h1, h2, h3⟩⟩

/-- Conversely, `VarchenkoTheoremFor n` gives the full coordinate description because the reverse inclusion has been proved. -/
theorem AGV_of_varchenkoTheoremFor {n : ℕ} (h : VarchenkoTheoremFor n) : «AGV定理14_8For» n :=
  fun _ _ _ hw hd hf hcrit _ _ _ hβ => «定理3_4_完整_由反向包含» h hw hf hd hcrit hβ

/-- The neighborhood form of AGV, Theorem 14.8 is equivalent to `VarchenkoTheoremFor n`. -/
theorem «AGV定理14_8For_iff» (n : ℕ) : «AGV定理14_8For» n ↔ VarchenkoTheoremFor n :=
  ⟨varchenkoTheoremFor_of_AGV, AGV_of_varchenkoTheoremFor⟩

/-- AGV, Theorem 14.8 in one variable, proved directly. -/
theorem «AGV定理14_8_一元» : «AGV定理14_8For» 1 := AGV_of_varchenkoTheoremFor «定理3_4_一元»

/-- AGV, Theorem 14.8 in zero variables, proved directly. -/
theorem «AGV定理14_8_零元» : «AGV定理14_8For» 0 := AGV_of_varchenkoTheoremFor «定理3_4_零元»

/-- The main theorem assuming AGV, Theorem 14.8 for `n ≥ 2`: a weighted homogeneous polynomial with positive weights and an isolated critical point has no nonzero negative-degree derivation on its Milnor algebra. -/
theorem «Yau猜想_假定AGV定理14_8» (hA : ∀ m, 2 ≤ m → «AGV定理14_8For» m) {n : ℕ}
    (w : Fin n → ℕ) (d : ℕ) (f : Poly n) (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hcrit : HasIsolatedCriticalPoint f) (k : ℤ) (hk : k < 0)
    (δ : Derivation ℂ (MilnorAlgebra f) (MilnorAlgebra f))
    (hδ : IsDerivationOfDegree w f k δ) : δ = 0 :=
  «Yau猜想» (varchenkoTheorem_iff_two_le.2 fun m hm => varchenkoTheoremFor_of_AGV (hA m hm))
    w d f hw hf hcrit k hk δ hδ

end Yau
