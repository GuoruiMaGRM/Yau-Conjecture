import RequestProject.Yau.Final.MainResult
import RequestProject.Yau.LowDim.ThreeVar
import RequestProject.Yau.Sec3_Radical.VarchenkoOneVar
import RequestProject.Yau.Sec3_Radical.VarchenkoInclusion
import RequestProject.Yau.Final.ThreeNew
import RequestProject.Yau.Final.AGV148
import RequestProject.Yau.Final.ThreeNewLocal
import RequestProject.Yau.LowDim.Homogeneous
import RequestProject.Yau.LowDim.QuadraticHeavy
import RequestProject.Yau.LowDim.LocalLevels
import RequestProject.Yau.LowDim.ThomSebastiani

/-!
# Lean companion to Yau's conjecture

Import this file to access all results. The reader's guide is in `README.md`
and `docs/Proof.md`.

The modules follow the accompanying paper:

* `Basic/` and `CommAlg/`: weighted grading, Milnor algebras, analytic local
  rings, and regular-sequence tools.
* `Sec2_Splitting/`: removal of quadratic variables and choice of the derivation.
* `Sec3_Radical/`: the Hessian and radical arguments, square deformations,
  and the monomial-basis deformation used in Lemma 3.4.
* `Analytic/` and `Versality/`: local Milnor numbers and the right-equivalence
  construction required in the proof of Lemma 3.4.
* `Sec4_Proof/`: the orbit argument and the final contradiction.
* `Appendix/`: the local-algebra comparison, Euler identity, syzygies, and lifting.
* `Final/AGV148.lean` and `Final/ThreeNewLocal.lean`: the textbook hypothesis
  and the main theorem under AGV, Theorem 14.8 for at least two variables.
* `LowDim/`: additional special cases and algebraic criteria.

The main theorem formalizes the paper's proof with the cited stratum theorem
as an explicit hypothesis. The required fixed-origin versality statement and
the zero- and one-variable cases of the stratum statement are proved here.
-/

open MvPolynomial

namespace Yau

/-- The main theorem for at most three variables, without the stratum hypothesis. -/
theorem yau_conjecture_le_three {n : ℕ} (hn : n ≤ 3) (w : Fin n → ℕ) (d : ℕ) (f : Poly n)
    (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hcrit : HasIsolatedCriticalPoint f) (k : ℤ) (hk : k < 0)
    (δ : Derivation ℂ (MilnorAlgebra f) (MilnorAlgebra f))
    (hδ : IsDerivationOfDegree w f k δ) : δ = 0 :=
  yau_conjecture_of_critical_of_le_three hn w d f hw hf hcrit k hk δ hδ

/-- The main theorem for Brieskorn–Pham polynomials with nonzero coefficients and exponents at least three, without the stratum hypothesis. -/
theorem yau_conjecture_brieskorn_pham {n : ℕ} {w : Fin n → ℕ} {d : ℕ} (c : Fin n → ℂ) (a : Fin n → ℕ)
    (hc : ∀ i, c i ≠ 0) (ha : ∀ i, 3 ≤ a i) (hw : ∀ i, 0 < w i) (hwd : ∀ i, a i * w i = d)
    (k : ℤ) (hk : k < 0)
    (δ : Derivation ℂ (MilnorAlgebra (brieskornPham c a)) (MilnorAlgebra (brieskornPham c a)))
    (hδ : IsDerivationOfDegree w (brieskornPham c a) k δ) : δ = 0 :=
  yau_conjecture_brieskornPham c a hc ha hw hwd k hk δ hδ

/-- The main theorem assuming the stratum statement only for at least two variables; its zero- and one-variable cases are proved directly. -/
theorem yau_conjecture_of_varchenko_two_le (hV : ∀ m, 2 ≤ m → VarchenkoTheoremFor m) {n : ℕ}
    (w : Fin n → ℕ) (d : ℕ) (f : Poly n) (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hcrit : HasIsolatedCriticalPoint f) (k : ℤ) (hk : k < 0)
    (δ : Derivation ℂ (MilnorAlgebra f) (MilnorAlgebra f))
    (hδ : IsDerivationOfDegree w f k δ) : δ = 0 :=
  yau_conjecture_of_varchenko (varchenkoTheorem_iff_two_le.2 hV) w d f hw hf hcrit k hk δ hδ

end Yau
