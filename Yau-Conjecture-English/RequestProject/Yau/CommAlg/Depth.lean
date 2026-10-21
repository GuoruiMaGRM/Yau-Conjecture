module

public import Mathlib

/-!
# Regular sequences over Noetherian local rings

Elementary depth theory for finite modules, culminating in the Cohen–Macaulay
criterion used here: an appropriate system of parameters is a regular sequence.
-/

@[expose] public section

open IsLocalRing RingTheory.Sequence Pointwise

namespace Yau.Depth

universe u v

variable {R : Type u} [CommRing R]

section Socle

variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The quotient `M/xM` has a nonzero element annihilated by the ideal `𝔞`, expressed in `M`. -/
def HasSocle (𝔞 : Ideal R) (x : R) : Prop :=
  ∃ u : M, u ∉ x • (⊤ : Submodule R M) ∧ ∀ a ∈ 𝔞, a • u ∈ x • (⊤ : Submodule R M)

lemma mem_smul_top_iff (x : R) (u : M) : u ∈ x • (⊤ : Submodule R M) ↔ ∃ v : M, x • v = u := by
  rw [Submodule.mem_smul_pointwise_iff_exists]; simp

/-- An interchange lemma: for regular elements `x,y`, with `y ∈ 𝔞`, a socle element of `M/xM` gives one of `M/yM`. -/
lemma hasSocle_swap {𝔞 : Ideal R} {x y : R} (hx : IsSMulRegular M x) (hy : IsSMulRegular M y)
    (hy𝔞 : y ∈ 𝔞) (h : HasSocle (M := M) 𝔞 x) : HasSocle (M := M) 𝔞 y := by
  obtain ⟨u, hu, hau⟩ := h
  obtain ⟨v, hv⟩ := (mem_smul_top_iff x _).1 (hau y hy𝔞)
  refine ⟨v, fun hvy => hu ?_, fun a ha => ?_⟩
  · obtain ⟨w, rfl⟩ := (mem_smul_top_iff y _).1 hvy
    rw [mem_smul_top_iff]
    refine ⟨w, hy ?_⟩
    simp only
    rw [← hv, smul_comm y x w]
  · obtain ⟨u', hu'⟩ := (mem_smul_top_iff x _).1 (hau a ha)
    rw [mem_smul_top_iff]
    refine ⟨u', hx ?_⟩
    simp only
    rw [smul_comm x y u', hu', smul_comm x a v, hv, smul_comm]

end Socle

section Local

variable [IsLocalRing R] [IsNoetherianRing R]

/-- The module `N` has no nonzero element annihilated by the maximal ideal. -/
def NoSocle (N : Type v) [AddCommGroup N] [Module R N] : Prop :=
  ∀ u : N, (∀ a ∈ maximalIdeal R, a • u = 0) → u = 0

variable {M : Type v} [AddCommGroup M] [Module R M]

omit [IsNoetherianRing R] in
lemma noSocle_quot_iff (x : R) :
    NoSocle (R := R) (QuotSMulTop x M) ↔ ¬ HasSocle (M := M) (maximalIdeal R) x := by
  constructor
  · rintro h ⟨u, hu, hau⟩
    refine hu ((Submodule.Quotient.mk_eq_zero _).1 (h _ fun a ha => ?_))
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hau a ha
  · intro h u hu
    induction u using Submodule.Quotient.induction_on with
    | _ u =>
    by_contra hne
    refine h ⟨u, fun hm => hne ((Submodule.Quotient.mk_eq_zero _).2 hm), fun a ha => ?_⟩
    have := hu a ha
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this

omit [IsNoetherianRing R] in
/-- An associated prime of a module with zero socle is not maximal. -/
lemma not_le_of_mem_associatedPrimes {N : Type v} [AddCommGroup N] [Module R N]
    (hN : NoSocle (R := R) N) {p : Ideal R} (hp : p ∈ associatedPrimes R N) :
    ¬ maximalIdeal R ≤ p := by
  intro hle
  obtain ⟨hpr, u, rfl⟩ := hp
  have hu : u = 0 := hN u fun a ha => by
    have := hle ha
    rw [Submodule.mem_colon_singleton] at this
    simpa using this
  subst hu
  apply hpr.ne_top
  rw [eq_top_iff]
  intro a _
  rw [Submodule.mem_colon_singleton]
  simp

/-- Prime avoidance gives a common regular element in the maximal ideal for two finite modules with zero socle. -/
lemma exists_regular_two {N₁ : Type v} [AddCommGroup N₁] [Module R N₁] [Module.Finite R N₁]
    {N₂ : Type v} [AddCommGroup N₂] [Module R N₂] [Module.Finite R N₂]
    (h₁ : NoSocle (R := R) N₁) (h₂ : NoSocle (R := R) N₂) :
    ∃ z ∈ maximalIdeal R, IsSMulRegular N₁ z ∧ IsSMulRegular N₂ z := by
  have fin : (associatedPrimes R N₁ ∪ associatedPrimes R N₂).Finite :=
    (associatedPrimes.finite R N₁).union (associatedPrimes.finite R N₂)
  have hnot : ¬ ((maximalIdeal R : Set R) ⊆
      ⋃ i ∈ associatedPrimes R N₁ ∪ associatedPrimes R N₂, id i) := by
    intro hsub
    obtain ⟨p, hp, hle⟩ := ((maximalIdeal R).subset_union_prime_finite fin (f := id) 0 0
      fun _ h _ _ => h.elim (fun h => h.isPrime) (fun h => h.isPrime)).1 hsub
    rcases hp with hp | hp
    · exact not_le_of_mem_associatedPrimes h₁ hp hle
    · exact not_le_of_mem_associatedPrimes h₂ hp hle
  rw [Set.not_subset] at hnot
  obtain ⟨z, hz, hzU⟩ := hnot
  refine ⟨z, hz, ?_, ?_⟩
  · by_contra hr
    have : z ∈ ⋃ p ∈ associatedPrimes R N₁, p := by
      rw [biUnion_associatedPrimes_eq_compl_regular R N₁]; exact hr
    simp only [Set.mem_iUnion] at this
    obtain ⟨p, hp, hzp⟩ := this
    exact hzU (Set.mem_biUnion (Or.inl hp) hzp)
  · by_contra hr
    have : z ∈ ⋃ p ∈ associatedPrimes R N₂, p := by
      rw [biUnion_associatedPrimes_eq_compl_regular R N₂]; exact hr
    simp only [Set.mem_iUnion] at this
    obtain ⟨p, hp, hzp⟩ := this
    exact hzU (Set.mem_biUnion (Or.inr hp) hzp)

omit [IsNoetherianRing R] in
/-- A module with a regular element in the maximal ideal has zero socle. -/
lemma noSocle_of_regular {N : Type v} [AddCommGroup N] [Module R N] {r : R}
    (hr : r ∈ maximalIdeal R) (hreg : IsSMulRegular N r) : NoSocle (R := R) N :=
  fun u hu => hreg (by show r • u = r • 0; rw [hu r hr, smul_zero])

lemma isWeaklyRegular_perm {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N]
    {rs rs' : List R} (h1 : IsWeaklyRegular N rs) (h2 : List.Perm rs rs')
    (h3 : ∀ r ∈ rs, r ∈ maximalIdeal R) : IsWeaklyRegular N rs' :=
  IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal h1 h2 h3

/-- Depth drops by one on quotienting by a regular element: a regular `x` extends to a regular sequence of the same maximal available length. -/
theorem depth_descent (k : ℕ) : ∀ (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (x : R), x ∈ maximalIdeal R → IsSMulRegular M x →
    ∀ (y : R) (ys : List R), ys.length = k → y ∈ maximalIdeal R →
    (∀ r ∈ ys, r ∈ maximalIdeal R) → IsWeaklyRegular M (y :: ys) →
    ∃ zs : List R, zs.length = k ∧ (∀ r ∈ zs, r ∈ maximalIdeal R) ∧
      IsWeaklyRegular M (x :: zs) := by
  induction k with
  | zero =>
    intro M _ _ _ x _ hxreg _ _ _ _ _ _
    exact ⟨[], rfl, by simp, (isWeaklyRegular_cons_iff M x []).2 ⟨hxreg, .nil R _⟩⟩
  | succ k ih =>
    intro M _ _ _ x hx hxreg y ys hlen hy hys hreg
    obtain ⟨y', ys', rfl⟩ : ∃ y' ys', ys = y' :: ys' := by
      cases ys with
      | nil => simp at hlen
      | cons a l => exact ⟨a, l, rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    have hy' : y' ∈ maximalIdeal R := hys y' List.mem_cons_self
    have hys' : ∀ r ∈ ys', r ∈ maximalIdeal R := fun r hr => hys r (List.mem_cons_of_mem _ hr)
    obtain ⟨hyreg, hreg'⟩ := (isWeaklyRegular_cons_iff M y _).1 hreg
    have hy'reg := ((isWeaklyRegular_cons_iff _ y' ys').1 hreg').1
    have hNy : NoSocle (R := R) (QuotSMulTop y M) := noSocle_of_regular hy' hy'reg
    have hNx : NoSocle (R := R) (QuotSMulTop x M) := by
      rw [noSocle_quot_iff] at hNy ⊢
      exact fun h => hNy (hasSocle_swap hxreg hyreg hy h)
    obtain ⟨z, hz, hzx, hzy⟩ := exists_regular_two hNx hNy
    obtain ⟨zs, hzslen, hzs, hzsreg⟩ :=
      ih (QuotSMulTop y M) z hz hzy y' ys' hlen hy' hys' hreg'
    have h1 : IsWeaklyRegular M (y :: z :: zs) :=
      (isWeaklyRegular_cons_iff M y _).2 ⟨hyreg, hzsreg⟩
    have hall : ∀ r ∈ y :: z :: zs, r ∈ maximalIdeal R := by
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | rfl | hr
      · exact hy
      · exact hz
      · exact hzs r hr
    have h2 : IsWeaklyRegular M (z :: y :: zs) :=
      isWeaklyRegular_perm h1 (List.Perm.swap z y zs) hall
    obtain ⟨hzreg, h2'⟩ := (isWeaklyRegular_cons_iff M z _).1 h2
    have h3 : IsWeaklyRegular M [x, z] :=
      (isWeaklyRegular_cons_iff M x _).2
        ⟨hxreg, (isWeaklyRegular_cons_iff _ z []).2 ⟨hzx, .nil R _⟩⟩
    have h4 : IsWeaklyRegular M [z, x] :=
      isWeaklyRegular_perm h3 (List.Perm.swap z x [])
        (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl <;> assumption)
    have hxz : IsSMulRegular (QuotSMulTop z M) x :=
      ((isWeaklyRegular_cons_iff _ x []).1 ((isWeaklyRegular_cons_iff M z _).1 h4).2).1
    obtain ⟨ws, hwslen, hws, hwsreg⟩ :=
      ih (QuotSMulTop z M) x hx hxz y zs hzslen hy hzs h2'
    have h5 : IsWeaklyRegular M (z :: x :: ws) :=
      (isWeaklyRegular_cons_iff M z _).2 ⟨hzreg, hwsreg⟩
    have hall' : ∀ r ∈ z :: x :: ws, r ∈ maximalIdeal R := by
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | rfl | hr
      · exact hz
      · exact hx
      · exact hws r hr
    refine ⟨z :: ws, by simp [hwslen], ?_, isWeaklyRegular_perm h5 (List.Perm.swap x z ws) hall'⟩
    intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact hz
    · exact hws r hr

/-- An associated prime of `M` is contained in an associated prime of `M/xM` containing `x`. -/
lemma exists_associatedPrime_quot {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {p : Ideal R} (hp : p ∈ associatedPrimes R M) {x : R} (hx : x ∈ maximalIdeal R)
    (hxreg : IsSMulRegular M x) :
    ∃ q ∈ associatedPrimes R (QuotSMulTop x M), p ≤ q ∧ x ∈ q := by
  obtain ⟨hpr, u0, hu0⟩ := hp
  set N : Submodule R M := Submodule.torsionBySet R M (p : Set R) with hNdef
  have hmemN : ∀ u : M, u ∈ N ↔ ∀ a ∈ p, a • u = 0 := by
    intro u
    rw [hNdef, Submodule.mem_torsionBySet_iff]
    exact ⟨fun h a ha => h ⟨a, ha⟩, fun h a => h a a.2⟩
  have hu0N : u0 ∈ N := by
    rw [hmemN]
    intro a ha
    rw [hu0, Submodule.mem_colon_singleton] at ha
    simpa using ha
  have hu0ne : u0 ≠ 0 := by
    rintro rfl
    apply hpr.ne_top
    rw [hu0, eq_top_iff]
    intro a _
    rw [Submodule.mem_colon_singleton]
    simp
  have hex : ∃ u ∈ N, u ∉ x • (⊤ : Submodule R M) := by
    by_contra! hcon
    have hle : N ≤ Ideal.span {x} • N := by
      rw [Submodule.ideal_span_singleton_smul]
      intro u hu
      obtain ⟨v, rfl⟩ := (mem_smul_top_iff x u).1 (hcon u hu)
      have hv : v ∈ N := by
        rw [hmemN] at hu ⊢
        intro a ha
        apply hxreg
        simp only
        rw [smul_zero, smul_comm, hu a ha]
      exact Submodule.smul_mem_pointwise_smul v x N hv
    have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) N
      (IsNoetherian.noetherian N) hle
      (le_trans (by rw [Ideal.span_le]; simpa using hx) (IsLocalRing.maximalIdeal_le_jacobson _))
    exact hu0ne (by simpa [hbot] using hu0N)
  obtain ⟨u, huN, hux⟩ := hex
  have hne : (Submodule.Quotient.mk u : QuotSMulTop x M) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero]; exact hux
  obtain ⟨q, hq, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R _ hne
  refine ⟨q, hq, fun a ha => hle ?_, hle ?_⟩
  · rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
      (hmemN u).1 huN a ha, Submodule.Quotient.mk_zero]
  · rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul u x ⊤ Submodule.mem_top

end Local

section Dim

/-- A strict inclusion of prime ideals lowers the dimension of the quotient. -/
lemma ringKrullDim_quotient_succ_le {p q : Ideal R} [hp : p.IsPrime] (hpq : p ≤ q) {x : R}
    (hxq : x ∈ q) (hxp : x ∉ p) :
    ringKrullDim (R ⧸ q) + 1 ≤ ringKrullDim (R ⧸ p) := by
  have hr : Ideal.Quotient.mk p x ∈ nonZeroDivisors (R ⧸ p) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)
  gcongr
  have hle : Ideal.span {Ideal.Quotient.mk p x} ≤ q.map (Ideal.Quotient.mk p) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ hxq
  refine ringKrullDim_le_of_surjective
    ((DoubleQuot.quotQuotEquivQuotOfLE hpq).toRingHom.comp (Ideal.Quotient.factor hle)) ?_
  exact (DoubleQuot.quotQuotEquivQuotOfLE hpq).surjective.comp (Ideal.Quotient.factor_surjective hle)

end Dim

section Local2

variable [IsLocalRing R] [IsNoetherianRing R]

/-- The length of an `M`-regular sequence in the maximal ideal is at most `dim R/p` for an associated prime `p` of `M`. -/
theorem length_le_ringKrullDim (rs : List R) : ∀ (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (p : Ideal R), p ∈ associatedPrimes R M →
    (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular M rs →
    (rs.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  induction rs with
  | nil =>
    intro M _ _ _ p hp _ _
    have := hp.isPrime
    simpa using ringKrullDim_nonneg_of_nontrivial (R := R ⧸ p)
  | cons x rs ih =>
    intro M _ _ _ p hp hrs hreg
    have hx : x ∈ maximalIdeal R := hrs x List.mem_cons_self
    obtain ⟨hxreg, hreg'⟩ := (isWeaklyRegular_cons_iff M x rs).1 hreg
    obtain ⟨q, hq, hpq, hxq⟩ := exists_associatedPrime_quot hp hx hxreg
    have hxp : x ∉ p := by
      intro hxp
      have hp' := hp
      obtain ⟨_, u, rfl⟩ := hp'
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hxp
      have hu : u = 0 := hxreg (by simpa using hxp)
      subst hu
      exact hp.isPrime.ne_top (by rw [eq_top_iff]; intro a _; simp [Submodule.mem_colon_singleton])
    have := hp.isPrime
    have h1 := ih (QuotSMulTop x M) q hq (fun r hr => hrs r (List.mem_cons_of_mem _ hr)) hreg'
    have h2 := ringKrullDim_quotient_succ_le hpq hxq hxp
    calc ((x :: rs).length : WithBot ℕ∞) = (rs.length : WithBot ℕ∞) + 1 := by
          simp
      _ ≤ ringKrullDim (R ⧸ q) + 1 := by gcongr
      _ ≤ ringKrullDim (R ⧸ p) := h2

/-- The form of Krull's height theorem used below: if every prime containing `p` and `ys` is maximal, then `dim R/p ≤ length ys`. -/
lemma ringKrullDim_quotient_le_length (p : Ideal R) [p.IsPrime] (ys : List R)
    (hys : ∀ r ∈ ys, r ∈ maximalIdeal R)
    (hmax : ∀ P : Ideal R, P.IsPrime → p ≤ P → (∀ r ∈ ys, r ∈ P) → P.IsMaximal) :
    ringKrullDim (R ⧸ p) ≤ ys.length := by
  classical
  set s : Finset (R ⧸ p) := (ys.map (Ideal.Quotient.mk p)).toFinset with hsdef
  have hs : (s : Set (R ⧸ p)) ⊆ Ring.jacobson (R ⧸ p) := by
    intro a ha
    rw [hsdef, Finset.mem_coe, List.mem_toFinset, List.mem_map] at ha
    obtain ⟨r, hr, rfl⟩ := ha
    rw [← Ideal.jacobson_bot, Ideal.jacobson, SetLike.mem_coe, Ideal.mem_sInf]
    rintro J ⟨-, hJ⟩
    have hc : (J.comap (Ideal.Quotient.mk p)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    have := IsLocalRing.eq_maximalIdeal hc
    have hr' : r ∈ J.comap (Ideal.Quotient.mk p) := by rw [this]; exact hys r hr
    exact hr'
  have h1 := ringKrullDim_le_ringKrullDim_quotient_add_card s hs
  have h2 : ringKrullDim ((R ⧸ p) ⧸ Ideal.span (s : Set (R ⧸ p))) ≤ 0 := by
    have : Ring.KrullDimLE 0 ((R ⧸ p) ⧸ Ideal.span (s : Set (R ⧸ p))) := by
      rw [Ring.krullDimLE_zero_iff]
      intro Q hQ
      set g : R →+* (R ⧸ p) ⧸ Ideal.span (s : Set (R ⧸ p)) :=
        (Ideal.Quotient.mk _).comp (Ideal.Quotient.mk p) with hg
      have hgs : Function.Surjective g :=
        Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
      have hP : (Q.comap g).IsMaximal := by
        refine hmax _ (Ideal.comap_isPrime g Q) ?_ ?_
        · intro a ha
          rw [Ideal.mem_comap, hg, RingHom.comp_apply,
            Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
          exact Q.zero_mem
        · intro r hr
          rw [Ideal.mem_comap, hg, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2]
          · exact Q.zero_mem
          · apply Ideal.subset_span
            rw [hsdef, Finset.mem_coe, List.mem_toFinset]
            exact List.mem_map_of_mem hr
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective g hgs hP with h | h
      · rw [Ideal.map_comap_of_surjective g hgs] at h
        exact absurd h hQ.ne_top
      · rwa [Ideal.map_comap_of_surjective g hgs] at h
    have h := Ring.krullDimLE_iff.1 this
    simpa using h
  have hcard : s.card ≤ ys.length := by
    rw [hsdef]
    exact (List.toFinset_card_le _).trans (by simp)
  calc ringKrullDim (R ⧸ p) ≤ _ := h1
    _ ≤ 0 + (s.card : WithBot ℕ∞) := by gcongr
    _ ≤ ys.length := by
      rw [zero_add]; exact_mod_cast hcard

omit [IsLocalRing R] [IsNoetherianRing R] in
lemma le_annihilator_quotSMulTop {M : Type v} [AddCommGroup M] [Module R M] {I : Ideal R}
    (hI : I ≤ Module.annihilator R M) (y : R) :
    I ⊔ Ideal.span {y} ≤ Module.annihilator R (QuotSMulTop y M) := by
  refine sup_le ?_ ?_
  · intro a ha
    rw [Module.mem_annihilator]
    intro u
    induction u using Submodule.Quotient.induction_on with
    | _ u =>
    rw [← Submodule.Quotient.mk_smul, Module.mem_annihilator.1 (hI ha) u,
      Submodule.Quotient.mk_zero]
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Module.mem_annihilator]
    intro u
    induction u using Submodule.Quotient.induction_on with
    | _ u =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul u y ⊤ Submodule.mem_top

/-- Cohen–Macaulay criterion: given a regular sequence of length `n` on `M`, a list `ys` of at most `n` elements in the maximal ideal is regular if every prime containing `ys` and an annihilating ideal of `M` is maximal. -/
theorem isWeaklyRegular_of_primes_isMaximal (ys : List R) :
    ∀ (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] (I : Ideal R) (n : ℕ),
    I ≤ Module.annihilator R M →
    (∃ xs : List R, xs.length = n ∧ (∀ r ∈ xs, r ∈ maximalIdeal R) ∧ IsWeaklyRegular M xs) →
    ys.length ≤ n → (∀ r ∈ ys, r ∈ maximalIdeal R) →
    (∀ P : Ideal R, P.IsPrime → I ≤ P → (∀ r ∈ ys, r ∈ P) → P.IsMaximal) →
    IsWeaklyRegular M ys := by
  induction ys with
  | nil => intro M _ _ _ _ _ _ _ _ _ _; exact .nil R M
  | cons y ys ih =>
    intro M _ _ _ I n hI hdepth hlen hys hmax
    obtain ⟨xs, hxslen, hxs, hxsreg⟩ := hdepth
    have hy : y ∈ maximalIdeal R := hys y List.mem_cons_self
    have hys' : ∀ r ∈ ys, r ∈ maximalIdeal R := fun r hr => hys r (List.mem_cons_of_mem _ hr)
    -- Step 1: `y` is `M`-regular.
    have hyreg : IsSMulRegular M y := by
      by_contra hnreg
      have : y ∈ ⋃ p ∈ associatedPrimes R M, p := by
        rw [biUnion_associatedPrimes_eq_compl_regular R M]; exact hnreg
      simp only [Set.mem_iUnion] at this
      obtain ⟨p, hp, hyp⟩ := this
      have := hp.isPrime
      have hIp : I ≤ p := by
        intro a ha
        obtain ⟨_, u, rfl⟩ := hp
        rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
        exact Module.mem_annihilator.1 (hI ha) u
      have h1 := length_le_ringKrullDim xs M p hp hxs hxsreg
      have h2 := ringKrullDim_quotient_le_length p ys hys' fun P hP hpP hysP =>
        hmax P hP (hIp.trans hpP) (by
          intro r hr
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact hpP hyp
          · exact hysP r hr)
      have h3 : (n : WithBot ℕ∞) ≤ ys.length := hxslen ▸ h1.trans h2
      have h4 : n ≤ ys.length := by exact_mod_cast h3
      simp only [List.length_cons] at hlen
      omega
    -- Step 2: pass to `M/yM`.
    refine (isWeaklyRegular_cons_iff M y ys).2 ⟨hyreg, ?_⟩
    obtain ⟨x, xs', rfl⟩ : ∃ x xs', xs = x :: xs' := by
      cases xs with
      | nil => simp only [List.length_nil] at hxslen; simp at hlen; omega
      | cons a l => exact ⟨a, l, rfl⟩
    obtain ⟨zs, hzslen, hzs, hzsreg⟩ := depth_descent xs'.length M y hy hyreg x xs' rfl
      (hxs x List.mem_cons_self) (fun r hr => hxs r (List.mem_cons_of_mem _ hr)) hxsreg
    have hzsreg' := ((isWeaklyRegular_cons_iff M y zs).1 hzsreg).2
    refine ih (QuotSMulTop y M) (I ⊔ Ideal.span {y}) xs'.length
      (le_annihilator_quotSMulTop hI y) ⟨zs, hzslen, hzs, hzsreg'⟩ ?_ hys' ?_
    · simp only [List.length_cons] at hlen hxslen; omega
    · intro P hP hIP hysP
      refine hmax P hP (le_sup_left.trans hIP) ?_
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact hIP (le_sup_right (a := I) (Ideal.mem_span_singleton_self r))
      · exact hysP r hr

end Local2

end Yau.Depth
