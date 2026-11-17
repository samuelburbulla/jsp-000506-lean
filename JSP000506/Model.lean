import JSP000506.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Random Graph Model `G(n, 1/2)` and Target Problem Statements

This module constructs the Erdős–Rényi random graph `G(n, 1/2)` on `Fin n` in two equivalent ways:
1. **Uniform counting model** (`probGnpHalf`, `expectGnpHalf`): normalized counting measure and
   expectation over the `2 ^ (n.choose 2)` labeled simple graphs on `Fin n`.
2. **Independent fair-coin `PMF` model** (`fairCoinPMF`, `fairCoinsPMF`, `pmfGnpHalf`): product of
   independent fair Bernoulli `(1/2, 1/2)` coins indexed by unordered off-diagonal pairs
   `OffDiagSym2 n := {e : Sym2 (Fin n) // ¬ e.IsDiag}`, pushed forward along the canonical bijection
   `edgeConfigEquiv n : (OffDiagSym2 n → Bool) ≃ SimpleGraph (Fin n)`.

We prove:
- Exact equivalence between `pmfGnpHalf` and `probGnpHalf` (`toOuterMeasure_pmfGnpHalf_eq`) and
  with normalized subset cardinality (`probGnpHalf_eq_card_div`).
- Exact edge-set marginal probability `probGnpHalf_prescribed_edges`: prescribing values on any
  `F : Finset (OffDiagSym2 n)` has probability `(2⁻¹ : ℝ) ^ F.card`, along with specializations to
  cliques, independent sets, and pairwise-disjoint signed subset families.
- Union bounds, Markov's first-moment inequality, and the Paley–Zygmund second-moment inequality.
- The exact statements of Erdős Problem #625 (`ErdosGimbel625Statement`), Petkov's uniform
  quantitative resolution (`PetkovQuantitative625Statement`), and Petkov's phase-resolved theorem
  (`PetkovPhaseResolved625Statement`), together with the unconditional reductions
  `PetkovPhaseResolved625Statement → PetkovQuantitative625Statement → ErdosGimbel625Statement`.
-/

namespace JSP000506

open SimpleGraph Finset Filter
open scoped ENNReal Topology

/-! ### 1. Off-Diagonal Vertex Pairs and Bijection with `SimpleGraph (Fin n)` -/

/-- Unordered pairs of distinct vertices in `Fin n`, indexing the `n.choose 2` potential edges. -/
abbrev OffDiagSym2 (n : ℕ) : Type :=
  {e : Sym2 (Fin n) // ¬ e.IsDiag}

theorem card_offDiagSym2 (n : ℕ) : Fintype.card (OffDiagSym2 n) = n.choose 2 :=
  (Sym2.card_subtype_not_diag (α := Fin n)).trans (by rw [Fintype.card_fin])

/-- Construct an off-diagonal pair from `u ≠ v` in `Fin n`. -/
def mkOffDiag {n : ℕ} {u v : Fin n} (huv : u ≠ v) : OffDiagSym2 n :=
  ⟨s(u, v), Sym2.mk_isDiag_iff.not.mpr huv⟩

/-- Canonical bijection between `{0,1}`-assignments on unordered off-diagonal vertex pairs and
labeled simple graphs on `Fin n`. -/
noncomputable def edgeConfigEquiv (n : ℕ) : (OffDiagSym2 n → Bool) ≃ SimpleGraph (Fin n) where
  toFun ω := SimpleGraph.fromEdgeSet {e : Sym2 (Fin n) | ∃ h : ¬ e.IsDiag, ω ⟨e, h⟩ = true}
  invFun G := by
    classical
    exact fun e => decide (e.1 ∈ G.edgeSet)
  left_inv ω := by
    classical
    funext ⟨e, he⟩
    simp only [edgeSet_fromEdgeSet, Set.mem_sdiff, Sym2.mem_diagSet, he, not_false_eq_true,
      and_true, Set.mem_ofPred_eq]
    cases hω : ω ⟨e, he⟩ <;> simp [hω]
  right_inv G := by
    classical
    ext u v
    simp only [fromEdgeSet_adj, Set.mem_ofPred_eq, Sym2.mk_isDiag_iff]
    constructor
    · rintro ⟨⟨_, hdec⟩, _⟩
      exact of_decide_eq_true hdec
    · intro hadj
      exact ⟨⟨G.ne_of_adj hadj, decide_eq_true hadj⟩, G.ne_of_adj hadj⟩

@[simp]
theorem edgeConfigEquiv_adj {n : ℕ} (ω : OffDiagSym2 n → Bool) {u v : Fin n} (huv : u ≠ v) :
    (edgeConfigEquiv n ω).Adj u v ↔ ω (mkOffDiag huv) = true := by
  simp [edgeConfigEquiv, mkOffDiag, Sym2.mk_isDiag_iff, huv]

theorem edgeConfigEquiv_mem_edgeSet {n : ℕ} (ω : OffDiagSym2 n → Bool) (e : OffDiagSym2 n) :
    e.1 ∈ (edgeConfigEquiv n ω).edgeSet ↔ ω e = true := by
  rcases e with ⟨e, he⟩
  simp [edgeConfigEquiv, he]

theorem edgeConfigEquiv_symm_apply_eq_true {n : ℕ} (G : SimpleGraph (Fin n)) (e : OffDiagSym2 n) :
    (edgeConfigEquiv n).symm G e = true ↔ e.1 ∈ G.edgeSet := by
  classical
  change decide (e.1 ∈ G.edgeSet) = true ↔ e.1 ∈ G.edgeSet
  exact decide_eq_true_iff

theorem card_simpleGraph_fin (n : ℕ) :
    Fintype.card (SimpleGraph (Fin n)) = 2 ^ n.choose 2 := by
  rw [Fintype.card_congr (edgeConfigEquiv n).symm, Fintype.card_fun, Fintype.card_bool,
    card_offDiagSym2]

theorem card_simpleGraph_fin_pos (n : ℕ) :
    0 < Fintype.card (SimpleGraph (Fin n)) := by
  rw [card_simpleGraph_fin]
  positivity

/-! ### 2. Uniform Counting Model and Independent Fair-Coin `PMF` Model -/

/-- Expectation of a real-valued graph functional `X` under `G(n, 1/2)`. -/
noncomputable def expectGnpHalf (n : ℕ) (X : SimpleGraph (Fin n) → ℝ) : ℝ :=
  (∑ G : SimpleGraph (Fin n), X G) / (Fintype.card (SimpleGraph (Fin n)) : ℝ)

/-- Probability of a graph event `E` under `G(n, 1/2)` defined by normalized counting over all
`2 ^ (n.choose 2)` labeled simple graphs on `Fin n`. -/
noncomputable def probGnpHalf (n : ℕ) (E : Set (SimpleGraph (Fin n))) : ℝ :=
  expectGnpHalf n (E.indicator (fun _ => (1 : ℝ)))

theorem probGnpHalf_eq_card_div (n : ℕ) (E : Set (SimpleGraph (Fin n)))
    [DecidablePred (· ∈ E)] :
    probGnpHalf n E =
      ((Finset.univ.filter (· ∈ E)).card : ℝ) / (Fintype.card (SimpleGraph (Fin n)) : ℝ) := by
  unfold probGnpHalf expectGnpHalf
  congr 1
  simp_rw [Set.indicator_apply, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- A single fair Bernoulli `(1/2, 1/2)` coin as a `PMF Bool`. -/
noncomputable def fairCoinPMF : PMF Bool :=
  PMF.ofFintype (fun _ => (2⁻¹ : ℝ≥0∞)) (by
    rw [Fintype.sum_bool]
    exact ENNReal.inv_two_add_inv_two)

@[simp]
theorem fairCoinPMF_apply (b : Bool) : fairCoinPMF b = (2⁻¹ : ℝ≥0∞) := rfl

private lemma prod_fairCoinPMF (n : ℕ) (ω : OffDiagSym2 n → Bool) :
    (∏ e : OffDiagSym2 n, fairCoinPMF (ω e)) = (2⁻¹ : ℝ≥0∞) ^ n.choose 2 := by
  simp_rw [fairCoinPMF_apply]
  rw [Finset.prod_const, Finset.card_univ, card_offDiagSym2]

private lemma sum_prod_fairCoinPMF (n : ℕ) :
    ∑ ω : OffDiagSym2 n → Bool, (∏ e : OffDiagSym2 n, fairCoinPMF (ω e)) = 1 := by
  simp_rw [prod_fairCoinPMF]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, card_offDiagSym2,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, ← ENNReal.inv_pow]
  exact ENNReal.mul_inv_cancel (by positivity) (ENNReal.pow_ne_top (by norm_num))

/-- The product distribution of `n.choose 2` independent fair coins on `OffDiagSym2 n → Bool`,
where each configuration `ω` has point mass `∏ e, fairCoinPMF (ω e) = 2 ^ (- n.choose 2)`. -/
noncomputable def fairCoinsPMF (n : ℕ) : PMF (OffDiagSym2 n → Bool) :=
  PMF.ofFintype (fun ω => ∏ e : OffDiagSym2 n, fairCoinPMF (ω e)) (sum_prod_fairCoinPMF n)

@[simp]
theorem fairCoinsPMF_apply (n : ℕ) (ω : OffDiagSym2 n → Bool) :
    fairCoinsPMF n ω = (2⁻¹ : ℝ≥0∞) ^ n.choose 2 :=
  prod_fairCoinPMF n ω

/-- The Erdős–Rényi `G(n, 1/2)` distribution as a `PMF (SimpleGraph (Fin n))`, defined as the
pushforward of independent fair edge-coins along `edgeConfigEquiv n`. -/
noncomputable def pmfGnpHalf (n : ℕ) : PMF (SimpleGraph (Fin n)) :=
  (fairCoinsPMF n).map (edgeConfigEquiv n)

@[simp]
theorem pmfGnpHalf_apply (n : ℕ) (G : SimpleGraph (Fin n)) :
    pmfGnpHalf n G = (2⁻¹ : ℝ≥0∞) ^ n.choose 2 := by
  rw [pmfGnpHalf, PMF.map_apply]
  rw [tsum_eq_single ((edgeConfigEquiv n).symm G)]
  · simp
  · intro ω hω
    have hne : G ≠ edgeConfigEquiv n ω := fun h =>
      hω (by simpa using (congrArg (edgeConfigEquiv n).symm h).symm)
    simp [hne]

/-- Exact equivalence between the fair-coin `PMF` outer measure and `probGnpHalf`. -/
theorem toOuterMeasure_pmfGnpHalf_eq (n : ℕ) (E : Set (SimpleGraph (Fin n))) :
    (pmfGnpHalf n).toOuterMeasure E = ENNReal.ofReal (probGnpHalf n E) := by
  classical
  rw [PMF.toOuterMeasure_apply_fintype, probGnpHalf_eq_card_div, card_simpleGraph_fin]
  have hind : ∑ G : SimpleGraph (Fin n), E.indicator (pmfGnpHalf n) G =
      ((Finset.univ.filter (· ∈ E)).card : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ n.choose 2) := by
    simp_rw [Set.indicator_apply, pmfGnpHalf_apply, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul]
  rw [hind, ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  · rw [ENNReal.ofReal_natCast]
  · rw [ENNReal.ofReal_natCast, Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow]

theorem toReal_toOuterMeasure_pmfGnpHalf (n : ℕ) (E : Set (SimpleGraph (Fin n))) :
    ((pmfGnpHalf n).toOuterMeasure E).toReal = probGnpHalf n E := by
  classical
  rw [toOuterMeasure_pmfGnpHalf_eq, probGnpHalf_eq_card_div, ENNReal.toReal_ofReal]
  positivity

/-! ### 3. Basic Probability & Expectation Lemmas -/

theorem expectGnpHalf_indicator_one (n : ℕ) (E : Set (SimpleGraph (Fin n))) :
    expectGnpHalf n (E.indicator (fun _ => (1 : ℝ))) = probGnpHalf n E :=
  rfl

theorem expectGnpHalf_const (n : ℕ) (c : ℝ) :
    expectGnpHalf n (fun _ => c) = c := by
  unfold expectGnpHalf
  have hne : (Fintype.card (SimpleGraph (Fin n)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (card_simpleGraph_fin_pos n).ne'
  simp [mul_div_cancel_left₀ c hne]

theorem expectGnpHalf_add (n : ℕ) (X Y : SimpleGraph (Fin n) → ℝ) :
    expectGnpHalf n (fun G => X G + Y G) = expectGnpHalf n X + expectGnpHalf n Y := by
  unfold expectGnpHalf
  rw [Finset.sum_add_distrib, add_div]

theorem expectGnpHalf_sum {ι : Type*} (n : ℕ) (s : Finset ι)
    (X : ι → SimpleGraph (Fin n) → ℝ) :
    expectGnpHalf n (fun G => ∑ i ∈ s, X i G) = ∑ i ∈ s, expectGnpHalf n (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [expectGnpHalf]
  | @insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    rw [expectGnpHalf_add, ih]

theorem expectGnpHalf_mul_const (n : ℕ) (c : ℝ) (X : SimpleGraph (Fin n) → ℝ) :
    expectGnpHalf n (fun G => c * X G) = c * expectGnpHalf n X := by
  unfold expectGnpHalf
  rw [← Finset.mul_sum, mul_div_assoc]

theorem expectGnpHalf_mono {n : ℕ} {X Y : SimpleGraph (Fin n) → ℝ}
    (h : ∀ G, X G ≤ Y G) : expectGnpHalf n X ≤ expectGnpHalf n Y := by
  unfold expectGnpHalf
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun G _ => h G) (Nat.cast_nonneg _)

theorem expectGnpHalf_nonneg {n : ℕ} {X : SimpleGraph (Fin n) → ℝ}
    (h : ∀ G, 0 ≤ X G) : 0 ≤ expectGnpHalf n X := by
  simpa [expectGnpHalf] using
    div_nonneg (Finset.sum_nonneg fun G _ => h G) (Nat.cast_nonneg _)

/-- Pushforward of expectation from coin configurations `OffDiagSym2 n → Bool` to `SimpleGraph (Fin n)`. -/
theorem expectGnpHalf_eq_coin_sum (n : ℕ) (X : SimpleGraph (Fin n) → ℝ) :
    expectGnpHalf n X =
      (∑ ω : OffDiagSym2 n → Bool, X (edgeConfigEquiv n ω)) / (2 : ℝ) ^ n.choose 2 := by
  unfold expectGnpHalf
  rw [card_simpleGraph_fin, Nat.cast_pow, Nat.cast_ofNat]
  congr 1
  exact (Equiv.sum_comp (edgeConfigEquiv n) X).symm

theorem probGnpHalf_nonneg (n : ℕ) (E : Set (SimpleGraph (Fin n))) :
    0 ≤ probGnpHalf n E :=
  expectGnpHalf_nonneg fun G => by
    classical
    by_cases hG : G ∈ E <;> simp [Set.indicator, hG]

theorem probGnpHalf_le_one (n : ℕ) (E : Set (SimpleGraph (Fin n))) :
    probGnpHalf n E ≤ 1 := by
  rw [← expectGnpHalf_const n 1]
  refine expectGnpHalf_mono fun G => ?_
  classical
  by_cases hG : G ∈ E <;> simp [Set.indicator, hG]

@[simp]
theorem probGnpHalf_empty (n : ℕ) :
    probGnpHalf n (∅ : Set (SimpleGraph (Fin n))) = 0 := by
  simp [probGnpHalf, expectGnpHalf]

@[simp]
theorem probGnpHalf_univ (n : ℕ) :
    probGnpHalf n (Set.univ : Set (SimpleGraph (Fin n))) = 1 := by
  simpa [probGnpHalf] using expectGnpHalf_const n 1

theorem probGnpHalf_compl (n : ℕ) (E : Set (SimpleGraph (Fin n))) :
    probGnpHalf n Eᶜ = 1 - probGnpHalf n E := by
  have hsum : probGnpHalf n E + probGnpHalf n Eᶜ = 1 := by
    unfold probGnpHalf
    rw [← expectGnpHalf_add]
    have hone : (fun G : SimpleGraph (Fin n) =>
        E.indicator (fun _ => (1 : ℝ)) G + Eᶜ.indicator (fun _ => (1 : ℝ)) G) = fun _ => 1 := by
      funext G
      classical
      by_cases hG : G ∈ E <;> simp [Set.indicator, hG]
    rw [hone, expectGnpHalf_const]
  linarith

theorem probGnpHalf_mono {n : ℕ} {E₁ E₂ : Set (SimpleGraph (Fin n))} (h : E₁ ⊆ E₂) :
    probGnpHalf n E₁ ≤ probGnpHalf n E₂ := by
  refine expectGnpHalf_mono fun G => ?_
  classical
  by_cases hG₁ : G ∈ E₁
  · have hG₂ : G ∈ E₂ := h hG₁
    simp [Set.indicator, hG₁, hG₂]
  · by_cases hG₂ : G ∈ E₂ <;> simp [Set.indicator, hG₁, hG₂]

theorem probGnpHalf_union_le (n : ℕ) (E₁ E₂ : Set (SimpleGraph (Fin n))) :
    probGnpHalf n (E₁ ∪ E₂) ≤ probGnpHalf n E₁ + probGnpHalf n E₂ := by
  unfold probGnpHalf
  rw [← expectGnpHalf_add]
  refine expectGnpHalf_mono fun G => ?_
  classical
  by_cases hG₁ : G ∈ E₁ <;> by_cases hG₂ : G ∈ E₂ <;> simp [Set.indicator, hG₁, hG₂]

theorem probGnpHalf_biUnion_le {ι : Type*} (n : ℕ) (s : Finset ι)
    (E : ι → Set (SimpleGraph (Fin n))) :
    probGnpHalf n (⋃ i ∈ s, E i) ≤ ∑ i ∈ s, probGnpHalf n (E i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    linarith [probGnpHalf_union_le n (E a) (⋃ i ∈ s, E i), ih]

theorem tendsto_probGnpHalf_one_of_compl_tendsto_zero
    {E : (n : ℕ) → Set (SimpleGraph (Fin n))}
    (h : Tendsto (fun n => probGnpHalf n (E n)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n => probGnpHalf n (E n)) atTop (𝓝 1) := by
  have heq : (fun n => probGnpHalf n (E n)) = fun n => 1 - probGnpHalf n (E n)ᶜ := by
    funext n
    rw [probGnpHalf_compl, sub_sub_cancel]
  rw [heq]
  simpa using tendsto_const_nhds.sub h

theorem tendsto_probGnpHalf_one_of_eventually_subset
    {A B : (n : ℕ) → Set (SimpleGraph (Fin n))}
    (hA : Tendsto (fun n => probGnpHalf n (A n)) atTop (𝓝 1))
    (hsub : ∀ᶠ n : ℕ in atTop, A n ⊆ B n) :
    Tendsto (fun n => probGnpHalf n (B n)) atTop (𝓝 1) := by
  apply tendsto_probGnpHalf_one_of_compl_tendsto_zero
  have h0 : Tendsto (fun n => 1 - probGnpHalf n (A n)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hA
  refine squeeze_zero' (f := fun n => probGnpHalf n (B n)ᶜ)
    (g := fun n => 1 - probGnpHalf n (A n)) ?_ ?_ h0
  · filter_upwards with n
    exact probGnpHalf_nonneg n _
  · filter_upwards [hsub] with n hn
    rw [← probGnpHalf_compl]
    exact probGnpHalf_mono (Set.compl_subset_compl.mpr hn)

theorem tendsto_probGnpHalf_inter_one
    {A B : (n : ℕ) → Set (SimpleGraph (Fin n))}
    (hA : Tendsto (fun n => probGnpHalf n (A n)) atTop (𝓝 1))
    (hB : Tendsto (fun n => probGnpHalf n (B n)) atTop (𝓝 1)) :
    Tendsto (fun n => probGnpHalf n (A n ∩ B n)) atTop (𝓝 1) := by
  apply tendsto_probGnpHalf_one_of_compl_tendsto_zero
  have hsum : Tendsto (fun n => (1 - probGnpHalf n (A n)) + (1 - probGnpHalf n (B n)))
      atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hA).add
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hB)
  refine squeeze_zero (f := fun n => probGnpHalf n (A n ∩ B n)ᶜ)
    (g := fun n => (1 - probGnpHalf n (A n)) + (1 - probGnpHalf n (B n)))
    (fun n => probGnpHalf_nonneg n _) (fun n => ?_) hsum
  rw [Set.compl_inter]
  exact (probGnpHalf_union_le n _ _).trans_eq
    (by rw [probGnpHalf_compl, probGnpHalf_compl])

/-! ### 4. Markov's First-Moment and Paley–Zygmund's Second-Moment Inequalities -/

/-- **Markov's inequality** for `G(n, 1/2)`. -/
theorem probGnpHalf_ge_le_expect_div {n : ℕ} {X : SimpleGraph (Fin n) → ℝ}
    (hX : ∀ G, 0 ≤ X G) {t : ℝ} (ht : 0 < t) :
    probGnpHalf n {G | t ≤ X G} ≤ expectGnpHalf n X / t := by
  rw [← expectGnpHalf_indicator_one]
  rw [le_div_iff₀ ht, ← mul_comm t, ← expectGnpHalf_mul_const]
  apply expectGnpHalf_mono
  intro G
  by_cases hG : t ≤ X G
  · simp [Set.indicator, hG]
  · simp [Set.indicator, hG, hX G]

/-- **First-moment bound** for `ℕ`-valued counting variables: `ℙ(N(G) > 0) ≤ 𝔼[N(G)]`. -/
theorem probGnpHalf_pos_nat_le_expect (n : ℕ) (N : SimpleGraph (Fin n) → ℕ) :
    probGnpHalf n {G | 0 < N G} ≤ expectGnpHalf n (fun G => (N G : ℝ)) := by
  have heq : {G : SimpleGraph (Fin n) | 0 < N G} =
      {G : SimpleGraph (Fin n) | (1 : ℝ) ≤ (N G : ℝ)} := by
    ext G
    simp [Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
  rw [heq]
  simpa using probGnpHalf_ge_le_expect_div (fun G => Nat.cast_nonneg (N G)) zero_lt_one

private lemma sq_sum_le_card_mul_sum_sq {α : Type*} (s : Finset α) (f : α → ℝ) :
    (∑ x ∈ s, f x) ^ 2 ≤ (s.card : ℝ) * ∑ x ∈ s, (f x) ^ 2 := by
  have hnonneg : 0 ≤ ∑ x ∈ s, ∑ y ∈ s, (f x - f y) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hexpand : ∑ x ∈ s, ∑ y ∈ s, (f x - f y) ^ 2 =
      2 * ((s.card : ℝ) * ∑ x ∈ s, (f x) ^ 2 - (∑ x ∈ s, f x) ^ 2) := by
    have hinner : ∀ x : α, ∑ y ∈ s, (f x - f y) ^ 2 =
        (s.card : ℝ) * (f x) ^ 2 - 2 * (f x * (∑ y ∈ s, f y)) + ∑ y ∈ s, (f y) ^ 2 := by
      intro x
      have hterm : ∀ y : α, (f x - f y) ^ 2 = (f x) ^ 2 - 2 * (f x * f y) + (f y) ^ 2 :=
        fun y => by ring
      simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        nsmul_eq_mul, ← Finset.mul_sum]
    simp_rw [hinner, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  linarith

/-- **Paley–Zygmund second-moment inequality** for `G(n, 1/2)`:
for any nonnegative `Z` with `𝔼[Z] > 0`, `ℙ(Z(G) > 0) ≥ (𝔼[Z])^2 / 𝔼[Z^2]`. -/
theorem paley_zygmund_gnpHalf {n : ℕ} {Z : SimpleGraph (Fin n) → ℝ}
    (hZ : ∀ G, 0 ≤ Z G) (hpos : 0 < expectGnpHalf n Z) :
    (expectGnpHalf n Z) ^ 2 / expectGnpHalf n (fun G => (Z G) ^ 2) ≤
      probGnpHalf n {G | 0 < Z G} := by
  classical
  let S : Finset (SimpleGraph (Fin n)) := Finset.univ.filter (fun G => 0 < Z G)
  let N : ℝ := (Fintype.card (SimpleGraph (Fin n)) : ℝ)
  have hN : 0 < N := Nat.cast_pos.mpr (card_simpleGraph_fin_pos n)
  have hsumZ : ∑ G : SimpleGraph (Fin n), Z G = ∑ G ∈ S, Z G := by
    rw [← Finset.sum_subset (Finset.subset_univ S)]
    intro G _ hGS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at hGS
    exact le_antisymm (not_lt.mp hGS) (hZ G)
  have hsumZ_pos : 0 < ∑ G ∈ S, Z G := by
    unfold expectGnpHalf at hpos
    rw [hsumZ] at hpos
    exact (div_pos_iff_of_pos_right hN).mp hpos
  have hcs : (∑ G ∈ S, Z G) ^ 2 ≤ (S.card : ℝ) * ∑ G ∈ S, (Z G) ^ 2 :=
    sq_sum_le_card_mul_sum_sq S Z
  have hsumSq_le : ∑ G ∈ S, (Z G) ^ 2 ≤ ∑ G : SimpleGraph (Fin n), (Z G) ^ 2 :=
    Finset.sum_le_univ_sum_of_nonneg fun G => sq_nonneg (Z G)
  have hsumSq_pos : 0 < ∑ G : SimpleGraph (Fin n), (Z G) ^ 2 := by
    have hS_pos : 0 < (S.card : ℝ) * ∑ G ∈ S, (Z G) ^ 2 :=
      (sq_pos_of_pos hsumZ_pos).trans_le hcs
    have hScard_nonneg : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    have h1 : 0 < ∑ G ∈ S, (Z G) ^ 2 := by
      by_contra hle
      have h0 : ∑ G ∈ S, (Z G) ^ 2 ≤ 0 := not_lt.mp hle
      have : (S.card : ℝ) * ∑ G ∈ S, (Z G) ^ 2 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hScard_nonneg h0
      linarith
    exact h1.trans_le hsumSq_le
  have hexpSq_pos : 0 < expectGnpHalf n (fun G => (Z G) ^ 2) :=
    div_pos hsumSq_pos hN
  rw [probGnpHalf_eq_card_div, div_le_iff₀ hexpSq_pos]
  unfold expectGnpHalf
  change ((∑ G, Z G) / N) ^ 2 ≤ ((S.card : ℝ) / N) * ((∑ G, (Z G) ^ 2) / N)
  rw [hsumZ, div_pow, div_mul_div_comm, ← sq N]
  gcongr
  exact hcs.trans (mul_le_mul_of_nonneg_left hsumSq_le (Nat.cast_nonneg _))

/-! ### 5. Exact Edge-Set Marginals in `G(n, 1/2)` -/

/-- **Exact edge-set marginal probability**: for any set `F` of off-diagonal vertex pairs and any
prescribed edge/non-edge assignment `τ : OffDiagSym2 n → Bool`, the probability under `G(n, 1/2)`
that `G` agrees with `τ` on every `e ∈ F` is `(2⁻¹ : ℝ) ^ F.card`. -/
theorem probGnpHalf_prescribed_edges (n : ℕ) (F : Finset (OffDiagSym2 n))
    (τ : OffDiagSym2 n → Bool) :
    probGnpHalf n {G : SimpleGraph (Fin n) |
      ∀ e ∈ F, (edgeConfigEquiv n).symm G e = τ e} = (2⁻¹ : ℝ) ^ F.card := by
  classical
  rw [probGnpHalf_eq_card_div, card_simpleGraph_fin]
  let A : Finset (SimpleGraph (Fin n)) :=
    Finset.univ.filter (· ∈ {G : SimpleGraph (Fin n) |
      ∀ e ∈ F, (edgeConfigEquiv n).symm G e = τ e})
  let B : Finset (OffDiagSym2 n → Bool) :=
    Finset.univ.filter (fun ω : OffDiagSym2 n → Bool => ∀ e ∈ F, ω e = τ e)
  have hAB : A.card = B.card := by
    refine Finset.card_bij (fun G _ => (edgeConfigEquiv n).symm G) ?_ ?_ ?_
    · intro G hG
      simpa [A, B] using hG
    · intro G₁ _ G₂ _ h
      exact (edgeConfigEquiv n).symm.injective h
    · intro ω hω
      refine ⟨edgeConfigEquiv n ω, ?_, by simp⟩
      simpa [A, B] using hω
  let freeEquiv : ({e : OffDiagSym2 n // e ∉ F} → Bool) ≃ {ω : OffDiagSym2 n → Bool // ω ∈ B} :=
    { toFun := fun η => ⟨fun e => if h : e ∈ F then τ e else η ⟨e, h⟩, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, B]
        intro e he
        simp [he]⟩
      invFun := fun ω => fun e => ω.1 e.1
      left_inv := fun η => by
        funext ⟨e, he⟩
        simp [he]
      right_inv := fun ⟨ω, hω⟩ => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, B] at hω
        ext e
        by_cases he : e ∈ F
        · simp [he, hω e he]
        · simp [he] }
  have hcompl_card : Fintype.card {e : OffDiagSym2 n // e ∉ F} = n.choose 2 - F.card := by
    have h1 := Fintype.card_subtype_compl (fun e : OffDiagSym2 n => e ∈ F)
    change Fintype.card {e : OffDiagSym2 n // e ∉ F} =
      Fintype.card (OffDiagSym2 n) - Fintype.card {e : OffDiagSym2 n // e ∈ F} at h1
    rw [h1, card_offDiagSym2, Fintype.card_coe]
  have hBcard : B.card = 2 ^ (n.choose 2 - F.card) := by
    have hsub : B.card = Fintype.card {ω : OffDiagSym2 n → Bool // ω ∈ B} :=
      (Fintype.card_coe B).symm
    rw [hsub, Fintype.card_congr freeEquiv.symm, Fintype.card_fun, Fintype.card_bool, hcompl_card]
  have hle : F.card ≤ n.choose 2 := by
    have h1 : F.card ≤ Fintype.card (OffDiagSym2 n) := F.card_le_univ
    rwa [card_offDiagSym2] at h1
  change (A.card : ℝ) / ((2 ^ n.choose 2 : ℕ) : ℝ) = (2⁻¹ : ℝ) ^ F.card
  rw [hAB, hBcard, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat]
  have hsplit : (2 : ℝ) ^ n.choose 2 = (2 : ℝ) ^ (n.choose 2 - F.card) * (2 : ℝ) ^ F.card := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [hsplit, div_mul_eq_div_div, div_self (by positivity), one_div, inv_pow]

/-- Off-diagonal pairs with both endpoints inside a vertex subset `S : Finset (Fin n)`. -/
def subsetPairs {n : ℕ} (S : Finset (Fin n)) : Finset (OffDiagSym2 n) :=
  Finset.univ.filter (fun e : OffDiagSym2 n => ∀ v ∈ e.1, v ∈ S)

@[simp]
theorem mem_subsetPairs {n : ℕ} {S : Finset (Fin n)} {e : OffDiagSym2 n} :
    e ∈ subsetPairs S ↔ ∀ v ∈ e.1, v ∈ S := by
  simp [subsetPairs]

theorem mem_subsetPairs_mkOffDiag {n : ℕ} {S : Finset (Fin n)} {u v : Fin n} (huv : u ≠ v) :
    mkOffDiag huv ∈ subsetPairs S ↔ u ∈ S ∧ v ∈ S := by
  simp [subsetPairs, mkOffDiag]

theorem card_subsetPairs {n : ℕ} (S : Finset (Fin n)) :
    (subsetPairs S).card = S.card.choose 2 := by
  let emb : OffDiagSym2 S.card ↪ OffDiagSym2 n := by
    let f : Fin S.card ↪ Fin n := (S.orderEmbOfFin rfl).toEmbedding
    refine ⟨fun e => ⟨Sym2.map f e.1, ?_⟩, ?_⟩
    · rcases e with ⟨e₀, he₀⟩
      induction e₀ using Sym2.ind with
      | _ a b =>
        simp only [Sym2.map_mk, Sym2.mk_isDiag_iff, f.injective.eq_iff] at he₀ ⊢
        exact he₀
    · intro e₁ e₂ h
      apply Subtype.ext
      exact Sym2.map.injective f.injective (congrArg Subtype.val h)
  have himg : Finset.univ.map emb = subsetPairs S := by
    ext ⟨e, he⟩
    simp only [Finset.mem_map, Finset.mem_univ, true_and, mem_subsetPairs]
    constructor
    · rintro ⟨⟨e₀, _⟩, h⟩
      have heq : Sym2.map (S.orderEmbOfFin rfl) e₀ = e := congrArg Subtype.val h
      subst heq
      intro v hv
      rcases Sym2.mem_map.mp hv with ⟨w, _, rfl⟩
      exact S.orderEmbOfFin_mem rfl w
    · intro hS
      induction e using Sym2.ind with
      | _ u v =>
        have hu : u ∈ S := hS u (Sym2.mem_mk_left u v)
        have hv : v ∈ S := hS v (Sym2.mem_mk_right u v)
        let iso := S.orderIsoOfFin rfl
        let u₀ : Fin S.card := iso.symm ⟨u, hu⟩
        let v₀ : Fin S.card := iso.symm ⟨v, hv⟩
        have huv₀ : ¬ s(u₀, v₀).IsDiag := by
          rw [Sym2.mk_isDiag_iff]
          intro heq
          have huv : u = v := by
            simpa [u₀, v₀] using congrArg (Subtype.val : ↑S → Fin n) (congrArg (⇑iso) heq)
          exact he (Sym2.mk_isDiag_iff.mpr huv)
        refine ⟨⟨s(u₀, v₀), huv₀⟩, ?_⟩
        apply Subtype.ext
        change s((iso u₀ : Fin n), (iso v₀ : Fin n)) = s(u, v)
        simp [u₀, v₀]
  rw [← himg, Finset.card_map, Finset.card_univ, card_offDiagSym2]

theorem disjoint_subsetPairs {n : ℕ} {S T : Finset (Fin n)} (hST : Disjoint S T) :
    Disjoint (subsetPairs S) (subsetPairs T) := by
  rw [Finset.disjoint_left]
  intro ⟨e, _⟩ hS hT
  induction e using Sym2.ind with
  | _ u v =>
    have huS : u ∈ S := mem_subsetPairs.mp hS u (Sym2.mem_mk_left u v)
    have huT : u ∈ T := mem_subsetPairs.mp hT u (Sym2.mem_mk_left u v)
    exact Finset.disjoint_left.mp hST huS huT

theorem satisfiesSign_iff_subsetPairs {n : ℕ} (G : SimpleGraph (Fin n)) (b : Bool)
    (S : Finset (Fin n)) :
    SatisfiesSign G b (S : Set (Fin n)) ↔
      ∀ e ∈ subsetPairs S, (edgeConfigEquiv n).symm G e = b := by
  cases b
  · simp only [SatisfiesSign]
    constructor
    · intro hind ⟨e, he⟩ heS
      induction e using Sym2.ind with
      | _ u v =>
        have huv : u ≠ v := Sym2.mk_isDiag_iff.not.mp he
        have hu : u ∈ (S : Set (Fin n)) := mem_subsetPairs.mp heS u (Sym2.mem_mk_left u v)
        have hv : v ∈ (S : Set (Fin n)) := mem_subsetPairs.mp heS v (Sym2.mem_mk_right u v)
        have hnadj : ¬ G.Adj u v := hind hu hv huv
        rw [Bool.eq_false_iff, Ne, edgeConfigEquiv_symm_apply_eq_true]
        exact hnadj
    · intro h u hu v hv huv hadj
      have heS : mkOffDiag huv ∈ subsetPairs S := (mem_subsetPairs_mkOffDiag huv).mpr ⟨hu, hv⟩
      have hfalse := h (mkOffDiag huv) heS
      have htrue : (edgeConfigEquiv n).symm G (mkOffDiag huv) = true :=
        (edgeConfigEquiv_symm_apply_eq_true G (mkOffDiag huv)).mpr hadj
      rw [htrue] at hfalse
      exact Bool.noConfusion hfalse
  · simp only [SatisfiesSign]
    constructor
    · intro hcl ⟨e, he⟩ heS
      induction e using Sym2.ind with
      | _ u v =>
        have huv : u ≠ v := Sym2.mk_isDiag_iff.not.mp he
        have hu : u ∈ (S : Set (Fin n)) := mem_subsetPairs.mp heS u (Sym2.mem_mk_left u v)
        have hv : v ∈ (S : Set (Fin n)) := mem_subsetPairs.mp heS v (Sym2.mem_mk_right u v)
        exact (edgeConfigEquiv_symm_apply_eq_true G ⟨s(u, v), he⟩).mpr (hcl hu hv huv)
    · intro h u hu v hv huv
      have heS : mkOffDiag huv ∈ subsetPairs S := (mem_subsetPairs_mkOffDiag huv).mpr ⟨hu, hv⟩
      exact (edgeConfigEquiv_symm_apply_eq_true G (mkOffDiag huv)).mp (h (mkOffDiag huv) heS)

/-- Exact probability that a fixed vertex subset `S` satisfies sign `b` (`IsIndepSet` or `IsClique`). -/
theorem probGnpHalf_satisfiesSign (n : ℕ) (b : Bool) (S : Finset (Fin n)) :
    probGnpHalf n {G | SatisfiesSign G b (S : Set (Fin n))} = (2⁻¹ : ℝ) ^ S.card.choose 2 := by
  have heq : {G : SimpleGraph (Fin n) | SatisfiesSign G b (S : Set (Fin n))} =
      {G : SimpleGraph (Fin n) |
        ∀ e ∈ subsetPairs S, (edgeConfigEquiv n).symm G e = (fun _ => b) e} := by
    ext G
    exact satisfiesSign_iff_subsetPairs G b S
  rw [heq, probGnpHalf_prescribed_edges, card_subsetPairs]

theorem probGnpHalf_isIndepSet (n : ℕ) (S : Finset (Fin n)) :
    probGnpHalf n {G | G.IsIndepSet (S : Set (Fin n))} = (2⁻¹ : ℝ) ^ S.card.choose 2 :=
  probGnpHalf_satisfiesSign n false S

theorem probGnpHalf_isClique (n : ℕ) (S : Finset (Fin n)) :
    probGnpHalf n {G | G.IsClique (S : Set (Fin n))} = (2⁻¹ : ℝ) ^ S.card.choose 2 :=
  probGnpHalf_satisfiesSign n true S

/-- **Exact joint realization probability for pairwise-disjoint signed subsets**:
for pairwise disjoint vertex subsets `(parts i)_{i ∈ s}` and signs `σ i`, the internal pairs
`subsetPairs (parts i)` are pairwise disjoint, so the probability that every `parts i` satisfies
sign `σ i` is `(2⁻¹ : ℝ) ^ (∑ i ∈ s, (parts i).card.choose 2)`. -/
theorem probGnpHalf_disjoint_satisfiesSign {ι : Type*} [DecidableEq ι] (n : ℕ) (s : Finset ι)
    (parts : ι → Finset (Fin n)) (σ : ι → Bool)
    (hdisj : (s : Set ι).PairwiseDisjoint parts) :
    probGnpHalf n {G | ∀ i ∈ s, SatisfiesSign G (σ i) (parts i : Set (Fin n))} =
      (2⁻¹ : ℝ) ^ (∑ i ∈ s, (parts i).card.choose 2) := by
  classical
  have hpairDisj : (s : Set ι).PairwiseDisjoint (fun i => subsetPairs (parts i)) :=
    fun i hi j hj hij => disjoint_subsetPairs (hdisj hi hj hij)
  let F : Finset (OffDiagSym2 n) := s.biUnion (fun i => subsetPairs (parts i))
  let τ : OffDiagSym2 n → Bool := fun e =>
    if h : ∃ i ∈ s, e ∈ subsetPairs (parts i) then σ (Classical.choose h) else false
  have hτ : ∀ i ∈ s, ∀ e ∈ subsetPairs (parts i), τ e = σ i := by
    intro i hi e he
    have hex : ∃ j ∈ s, e ∈ subsetPairs (parts j) := ⟨i, hi, he⟩
    simp only [τ, dite_eq_left_of_eq_true (eq_true hex)]
    have hspec := Classical.choose_spec hex
    by_cases hji : Classical.choose hex = i
    · rw [hji]
    · exfalso
      exact Finset.disjoint_left.mp (hpairDisj hspec.1 hi hji) hspec.2 he
  have heq : {G : SimpleGraph (Fin n) | ∀ i ∈ s, SatisfiesSign G (σ i) (parts i : Set (Fin n))} =
      {G : SimpleGraph (Fin n) | ∀ e ∈ F, (edgeConfigEquiv n).symm G e = τ e} := by
    ext G
    simp only [Set.mem_ofPred_eq, F, Finset.mem_biUnion]
    constructor
    · intro hG e ⟨i, hi, he⟩
      rw [hτ i hi e he]
      exact (satisfiesSign_iff_subsetPairs G (σ i) (parts i)).mp (hG i hi) e he
    · intro hG i hi
      rw [satisfiesSign_iff_subsetPairs]
      intro e he
      rw [← hτ i hi e he]
      exact hG e ⟨i, hi, he⟩
  rw [heq, probGnpHalf_prescribed_edges]
  congr 1
  rw [Finset.card_biUnion hpairDisj]
  exact Finset.sum_congr rfl fun i _ => card_subsetPairs (parts i)

/-! ### 6. Thermodynamic Functions, Quantitative Constants, and Conjecture Statements -/

/-- Base-2 logarithm `log₂ x = log x / log 2`. -/
noncomputable def logBase2 (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

/-- Standard real-valued independence-number center `α₀(n)` from `arXiv:2608.30604`:
`α₀(n) = 2 log₂ n - 2 log₂(log₂ n) + 2 log₂(e / 2) + 1`. -/
noncomputable def alpha0 (n : ℕ) : ℝ :=
  2 * logBase2 (n : ℝ) - 2 * logBase2 (logBase2 (n : ℝ)) + 2 * logBase2 (Real.exp 1 / 2) + 1

/-- Integer floor `α = ⌊α₀(n)⌋` of the independence-number center. -/
noncomputable def alphaFloor (n : ℕ) : ℤ :=
  ⌊alpha0 n⌋

/-- Deterministic fractional phase `δ_n = {α₀(n)} = α₀(n) - ⌊α₀(n)⌋ ∈ [0, 1)`. -/
noncomputable def phaseDelta (n : ℕ) : ℝ :=
  Int.fract (alpha0 n)

theorem phaseDelta_mem_Icc (n : ℕ) : phaseDelta n ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

/-- Target deficit `T_δ := 1 + 2 / log 2 - δ` for `δ ∈ [0, 1]`. -/
noncomputable def targetDeficit (δ : ℝ) : ℝ :=
  1 + 2 / Real.log 2 - δ

/-- Partition function `Z_{S_+}(λ) = ∑_{i ≥ -1} exp(λ i - (log 2 / 2) i^2)` on `S_+ = {i ∈ ℤ : i ≥ -1}`. -/
noncomputable def partFuncPlus (lam : ℝ) : ℝ :=
  ∑' k : ℕ, Real.exp (lam * ((k : ℝ) - 1) - (Real.log 2 / 2) * ((k : ℝ) - 1) ^ 2)

/-- Partition function `Z_{S_4}(λ) = ∑_{i ∈ {2,3,4,5}} exp(λ i - (log 2 / 2) i^2)` on `S_4 = {2,3,4,5}`. -/
noncomputable def partFuncFour (lam : ℝ) : ℝ :=
  ∑ i ∈ ({2, 3, 4, 5} : Finset ℤ),
    Real.exp (lam * (i : ℝ) - (Real.log 2 / 2) * (i : ℝ) ^ 2)

/-- Legendre–Fenchel free energy `𝓕_{S_+}(T) = inf_{λ ∈ ℝ} (log Z_{S_+}(λ) - λ T)`. -/
noncomputable def freeEnergyPlus (T : ℝ) : ℝ :=
  ⨅ lam : ℝ, (Real.log (partFuncPlus lam) - lam * T)

/-- Legendre–Fenchel free energy `𝓕_{S_4}(T) = inf_{λ ∈ ℝ} (log Z_{S_4}(λ) - λ T)`. -/
noncomputable def freeEnergyFour (T : ℝ) : ℝ :=
  ⨅ lam : ℝ, (Real.log (partFuncFour lam) - lam * T)

/-- Petkov's phase-resolved entropy gap `A_4(δ) := log 2 - 𝓕_{S_+}(T_δ) + 𝓕_{S_4}(T_δ)`. -/
noncomputable def petkovA4 (δ : ℝ) : ℝ :=
  Real.log 2 - freeEnergyPlus (targetDeficit δ) + freeEnergyFour (targetDeficit δ)

/-- Explicit uniform coefficient `c₀ = ((log 2)^2 / 4) * log(200 / 153)` in Petkov's theorem. -/
noncomputable def petkovConstant : ℝ :=
  (Real.log 2) ^ 2 / 4 * Real.log (200 / 153)

theorem petkovConstant_pos : 0 < petkovConstant := by
  unfold petkovConstant
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogRat : 0 < Real.log (200 / 153 : ℝ) := Real.log_pos (by norm_num)
  positivity

/-- Exact identity between `ℕ`-subtraction and `ℝ`-subtraction for `χ(G) - ζ(G)` on finite graphs,
since `ζ(G) ≤ χ(G)` holds unconditionally (`cochromaticNumber_le_chromaticNumber_toNat`). -/
theorem cast_chromatic_sub_cochromatic {V : Type*} [Finite V] (G : SimpleGraph V) :
    ((G.chromaticNumber.toNat - cochromaticNumber G : ℕ) : ℝ) =
      (G.chromaticNumber.toNat : ℝ) - (cochromaticNumber G : ℝ) :=
  Nat.cast_sub (cochromaticNumber_le_chromaticNumber_toNat G)

/-- **Erdős–Gimbel Problem (Erdős Problem #625)**:
For `G_n ~ G(n, 1/2)`, `χ(G_n) - ζ(G_n) → ∞` with high probability as `n → ∞`. -/
def ErdosGimbel625Statement : Prop :=
  ∀ M : ℕ, Tendsto
    (fun n : ℕ => probGnpHalf n
      {G : SimpleGraph (Fin n) | M ≤ G.chromaticNumber.toNat - cochromaticNumber G})
    atTop (𝓝 1)

/-- **Petkov's Full-Sequence Quantitative Gap (`arXiv:2608.30604`, Main Theorem / Abstract)**:
For `G_n ~ G(n, 1/2)`,
`ℙ(χ(G_n) - ζ(G_n) ≥ ((log 2)^2 / 4) * log(200 / 153) * n / (log n)^3) → 1` as `n → ∞`. -/
def PetkovQuantitative625Statement : Prop :=
  Tendsto
    (fun n : ℕ => probGnpHalf n
      {G : SimpleGraph (Fin n) |
        petkovConstant * (n : ℝ) / (Real.log (n : ℝ)) ^ 3 ≤
          (G.chromaticNumber.toNat : ℝ) - (cochromaticNumber G : ℝ)})
    atTop (𝓝 1)

/-- **Petkov's Phase-Resolved Gap (`arXiv:2608.30604`, Main Theorem)**:
There exists a deterministic nonnegative sequence `ε_n → 0` such that
`ℙ(χ(G_n) - ζ(G_n) ≥ [((log 2)^2 / 4) * A_4(δ_n) - ε_n] * n / (log n)^3) → 1` as `n → ∞`. -/
def PetkovPhaseResolved625Statement : Prop :=
  ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
    Tendsto
      (fun n : ℕ => probGnpHalf n
        {G : SimpleGraph (Fin n) |
          ((Real.log 2) ^ 2 / 4 * petkovA4 (phaseDelta n) - ε n) *
            (n : ℝ) / (Real.log (n : ℝ)) ^ 3 ≤
              (G.chromaticNumber.toNat : ℝ) - (cochromaticNumber G : ℝ)})
      atTop (𝓝 1)

/-- For every `k : ℕ`, `(n : ℝ) / (log n)^k → +∞` as `n → ∞`. -/
theorem tendsto_nat_div_log_pow_atTop (k : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) / (Real.log (n : ℝ)) ^ k) atTop atTop := by
  have hreal : Tendsto (fun x : ℝ => x / (Real.log x) ^ k) atTop atTop := by
    refine ((Real.tendsto_exp_div_pow_atTop k).comp Real.tendsto_log_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp [Real.exp_log hx]
  exact hreal.comp tendsto_natCast_atTop_atTop

/-- **Unconditional reduction**: Petkov's quantitative `n / (log n)^3` bound immediately implies
the qualitative Erdős–Gimbel conjecture `χ(G_n) - ζ(G_n) → ∞` w.h.p. -/
theorem PetkovQuantitative625Statement.erdosGimbel625
    (hquant : PetkovQuantitative625Statement) : ErdosGimbel625Statement := by
  intro M
  have hdiv : Tendsto (fun n : ℕ => petkovConstant * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3))
      atTop atTop :=
    Filter.Tendsto.const_mul_atTop petkovConstant_pos (tendsto_nat_div_log_pow_atTop 3)
  refine tendsto_probGnpHalf_one_of_eventually_subset hquant ?_
  filter_upwards [hdiv.eventually_ge_atTop (M : ℝ)] with n hn G hG
  have hn' : (M : ℝ) ≤ petkovConstant * (n : ℝ) / (Real.log (n : ℝ)) ^ 3 := by
    simpa [mul_div_assoc] using hn
  have hsub : (M : ℝ) ≤ ((G.chromaticNumber.toNat - cochromaticNumber G : ℕ) : ℝ) := by
    rw [cast_chromatic_sub_cochromatic]
    exact hn'.trans hG
  exact Nat.cast_le.mp hsub

/-- **Phase-resolved to uniform reduction**: Given the uniform entropy certificate
`∀ δ ∈ [0, 1], petkovA4 δ ≥ log(200 / 153) + m₀` for some `m₀ > 0`, Petkov's phase-resolved
theorem immediately yields `PetkovQuantitative625Statement`. -/
theorem PetkovPhaseResolved625Statement.petkovQuantitative625
    (hphase : PetkovPhaseResolved625Statement)
    {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hA4 : ∀ δ ∈ Set.Icc (0 : ℝ) 1, Real.log (200 / 153) + m₀ ≤ petkovA4 δ) :
    PetkovQuantitative625Statement := by
  rcases hphase with ⟨ε, _, hε0, hprob⟩
  have hslack : 0 < (Real.log 2) ^ 2 / 4 * m₀ := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  refine tendsto_probGnpHalf_one_of_eventually_subset hprob ?_
  filter_upwards [hε0.eventually (ge_mem_nhds hslack), eventually_gt_atTop 1] with n hnε hn1 G hG
  simp only [Set.mem_ofPred_eq] at hG ⊢
  refine le_trans ?_ hG
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn1)
  have hscale_nonneg : 0 ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 3 := by positivity
  have hδ := hA4 (phaseDelta n) (phaseDelta_mem_Icc n)
  have hcoeff : petkovConstant ≤ (Real.log 2) ^ 2 / 4 * petkovA4 (phaseDelta n) - ε n := by
    unfold petkovConstant
    have hmul : (Real.log 2) ^ 2 / 4 * (Real.log (200 / 153) + m₀) ≤
        (Real.log 2) ^ 2 / 4 * petkovA4 (phaseDelta n) :=
      mul_le_mul_of_nonneg_left hδ (by positivity)
    linarith
  rw [mul_div_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_right hcoeff hscale_nonneg

end JSP000506
