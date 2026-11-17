import Mathlib.Data.Fintype.Pi
import JSP000506.PartA

/-!
# Part B: High-Probability First-Moment Lower Bound on `χ(G_n)`

This module formalizes Section 5 (Part B) of Samuil Petkov's *A Full-Sequence Quantitative Gap
Between the Chromatic and Cochromatic Numbers of a Random Graph* (`arXiv:2608.30604`):

1. **Surjective Coloring Promotion and `k!`-Orbit Multiplicity**:
   Any proper `k`-coloring of an `n`-vertex graph (`k ≤ n`) can be promoted by single-vertex
   recolorings to a surjective proper `k`-coloring (`exists_surjective_proper_coloring`). On the
   high-probability event `IndepCapEvent n` (`α(G) ≤ α_n + 1`), permuting colors yields at least
   `k!` distinct capped proper `k`-colorings whenever `G` is `k`-colorable.
2. **Exact First Moment and Multinomial Histogram Decomposition**:
   For each capped `c : Fin n → Fin k`, the probability under `G(n, 1/2)` that `c` is proper is
   `(2⁻¹) ^ (∑_r (fiber c r).card.choose 2)`. Grouping colorings by fiber-size tuples (`≤ n! / ∏ s_r!`)
   and deficit histograms `m : Fin (α_n + 2) → ℕ` bounds the normalized first moment cleanly via
   `falling_shift_upper_all` and `gibbs_upper_bound_plus` with zero Stirling loss on `m_j!`.
3. **Main Theorem (`tendsto_probGnpHalf_chromatic_gt_kChiMinus`)**:
   Combining the subcriticality bound `eventually_kChiMinus_subcritical` from `PartA.lean` with
   `tendsto_probGnpHalf_indepCapEvent` from `Phase.lean` yields unconditionally
   `ℙ(χ(G_n) > k_χ^-(n)) → 1` as `n → ∞`.
-/

open Filter SimpleGraph Finset
open scoped Topology BigOperators Nat

namespace JSP000506

/-! ### 1. Proper Colorings, Fibers, and Surjective Promotion -/

/-- Function-level predicate that `c : V → α` is a proper vertex coloring of `G`. -/
def IsProperColoring {V α : Type*} (G : SimpleGraph V) (c : V → α) : Prop :=
  ∀ ⦃u v : V⦄, G.Adj u v → c u ≠ c v

/-- Color fiber `{v : V | c v = r}` as a `Finset V`. -/
def coloringFiber {V α : Type*} [Fintype V] [DecidableEq α] (c : V → α) (r : α) : Finset V :=
  Finset.univ.filter (fun v => c v = r)

@[simp]
theorem mem_coloringFiber {V α : Type*} [Fintype V] [DecidableEq α]
    {c : V → α} {r : α} {v : V} :
    v ∈ coloringFiber c r ↔ c v = r := by
  simp [coloringFiber]

theorem pairwiseDisjoint_coloringFiber {V α : Type*} [Fintype V] [DecidableEq α] (c : V → α) :
    (Set.univ : Set α).PairwiseDisjoint (coloringFiber c) := by
  intro r₁ _ r₂ _ hne
  exact Finset.disjoint_left.mpr fun v hv₁ hv₂ =>
    hne ((mem_coloringFiber.mp hv₁).symm.trans (mem_coloringFiber.mp hv₂))

theorem sum_card_coloringFiber {V α : Type*} [Fintype V] [Fintype α] [DecidableEq α]
    (c : V → α) :
    ∑ r : α, (coloringFiber c r).card = Fintype.card V := by
  classical
  have huniv : (Finset.univ : Finset V) = Finset.univ.biUnion (coloringFiber c) := by
    ext v
    simp
  have hdisj : ((Finset.univ : Finset α) : Set α).PairwiseDisjoint (coloringFiber c) :=
    fun r₁ _ r₂ _ hne => pairwiseDisjoint_coloringFiber c trivial trivial hne
  rw [← Finset.card_univ, huniv, Finset.card_biUnion hdisj]

theorem colorable_iff_exists_properColoring {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    G.Colorable k ↔ ∃ c : V → Fin k, IsProperColoring G c := by
  constructor
  · rintro ⟨col⟩
    exact ⟨col, fun _ _ hadj => col.valid hadj⟩
  · rintro ⟨c, hc⟩
    exact ⟨Coloring.mk c fun hadj => hc hadj⟩

theorem colorable_of_chromaticNumber_toNat_le {V : Type*} [Finite V] (G : SimpleGraph V) {k : ℕ}
    (h : G.chromaticNumber.toNat ≤ k) : G.Colorable k := by
  rw [← chromaticNumber_le_iff_colorable, ← coe_chromaticNumber_toNat G]
  exact Nat.cast_le.mpr h

theorem isProperColoring_iff_satisfiesSign {n k : ℕ} (G : SimpleGraph (Fin n))
    (c : Fin n → Fin k) :
    IsProperColoring G c ↔
      ∀ r ∈ (Finset.univ : Finset (Fin k)),
        SatisfiesSign G false (coloringFiber c r : Set (Fin n)) := by
  constructor
  · intro hprop r _ u hu v hv _ hadj
    simp only [Finset.mem_coe, mem_coloringFiber] at hu hv
    exact hprop hadj (hu.trans hv.symm)
  · intro hfib u v hadj heq
    have hu : u ∈ (coloringFiber c (c u) : Set (Fin n)) := by simp
    have hv : v ∈ (coloringFiber c (c u) : Set (Fin n)) := by simp [heq]
    exact hfib (c u) (Finset.mem_univ _) hu hv (G.ne_of_adj hadj) hadj

private lemma exists_surjective_proper_aux {n k : ℕ} (hk : k ≤ n) (G : SimpleGraph (Fin n)) :
    ∀ (m : ℕ) (c : Fin n → Fin k), IsProperColoring G c →
      k - (Finset.univ.image c).card ≤ m →
      ∃ c' : Fin n → Fin k, IsProperColoring G c' ∧ Function.Surjective c' := by
  intro m
  induction m with
  | zero =>
    intro c hprop hrem
    have himg_le : (Finset.univ.image c).card ≤ k := by
      simpa using (Finset.univ.image c).card_le_univ
    have himg_eq : (Finset.univ.image c).card = k := by omega
    have huniv : Finset.univ.image c = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa using himg_eq)
    refine ⟨c, hprop, fun r => ?_⟩
    have hr : r ∈ Finset.univ.image c := by rw [huniv]; exact Finset.mem_univ r
    rcases Finset.mem_image.mp hr with ⟨v, _, rfl⟩
    exact ⟨v, rfl⟩
  | succ m ih =>
    intro c hprop hrem
    by_cases hfull : k ≤ (Finset.univ.image c).card
    · have himg_le : (Finset.univ.image c).card ≤ k := by
        simpa using (Finset.univ.image c).card_le_univ
      have huniv : Finset.univ.image c = Finset.univ :=
        Finset.eq_univ_of_card _ (by simpa using le_antisymm himg_le hfull)
      refine ⟨c, hprop, fun r => ?_⟩
      have hr : r ∈ Finset.univ.image c := by rw [huniv]; exact Finset.mem_univ r
      rcases Finset.mem_image.mp hr with ⟨v, _, rfl⟩
      exact ⟨v, rfl⟩
    · have hlt_k : (Finset.univ.image c).card < k := not_le.mp hfull
      -- Pick an unused color `r₀ ∉ univ.image c`
      have hex_unused : ∃ r₀ : Fin k, r₀ ∉ Finset.univ.image c := by
        by_contra hall
        push Not at hall
        have hsub : (Finset.univ : Finset (Fin k)) ⊆ Finset.univ.image c := fun r _ => hall r
        have hle := Finset.card_le_card hsub
        simp only [Finset.card_univ, Fintype.card_fin] at hle
        omega
      rcases hex_unused with ⟨r₀, hr₀⟩
      have hc_ne_r₀ : ∀ x : Fin n, c x ≠ r₀ := by
        intro x heq
        exact hr₀ (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, heq⟩)
      -- Pick two distinct vertices sharing a color (`c` cannot be injective since `card < k ≤ n`)
      have hnot_inj : ¬ Function.Injective c := by
        intro hinj
        have hcard_eq : (Finset.univ.image c).card = n := by
          rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
        omega
      have hex_coll : ∃ v₁ v₂ : Fin n, v₁ ≠ v₂ ∧ c v₁ = c v₂ := by
        unfold Function.Injective at hnot_inj
        push Not at hnot_inj
        rcases hnot_inj with ⟨v₁, v₂, heq, hne⟩
        exact ⟨v₁, v₂, hne, heq⟩
      rcases hex_coll with ⟨v₁, v₂, hv_ne, hv_eq⟩
      let c₁ : Fin n → Fin k := Function.update c v₁ r₀
      have hprop₁ : IsProperColoring G c₁ := by
        intro u w hadj
        by_cases hu : u = v₁
        · subst hu
          have hw : w ≠ u := (G.ne_of_adj hadj).symm
          simp only [c₁, Function.update_self, Function.update_of_ne hw]
          exact (hc_ne_r₀ w).symm
        · by_cases hw : w = v₁
          · subst hw
            simp only [c₁, Function.update_self, Function.update_of_ne hu]
            exact hc_ne_r₀ u
          · simp only [c₁, Function.update_of_ne hu, Function.update_of_ne hw]
            exact hprop hadj
      have hsub_img : insert r₀ (Finset.univ.image c) ⊆ Finset.univ.image c₁ := by
        intro r hr
        rcases Finset.mem_insert.mp hr with rfl | hr_old
        · exact Finset.mem_image.mpr ⟨v₁, Finset.mem_univ v₁, by simp [c₁]⟩
        · rcases Finset.mem_image.mp hr_old with ⟨x, _, rfl⟩
          by_cases hx : x = v₁
          · subst hx
            refine Finset.mem_image.mpr ⟨v₂, Finset.mem_univ v₂, ?_⟩
            simp [c₁, Function.update_of_ne hv_ne.symm, hv_eq]
          · refine Finset.mem_image.mpr ⟨x, Finset.mem_univ x, ?_⟩
            simp [c₁, Function.update_of_ne hx]
      have hcard_inc : (Finset.univ.image c).card + 1 ≤ (Finset.univ.image c₁).card := by
        rw [← Finset.card_insert_of_notMem hr₀]
        exact Finset.card_le_card hsub_img
      exact ih c₁ hprop₁ (by omega)

/-- Every proper `k`-coloring of an `n`-vertex graph with `k ≤ n` can be promoted to a surjective
proper `k`-coloring. -/
theorem exists_surjective_proper_coloring {n k : ℕ} (hk : k ≤ n) {G : SimpleGraph (Fin n)}
    (hcol : G.Colorable k) :
    ∃ c : Fin n → Fin k, IsProperColoring G c ∧ Function.Surjective c := by
  rcases (colorable_iff_exists_properColoring G k).mp hcol with ⟨c, hprop⟩
  exact exists_surjective_proper_aux hk G k c hprop (Nat.sub_le _ _)

/-! ### 2. Capped Colorings, `k!`-Multiplicity, and Exact First Moment -/

/-- Set of vertex maps `c : Fin n → Fin k` whose color fibers all have size at most `alphaNat n + 1`. -/
noncomputable def cappedColorings (n k : ℕ) : Finset (Fin n → Fin k) :=
  Finset.univ.filter (fun c : Fin n → Fin k =>
    ∀ r : Fin k, (coloringFiber c r).card ≤ alphaNat n + 1)

/-- Number of capped proper `k`-colorings of `G`. -/
noncomputable def cappedProperCount (n k : ℕ) (G : SimpleGraph (Fin n)) : ℝ := by
  classical
  exact (((cappedColorings n k).filter (fun c => IsProperColoring G c)).card : ℝ)

theorem cappedProperCount_nonneg (n k : ℕ) (G : SimpleGraph (Fin n)) :
    0 ≤ cappedProperCount n k G := by
  classical
  unfold cappedProperCount
  exact Nat.cast_nonneg _

/-- On `{G | G.Colorable k} ∩ IndepCapEvent n` (with `k ≤ n`), permuting colors of a surjective
proper `k`-coloring produces at least `k!` distinct capped proper `k`-colorings. -/
theorem factorial_le_cappedProperCount {n k : ℕ} (hk : k ≤ n) {G : SimpleGraph (Fin n)}
    (hcol : G.Colorable k) (hcap : G ∈ IndepCapEvent n) :
    (k ! : ℝ) ≤ cappedProperCount n k G := by
  classical
  obtain ⟨c₀, hprop₀, hsurj₀⟩ := exists_surjective_proper_coloring hk hcol
  let emb : Equiv.Perm (Fin k) → (Fin n → Fin k) := fun σ v => σ (c₀ v)
  have hemb_inj : Function.Injective emb := by
    intro σ₁ σ₂ heq
    refine Equiv.ext fun r => ?_
    obtain ⟨v, rfl⟩ := hsurj₀ r
    exact congrFun heq v
  have hemb_mem : ∀ σ : Equiv.Perm (Fin k),
      emb σ ∈ (cappedColorings n k).filter (fun c => IsProperColoring G c) := by
    intro σ
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · simp only [cappedColorings, Finset.mem_filter, Finset.mem_univ, true_and]
      intro r
      have hfib_eq : coloringFiber (emb σ) r = coloringFiber c₀ (σ.symm r) := by
        ext v
        simp only [mem_coloringFiber, emb]
        exact ⟨fun h => by simpa using congrArg σ.symm h,
          fun h => by simpa using congrArg σ h⟩
      rw [hfib_eq]
      have hind : G.IsIndepSet (coloringFiber c₀ (σ.symm r) : Set (Fin n)) :=
        (isProperColoring_iff_satisfiesSign G c₀).mp hprop₀ (σ.symm r) (Finset.mem_univ _)
      exact hcap _ hind
    · intro u v hadj
      exact σ.injective.ne (hprop₀ hadj)
  have hcard : k ! ≤ ((cappedColorings n k).filter (fun c => IsProperColoring G c)).card := by
    calc
      k ! = Fintype.card (Equiv.Perm (Fin k)) := by rw [Fintype.card_perm, Fintype.card_fin]
      _ = (Finset.univ.image emb).card := by
        rw [Finset.card_image_of_injective _ hemb_inj, Finset.card_univ]
      _ ≤ ((cappedColorings n k).filter (fun c => IsProperColoring G c)).card :=
        Finset.card_le_card fun c hc => by
          rcases Finset.mem_image.mp hc with ⟨σ, _, rfl⟩
          exact hemb_mem σ
  unfold cappedProperCount
  exact_mod_cast hcard

/-- Exact probability under `G(n, 1/2)` that a fixed map `c : Fin n → Fin k` is a proper coloring. -/
theorem probGnpHalf_isProperColoring (n k : ℕ) (c : Fin n → Fin k) :
    probGnpHalf n {G | IsProperColoring G c} =
      (2⁻¹ : ℝ) ^ (∑ r : Fin k, (coloringFiber c r).card.choose 2) := by
  have heq : {G : SimpleGraph (Fin n) | IsProperColoring G c} =
      {G : SimpleGraph (Fin n) |
        ∀ r ∈ (Finset.univ : Finset (Fin k)),
          SatisfiesSign G false (coloringFiber c r : Set (Fin n))} := by
    ext G
    exact isProperColoring_iff_satisfiesSign G c
  have hdisj : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint (coloringFiber c) :=
    fun r₁ _ r₂ _ hne => pairwiseDisjoint_coloringFiber c trivial trivial hne
  rw [heq]
  exact probGnpHalf_disjoint_satisfiesSign n Finset.univ (coloringFiber c) (fun _ => false) hdisj

/-- Exact first moment of `cappedProperCount n k` under `G(n, 1/2)`. -/
theorem expectGnpHalf_cappedProperCount (n k : ℕ) :
    expectGnpHalf n (cappedProperCount n k) =
      ∑ c ∈ cappedColorings n k,
        (2⁻¹ : ℝ) ^ (∑ r : Fin k, (coloringFiber c r).card.choose 2) := by
  classical
  have hfun : cappedProperCount n k = fun G =>
      ∑ c ∈ cappedColorings n k, {H | IsProperColoring H c}.indicator (fun _ => (1 : ℝ)) G := by
    funext G
    unfold cappedProperCount
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : IsProperColoring G c <;> simp [Set.indicator, hc]
  rw [hfun, expectGnpHalf_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [expectGnpHalf_indicator_one, probGnpHalf_isProperColoring]

/-- Normalized first-moment bound on `ℙ(G.Colorable k ∧ IndepCapEvent n)`. -/
theorem probGnpHalf_colorable_inter_indepCap_le {n k : ℕ} (hk : k ≤ n) :
    probGnpHalf n ({G | G.Colorable k} ∩ IndepCapEvent n) ≤
      expectGnpHalf n (cappedProperCount n k) / (k ! : ℝ) := by
  have hfac_pos : (0 : ℝ) < (k ! : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have hsub : {G : SimpleGraph (Fin n) | G.Colorable k} ∩ IndepCapEvent n ⊆
      {G : SimpleGraph (Fin n) | (k ! : ℝ) ≤ cappedProperCount n k G} := by
    rintro G ⟨hcol, hcap⟩
    exact factorial_le_cappedProperCount hk hcol hcap
  exact (probGnpHalf_mono hsub).trans
    (probGnpHalf_ge_le_expect_div (cappedProperCount_nonneg n k) hfac_pos)

/-! ### 3. Counting Colorings with Prescribed Fiber Sizes and Deficit Histograms -/

private def extendColoring {V : Type*} [DecidableEq V] {k : ℕ}
    (S : Finset V) (c' : {v : V // v ∉ S} → Fin k) (v : V) : Fin (k + 1) :=
  if hv : v ∈ S then 0 else (c' ⟨v, hv⟩).succ

/-- Multinomial count of vertex maps `c : V → Fin k` with prescribed fiber sizes `s : Fin k → ℕ`:
`#{c | ∀ r, (coloringFiber c r).card = s r} * ∏ r, (s r)! ≤ (Fintype.card V)!`. -/
theorem card_colorings_with_fiber_sizes :
    ∀ (k : ℕ) {V : Type*} [Fintype V] [DecidableEq V] (s : Fin k → ℕ),
      (Finset.univ.filter (fun c : V → Fin k => ∀ r : Fin k, (coloringFiber c r).card = s r)).card *
        (∏ r : Fin k, (s r) !) ≤ (Fintype.card V) ! := by
  intro k
  induction k with
  | zero =>
    intro V _ _ s
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    by_cases hV : Fintype.card V = 0
    · rw [hV]
      have : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
      calc
        (Finset.univ.filter (fun c : V → Fin 0 => ∀ r : Fin 0, (coloringFiber c r).card = s r)).card
            ≤ Fintype.card (V → Fin 0) := Finset.card_le_univ _
        _ = 1 := by simp
    · obtain ⟨v₀⟩ : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
      have hempty : (Finset.univ.filter
          (fun c : V → Fin 0 => ∀ r : Fin 0, (coloringFiber c r).card = s r)) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro c _
        exact Fin.elim0 (c v₀)
      rw [hempty, Finset.card_empty]
      exact Nat.zero_le _
  | succ k ih =>
    intro V _ _ s
    let F : Finset (V → Fin (k + 1)) :=
      Finset.univ.filter (fun c : V → Fin (k + 1) => ∀ r, (coloringFiber c r).card = s r)
    by_cases hs0 : s 0 ≤ Fintype.card V
    · let P : Finset (Finset V) := Finset.univ.powersetCard (s 0)
      have hdecomp : F = P.biUnion (fun S => F.filter (fun c => coloringFiber c 0 = S)) := by
        ext c
        simp only [Finset.mem_biUnion, Finset.mem_filter, P]
        constructor
        · intro hc
          refine ⟨coloringFiber c 0, ?_, hc, rfl⟩
          rw [Finset.mem_powersetCard]
          exact ⟨Finset.subset_univ _, (Finset.mem_filter.mp hc).2 0⟩
        · rintro ⟨_, _, hc, _⟩
          exact hc
      have hdisj : (P : Set (Finset V)).PairwiseDisjoint
          (fun S => F.filter (fun c => coloringFiber c 0 = S)) := by
        intro S₁ _ S₂ _ hne
        exact Finset.disjoint_left.mpr fun c hc₁ hc₂ =>
          hne ((Finset.mem_filter.mp hc₁).2.symm.trans (Finset.mem_filter.mp hc₂).2)
      have hslice_bound : ∀ S ∈ P,
          (F.filter (fun c => coloringFiber c 0 = S)).card * (∏ j : Fin k, (s j.succ) !) ≤
            (Fintype.card V - s 0) ! := by
        intro S hSP
        have hScard : S.card = s 0 := (Finset.mem_powersetCard.mp hSP).2
        let V' := {v : V // v ∉ S}
        have hV'card : Fintype.card V' = Fintype.card V - s 0 := by
          have h1 := Fintype.card_subtype_compl (fun v : V => v ∈ S)
          change Fintype.card V' = Fintype.card V - Fintype.card {v : V // v ∈ S} at h1
          rw [h1, Fintype.card_coe, hScard]
        let F' : Finset (V' → Fin k) :=
          Finset.univ.filter (fun c' : V' → Fin k => ∀ j : Fin k, (coloringFiber c' j).card = s j.succ)
        have hsub_img : F.filter (fun c => coloringFiber c 0 = S) ⊆ F'.image (extendColoring S) := by
          intro c hc
          have hcF : ∀ r, (coloringFiber c r).card = s r :=
            (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).2
          have hc0 : coloringFiber c 0 = S := (Finset.mem_filter.mp hc).2
          have hne0 : ∀ x : V', c x.1 ≠ 0 := by
            intro x h0
            have hmem : x.1 ∈ coloringFiber c 0 := mem_coloringFiber.mpr h0
            exact x.2 (hc0 ▸ hmem)
          let c' : V' → Fin k := fun x => (c x.1).pred (hne0 x)
          refine Finset.mem_image.mpr ⟨c', ?_, ?_⟩
          · rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ _, fun j => ?_⟩
            have hbij : (coloringFiber c' j).card = (coloringFiber c j.succ).card := by
              refine Finset.card_bij (fun (x : V') _ => x.1) ?_ ?_ ?_
              · intro x hx
                rw [mem_coloringFiber] at hx ⊢
                have hpred : (c x.1).pred (hne0 x) = j := hx
                simpa [Fin.succ_pred] using congrArg Fin.succ hpred
              · intro x₁ _ x₂ _ heq
                exact Subtype.ext heq
              · intro v hv
                rw [mem_coloringFiber] at hv
                have hvS : v ∉ S := by
                  intro hv_in
                  have hmem : v ∈ coloringFiber c 0 := hc0.symm ▸ hv_in
                  rw [mem_coloringFiber, hv] at hmem
                  exact Fin.succ_ne_zero j hmem
                refine ⟨⟨v, hvS⟩, ?_, rfl⟩
                rw [mem_coloringFiber]
                dsimp [c']
                simp [hv]
            rw [hbij, hcF j.succ]
          · funext v
            unfold extendColoring
            by_cases hv : v ∈ S
            · simp only [hv, ↓reduceDIte]
              have hmem : v ∈ coloringFiber c 0 := hc0.symm ▸ hv
              exact (mem_coloringFiber.mp hmem).symm
            · simp only [hv, ↓reduceDIte, c', Fin.succ_pred]
        have hcard_le : (F.filter (fun c => coloringFiber c 0 = S)).card ≤ F'.card :=
          (Finset.card_le_card hsub_img).trans Finset.card_image_le
        calc
          (F.filter (fun c => coloringFiber c 0 = S)).card * (∏ j : Fin k, (s j.succ) !)
              ≤ F'.card * (∏ j : Fin k, (s j.succ) !) := Nat.mul_le_mul_right _ hcard_le
          _ ≤ (Fintype.card V') ! := ih (fun j => s j.succ)
          _ = (Fintype.card V - s 0) ! := by rw [hV'card]
      have hsum_F : F.card * (∏ j : Fin k, (s j.succ) !) ≤
          P.card * (Fintype.card V - s 0) ! := by
        rw [hdecomp, Finset.card_biUnion hdisj, Finset.sum_mul]
        calc
          ∑ S ∈ P, (F.filter (fun c => coloringFiber c 0 = S)).card * (∏ j : Fin k, (s j.succ) !)
              ≤ ∑ _ ∈ P, (Fintype.card V - s 0) ! := Finset.sum_le_sum hslice_bound
          _ = P.card * (Fintype.card V - s 0) ! := by simp
      have hPcard : P.card = (Fintype.card V).choose (s 0) := by
        simp [P]
      change F.card * (∏ r : Fin (k + 1), (s r) !) ≤ Nat.factorial (Fintype.card V)
      rw [Fin.prod_univ_succ]
      calc
        F.card * ((s 0) ! * ∏ j : Fin k, (s j.succ) !)
            = (s 0) ! * (F.card * ∏ j : Fin k, (s j.succ) !) := by ring
        _ ≤ (s 0) ! * (P.card * (Fintype.card V - s 0) !) :=
          Nat.mul_le_mul_left _ hsum_F
        _ = (Fintype.card V).choose (s 0) * (s 0) ! * (Fintype.card V - s 0) ! := by
          rw [hPcard]
          ring
        _ = Nat.factorial (Fintype.card V) := Nat.choose_mul_factorial_mul_factorial hs0
    · have hempty : F = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro c hc
        have hc0 : (coloringFiber c 0).card = s 0 := (Finset.mem_filter.mp hc).2 0
        have hle : (coloringFiber c 0).card ≤ Fintype.card V := Finset.card_le_univ _
        omega
      change F.card * (∏ r : Fin (k + 1), (s r) !) ≤ Nat.factorial (Fintype.card V)
      rw [hempty, Finset.card_empty, zero_mul]
      exact Nat.zero_le _

/-! ### 4. Shifted-Deficit Tuples and Multinomial Entropy Inequality -/

/-- Shifted deficit index `j = α + 1 - min s (α + 1) ∈ Fin (α + 2)` (corresponding to `i = j - 1 ≥ -1`). -/
def deficitIdx (α s : ℕ) : Fin (α + 2) :=
  ⟨α + 1 - min s (α + 1), by omega⟩

/-- Empirical histogram `m : β → ℕ` of a tuple `d : Fin k → β`. -/
def tupleHist {k : ℕ} {β : Type*} [DecidableEq β] (d : Fin k → β) (j : β) : ℕ :=
  (Finset.univ.filter (fun r : Fin k => d r = j)).card

private lemma sum_comp_eq_sum_tupleHist {k : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    (d : Fin k → β) (f : β → ℕ) :
    ∑ r : Fin k, f (d r) = ∑ j : β, tupleHist d j * f j := by
  have huniv : (Finset.univ : Finset (Fin k)) =
      Finset.univ.biUnion (fun j : β => Finset.univ.filter (fun r : Fin k => d r = j)) := by
    ext r
    simp
  have hdisj : ((Finset.univ : Finset β) : Set β).PairwiseDisjoint
      (fun j : β => Finset.univ.filter (fun r : Fin k => d r = j)) := by
    intro j₁ _ j₂ _ hne
    exact Finset.disjoint_left.mpr fun r hr₁ hr₂ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr₁ hr₂
      exact hne (hr₁.symm.trans hr₂)
  conv_lhs => rw [huniv]
  rw [Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hconst : ∀ r ∈ Finset.univ.filter (fun r : Fin k => d r = j), f (d r) = f j := by
    intro r hr
    rw [(Finset.mem_filter.mp hr).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, tupleHist]

private lemma prod_comp_eq_prod_tupleHist {k : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    (d : Fin k → β) (f : β → ℝ) :
    ∏ r : Fin k, f (d r) = ∏ j : β, (f j) ^ (tupleHist d j) := by
  have huniv : (Finset.univ : Finset (Fin k)) =
      Finset.univ.biUnion (fun j : β => Finset.univ.filter (fun r : Fin k => d r = j)) := by
    ext r
    simp
  have hdisj : ((Finset.univ : Finset β) : Set β).PairwiseDisjoint
      (fun j : β => Finset.univ.filter (fun r : Fin k => d r = j)) := by
    intro j₁ _ j₂ _ hne
    exact Finset.disjoint_left.mpr fun r hr₁ hr₂ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr₁ hr₂
      exact hne (hr₁.symm.trans hr₂)
  conv_lhs => rw [huniv]
  rw [Finset.prod_biUnion hdisj]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hconst : ∀ r ∈ Finset.univ.filter (fun r : Fin k => d r = j), f (d r) = f j := by
    intro r hr
    rw [(Finset.mem_filter.mp hr).2]
  rw [Finset.prod_congr rfl hconst, Finset.prod_const, tupleHist]

private lemma sum_prod_pi_eq_pow {β : Type*} [Fintype β] (f : β → ℝ) :
    ∀ k : ℕ, (∑ d : Fin k → β, ∏ r : Fin k, f (d r)) = (∑ j : β, f j) ^ k := by
  intro k
  induction k with
  | zero =>
    have huniq : (Finset.univ : Finset (Fin 0 → β)).card = 1 := by simp
    rcases Finset.card_eq_one.mp huniq with ⟨d₀, hd₀⟩
    rw [hd₀, Finset.sum_singleton, Finset.univ_eq_empty, Finset.prod_empty, pow_zero]
  | succ k ih =>
    let e : (β × (Fin k → β)) ≃ (Fin (k + 1) → β) :=
      { toFun := fun p => Fin.cases p.1 p.2
        invFun := fun d => (d 0, fun i => d i.succ)
        left_inv := fun ⟨b, d'⟩ => by
          ext <;> simp
        right_inv := fun d => by
          funext r
          cases r using Fin.cases <;> simp }
    rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
    have hstep : ∀ b : β,
        (∑ d' : Fin k → β, ∏ r : Fin (k + 1), f (e (b, d') r)) =
          f b * (∑ j : β, f j) ^ k := by
      intro b
      have hprod : ∀ d' : Fin k → β,
          (∏ r : Fin (k + 1), f (e (b, d') r)) = f b * ∏ i : Fin k, f (d' i) := by
        intro d'
        rw [Fin.prod_univ_succ]
        simp [e]
      simp_rw [hprod, ← Finset.mul_sum, ih]
    simp_rw [hstep, ← Finset.sum_mul, pow_succ']

/-- **Exact Stirling-free multinomial entropy upper bound**:
For `1 ≤ k` and any histogram `m : β → ℕ` with `∑ j, m j = k`, setting `p j = m j / k`,
`#{d : Fin k → β | tupleHist d = m} ≤ exp(∑ j, if p j = 0 then 0 else - m j * log(p j))`. -/
theorem card_tuples_with_hist_le_exp {k : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    (hk : 1 ≤ k) (m : β → ℕ) (hsum : ∑ j : β, m j = k) :
    let p : β → ℝ := fun j => (m j : ℝ) / (k : ℝ);
    ((Finset.univ.filter (fun d : Fin k → β => tupleHist d = m)).card : ℝ) ≤
      Real.exp (∑ j : β, if p j = 0 then 0 else -(m j : ℝ) * Real.log (p j)) := by
  intro p
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hp_nonneg : ∀ j : β, 0 ≤ p j := fun j => div_nonneg (Nat.cast_nonneg _) hk_pos.le
  have hp_sum : ∑ j : β, p j = 1 := by
    dsimp [p]
    rw [← Finset.sum_div, ← Nat.cast_sum, hsum, div_self hk_pos.ne']
  let H : Finset (Fin k → β) := Finset.univ.filter (fun d : Fin k → β => tupleHist d = m)
  let E : ℝ := ∑ j : β, if p j = 0 then 0 else -(m j : ℝ) * Real.log (p j)
  have hprod_inv : (∏ j : β, (p j) ^ (m j)) * Real.exp E = 1 := by
    dsimp [E]
    rw [Real.exp_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun j _ => ?_
    by_cases hmj : m j = 0
    · have hp0 : p j = 0 := by simp [p, hmj]
      simp [hmj, hp0]
    · have hp_pos : 0 < p j := div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hmj)) hk_pos
      simp only [hp_pos.ne', ↓reduceIte]
      have hpow : (p j) ^ (m j) = Real.exp ((m j : ℝ) * Real.log (p j)) := by
        rw [Real.exp_nat_mul, Real.exp_log hp_pos]
      rw [hpow, ← Real.exp_add]
      ring_nf
      exact Real.exp_zero
  have hH_sum : (H.card : ℝ) * (∏ j : β, (p j) ^ (m j)) ≤ 1 := by
    have hconst : ∑ d ∈ H, ∏ r : Fin k, p (d r) = (H.card : ℝ) * (∏ j : β, (p j) ^ (m j)) := by
      have heach : ∀ d ∈ H, (∏ r : Fin k, p (d r)) = ∏ j : β, (p j) ^ (m j) := by
        intro d hd
        rw [prod_comp_eq_prod_tupleHist, (Finset.mem_filter.mp hd).2]
      rw [Finset.sum_congr rfl heach, Finset.sum_const, nsmul_eq_mul]
    rw [← hconst]
    calc
      ∑ d ∈ H, ∏ r : Fin k, p (d r)
          ≤ ∑ d : Fin k → β, ∏ r : Fin k, p (d r) :=
        Finset.sum_le_univ_sum_of_nonneg fun d => Finset.prod_nonneg fun r _ => hp_nonneg (d r)
      _ = (∑ j : β, p j) ^ k := sum_prod_pi_eq_pow p k
      _ = 1 := by rw [hp_sum, one_pow]
  calc
    (H.card : ℝ) = ((H.card : ℝ) * (∏ j : β, (p j) ^ (m j))) * Real.exp E := by
      rw [mul_assoc, hprod_inv, mul_one]
    _ ≤ 1 * Real.exp E := mul_le_mul_of_nonneg_right hH_sum (Real.exp_pos E).le
    _ = Real.exp E := one_mul _

/-! ### 5. Subcritical First-Moment Decay at `kChiMinus n` and Main Part B Theorem -/

private def validDeficitHists (α k n : ℕ) : Finset (Fin (α + 2) → ℕ) :=
  (Fintype.piFinset (fun _ : Fin (α + 2) => Finset.range (k + 1))).filter (fun m =>
    (∑ j : Fin (α + 2), m j = k) ∧
    (∑ j : Fin (α + 2), m j * (α + 1 - j.val) = n))

private lemma pow_sum_fin {ι : Type*} (s : Finset ι) (a : ℝ) (g : ι → ℕ) :
    a ^ (∑ i ∈ s, g i) = ∏ i ∈ s, a ^ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    rw [Finset.sum_insert hx, pow_add, Finset.prod_insert hx, ih]

/-- Normalized first moment of capped proper `k`-colorings is bounded by the sum over valid
deficit histograms. -/
lemma normalized_cappedProper_le_hist_sum {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (hα1 : 1 ≤ alphaNat n) :
    let α := alphaNat n;
    let s_k := (n : ℝ) / (k : ℝ);
    let T_k := (α : ℝ) - s_k;
    expectGnpHalf n (cappedProperCount n k) / (k ! : ℝ) ≤
      ((validDeficitHists α k n).card : ℝ) *
        Real.exp ((k : ℝ) * (profileBasePhi n s_k + freeEnergyPlus T_k) +
          Real.log (n : ℝ) + 1) := by
  intro α s_k T_k
  have hn1 : 1 ≤ n := hk1.trans hkn
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hs_k_pos : 0 < s_k := div_pos hn_pos hk_pos
  set L : ℝ := Real.log (n : ℝ)
  set q : ℝ := Real.log 2
  let tupOf : (Fin n → Fin k) → (Fin k → Fin (α + 2)) :=
    fun c r => deficitIdx α (coloringFiber c r).card
  let mapToHist : (Fin n → Fin k) → (Fin (α + 2) → ℕ) :=
    fun c => tupleHist (tupOf c)
  have hmaps : ∀ c ∈ cappedColorings n k, mapToHist c ∈ validDeficitHists α k n := by
    intro c hc
    have hcap : ∀ r : Fin k, (coloringFiber c r).card ≤ α + 1 :=
      (Finset.mem_filter.mp hc).2
    have hfib_eq : ∀ r : Fin k, α + 1 - (tupOf c r).val = (coloringFiber c r).card := by
      intro r
      have hr := hcap r
      dsimp [tupOf, deficitIdx]
      omega
    have hsum_k : ∑ j : Fin (α + 2), mapToHist c j = k := by
      have h1 := sum_comp_eq_sum_tupleHist (tupOf c) (fun _ => 1)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h1
      exact h1.symm
    have hsum_n : ∑ j : Fin (α + 2), mapToHist c j * (α + 1 - j.val) = n := by
      rw [← sum_comp_eq_sum_tupleHist (tupOf c) (fun j => α + 1 - j.val)]
      simp_rw [hfib_eq]
      simpa using sum_card_coloringFiber c
    rw [validDeficitHists, Finset.mem_filter]
    refine ⟨Fintype.mem_piFinset.mpr fun j => Finset.mem_range.mpr ?_, hsum_k, hsum_n⟩
    have hle_k : mapToHist c j ≤ k := by
      rw [← hsum_k]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  -- Slice `expectGnpHalf n (cappedProperCount n k)` over `m ∈ validDeficitHists α k n`
  have hbiUnion : cappedColorings n k =
      (validDeficitHists α k n).biUnion
        (fun m => (cappedColorings n k).filter (fun c => mapToHist c = m)) := by
    ext c
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    exact ⟨fun hc => ⟨mapToHist c, hmaps c hc, hc, rfl⟩,
      fun ⟨_, _, hc, _⟩ => hc⟩
  have hdisj_m : (validDeficitHists α k n : Set (Fin (α + 2) → ℕ)).PairwiseDisjoint
      (fun m => (cappedColorings n k).filter (fun c => mapToHist c = m)) := by
    intro m₁ _ m₂ _ hne
    exact Finset.disjoint_left.mpr fun c hc₁ hc₂ =>
      hne ((Finset.mem_filter.mp hc₁).2.symm.trans (Finset.mem_filter.mp hc₂).2)
  rw [expectGnpHalf_cappedProperCount, hbiUnion, Finset.sum_biUnion hdisj_m, Finset.sum_div]
  -- Bound each histogram slice by `Real.exp ((k : ℝ) * (profileBasePhi n s_k + freeEnergyPlus T_k) + L + 1)`
  have hslice_le : ∀ m ∈ validDeficitHists α k n,
      (∑ c ∈ (cappedColorings n k).filter (fun c => mapToHist c = m),
        (2⁻¹ : ℝ) ^ (∑ r : Fin k, (coloringFiber c r).card.choose 2)) / (k ! : ℝ) ≤
      Real.exp ((k : ℝ) * (profileBasePhi n s_k + freeEnergyPlus T_k) + L + 1) := by
    intro m hm
    have hm_spec := (Finset.mem_filter.mp hm).2
    have hm_sum_k : ∑ j : Fin (α + 2), m j = k := hm_spec.1
    have hm_sum_n : ∑ j : Fin (α + 2), m j * (α + 1 - j.val) = n := hm_spec.2
    let H_m : Finset (Fin k → Fin (α + 2)) :=
      Finset.univ.filter (fun d : Fin k → Fin (α + 2) => tupleHist d = m)
    -- Sub-slice by `d = tupOf c ∈ H_m`
    have hsub_d : (cappedColorings n k).filter (fun c => mapToHist c = m) =
        H_m.biUnion (fun d =>
          ((cappedColorings n k).filter (fun c => mapToHist c = m)).filter (fun c => tupOf c = d)) := by
      ext c
      simp only [Finset.mem_biUnion, Finset.mem_filter, H_m, Finset.mem_univ, true_and]
      exact ⟨fun hc => ⟨tupOf c, hc.2, hc, rfl⟩, fun ⟨_, _, hc, _⟩ => hc⟩
    have hdisj_d : (H_m : Set (Fin k → Fin (α + 2))).PairwiseDisjoint (fun d =>
        ((cappedColorings n k).filter (fun c => mapToHist c = m)).filter (fun c => tupOf c = d)) := by
      intro d₁ _ d₂ _ hne
      exact Finset.disjoint_left.mpr fun c hc₁ hc₂ =>
        hne ((Finset.mem_filter.mp hc₁).2.symm.trans (Finset.mem_filter.mp hc₂).2)
    let w : Fin (α + 2) → ℝ := fun j =>
      (((α + 1 - j.val) ! : ℝ))⁻¹ * (2⁻¹ : ℝ) ^ ((α + 1 - j.val).choose 2)
    have hd_bound : ∀ d ∈ H_m,
        (∑ c ∈ ((cappedColorings n k).filter (fun c => mapToHist c = m)).filter
          (fun c => tupOf c = d),
          (2⁻¹ : ℝ) ^ (∑ r : Fin k, (coloringFiber c r).card.choose 2)) ≤
        (n ! : ℝ) * ∏ j : Fin (α + 2), (w j) ^ (m j) := by
      intro d hd
      have hd_hist : tupleHist d = m := (Finset.mem_filter.mp hd).2
      let C_d := ((cappedColorings n k).filter (fun c => mapToHist c = m)).filter
        (fun c => tupOf c = d)
      have hc_fib : ∀ c ∈ C_d, ∀ r : Fin k, (coloringFiber c r).card = α + 1 - (d r).val := by
        intro c hc r
        have hc_cap : (coloringFiber c r).card ≤ α + 1 :=
          (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1).2 r
        have hcd : tupOf c r = d r := congrFun (Finset.mem_filter.mp hc).2 r
        have hval : (d r).val = α + 1 - (coloringFiber c r).card := by
          rw [← hcd]
          dsimp [tupOf, deficitIdx]
          omega
        omega
      have hconst_c : ∀ c ∈ C_d,
          (2⁻¹ : ℝ) ^ (∑ r : Fin k, (coloringFiber c r).card.choose 2) =
          ∏ r : Fin k, (2⁻¹ : ℝ) ^ ((α + 1 - (d r).val).choose 2) := by
        intro c hc
        rw [pow_sum_fin]
        refine Finset.prod_congr rfl fun r _ => ?_
        rw [hc_fib c hc r]
      rw [Finset.sum_congr rfl hconst_c, Finset.sum_const, nsmul_eq_mul]
      have hcard_Cd : (C_d.card : ℝ) ≤ (n ! : ℝ) * ∏ r : Fin k, (((α + 1 - (d r).val) ! : ℝ))⁻¹ := by
        have hsub_full : C_d ⊆ Finset.univ.filter
            (fun c : Fin n → Fin k => ∀ r : Fin k, (coloringFiber c r).card = α + 1 - (d r).val) :=
          fun c hc => Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc_fib c hc⟩
        have hnat : C_d.card * (∏ r : Fin k, (α + 1 - (d r).val) !) ≤ n ! := by
          calc
            C_d.card * (∏ r : Fin k, (α + 1 - (d r).val) !)
                ≤ (Finset.univ.filter (fun c : Fin n → Fin k =>
                    ∀ r : Fin k, (coloringFiber c r).card = α + 1 - (d r).val)).card *
                  (∏ r : Fin k, (α + 1 - (d r).val) !) :=
              Nat.mul_le_mul_right _ (Finset.card_le_card hsub_full)
            _ ≤ (Fintype.card (Fin n)) ! :=
              card_colorings_with_fiber_sizes k (fun r => α + 1 - (d r).val)
            _ = n ! := by simp
        have hprod_pos : (0 : ℝ) < ∏ r : Fin k, ((α + 1 - (d r).val) ! : ℝ) :=
          Finset.prod_pos fun r _ => Nat.cast_pos.mpr (Nat.factorial_pos _)
        have hreal : (C_d.card : ℝ) * (∏ r : Fin k, ((α + 1 - (d r).val) ! : ℝ)) ≤ (n ! : ℝ) := by
          exact_mod_cast hnat
        rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, le_div_iff₀ hprod_pos]
        exact hreal
      calc
        (C_d.card : ℝ) * (∏ r : Fin k, (2⁻¹ : ℝ) ^ ((α + 1 - (d r).val).choose 2))
            ≤ ((n ! : ℝ) * ∏ r : Fin k, (((α + 1 - (d r).val) ! : ℝ))⁻¹) *
              (∏ r : Fin k, (2⁻¹ : ℝ) ^ ((α + 1 - (d r).val).choose 2)) :=
          mul_le_mul_of_nonneg_right hcard_Cd
            (Finset.prod_nonneg fun _ _ => by positivity)
        _ = (n ! : ℝ) * ∏ r : Fin k, w (d r) := by
          rw [mul_assoc, ← Finset.prod_mul_distrib]
        _ = (n ! : ℝ) * ∏ j : Fin (α + 2), (w j) ^ (m j) := by
          rw [prod_comp_eq_prod_tupleHist, hd_hist]
    have hsum_m_le :
        (∑ c ∈ (cappedColorings n k).filter (fun c => mapToHist c = m),
          (2⁻¹ : ℝ) ^ (∑ r : Fin k, (coloringFiber c r).card.choose 2)) / (k ! : ℝ) ≤
        ((n ! : ℝ) / (k ! : ℝ)) * (H_m.card : ℝ) * ∏ j : Fin (α + 2), (w j) ^ (m j) := by
      rw [hsub_d, Finset.sum_biUnion hdisj_d]
      have h1 : ∑ d ∈ H_m,
          (∑ c ∈ ((cappedColorings n k).filter (fun c => mapToHist c = m)).filter
            (fun c => tupOf c = d),
            (2⁻¹ : ℝ) ^ (∑ r : Fin k, (coloringFiber c r).card.choose 2)) ≤
          (H_m.card : ℝ) * ((n ! : ℝ) * ∏ j : Fin (α + 2), (w j) ^ (m j)) := by
        calc
          _ ≤ ∑ _ ∈ H_m, ((n ! : ℝ) * ∏ j : Fin (α + 2), (w j) ^ (m j)) :=
            Finset.sum_le_sum hd_bound
          _ = (H_m.card : ℝ) * ((n ! : ℝ) * ∏ j : Fin (α + 2), (w j) ^ (m j)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      have hfac_pos : (0 : ℝ) < (k ! : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
      calc
        _ ≤ ((H_m.card : ℝ) * ((n ! : ℝ) * ∏ j : Fin (α + 2), (w j) ^ (m j))) / (k ! : ℝ) :=
          div_le_div_of_nonneg_right h1 hfac_pos.le
        _ = ((n ! : ℝ) / (k ! : ℝ)) * (H_m.card : ℝ) * ∏ j : Fin (α + 2), (w j) ^ (m j) := by
          ring
    -- Convert factors to `Real.exp` and bound the exponent
    let p : Fin (α + 2) → ℝ := fun j => (m j : ℝ) / (k : ℝ)
    have hHm_exp : (H_m.card : ℝ) ≤
        Real.exp (∑ j : Fin (α + 2), if p j = 0 then 0 else -(m j : ℝ) * Real.log (p j)) :=
      card_tuples_with_hist_le_exp hk1 m hm_sum_k
    have hnfac_pos : (0 : ℝ) < (n ! : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
    have hkfac_pos : (0 : ℝ) < (k ! : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
    have hfac_ratio : (n ! : ℝ) / (k ! : ℝ) =
        Real.exp (Real.log (n ! : ℝ) - Real.log (k ! : ℝ)) := by
      rw [Real.exp_sub, Real.exp_log hnfac_pos, Real.exp_log hkfac_pos]
    have hw_exp : ∏ j : Fin (α + 2), (w j) ^ (m j) =
        Real.exp (∑ j : Fin (α + 2),
          (m j : ℝ) * (-Real.log ((α + 1 - j.val) ! : ℝ) -
            q * ((α + 1 - j.val).choose 2 : ℝ))) := by
      rw [Real.exp_sum]
      refine Finset.prod_congr rfl fun j _ => ?_
      have hsf_pos : (0 : ℝ) < ((α + 1 - j.val) ! : ℝ) :=
        Nat.cast_pos.mpr (Nat.factorial_pos _)
      have hwj : w j = Real.exp (-Real.log ((α + 1 - j.val) ! : ℝ) -
          q * ((α + 1 - j.val).choose 2 : ℝ)) := by
        dsimp [w, q]
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg, Real.exp_log hsf_pos]
        congr 1
        rw [show -(Real.log 2 * (((α + 1 - j.val).choose 2 : ℝ))) =
            (((α + 1 - j.val).choose 2 : ℕ) : ℝ) * Real.log (2⁻¹) by
              rw [Real.log_inv]; ring,
          Real.exp_nat_mul, Real.exp_log (by norm_num)]
      rw [hwj, ← Real.exp_nat_mul]
    have hprod_exp_le : ((n ! : ℝ) / (k ! : ℝ)) * (H_m.card : ℝ) *
        (∏ j : Fin (α + 2), (w j) ^ (m j)) ≤
        Real.exp ((Real.log (n ! : ℝ) - Real.log (k ! : ℝ)) +
          (∑ j : Fin (α + 2), if p j = 0 then 0 else -(m j : ℝ) * Real.log (p j)) +
          (∑ j : Fin (α + 2),
            (m j : ℝ) * (-Real.log ((α + 1 - j.val) ! : ℝ) -
              q * ((α + 1 - j.val).choose 2 : ℝ)))) := by
      calc
        ((n ! : ℝ) / (k ! : ℝ)) * (H_m.card : ℝ) * (∏ j : Fin (α + 2), (w j) ^ (m j))
            ≤ Real.exp (Real.log (n ! : ℝ) - Real.log (k ! : ℝ)) *
                Real.exp (∑ j : Fin (α + 2),
                  if p j = 0 then 0 else -(m j : ℝ) * Real.log (p j)) *
                Real.exp (∑ j : Fin (α + 2),
                  (m j : ℝ) * (-Real.log ((α + 1 - j.val) ! : ℝ) -
                    q * ((α + 1 - j.val).choose 2 : ℝ))) := by
          rw [← hfac_ratio, ← hw_exp]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hHm_exp (by positivity))
            (Finset.prod_nonneg fun _ _ => by positivity)
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
    refine hsum_m_le.trans (hprod_exp_le.trans (Real.exp_le_exp.mpr ?_))
    -- 1. Bound `log(n!) - log(k!)`
    have hlog_n : Real.log (n ! : ℝ) ≤ (n : ℝ) * L - (n : ℝ) + L + 1 := by
      have hst := (log_factorial_bounds hn1).2
      have hL0 : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hn1)
      change Real.log (n ! : ℝ) ≤ (n : ℝ) * L - (n : ℝ) + L / 2 + 1 at hst
      linarith only [hst, hL0]
    have hlog_k_eq : Real.log (k : ℝ) = L - Real.log s_k := by
      have hk_eq : (k : ℝ) = (n : ℝ) / s_k := by
        dsimp [s_k]
        rw [div_div_cancel₀ hn_pos.ne']
      rw [hk_eq, Real.log_div hn_pos.ne' hs_k_pos.ne']
    have hlog_k : (k : ℝ) * (L - Real.log s_k - 1) ≤ Real.log (k ! : ℝ) := by
      have hst := (log_factorial_bounds hk1).1
      have hk0 : 0 ≤ Real.log (k : ℝ) / 2 :=
        div_nonneg (Real.log_nonneg (by exact_mod_cast hk1)) (by norm_num)
      have hst' : (k : ℝ) * Real.log (k : ℝ) - (k : ℝ) ≤ Real.log (k ! : ℝ) := by
        linarith only [hst, hk0]
      rw [hlog_k_eq] at hst'
      have hid : (k : ℝ) * (L - Real.log s_k - 1) = (k : ℝ) * (L - Real.log s_k) - (k : ℝ) := by
        ring
      linarith only [hst', hid]
    -- 2. Apply `falling_shift_upper_all` to each `j : Fin (α + 2)`
    have hfall_sum :
        (∑ j : Fin (α + 2),
          (m j : ℝ) * (-Real.log ((α + 1 - j.val) ! : ℝ) -
            q * ((α + 1 - j.val).choose 2 : ℝ))) ≤
        (k : ℝ) * (-Real.log (α ! : ℝ) - q * (α.choose 2 : ℝ)) +
          ((k : ℝ) * T_k) * (q * (α : ℝ) - q / 2 + Real.log (α : ℝ)) +
          ∑ j : Fin (α + 2), (m j : ℝ) * (-(q / 2) * ((j.val : ℝ) - 1) ^ 2) := by
      have hterm : ∀ j : Fin (α + 2),
          (m j : ℝ) * (-Real.log ((α + 1 - j.val) ! : ℝ) -
            q * ((α + 1 - j.val).choose 2 : ℝ)) ≤
          (m j : ℝ) * (-Real.log (α ! : ℝ) - q * (α.choose 2 : ℝ)) +
            ((m j : ℝ) * ((j.val : ℝ) - 1)) * (q * (α : ℝ) - q / 2 + Real.log (α : ℝ)) +
            (m j : ℝ) * (-(q / 2) * ((j.val : ℝ) - 1) ^ 2) := by
        intro j
        have hf := falling_shift_upper_all hα1 (Nat.lt_succ_iff.mp j.isLt)
        change -Real.log ((α + 1 - j.val) ! : ℝ) - q * ((α + 1 - j.val).choose 2 : ℝ) ≤
          -Real.log (α ! : ℝ) - q * (α.choose 2 : ℝ) +
            ((j.val : ℝ) - 1) * (q * (α : ℝ) - q / 2 + Real.log (α : ℝ)) -
            (q / 2) * ((j.val : ℝ) - 1) ^ 2 at hf
        have hm_mul := mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg (m j))
        linarith
      have hsum1 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm j
      have hm_k_real : ∑ j : Fin (α + 2), (m j : ℝ) = (k : ℝ) := by exact_mod_cast hm_sum_k
      have hm_def_real : ∑ j : Fin (α + 2), (m j : ℝ) * ((j.val : ℝ) - 1) = (k : ℝ) * T_k := by
        have hm_n_real : ∑ j : Fin (α + 2), (m j : ℝ) * ((α + 1 - j.val : ℕ) : ℝ) = (n : ℝ) := by
          exact_mod_cast hm_sum_n
        have hj_id : ∀ j : Fin (α + 2),
            (m j : ℝ) * ((j.val : ℝ) - 1) =
              (m j : ℝ) * (α : ℝ) - (m j : ℝ) * ((α + 1 - j.val : ℕ) : ℝ) := by
          intro j
          have hj_le : j.val ≤ α + 1 := Nat.lt_succ_iff.mp j.isLt
          rw [Nat.cast_sub hj_le]
          push_cast
          ring
        simp_rw [hj_id, Finset.sum_sub_distrib, ← Finset.sum_mul, hm_k_real, hm_n_real]
        dsimp [T_k, s_k]
        rw [mul_sub, mul_div_cancel₀ _ hk_pos.ne']
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
        hm_k_real, hm_def_real] at hsum1
      exact hsum1
    -- 3. Apply `gibbs_upper_bound_plus` on `Finset.range (α + 2)`
    let pNat : ℕ → ℝ := fun t => if ht : t < α + 2 then p ⟨t, ht⟩ else 0
    have hpNat_val : ∀ j : Fin (α + 2), pNat j.val = p j := fun j => by
      simp [pNat, j.isLt]
    have hpNat_nonneg : ∀ t ∈ Finset.range (α + 2), 0 ≤ pNat t := by
      intro t ht
      have ht' : t < α + 2 := Finset.mem_range.mp ht
      simp only [pNat, ht', ↓reduceDIte, p]
      exact div_nonneg (Nat.cast_nonneg _) hk_pos.le
    have hpNat_sum : ∑ t ∈ Finset.range (α + 2), pNat t = 1 := by
      rw [← Fin.sum_univ_eq_sum_range]
      simp_rw [hpNat_val]
      dsimp [p]
      rw [← Finset.sum_div, ← Nat.cast_sum, hm_sum_k, div_self hk_pos.ne']
    have hpNat_mean : ∑ t ∈ Finset.range (α + 2), ((t : ℝ) - 1) * pNat t = T_k := by
      rw [← Fin.sum_univ_eq_sum_range]
      simp_rw [hpNat_val]
      have hm_n_real : ∑ j : Fin (α + 2), (m j : ℝ) * ((α + 1 - j.val : ℕ) : ℝ) = (n : ℝ) := by
        exact_mod_cast hm_sum_n
      have hm_k_real : ∑ j : Fin (α + 2), (m j : ℝ) = (k : ℝ) := by exact_mod_cast hm_sum_k
      have hj_id : ∀ j : Fin (α + 2),
          ((j.val : ℝ) - 1) * p j =
            ((m j : ℝ) * (α : ℝ) - (m j : ℝ) * ((α + 1 - j.val : ℕ) : ℝ)) / (k : ℝ) := by
        intro j
        have hj_le : j.val ≤ α + 1 := Nat.lt_succ_iff.mp j.isLt
        dsimp [p]
        rw [Nat.cast_sub hj_le]
        push_cast
        ring
      simp_rw [hj_id, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul,
        hm_k_real, hm_n_real]
      dsimp [T_k, s_k]
      rw [sub_div, mul_div_cancel_left₀ _ hk_pos.ne']
    have hgibbs :
        (∑ j : Fin (α + 2), if p j = 0 then 0 else -(m j : ℝ) * Real.log (p j)) +
          (∑ j : Fin (α + 2), (m j : ℝ) * (-(q / 2) * ((j.val : ℝ) - 1) ^ 2)) ≤
        (k : ℝ) * freeEnergyPlus T_k := by
      have hg := gibbs_upper_bound_plus (Finset.range (α + 2)) pNat hpNat_nonneg hpNat_sum
      rw [hpNat_mean, ← Fin.sum_univ_eq_sum_range] at hg
      have hmul_g := mul_le_mul_of_nonneg_left hg hk_pos.le
      rw [Finset.mul_sum] at hmul_g
      have hterm_eq : ∀ j : Fin (α + 2),
          (if p j = 0 then 0 else -(m j : ℝ) * Real.log (p j)) +
            (m j : ℝ) * (-(q / 2) * ((j.val : ℝ) - 1) ^ 2) =
          (k : ℝ) * (if pNat j.val = 0 then 0
            else pNat j.val * (-(Real.log 2 / 2) * ((j.val : ℝ) - 1) ^ 2 -
              Real.log (pNat j.val))) := by
        intro j
        rw [hpNat_val j]
        by_cases hmj : m j = 0
        · have hp0 : p j = 0 := by simp [p, hmj]
          simp [hmj, hp0]
        · have hp_ne : p j ≠ 0 := div_ne_zero (Nat.cast_ne_zero.mpr hmj) hk_pos.ne'
          simp only [hp_ne, ↓reduceIte]
          have hmk : (m j : ℝ) = (k : ℝ) * p j := by
            dsimp [p]
            rw [mul_div_cancel₀ _ hk_pos.ne']
          rw [hmk]
          dsimp [q]
          ring
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun j _ => hterm_eq j]
      exact hmul_g
    -- 4. Combine with `profileBasePhi n s_k`
    have hn_eq_ks : (n : ℝ) = (k : ℝ) * s_k := by
      dsimp [s_k]
      rw [mul_div_cancel₀ _ hk_pos.ne']
    have hphi_id :
        ((n : ℝ) * L - (n : ℝ)) - (k : ℝ) * (L - Real.log s_k - 1) +
          (k : ℝ) * (-Real.log (α ! : ℝ) - q * (α.choose 2 : ℝ)) +
          ((k : ℝ) * T_k) * (q * (α : ℝ) - q / 2 + Real.log (α : ℝ)) =
        (k : ℝ) * profileBasePhi n s_k := by
      have hbase : profileBasePhi n s_k =
          (s_k * L - s_k - L + Real.log s_k + 1) -
            Real.log (α ! : ℝ) - q * (α.choose 2 : ℝ) +
            ((α : ℝ) - s_k) * (q * (α : ℝ) - q / 2 + Real.log (α : ℝ)) := rfl
      rw [hbase, hn_eq_ks]
      dsimp [T_k]
      ring
    linarith only [hlog_n, hlog_k, hfall_sum, hgibbs, hphi_id]
  calc
    ∑ m ∈ validDeficitHists α k n,
        (∑ c ∈ (cappedColorings n k).filter (fun c => mapToHist c = m),
          (2⁻¹ : ℝ) ^ (∑ r : Fin k, (coloringFiber c r).card.choose 2)) / (k ! : ℝ)
        ≤ ∑ _ ∈ validDeficitHists α k n,
            Real.exp ((k : ℝ) * (profileBasePhi n s_k + freeEnergyPlus T_k) + L + 1) :=
      Finset.sum_le_sum hslice_le
    _ = ((validDeficitHists α k n).card : ℝ) *
          Real.exp ((k : ℝ) * (profileBasePhi n s_k + freeEnergyPlus T_k) + L + 1) := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- The intersection probability `ℙ(G.Colorable (kChiMinus n) ∧ IndepCapEvent n)` tends to `0`. -/
theorem tendsto_probGnpHalf_colorable_kChiMinus_inter_indepCap_zero :
    Tendsto
      (fun n : ℕ => probGnpHalf n ({G | G.Colorable (kChiMinus n)} ∩ IndepCapEvent n))
      atTop (𝓝 0) := by
  have hL : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hexp0 : Tendsto (fun n : ℕ => Real.exp (-Real.log (n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hL)
  refine squeeze_zero'
    (f := fun n : ℕ => probGnpHalf n ({G | G.Colorable (kChiMinus n)} ∩ IndepCapEvent n))
    (g := fun n : ℕ => Real.exp (-Real.log (n : ℝ))) ?_ ?_ hexp0
  · filter_upwards with n
    exact probGnpHalf_nonneg n _
  · filter_upwards [eventually_alphaNat_regime, eventually_kChiMinus_subcritical,
      hL.eventually_ge_atTop 100,
      (tendsto_nat_div_log_pow_atTop 4).eventually_ge_atTop 10] with
        n ⟨hn16, hα20, _, _, _, hhi⟩ ⟨hk1, hkn, _, hsubcrit⟩ hL100 hnL4
    set α : ℕ := alphaNat n
    set k : ℕ := kChiMinus n
    set L : ℝ := Real.log (n : ℝ)
    have hL100' : (100 : ℝ) ≤ L := hL100
    have hnL4' : (10 : ℝ) ≤ (n : ℝ) / L ^ 4 := hnL4
    have hL_pos : 0 < L := by linarith only [hL100']
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hα1 : 1 ≤ α := by omega
    -- 1. Bound `(validDeficitHists α k n).card ≤ exp(12 * L^2)`
    have hcard_nat : (validDeficitHists α k n).card ≤ (n + 1) ^ (α + 2) := by
      calc
        (validDeficitHists α k n).card
            ≤ (Fintype.piFinset (fun _ : Fin (α + 2) => Finset.range (k + 1))).card :=
          Finset.card_filter_le _ _
        _ = (k + 1) ^ (α + 2) := by
          rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_range,
            Finset.card_univ, Fintype.card_fin]
        _ ≤ (n + 1) ^ (α + 2) := Nat.pow_le_pow_left (by omega) _
    have hcard_exp : ((validDeficitHists α k n).card : ℝ) ≤ Real.exp (12 * L ^ 2) := by
      have hn1_sq : ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
        have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
        push_cast
        nlinarith
      have hpow_le : (((n + 1 : ℕ) ^ (α + 2) : ℕ) : ℝ) ≤ Real.exp (2 * ((α + 2 : ℕ) : ℝ) * L) := by
        calc
          (((n + 1 : ℕ) ^ (α + 2) : ℕ) : ℝ)
              = ((n + 1 : ℕ) : ℝ) ^ (α + 2) := Nat.cast_pow _ _
          _ ≤ ((n : ℝ) ^ 2) ^ (α + 2) := pow_le_pow_left₀ (by positivity) hn1_sq _
          _ = (n : ℝ) ^ (2 * (α + 2)) := (pow_mul (n : ℝ) 2 (α + 2)).symm
          _ = Real.exp (((2 * (α + 2) : ℕ) : ℝ) * L) := by
            rw [Real.exp_nat_mul, Real.exp_log hn_pos]
          _ = Real.exp (2 * ((α + 2 : ℕ) : ℝ) * L) := by push_cast; rfl
      have hα_le_5L : (α : ℝ) ≤ 5 * L := by
        have hq_gt : (0.69 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
        have hα_nonneg : (0 : ℝ) ≤ (α : ℝ) := Nat.cast_nonneg α
        have hm := mul_le_mul_of_nonneg_right hq_gt.le hα_nonneg
        have hhi' : Real.log 2 * (α : ℝ) ≤ 2 * L := hhi
        linarith only [hm, hhi', hL_pos]
      have hexp_12 : 2 * ((α + 2 : ℕ) : ℝ) * L ≤ 12 * L ^ 2 := by
        push_cast
        nlinarith only [hα_le_5L, hL100']
      exact (Nat.cast_le.mpr hcard_nat).trans (hpow_le.trans (Real.exp_le_exp.mpr hexp_12))
    -- 2. Combine `probGnpHalf_colorable_inter_indepCap_le`, `normalized_cappedProper_le_hist_sum`,
    --    and `hsubcrit`
    have hstep1 := probGnpHalf_colorable_inter_indepCap_le hkn
    have hstep2 := normalized_cappedProper_le_hist_sum hk1 hkn hα1
    have hnL2_ge : 10 * L ^ 2 ≤ (n : ℝ) / L ^ 2 := by
      have hn_ge : 10 * L ^ 4 ≤ (n : ℝ) := (le_div_iff₀ (by positivity)).mp hnL4'
      rw [le_div_iff₀ (by positivity)]
      calc
        10 * L ^ 2 * L ^ 2 = 10 * L ^ 4 := by ring
        _ ≤ (n : ℝ) := hn_ge
    calc
      probGnpHalf n ({G | G.Colorable k} ∩ IndepCapEvent n)
          ≤ expectGnpHalf n (cappedProperCount n k) / (k ! : ℝ) := hstep1
      _ ≤ ((validDeficitHists α k n).card : ℝ) *
            Real.exp ((k : ℝ) * (profileBasePhi n ((n : ℝ) / (k : ℝ)) +
              freeEnergyPlus ((α : ℝ) - (n : ℝ) / (k : ℝ))) + L + 1) := hstep2
      _ ≤ Real.exp (12 * L ^ 2) * Real.exp (-50 * (n : ℝ) / L ^ 2 + L + 1) := by
        refine mul_le_mul hcard_exp (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (Real.exp_pos _).le
        linarith only [hsubcrit]
      _ = Real.exp (12 * L ^ 2 - 50 * ((n : ℝ) / L ^ 2) + L + 1) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-L) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [hnL2_ge, hL100']

/-- **Part B Main Theorem (`arXiv:2608.30604`, Section 5 / Proposition 5.1)**:
With probability tending to `1` as `n → ∞` in `G(n, 1/2)`, `χ(G_n) > k_χ^-(n)`. -/
theorem tendsto_probGnpHalf_chromatic_gt_kChiMinus :
    Tendsto
      (fun n : ℕ => probGnpHalf n
        {G : SimpleGraph (Fin n) | kChiMinus n < G.chromaticNumber.toNat})
      atTop (𝓝 1) := by
  apply tendsto_probGnpHalf_one_of_compl_tendsto_zero
  have hcap_compl : Tendsto (fun n : ℕ => probGnpHalf n (IndepCapEvent n)ᶜ) atTop (𝓝 0) := by
    have h1 : (fun n : ℕ => probGnpHalf n (IndepCapEvent n)ᶜ) =
        fun n => 1 - probGnpHalf n (IndepCapEvent n) := by
      funext n
      exact probGnpHalf_compl n _
    rw [h1]
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_probGnpHalf_indepCapEvent
  have hsum0 : Tendsto
      (fun n : ℕ => probGnpHalf n ({G | G.Colorable (kChiMinus n)} ∩ IndepCapEvent n) +
        probGnpHalf n (IndepCapEvent n)ᶜ)
      atTop (𝓝 0) := by
    simpa using tendsto_probGnpHalf_colorable_kChiMinus_inter_indepCap_zero.add hcap_compl
  refine squeeze_zero
    (f := fun n : ℕ => probGnpHalf n
      {G : SimpleGraph (Fin n) | kChiMinus n < G.chromaticNumber.toNat}ᶜ)
    (g := fun n : ℕ => probGnpHalf n ({G | G.Colorable (kChiMinus n)} ∩ IndepCapEvent n) +
      probGnpHalf n (IndepCapEvent n)ᶜ)
    (fun n => probGnpHalf_nonneg n _) (fun n => ?_) hsum0
  have hsub : {G : SimpleGraph (Fin n) | kChiMinus n < G.chromaticNumber.toNat}ᶜ ⊆
      ({G | G.Colorable (kChiMinus n)} ∩ IndepCapEvent n) ∪ (IndepCapEvent n)ᶜ := by
    intro G hG
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hG
    have hcol : G.Colorable (kChiMinus n) := colorable_of_chromaticNumber_toNat_le G hG
    by_cases hcap : G ∈ IndepCapEvent n
    · exact Or.inl ⟨hcol, hcap⟩
    · exact Or.inr hcap
  exact (probGnpHalf_mono hsub).trans (probGnpHalf_union_le n _ _)

end JSP000506
