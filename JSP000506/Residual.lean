import Mathlib.Data.Fintype.CardEmbedding
import JSP000506.HighCells

/-!
# Section 9: Canonical High-Cell Conditioning, Prescribed-Cell Bounds, and Subcritical Second Moment

This module formalizes Lemma 6.2 and Section 9 of Samuil Petkov's *A Full-Sequence Quantitative Gap
Between the Chromatic and Cochromatic Numbers of a Random Graph* (`arXiv:2608.30604`), completing
the unconditional proof of the subcritical normalized second-moment estimate
`secondMomentRatio n ≤ exp(η(n) * n / (log n)^4)` with `η(n) → 0`:

1. **Single-Permutation Reduction (`secondMomentRatio_eq_single_perm_sum`)**:
   By `S_n`-invariance of `overlapPairFactor`, reduces the double sum over `(π₁, π₂) ∈ S_n × S_n`
   in `secondMomentRatio_eq_overlap_sum` to a single uniform average over `π : Equiv.Perm (Fin n)`
   comparing `canonicalBlocks n` against `permBlock n π.symm`.
2. **Matching Restriction Injectivity (`evenSubgraph_sdiff_matching_inj`, Lemma 9.3)**:
   Proves that for any partial block matching `M`, the map `F ↦ F \ M` is injective on
   even-degree overlap subgraphs `IsEvenOverlapSubgraph`, yielding both the pointwise cycle-space
   bound `2 ^ H.card` and the subset-product bound `∏ p ∈ E₀, (1 + w p)`.
3. **Joint Prescribed-Cell Bound (`card_prescribed_absResBij_le`, Lemma 6.2)**:
   For uniform bijections between `m₀`-element residual domain and codomain sets partitioned into
   row blocks `A'` and column blocks `B'`, bounds the count of bijections with at least `x p`
   elements in every cell `p` by `m₀! * ∏ p, (θ p)^(x p) / (x p)!` where
   `θ p = exp 2 * |A'_{p.1}| * |B'_{p.2}| / m₀`.
4. **Intrinsic and Complementary Residual Regimes (`absResSum_le_master`)**:
   Combines the `m₀ = 0` boundary case, the complementary regime `(m₀ : ℝ)^3 < 2^U`, and the
   intrinsic regime `2^U ≤ (m₀ : ℝ)^3` (via `Finset.prod_univ_sum` expansion, Lemma 6.2, and
   Lemma 9.3) to bound the conditional residual average uniformly by `exp(n / (log n)^5)`.
5. **High-Cell Fiber Conditioning & Master Theorem (`eventually_secondMomentRatio_subcritical`)**:
   Partitions `Equiv.Perm (Fin n)` by `(permHighMatching n π, permHighMult n π)` and high-cell
   realization choices `HighChoice`, restricts injectively to residual bijections, and combines
   with Section 8 (`eventually_sum_highSkeletonWeight_le`).
-/

open Filter SimpleGraph Finset
open scoped Topology BigOperators Nat

namespace JSP000506

noncomputable local instance instDecidablePredIsEvenOverlapSubgraph {K : ℕ} :
    DecidablePred (@IsEvenOverlapSubgraph K) :=
  fun H => Classical.propDecidable (IsEvenOverlapSubgraph H)

/-! ### 1. Single-Permutation Reduction and Cell Overlap Decomposition -/

/-- Domain vertices in row block `p.1` mapped by `π` into column block `p.2`. -/
noncomputable def cellSet (n : ℕ) (π : Equiv.Perm (Fin n))
    (p : Fin (kCoSeed n) × Fin (kCoSeed n)) : Finset (Fin n) :=
  (canonicalBlocks n p.1).filter (fun x => π x ∈ canonicalBlocks n p.2)

/-- Overlap multiplicity `r_p(π) = |cellSet n π p|`. -/
noncomputable def cellCard (n : ℕ) (π : Equiv.Perm (Fin n))
    (p : Fin (kCoSeed n) × Fin (kCoSeed n)) : ℕ :=
  (cellSet n π p).card

/-- `cellSet n π p` equals the intersection `canonicalBlocks n p.1 ∩ permBlock n π.symm p.2`. -/
theorem cellSet_eq_inter_permBlock_symm (n : ℕ) (π : Equiv.Perm (Fin n))
    (p : Fin (kCoSeed n) × Fin (kCoSeed n)) :
    cellSet n π p = canonicalBlocks n p.1 ∩ permBlock n π.symm p.2 := by
  ext x
  simp only [cellSet, permBlock, Finset.mem_filter, Finset.mem_inter, Finset.mem_map,
    Equiv.coe_toEmbedding]
  refine ⟨fun ⟨hx1, hx2⟩ => ⟨hx1, ⟨π x, hx2, π.symm_apply_apply x⟩⟩, ?_⟩
  rintro ⟨hx1, ⟨y, hy, rfl⟩⟩
  exact ⟨hx1, by simpa using hy⟩

/-- Transporting `cellSet n (π₂.symm * π₁) p` by `π₁` yields `permBlock n π₁ p.1 ∩ permBlock n π₂ p.2`. -/
theorem permBlock_inter_eq_map_cellSet (n : ℕ) (π₁ π₂ : Equiv.Perm (Fin n))
    (p : Fin (kCoSeed n) × Fin (kCoSeed n)) :
    permBlock n π₁ p.1 ∩ permBlock n π₂ p.2 =
      (cellSet n (π₂.symm * π₁) p).map π₁.toEmbedding := by
  ext v
  rw [Finset.mem_inter, permBlock, permBlock, Finset.mem_map, Finset.mem_map, Finset.mem_map]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, ⟨y, hy, heq⟩⟩
    refine ⟨x, ?_, rfl⟩
    rw [cellSet, Finset.mem_filter]
    refine ⟨hx, ?_⟩
    have hyx : (π₂.symm * π₁) x = y := by
      rw [Equiv.coe_toEmbedding, Equiv.coe_toEmbedding] at heq
      rw [Equiv.Perm.mul_apply, ← heq]
      exact π₂.symm_apply_apply y
    rwa [hyx]
  · rintro ⟨x, hx, rfl⟩
    rw [cellSet, Finset.mem_filter, Equiv.Perm.mul_apply] at hx
    exact ⟨⟨x, hx.1, rfl⟩, ⟨π₂.symm (π₁ x), hx.2, by
      rw [Equiv.coe_toEmbedding, Equiv.coe_toEmbedding]
      exact π₂.apply_symm_apply (π₁ x)⟩⟩

theorem card_permBlock_inter_eq (n : ℕ) (π₁ π₂ : Equiv.Perm (Fin n))
    (p : Fin (kCoSeed n) × Fin (kCoSeed n)) :
    (permBlock n π₁ p.1 ∩ permBlock n π₂ p.2).card =
      (canonicalBlocks n p.1 ∩ permBlock n (π₂.symm * π₁).symm p.2).card := by
  rw [permBlock_inter_eq_map_cellSet, Finset.card_map, ← cellSet_eq_inter_permBlock_symm]

theorem heavyOverlapPairs_permBlock_eq (n : ℕ) (π₁ π₂ : Equiv.Perm (Fin n)) :
    heavyOverlapPairs (permBlock n π₁) (permBlock n π₂) =
      heavyOverlapPairs (canonicalBlocks n) (permBlock n (π₂.symm * π₁).symm) := by
  ext p
  simp only [heavyOverlapPairs, Finset.mem_filter, Finset.mem_univ, true_and,
    card_permBlock_inter_eq]

theorem overlapPairFactor_permBlock_eq (n : ℕ) (π₁ π₂ : Equiv.Perm (Fin n)) :
    overlapPairFactor (permBlock n π₁) (permBlock n π₂) =
      overlapPairFactor (canonicalBlocks n) (permBlock n (π₂.symm * π₁).symm) := by
  classical
  unfold overlapPairFactor
  rw [heavyOverlapPairs_permBlock_eq]
  have hsum :
      ∑ p ∈ heavyOverlapPairs (canonicalBlocks n) (permBlock n (π₂.symm * π₁).symm),
        ((permBlock n π₁ p.1 ∩ permBlock n π₂ p.2).card.choose 2 - 1) =
      ∑ p ∈ heavyOverlapPairs (canonicalBlocks n) (permBlock n (π₂.symm * π₁).symm),
        ((canonicalBlocks n p.1 ∩ permBlock n (π₂.symm * π₁).symm p.2).card.choose 2 - 1) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [card_permBlock_inter_eq]
  rw [hsum]

/-- **Single-Permutation Second-Moment Formula**:
`secondMomentRatio n` equals `(n!)⁻¹ * ∑_{π ∈ S_n} overlapPairFactor (canonicalBlocks n) (permBlock n π.symm)`. -/
theorem secondMomentRatio_eq_single_perm_sum (n : ℕ) :
    secondMomentRatio n =
      ((n ! : ℝ))⁻¹ *
        ∑ π : Equiv.Perm (Fin n),
          overlapPairFactor (canonicalBlocks n) (permBlock n π.symm) := by
  rw [secondMomentRatio_eq_overlap_sum]
  have hinner : ∀ π₁ : Equiv.Perm (Fin n),
      ∑ π₂ : Equiv.Perm (Fin n), overlapPairFactor (permBlock n π₁) (permBlock n π₂) =
        ∑ π : Equiv.Perm (Fin n), overlapPairFactor (canonicalBlocks n) (permBlock n π.symm) := by
    intro π₁
    let eqv : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) :=
      { toFun := fun π => π₁ * π.symm
        invFun := fun π₂ => π₂.symm * π₁
        left_inv := fun π => Equiv.ext fun x => (π₁ * π.symm).injective (by
          rw [Equiv.Perm.mul_apply (π₁ * π.symm).symm π₁ x, Equiv.apply_symm_apply,
            Equiv.Perm.mul_apply π₁ π.symm (π x), Equiv.symm_apply_apply])
        right_inv := fun π₂ => Equiv.ext fun x => π₂.symm.injective (by
          rw [Equiv.Perm.mul_apply π₁ (π₂.symm * π₁).symm x,
            ← Equiv.Perm.mul_apply π₂.symm π₁ ((π₂.symm * π₁).symm x),
            Equiv.apply_symm_apply, Equiv.symm_apply_apply]) }
    rw [← Equiv.sum_comp eqv]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [overlapPairFactor_permBlock_eq]
    have heqv_inv : (eqv π).symm * π₁ = π := eqv.left_inv π
    rw [heqv_inv]
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  have hnfac_ne : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp [hnfac_ne]

/-- Heavy overlap pairs `(a, b)` for permutation `π`, i.e. cells with `2 ≤ cellCard n π (a, b)`. -/
noncomputable def permHeavyPairs (n : ℕ) (π : Equiv.Perm (Fin n)) :
    Finset (Fin (kCoSeed n) × Fin (kCoSeed n)) :=
  Finset.univ.filter (fun p => 2 ≤ cellCard n π p)

theorem heavyOverlapPairs_canonical_permBlock_symm (n : ℕ) (π : Equiv.Perm (Fin n)) :
    heavyOverlapPairs (canonicalBlocks n) (permBlock n π.symm) = permHeavyPairs n π := by
  ext p
  simp only [heavyOverlapPairs, permHeavyPairs, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← cellSet_eq_inter_permBlock_symm, cellCard]

/-- Exact factorization of `overlapPairFactor (canonicalBlocks n) (permBlock n π.symm)` into
`(∏ p, localCellReward (cellCard n π p)) * #{F ⊆ permHeavyPairs n π | IsEvenOverlapSubgraph F}`. -/
theorem overlapPairFactor_canonical_eq (n : ℕ) (π : Equiv.Perm (Fin n)) :
    overlapPairFactor (canonicalBlocks n) (permBlock n π.symm) =
      (∏ p : Fin (kCoSeed n) × Fin (kCoSeed n), localCellReward (cellCard n π p)) *
        (((permHeavyPairs n π).powerset.filter IsEvenOverlapSubgraph).card : ℝ) := by
  unfold overlapPairFactor
  rw [heavyOverlapPairs_canonical_permBlock_symm]
  have hprod_eq :
      (2 : ℝ) ^ (∑ p ∈ permHeavyPairs n π,
        ((canonicalBlocks n p.1 ∩ permBlock n π.symm p.2).card.choose 2 - 1)) =
      ∏ p : Fin (kCoSeed n) × Fin (kCoSeed n), localCellReward (cellCard n π p) := by
    have hsum_congr :
        ∑ p ∈ permHeavyPairs n π,
          ((canonicalBlocks n p.1 ∩ permBlock n π.symm p.2).card.choose 2 - 1) =
        ∑ p ∈ permHeavyPairs n π, ((cellCard n π p).choose 2 - 1) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← cellSet_eq_inter_permBlock_symm, cellCard]
    rw [hsum_congr, ← prod_pow_eq_pow_sum_real (permHeavyPairs n π) (2 : ℝ)
      (fun p => (cellCard n π p).choose 2 - 1)]
    have hsub_prod :
        (∏ p ∈ permHeavyPairs n π, localCellReward (cellCard n π p)) =
          ∏ p : Fin (kCoSeed n) × Fin (kCoSeed n), localCellReward (cellCard n π p) := by
      refine Finset.prod_subset (Finset.subset_univ _) fun p _ hp => ?_
      have hlt : cellCard n π p < 2 := by
        simpa [permHeavyPairs] using hp
      exact localCellReward_eq_one_of_le_two (by omega)
    rw [← hsub_prod]
    rfl
  rw [hprod_eq]

/-! ### 2. Matching Restriction Injectivity and Cycle-Space Bounds (Lemma 9.3) -/

/-- Symmetric difference `(A \ B) ∪ (B \ A)` of two even-cardinality finsets has even cardinality. -/
theorem even_card_symmDiff_of_even {α : Type*} [DecidableEq α] {A B : Finset α}
    (hA : Even A.card) (hB : Even B.card) :
    Even ((A \ B) ∪ (B \ A)).card := by
  have hdisj : Disjoint (A \ B) (B \ A) :=
    Finset.disjoint_left.mpr fun _ hx1 hx2 =>
      (Finset.mem_sdiff.mp hx2).2 (Finset.mem_sdiff.mp hx1).1
  have hu := Finset.card_union_of_disjoint hdisj
  have h1 := Finset.card_sdiff_add_card_inter A B
  have h2 := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at h2
  rcases hA with ⟨k₁, hk₁⟩
  rcases hB with ⟨k₂, hk₂⟩
  refine ⟨k₁ + k₂ - (A ∩ B).card, ?_⟩
  omega

/-- **Lemma 9.3 (`arXiv:2608.30604`) — Matching Restriction Injectivity**:
If `M` is a partial block matching (`IsBlockMatching K M`), then on even-degree overlap subgraphs
`IsEvenOverlapSubgraph`, the restriction map `F ↦ F \ M` is injective. -/
theorem evenSubgraph_sdiff_matching_inj {K : ℕ} {M F₁ F₂ : Finset (Fin K × Fin K)}
    (hM : IsBlockMatching K M)
    (h₁ : IsEvenOverlapSubgraph F₁)
    (h₂ : IsEvenOverlapSubgraph F₂)
    (hsdiff : F₁ \ M = F₂ \ M) :
    F₁ = F₂ := by
  let D : Finset (Fin K × Fin K) := (F₁ \ F₂) ∪ (F₂ \ F₁)
  have hD_sub : D ⊆ M := by
    intro p hp
    by_contra hpM
    rcases Finset.mem_union.mp hp with hp1 | hp2
    · rcases Finset.mem_sdiff.mp hp1 with ⟨hF1, hnF2⟩
      have hmem : p ∈ F₁ \ M := Finset.mem_sdiff.mpr ⟨hF1, hpM⟩
      rw [hsdiff] at hmem
      exact hnF2 (Finset.mem_sdiff.mp hmem).1
    · rcases Finset.mem_sdiff.mp hp2 with ⟨hF2, hnF1⟩
      have hmem : p ∈ F₂ \ M := Finset.mem_sdiff.mpr ⟨hF2, hpM⟩
      rw [← hsdiff] at hmem
      exact hnF1 (Finset.mem_sdiff.mp hmem).1
  have hD_row_zero : ∀ i : Fin K, (D.filter (fun p => p.1 = i)).card = 0 := by
    intro i
    have hfilt_eq :
        D.filter (fun p => p.1 = i) =
          ((F₁.filter (fun p => p.1 = i)) \ (F₂.filter (fun p => p.1 = i))) ∪
            ((F₂.filter (fun p => p.1 = i)) \ (F₁.filter (fun p => p.1 = i))) := by
      ext p
      simp only [D, Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
      tauto
    have hev : Even (D.filter (fun p => p.1 = i)).card := by
      rw [hfilt_eq]
      exact even_card_symmDiff_of_even (h₁.1 i) (h₂.1 i)
    have hle1 : (D.filter (fun p => p.1 = i)).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun p₁ hp₁ p₂ hp₂ => ?_
      have hm₁ := Finset.mem_filter.mp hp₁
      have hm₂ := Finset.mem_filter.mp hp₂
      exact hM.1 p₁ (hD_sub hm₁.1) p₂ (hD_sub hm₂.1) (hm₁.2.trans hm₂.2.symm)
    rcases hev with ⟨k, hk⟩
    omega
  ext p
  constructor
  · intro hp1
    by_contra hp2
    have hpD : p ∈ D.filter (fun q => q.1 = p.1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hp1, hp2⟩), rfl⟩
    have hpos : 0 < (D.filter (fun q => q.1 = p.1)).card := Finset.card_pos.mpr ⟨p, hpD⟩
    have h0 := hD_row_zero p.1
    omega
  · intro hp2
    by_contra hp1
    have hpD : p ∈ D.filter (fun q => q.1 = p.1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hp2, hp1⟩), rfl⟩
    have hpos : 0 < (D.filter (fun q => q.1 = p.1)).card := Finset.card_pos.mpr ⟨p, hpD⟩
    have h0 := hD_row_zero p.1
    omega

/-- Pointwise cycle-space cardinality bound: when `M` is a partial block matching,
`#{F ⊆ M ∪ H | IsEvenOverlapSubgraph F} ≤ 2 ^ H.card`. -/
theorem card_evenSubgraphs_union_le {K : ℕ}
    {M H : Finset (Fin K × Fin K)} (hM : IsBlockMatching K M) :
    ((M ∪ H).powerset.filter IsEvenOverlapSubgraph).card ≤ 2 ^ H.card := by
  let E := (M ∪ H).powerset.filter IsEvenOverlapSubgraph
  have hmaps : ∀ F ∈ E, F \ M ∈ H.powerset := by
    intro F hF
    rw [Finset.mem_powerset]
    have hsub : F ⊆ M ∪ H := Finset.mem_powerset.mp (Finset.mem_filter.mp hF).1
    intro p hp
    rcases Finset.mem_sdiff.mp hp with ⟨hpF, hpM⟩
    rcases Finset.mem_union.mp (hsub hpF) with h1 | h2
    · exact False.elim (hpM h1)
    · exact h2
  have hinj : Set.InjOn (fun F : Finset (Fin K × Fin K) => F \ M) (E : Set _) :=
    fun F₁ h₁ F₂ h₂ hsdiff =>
      evenSubgraph_sdiff_matching_inj hM (Finset.mem_filter.mp h₁).2
        (Finset.mem_filter.mp h₂).2 hsdiff
  calc
    E.card ≤ H.powerset.card := Finset.card_le_card_of_injOn (fun F => F \ M) hmaps hinj
    _ = 2 ^ H.card := Finset.card_powerset H

theorem sum_powerset_prod_eq_prod_one_add {α : Type*} [DecidableEq α]
    (E₀ : Finset α) (w : α → ℝ) :
    (∑ S ∈ E₀.powerset, ∏ p ∈ S, w p) = ∏ p ∈ E₀, (1 + w p) := by
  induction E₀ using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hdisj : Disjoint s.powerset (s.powerset.image (insert a)) :=
      Finset.disjoint_left.mpr fun H h1 h2 => by
        rcases Finset.mem_image.mp h2 with ⟨H', _, rfl⟩
        exact ha (Finset.mem_powerset.mp h1 (Finset.mem_insert_self a H'))
    have hinj : Set.InjOn (insert a) (s.powerset : Set (Finset α)) := by
      intro H₁ h₁ H₂ h₂ heq
      have ha₁ : a ∉ H₁ := fun h => ha (Finset.mem_powerset.mp h₁ h)
      have ha₂ : a ∉ H₂ := fun h => ha (Finset.mem_powerset.mp h₂ h)
      simpa [Finset.erase_insert ha₁, Finset.erase_insert ha₂] using
        congrArg (fun T => T.erase a) heq
    rw [Finset.powerset_insert, Finset.sum_union hdisj, Finset.sum_image hinj,
      Finset.prod_insert ha, ← ih]
    have himg : (∑ H ∈ s.powerset, ∏ p ∈ insert a H, w p) =
        w a * ∑ H ∈ s.powerset, ∏ p ∈ H, w p := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun H hH => ?_
      have haH : a ∉ H := fun h => ha (Finset.mem_powerset.mp hH h)
      exact Finset.prod_insert haH
    rw [himg]
    ring

/-- Subset-product generating bound over `(M ∪ E₀).powerset.filter IsEvenOverlapSubgraph`
from Lemma 9.3. -/
theorem sum_evenSubgraphs_prod_sdiff_le {K : ℕ}
    {M E₀ : Finset (Fin K × Fin K)} (hM : IsBlockMatching K M)
    {w : Fin K × Fin K → ℝ} (hw : ∀ p ∈ E₀, 0 ≤ w p) :
    (∑ F ∈ (M ∪ E₀).powerset.filter IsEvenOverlapSubgraph, ∏ p ∈ F \ M, w p) ≤
      ∏ p ∈ E₀, (1 + w p) := by
  let E := (M ∪ E₀).powerset.filter IsEvenOverlapSubgraph
  have hinj : Set.InjOn (fun F : Finset (Fin K × Fin K) => F \ M) (E : Set _) :=
    fun F₁ h₁ F₂ h₂ hsdiff =>
      evenSubgraph_sdiff_matching_inj hM (Finset.mem_filter.mp h₁).2
        (Finset.mem_filter.mp h₂).2 hsdiff
  have hsub : E.image (fun F => F \ M) ⊆ E₀.powerset := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨F, hF, rfl⟩
    rw [Finset.mem_powerset]
    have hF_sub : F ⊆ M ∪ E₀ := Finset.mem_powerset.mp (Finset.mem_filter.mp hF).1
    intro p hp
    rcases Finset.mem_sdiff.mp hp with ⟨hpF, hpM⟩
    rcases Finset.mem_union.mp (hF_sub hpF) with h1 | h2
    · exact False.elim (hpM h1)
    · exact h2
  calc
    (∑ F ∈ E, ∏ p ∈ F \ M, w p)
        = ∑ S ∈ E.image (fun F => F \ M), ∏ p ∈ S, w p :=
          (Finset.sum_image (f := fun S => ∏ p ∈ S, w p) hinj).symm
    _ ≤ ∑ S ∈ E₀.powerset, ∏ p ∈ S, w p := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun S hS _ => ?_
      exact Finset.prod_nonneg fun p hp => hw p (Finset.mem_powerset.mp hS hp)
    _ = ∏ p ∈ E₀, (1 + w p) := sum_powerset_prod_eq_prod_one_add E₀ w

theorem prod_one_add_le_exp_sum {α : Type*} (E₀ : Finset α) {w : α → ℝ}
    (hw : ∀ p ∈ E₀, 0 ≤ w p) :
    (∏ p ∈ E₀, (1 + w p)) ≤ Real.exp (∑ p ∈ E₀, w p) := by
  calc
    (∏ p ∈ E₀, (1 + w p))
        ≤ ∏ p ∈ E₀, Real.exp (w p) := by
      refine prod_le_prod_real E₀ (fun p hp => by linarith [hw p hp]) fun p _ => ?_
      linarith [Real.add_one_le_exp (w p)]
    _ = Real.exp (∑ p ∈ E₀, w p) := by rw [Real.exp_sum]

/-! ### 3. Abstract Residual Bijection Model and Joint Prescribed-Cell Bound (Lemma 6.2) -/

theorem card_equiv_finset_eq_factorial {α β : Type*} [DecidableEq α] [DecidableEq β] {m₀ : ℕ}
    {U_dom : Finset α} {U_cod : Finset β}
    (hdom : U_dom.card = m₀) (hcod : U_cod.card = m₀) :
    Fintype.card ({u // u ∈ U_dom} ≃ {v // v ∈ U_cod}) = m₀ ! := by
  let edom : {u // u ∈ U_dom} ≃ Fin m₀ := U_dom.equivFinOfCardEq hdom
  let ecod : {v // v ∈ U_cod} ≃ Fin m₀ := U_cod.equivFinOfCardEq hcod
  rw [Fintype.card_congr (Equiv.equivCongr edom ecod), Fintype.card_perm, Fintype.card_fin]

/-- Residual elements in `U_dom` lying in row block `A' p.1` and mapped by `f` into `B' p.2`. -/
def absResCellSet {n K : ℕ} {U_dom U_cod : Finset (Fin n)}
    (A' B' : Fin K → Finset (Fin n))
    (f : {u // u ∈ U_dom} ≃ {v // v ∈ U_cod}) (p : Fin K × Fin K) :
    Finset {u // u ∈ U_dom} :=
  Finset.univ.filter (fun u => u.1 ∈ A' p.1 ∧ (f u).1 ∈ B' p.2)

/-- Residual cell multiplicity `r'_p(f) = |absResCellSet A' B' f p|`. -/
def absResCellCard {n K : ℕ} {U_dom U_cod : Finset (Fin n)}
    (A' B' : Fin K → Finset (Fin n))
    (f : {u // u ∈ U_dom} ≃ {v // v ∈ U_cod}) (p : Fin K × Fin K) : ℕ :=
  (absResCellSet A' B' f p).card

theorem pairwiseDisjoint_absResCellSet {n K : ℕ} {U_dom U_cod : Finset (Fin n)}
    {A' B' : Fin K → Finset (Fin n)}
    (hA_disj : (Set.univ : Set (Fin K)).PairwiseDisjoint A')
    (hB_disj : (Set.univ : Set (Fin K)).PairwiseDisjoint B')
    (f : {u // u ∈ U_dom} ≃ {v // v ∈ U_cod}) :
    (Set.univ : Set (Fin K × Fin K)).PairwiseDisjoint (absResCellSet A' B' f) := by
  intro p₁ _ p₂ _ hne
  refine Finset.disjoint_left.mpr fun u hu₁ hu₂ => ?_
  have h1 := (Finset.mem_filter.mp hu₁).2
  have h2 := (Finset.mem_filter.mp hu₂).2
  by_cases hfst : p₁.1 = p₂.1
  · have hsnd : p₁.2 ≠ p₂.2 := fun hs => hne (Prod.ext hfst hs)
    exact Finset.disjoint_left.mp (hB_disj trivial trivial hsnd) h1.2 h2.2
  · exact Finset.disjoint_left.mp (hA_disj trivial trivial hfst) h1.1 h2.1

theorem sum_absResCellCard_eq {n K m₀ : ℕ} {U_dom U_cod : Finset (Fin n)}
    {A' B' : Fin K → Finset (Fin n)}
    (hdom : U_dom.card = m₀)
    (hA_disj : (Set.univ : Set (Fin K)).PairwiseDisjoint A')
    (hA_union : Finset.univ.biUnion A' = U_dom)
    (hB_disj : (Set.univ : Set (Fin K)).PairwiseDisjoint B')
    (hB_union : Finset.univ.biUnion B' = U_cod)
    (f : {u // u ∈ U_dom} ≃ {v // v ∈ U_cod}) :
    ∑ p : Fin K × Fin K, absResCellCard A' B' f p = m₀ := by
  have hdisj : ((Finset.univ : Finset (Fin K × Fin K)) : Set (Fin K × Fin K)).PairwiseDisjoint
      (absResCellSet A' B' f) :=
    fun p₁ _ p₂ _ hne => pairwiseDisjoint_absResCellSet hA_disj hB_disj f trivial trivial hne
  have huniv : Finset.univ.biUnion (absResCellSet A' B' f) = Finset.univ := by
    ext u
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true, absResCellSet,
      Finset.mem_filter]
    have hu_dom : u.1 ∈ Finset.univ.biUnion A' := by rw [hA_union]; exact u.2
    have hv_cod : (f u).1 ∈ Finset.univ.biUnion B' := by rw [hB_union]; exact (f u).2
    rcases Finset.mem_biUnion.mp hu_dom with ⟨a, _, ha⟩
    rcases Finset.mem_biUnion.mp hv_cod with ⟨b, _, hb⟩
    exact ⟨(a, b), ha, hb⟩
  have hcard : (Finset.univ.biUnion (absResCellSet A' B' f)).card = m₀ := by
    rw [huniv, Finset.card_univ, Fintype.card_coe, hdom]
  rw [Finset.card_biUnion hdisj] at hcard
  exact hcard

theorem sum_block_cards_eq {n K m₀ : ℕ} {U_set : Finset (Fin n)}
    {A' : Fin K → Finset (Fin n)}
    (hcard : U_set.card = m₀)
    (hA_disj : (Set.univ : Set (Fin K)).PairwiseDisjoint A')
    (hA_union : Finset.univ.biUnion A' = U_set) :
    ∑ a : Fin K, (A' a).card = m₀ := by
  have hdisj : ((Finset.univ : Finset (Fin K)) : Set (Fin K)).PairwiseDisjoint A' :=
    fun a₁ _ a₂ _ hne => hA_disj trivial trivial hne
  rw [← Finset.card_biUnion hdisj, hA_union, hcard]

theorem factorial_le_descFactorial {k r : ℕ} (h : k ≤ r) :
    k ! ≤ r.descFactorial k := by
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  have hpos : 1 ≤ r.choose k := Nat.choose_pos h
  calc
    k ! = k ! * 1 := (mul_one _).symm
    _ ≤ k ! * r.choose k := Nat.mul_le_mul_left _ hpos

theorem factorial_le_pow_of_le {k m : ℕ} (h : k ≤ m) :
    k ! ≤ m ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ, pow_succ']
    exact Nat.mul_le_mul h (ih (Nat.le_of_succ_le h))

theorem pow_le_two_pow_mul_descFactorial_of_two_mul_le {m₀ X : ℕ} (h : 2 * X ≤ m₀) :
    m₀ ^ X ≤ 2 ^ X * m₀.descFactorial X := by
  induction X with
  | zero => simp
  | succ X ih =>
    have h' : 2 * X ≤ m₀ := by omega
    have hstep : m₀ ≤ 2 * (m₀ - X) := by omega
    calc
      m₀ ^ (X + 1) = m₀ ^ X * m₀ := pow_succ m₀ X
      _ ≤ (2 ^ X * m₀.descFactorial X) * (2 * (m₀ - X)) := Nat.mul_le_mul (ih h') hstep
      _ = 2 ^ (X + 1) * ((m₀ - X) * m₀.descFactorial X) := by ring
      _ = 2 ^ (X + 1) * m₀.descFactorial (X + 1) := by rw [← Nat.descFactorial_succ]

/-- Uniform falling-factorial lower bound `m₀^X ≤ (exp 2)^X * (m₀)_X` for all `X ≤ m₀`. -/
theorem pow_le_exp_two_mul_descFactorial {m₀ X : ℕ} (hX : X ≤ m₀) :
    (m₀ : ℝ) ^ X ≤ (Real.exp 2) ^ X * (m₀.descFactorial X : ℝ) := by
  by_cases hhalf : 2 * X ≤ m₀
  · have hnat := pow_le_two_pow_mul_descFactorial_of_two_mul_le hhalf
    have hreal : (m₀ : ℝ) ^ X ≤ (2 : ℝ) ^ X * (m₀.descFactorial X : ℝ) := by exact_mod_cast hnat
    have h2_le : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    exact hreal.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num) h2_le X) (Nat.cast_nonneg _))
  · push Not at hhalf
    have hfac_sub : (m₀ - X) ! ≤ m₀ ^ (m₀ - X) := factorial_le_pow_of_le (Nat.sub_le m₀ X)
    have hpow_mul : m₀ ^ X * (m₀ - X) ! ≤ m₀ ^ m₀ := by
      calc
        m₀ ^ X * (m₀ - X) ! ≤ m₀ ^ X * m₀ ^ (m₀ - X) := Nat.mul_le_mul_left _ hfac_sub
        _ = m₀ ^ (X + (m₀ - X)) := (pow_add m₀ X (m₀ - X)).symm
        _ = m₀ ^ m₀ := by rw [Nat.add_sub_of_le hX]
    have hsplit_fac : m₀ ! = m₀.descFactorial X * (m₀ - X) ! := by
      have h := descFactorial_add_eq m₀ X (m₀ - X)
      rw [Nat.add_sub_of_le hX, Nat.descFactorial_self, Nat.descFactorial_self] at h
      exact h
    have hexp_m₀ : (m₀ : ℝ) ^ m₀ ≤ (m₀ ! : ℝ) * Real.exp (m₀ : ℝ) := by
      have hdiv := pow_div_factorial_le_exp (Nat.cast_nonneg m₀) m₀
      have hpos : 0 < (m₀ ! : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m₀)
      rw [mul_comm]
      exact (div_le_iff₀ hpos).mp hdiv
    have hexp_2X : Real.exp (m₀ : ℝ) ≤ (Real.exp 2) ^ X := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hlt : (m₀ : ℝ) ≤ 2 * (X : ℝ) := by exact_mod_cast hhalf.le
      linarith
    have hsub_pos : 0 < ((m₀ - X) ! : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hprod_le :
        (m₀ : ℝ) ^ X * ((m₀ - X) ! : ℝ) ≤
          ((Real.exp 2) ^ X * (m₀.descFactorial X : ℝ)) * ((m₀ - X) ! : ℝ) := by
      calc
        (m₀ : ℝ) ^ X * ((m₀ - X) ! : ℝ) ≤ (m₀ : ℝ) ^ m₀ := by exact_mod_cast hpow_mul
        _ ≤ (m₀ ! : ℝ) * Real.exp (m₀ : ℝ) := hexp_m₀
        _ ≤ (m₀ ! : ℝ) * (Real.exp 2) ^ X :=
          mul_le_mul_of_nonneg_left hexp_2X (Nat.cast_nonneg _)
        _ = ((m₀.descFactorial X : ℝ) * ((m₀ - X) ! : ℝ)) * (Real.exp 2) ^ X := by
          have hc : (m₀ ! : ℝ) = (m₀.descFactorial X : ℝ) * ((m₀ - X) ! : ℝ) := by
            exact_mod_cast hsplit_fac
          rw [hc]
        _ = ((Real.exp 2) ^ X * (m₀.descFactorial X : ℝ)) * ((m₀ - X) ! : ℝ) := by ring
    exact le_of_mul_le_mul_right hprod_le hsub_pos

/-- Prescribed-cell rate parameter `θ_p = exp 2 * |A'_{p.1}| * |B'_{p.2}| / m₀`. -/
noncomputable def absTheta {n K : ℕ} (A' B' : Fin K → Finset (Fin n)) (m₀ : ℕ)
    (p : Fin K × Fin K) : ℝ :=
  Real.exp 2 * ((A' p.1).card : ℝ) * ((B' p.2).card : ℝ) / (m₀ : ℝ)

theorem absTheta_nonneg {n K : ℕ} (A' B' : Fin K → Finset (Fin n)) (m₀ : ℕ)
    (p : Fin K × Fin K) :
    0 ≤ absTheta A' B' m₀ p := by
  unfold absTheta
  exact div_nonneg
    (mul_nonneg (mul_nonneg (Real.exp_pos 2).le (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)

/-- **Lemma 6.2 (`arXiv:2608.30604`) — Joint Prescribed-Cell Upper Bound**:
For `0 < m₀` and any multiplicity demand `x : Fin K × Fin K → ℕ`, the number of residual bijections
`f : {u // u ∈ U_dom} ≃ {v // v ∈ U_cod}` satisfying `∀ p, x p ≤ absResCellCard A' B' f p` is at
most `m₀! * ∏ p, (absTheta A' B' m₀ p) ^ (x p) / (x p)!`. -/
theorem card_prescribed_absResBij_le {n K m₀ : ℕ} {U_dom U_cod : Finset (Fin n)}
    {A' B' : Fin K → Finset (Fin n)}
    (hm₀_pos : 0 < m₀)
    (hdom : U_dom.card = m₀)
    (hcod : U_cod.card = m₀)
    (hA_disj : (Set.univ : Set (Fin K)).PairwiseDisjoint A')
    (hA_union : Finset.univ.biUnion A' = U_dom)
    (hB_disj : (Set.univ : Set (Fin K)).PairwiseDisjoint B')
    (hB_union : Finset.univ.biUnion B' = U_cod)
    (x : Fin K × Fin K → ℕ) :
    ((Finset.univ.filter (fun f : {u // u ∈ U_dom} ≃ {v // v ∈ U_cod} =>
        ∀ p : Fin K × Fin K, x p ≤ absResCellCard A' B' f p)).card : ℝ) ≤
      (m₀ ! : ℝ) * ∏ p : Fin K × Fin K, (absTheta A' B' m₀ p) ^ (x p) / ((x p) ! : ℝ) := by
  classical
  let ValSet := Finset.univ.filter (fun f : {u // u ∈ U_dom} ≃ {v // v ∈ U_cod} =>
    ∀ p : Fin K × Fin K, x p ≤ absResCellCard A' B' f p)
  set X : ℕ := ∑ p : Fin K × Fin K, x p
  by_cases hX_le : X ≤ m₀
  · -- Step 1: Combinatorial injection into row embeddings × col embeddings × remaining bijections
    have hA_sub : ∀ (a : Fin K) {w : Fin n}, w ∈ A' a → w ∈ U_dom := by
      intro a w hw
      rw [← hA_union]
      exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, hw⟩
    have hB_sub : ∀ (b : Fin K) {w : Fin n}, w ∈ B' b → w ∈ U_cod := by
      intro b w hw
      rw [← hB_union]
      exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, hw⟩
    let RowEmb := ∀ a : Fin K, (Σ b : Fin K, Fin (x (a, b))) ↪ {w // w ∈ A' a}
    let ColEmb := ∀ b : Fin K, (Σ a : Fin K, Fin (x (a, b))) ↪ {w // w ∈ B' b}
    let rowGlobal (re : RowEmb) : (Σ a : Fin K, Σ b : Fin K, Fin (x (a, b))) ↪
        {u // u ∈ U_dom} :=
      { toFun := fun ⟨a, b, i⟩ => ⟨(re a ⟨b, i⟩).1, hA_sub a (re a ⟨b, i⟩).2⟩
        inj' := by
          rintro ⟨a₁, b₁, i₁⟩ ⟨a₂, b₂, i₂⟩ heq
          have hval : (re a₁ ⟨b₁, i₁⟩).1 = (re a₂ ⟨b₂, i₂⟩).1 := congrArg Subtype.val heq
          have ha_eq : a₁ = a₂ := by
            by_contra hne
            exact Finset.disjoint_left.mp (hA_disj trivial trivial hne)
              (re a₁ ⟨b₁, i₁⟩).2 (hval ▸ (re a₂ ⟨b₂, i₂⟩).2)
          subst ha_eq
          have hbi := (re a₁).injective (Subtype.ext hval)
          rcases Sigma.mk.inj_iff.mp hbi with ⟨rfl, hi⟩
          rw [eq_of_heq hi] }
    let colGlobal (ce : ColEmb) : (Σ b : Fin K, Σ a : Fin K, Fin (x (a, b))) ↪
        {v // v ∈ U_cod} :=
      { toFun := fun ⟨b, a, i⟩ => ⟨(ce b ⟨a, i⟩).1, hB_sub b (ce b ⟨a, i⟩).2⟩
        inj' := by
          rintro ⟨b₁, a₁, i₁⟩ ⟨b₂, a₂, i₂⟩ heq
          have hval : (ce b₁ ⟨a₁, i₁⟩).1 = (ce b₂ ⟨a₂, i₂⟩).1 := congrArg Subtype.val heq
          have hb_eq : b₁ = b₂ := by
            by_contra hne
            exact Finset.disjoint_left.mp (hB_disj trivial trivial hne)
              (ce b₁ ⟨a₁, i₁⟩).2 (hval ▸ (ce b₂ ⟨a₂, i₂⟩).2)
          subst hb_eq
          have hai := (ce b₁).injective (Subtype.ext hval)
          rcases Sigma.mk.inj_iff.mp hai with ⟨rfl, hi⟩
          rw [eq_of_heq hi] }
    let remDomSub (re : RowEmb) : Finset {u // u ∈ U_dom} :=
      Finset.univ \ Finset.univ.map (rowGlobal re)
    let remCodSub (ce : ColEmb) : Finset {v // v ∈ U_cod} :=
      Finset.univ \ Finset.univ.map (colGlobal ce)
    have hcard_remDom : ∀ re : RowEmb, (remDomSub re).card = m₀ - X := by
      intro re
      dsimp only [remDomSub]
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_coe, hdom,
        Finset.card_map, Finset.card_univ]
      have hX_sigma : Fintype.card (Σ a : Fin K, Σ b : Fin K, Fin (x (a, b))) = X := by
        simp only [Fintype.card_sigma, Fintype.card_fin]
        exact (Fintype.sum_prod_type (fun p : Fin K × Fin K => x p)).symm
      rw [hX_sigma]
    have hcard_remCod : ∀ ce : ColEmb, (remCodSub ce).card = m₀ - X := by
      intro ce
      dsimp only [remCodSub]
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_coe, hcod,
        Finset.card_map, Finset.card_univ]
      have hX_sigma : Fintype.card (Σ b : Fin K, Σ a : Fin K, Fin (x (a, b))) = X := by
        simp only [Fintype.card_sigma, Fintype.card_fin]
        rw [Finset.sum_comm]
        exact (Fintype.sum_prod_type (fun p : Fin K × Fin K => x p)).symm
      rw [hX_sigma]
    let LHS := Σ f : {f // f ∈ ValSet},
      ∀ p : Fin K × Fin K, Fin (x p) ↪ {u // u ∈ absResCellSet A' B' f.1 p}
    let RHS := Σ rc : RowEmb × ColEmb,
      ({u // u ∈ remDomSub rc.1} ≃ {v // v ∈ remCodSub rc.2})
    let embMap : LHS → RHS := fun ⟨f, emb⟩ =>
      let re : RowEmb := fun a =>
        { toFun := fun ⟨b, i⟩ =>
            ⟨(emb (a, b) i).1.1, (Finset.mem_filter.mp (emb (a, b) i).2).2.1⟩
          inj' := by
            rintro ⟨b₁, i₁⟩ ⟨b₂, i₂⟩ heq
            have hval := congrArg Subtype.val heq
            have hu_eq : (emb (a, b₁) i₁).1 = (emb (a, b₂) i₂).1 := Subtype.ext hval
            have hb₁ := (Finset.mem_filter.mp (emb (a, b₁) i₁).2).2.2
            have hb₂ := (Finset.mem_filter.mp (emb (a, b₂) i₂).2).2.2
            rw [← hu_eq] at hb₂
            have hb_eq : b₁ = b₂ := by
              by_contra hne
              exact Finset.disjoint_left.mp (hB_disj trivial trivial hne) hb₁ hb₂
            subst hb_eq
            have hi_eq := (emb (a, b₁)).injective (Subtype.ext hu_eq)
            subst hi_eq
            rfl }
      let ce : ColEmb := fun b =>
        { toFun := fun ⟨a, i⟩ =>
            ⟨(f.1 (emb (a, b) i).1).1, (Finset.mem_filter.mp (emb (a, b) i).2).2.2⟩
          inj' := by
            rintro ⟨a₁, i₁⟩ ⟨a₂, i₂⟩ heq
            have hval := congrArg Subtype.val heq
            have hv_eq : f.1 (emb (a₁, b) i₁).1 = f.1 (emb (a₂, b) i₂).1 := Subtype.ext hval
            have hu_eq : (emb (a₁, b) i₁).1 = (emb (a₂, b) i₂).1 := f.1.injective hv_eq
            have ha₁ := (Finset.mem_filter.mp (emb (a₁, b) i₁).2).2.1
            have ha₂ := (Finset.mem_filter.mp (emb (a₂, b) i₂).2).2.1
            rw [← hu_eq] at ha₂
            have ha_eq : a₁ = a₂ := by
              by_contra hne
              exact Finset.disjoint_left.mp (hA_disj trivial trivial hne) ha₁ ha₂
            subst ha_eq
            have hi_eq := (emb (a₁, b)).injective (Subtype.ext hu_eq)
            subst hi_eq
            rfl }
      have hrel : ∀ (a b : Fin K) (i : Fin (x (a, b))),
          f.1 (rowGlobal re ⟨a, b, i⟩) = colGlobal ce ⟨b, a, i⟩ :=
        fun _ _ _ => Subtype.ext rfl
      ⟨(re, ce),
        { toFun := fun u =>
            ⟨f.1 u.1, by
              have hu_not : u.1 ∉ Finset.univ.map (rowGlobal re) :=
                (Finset.mem_sdiff.mp u.2).2
              refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hv_in => ?_⟩
              rcases Finset.mem_map.mp hv_in with ⟨⟨b, a, i⟩, _, hcol_eq⟩
              rw [← hrel a b i] at hcol_eq
              exact hu_not (Finset.mem_map.mpr ⟨⟨a, b, i⟩, Finset.mem_univ _,
                f.1.injective hcol_eq⟩)⟩
          invFun := fun v =>
            ⟨f.1.symm v.1, by
              have hv_not : v.1 ∉ Finset.univ.map (colGlobal ce) :=
                (Finset.mem_sdiff.mp v.2).2
              refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hu_in => ?_⟩
              rcases Finset.mem_map.mp hu_in with ⟨⟨a, b, i⟩, _, hrow_eq⟩
              have hfv : colGlobal ce ⟨b, a, i⟩ = v.1 := by
                rw [← hrel a b i, hrow_eq, f.1.apply_symm_apply]
              exact hv_not (Finset.mem_map.mpr ⟨⟨b, a, i⟩, Finset.mem_univ _, hfv⟩)⟩
          left_inv := fun u => Subtype.ext (f.1.symm_apply_apply u.1)
          right_inv := fun v => Subtype.ext (f.1.apply_symm_apply v.1) }⟩
    have hemb_inj : Function.Injective embMap := by
      rintro ⟨f₁, emb₁⟩ ⟨f₂, emb₂⟩ heq
      have hrc_eq : (embMap ⟨f₁, emb₁⟩).1 = (embMap ⟨f₂, emb₂⟩).1 := congrArg Sigma.fst heq
      have hre_eq := (Prod.mk.inj hrc_eq).1
      have hce_eq := (Prod.mk.inj hrc_eq).2
      have hemb_val : ∀ (p : Fin K × Fin K) (i : Fin (x p)),
          (emb₁ p i).1 = (emb₂ p i).1 := by
        rintro ⟨a, b⟩ i
        have h1 : ((embMap ⟨f₁, emb₁⟩).1.1 a ⟨b, i⟩).1 = ((embMap ⟨f₂, emb₂⟩).1.1 a ⟨b, i⟩).1 :=
          congrArg Subtype.val (DFunLike.congr_fun (congrFun hre_eq a) ⟨b, i⟩)
        exact Subtype.ext h1
      have hf_eq : f₁ = f₂ := by
        apply Subtype.ext
        apply Equiv.ext
        intro u
        by_cases hu_in : u ∈ Finset.univ.map (rowGlobal (embMap ⟨f₁, emb₁⟩).1.1)
        · rcases Finset.mem_map.mp hu_in with ⟨⟨a, b, i⟩, _, hrow_u⟩
          have hu1 : (emb₁ (a, b) i).1 = u := Subtype.ext (congrArg Subtype.val hrow_u)
          have hu2 : (emb₂ (a, b) i).1 = u := (hemb_val (a, b) i).symm.trans hu1
          have hc12 : ((embMap ⟨f₁, emb₁⟩).1.2 b ⟨a, i⟩).1 =
              ((embMap ⟨f₂, emb₂⟩).1.2 b ⟨a, i⟩).1 :=
            congrArg Subtype.val (DFunLike.congr_fun (congrFun hce_eq b) ⟨a, i⟩)
          apply Subtype.ext
          calc
            (f₁.1 u).1 = (f₁.1 (emb₁ (a, b) i).1).1 := by rw [hu1]
            _ = (f₂.1 (emb₂ (a, b) i).1).1 := hc12
            _ = (f₂.1 u).1 := by rw [hu2]
        · have hu_rem1 : u ∈ remDomSub (embMap ⟨f₁, emb₁⟩).1.1 :=
            Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, hu_in⟩
          have h_eval : ∀ (p₁ p₂ : RHS), p₁ = p₂ →
              ∀ (h₁ : u ∈ remDomSub p₁.1.1) (h₂ : u ∈ remDomSub p₂.1.1),
                (p₁.2 ⟨u, h₁⟩).1 = (p₂.2 ⟨u, h₂⟩).1 := by
            rintro p _ rfl _ _
            rfl
          have hu_rem2 : u ∈ remDomSub (embMap ⟨f₂, emb₂⟩).1.1 := by
            have hcongr : remDomSub (embMap ⟨f₁, emb₁⟩).1.1 =
                remDomSub (embMap ⟨f₂, emb₂⟩).1.1 := congrArg remDomSub hre_eq
            rwa [← hcongr]
          exact h_eval (embMap ⟨f₁, emb₁⟩) (embMap ⟨f₂, emb₂⟩) heq hu_rem1 hu_rem2
      subst hf_eq
      have hemb_eq : emb₁ = emb₂ := by
        funext p
        apply DFunLike.ext
        intro i
        exact Subtype.ext (hemb_val p i)
      subst hemb_eq
      rfl
    have hcard_inj := Fintype.card_le_of_injective embMap hemb_inj
    have hLHS_ge : ValSet.card * (∏ p : Fin K × Fin K, (x p) !) ≤ Fintype.card LHS := by
      dsimp [LHS]
      rw [Fintype.card_sigma]
      have hfib : ∀ f : {f // f ∈ ValSet},
          (∏ p : Fin K × Fin K, (x p) !) ≤
            Fintype.card (∀ p : Fin K × Fin K, Fin (x p) ↪ {u // u ∈ absResCellSet A' B' f.1 p}) := by
        intro f
        rw [Fintype.card_pi]
        refine prod_le_prod_nat Finset.univ fun p _ => ?_
        rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe]
        exact factorial_le_descFactorial ((Finset.mem_filter.mp f.2).2 p)
      calc
        ValSet.card * (∏ p : Fin K × Fin K, (x p) !)
            = ∑ _f : {f // f ∈ ValSet}, (∏ p : Fin K × Fin K, (x p) !) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
        _ ≤ ∑ f : {f // f ∈ ValSet},
              Fintype.card (∀ p : Fin K × Fin K, Fin (x p) ↪ {u // u ∈ absResCellSet A' B' f.1 p}) :=
          Finset.sum_le_sum fun f _ => hfib f
    have hRow_le : Fintype.card RowEmb ≤ ∏ p : Fin K × Fin K, ((A' p.1).card) ^ (x p) := by
      dsimp [RowEmb]
      rw [Fintype.card_pi]
      calc
        (∏ a : Fin K, Fintype.card ((Σ b : Fin K, Fin (x (a, b))) ↪ {w // w ∈ A' a}))
            = ∏ a : Fin K, (A' a).card.descFactorial (∑ b : Fin K, x (a, b)) := by
          refine Finset.prod_congr rfl fun a _ => ?_
          rw [Fintype.card_embedding_eq, Fintype.card_coe, Fintype.card_sigma]
          simp only [Fintype.card_fin]
        _ ≤ ∏ a : Fin K, ((A' a).card) ^ (∑ b : Fin K, x (a, b)) :=
          prod_le_prod_nat Finset.univ fun a _ => descFactorial_le_pow _ _
        _ = ∏ a : Fin K, ∏ b : Fin K, ((A' a).card) ^ (x (a, b)) := by
          refine Finset.prod_congr rfl fun a _ => ?_
          exact (Finset.prod_pow_eq_pow_sum Finset.univ (fun b => x (a, b)) (A' a).card).symm
        _ = ∏ p : Fin K × Fin K, ((A' p.1).card) ^ (x p) :=
          (Fintype.prod_prod_type (fun p : Fin K × Fin K => ((A' p.1).card) ^ (x p))).symm
    have hCol_le : Fintype.card ColEmb ≤ ∏ p : Fin K × Fin K, ((B' p.2).card) ^ (x p) := by
      dsimp [ColEmb]
      rw [Fintype.card_pi]
      calc
        (∏ b : Fin K, Fintype.card ((Σ a : Fin K, Fin (x (a, b))) ↪ {w // w ∈ B' b}))
            = ∏ b : Fin K, (B' b).card.descFactorial (∑ a : Fin K, x (a, b)) := by
          refine Finset.prod_congr rfl fun b _ => ?_
          rw [Fintype.card_embedding_eq, Fintype.card_coe, Fintype.card_sigma]
          simp only [Fintype.card_fin]
        _ ≤ ∏ b : Fin K, ((B' b).card) ^ (∑ a : Fin K, x (a, b)) :=
          prod_le_prod_nat Finset.univ fun b _ => descFactorial_le_pow _ _
        _ = ∏ b : Fin K, ∏ a : Fin K, ((B' b).card) ^ (x (a, b)) := by
          refine Finset.prod_congr rfl fun b _ => ?_
          exact (Finset.prod_pow_eq_pow_sum Finset.univ (fun a => x (a, b)) (B' b).card).symm
        _ = ∏ a : Fin K, ∏ b : Fin K, ((B' b).card) ^ (x (a, b)) := Finset.prod_comm
        _ = ∏ p : Fin K × Fin K, ((B' p.2).card) ^ (x p) :=
          (Fintype.prod_prod_type (fun p : Fin K × Fin K => ((B' p.2).card) ^ (x p))).symm
    have hRHS_le : Fintype.card RHS ≤
        (m₀ - X) ! * ∏ p : Fin K × Fin K, ((A' p.1).card * (B' p.2).card) ^ (x p) := by
      dsimp [RHS]
      rw [Fintype.card_sigma]
      have hrem_card : ∀ rc : RowEmb × ColEmb,
          Fintype.card ({u // u ∈ remDomSub rc.1} ≃ {v // v ∈ remCodSub rc.2}) = (m₀ - X) ! :=
        fun rc => card_equiv_finset_eq_factorial (hcard_remDom rc.1) (hcard_remCod rc.2)
      simp_rw [hrem_card]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, smul_eq_mul,
        mul_comm _ ((m₀ - X) !)]
      refine Nat.mul_le_mul_left ((m₀ - X) !) ?_
      calc
        Fintype.card RowEmb * Fintype.card ColEmb
            ≤ (∏ p : Fin K × Fin K, ((A' p.1).card) ^ (x p)) *
                (∏ p : Fin K × Fin K, ((B' p.2).card) ^ (x p)) :=
          Nat.mul_le_mul hRow_le hCol_le
        _ = ∏ p : Fin K × Fin K, (((A' p.1).card) ^ (x p) * ((B' p.2).card) ^ (x p)) :=
          Finset.prod_mul_distrib.symm
        _ = ∏ p : Fin K × Fin K, ((A' p.1).card * (B' p.2).card) ^ (x p) := by
          refine Finset.prod_congr rfl fun p _ => (mul_pow _ _ _).symm
    have hnat_bound :
        ValSet.card * (∏ p : Fin K × Fin K, (x p) !) ≤
          (m₀ - X) ! * ∏ p : Fin K × Fin K, ((A' p.1).card * (B' p.2).card) ^ (x p) :=
      hLHS_ge.trans (hcard_inj.trans hRHS_le)
    -- Step 2: Convert `(m₀ - X)!` into `m₀! * (exp 2 / m₀)^X` via `pow_le_exp_two_mul_descFactorial`
    have hm₀_r_pos : 0 < (m₀ : ℝ) := Nat.cast_pos.mpr hm₀_pos
    have hsplit_fac : (m₀ ! : ℝ) = (m₀.descFactorial X : ℝ) * ((m₀ - X) ! : ℝ) := by
      have h := descFactorial_add_eq m₀ X (m₀ - X)
      rw [Nat.add_sub_of_le hX_le, Nat.descFactorial_self, Nat.descFactorial_self] at h
      exact_mod_cast h
    have hsub_fac_le :
        ((m₀ - X) ! : ℝ) ≤ (m₀ ! : ℝ) * (Real.exp 2 / (m₀ : ℝ)) ^ X := by
      rw [div_pow, mul_div_assoc', le_div_iff₀ (pow_pos hm₀_r_pos X), hsplit_fac]
      calc
        ((m₀ - X) ! : ℝ) * (m₀ : ℝ) ^ X
            ≤ ((m₀ - X) ! : ℝ) * ((Real.exp 2) ^ X * (m₀.descFactorial X : ℝ)) :=
          mul_le_mul_of_nonneg_left (pow_le_exp_two_mul_descFactorial hX_le) (Nat.cast_nonneg _)
        _ = (m₀.descFactorial X : ℝ) * ((m₀ - X) ! : ℝ) * (Real.exp 2) ^ X := by ring
    have hprod_fac_pos : 0 < (∏ p : Fin K × Fin K, ((x p) ! : ℝ)) :=
      Finset.prod_pos fun p _ => Nat.cast_pos.mpr (Nat.factorial_pos (x p))
    have hprod_theta_eq :
        (m₀ ! : ℝ) * (Real.exp 2 / (m₀ : ℝ)) ^ X *
            (∏ p : Fin K × Fin K, (((A' p.1).card : ℝ) * ((B' p.2).card : ℝ)) ^ (x p)) =
          ((m₀ ! : ℝ) * ∏ p : Fin K × Fin K, (absTheta A' B' m₀ p) ^ (x p) / ((x p) ! : ℝ)) *
            (∏ p : Fin K × Fin K, ((x p) ! : ℝ)) := by
      have hpow_X :
          (Real.exp 2 / (m₀ : ℝ)) ^ X =
            ∏ p : Fin K × Fin K, (Real.exp 2 / (m₀ : ℝ)) ^ (x p) :=
        (prod_pow_eq_pow_sum_real Finset.univ (Real.exp 2 / (m₀ : ℝ)) x).symm
      have hprod_lhs :
          (∏ p : Fin K × Fin K, (Real.exp 2 / (m₀ : ℝ)) ^ (x p)) *
              (∏ p : Fin K × Fin K, (((A' p.1).card : ℝ) * ((B' p.2).card : ℝ)) ^ (x p)) =
            ∏ p : Fin K × Fin K, (absTheta A' B' m₀ p) ^ (x p) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun p _ => ?_
        rw [← mul_pow]
        congr 1
        unfold absTheta
        ring
      have hprod_rhs :
          (∏ p : Fin K × Fin K, (absTheta A' B' m₀ p) ^ (x p) / ((x p) ! : ℝ)) *
              (∏ p : Fin K × Fin K, ((x p) ! : ℝ)) =
            ∏ p : Fin K × Fin K, (absTheta A' B' m₀ p) ^ (x p) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun p _ => ?_
        exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (x p)))
      rw [hpow_X, mul_assoc (m₀ ! : ℝ), hprod_lhs, mul_assoc (m₀ ! : ℝ), hprod_rhs]
    have hmul_le :
        (ValSet.card : ℝ) * (∏ p : Fin K × Fin K, ((x p) ! : ℝ)) ≤
          ((m₀ ! : ℝ) * ∏ p : Fin K × Fin K, (absTheta A' B' m₀ p) ^ (x p) / ((x p) ! : ℝ)) *
            (∏ p : Fin K × Fin K, ((x p) ! : ℝ)) := by
      calc
        (ValSet.card : ℝ) * (∏ p : Fin K × Fin K, ((x p) ! : ℝ))
            ≤ ((m₀ - X) ! : ℝ) *
                (∏ p : Fin K × Fin K, (((A' p.1).card : ℝ) * ((B' p.2).card : ℝ)) ^ (x p)) := by
          exact_mod_cast hnat_bound
        _ ≤ ((m₀ ! : ℝ) * (Real.exp 2 / (m₀ : ℝ)) ^ X) *
              (∏ p : Fin K × Fin K, (((A' p.1).card : ℝ) * ((B' p.2).card : ℝ)) ^ (x p)) :=
          mul_le_mul_of_nonneg_right hsub_fac_le
            (Finset.prod_nonneg fun p _ =>
              pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _)
        _ = ((m₀ ! : ℝ) * ∏ p : Fin K × Fin K, (absTheta A' B' m₀ p) ^ (x p) / ((x p) ! : ℝ)) *
              (∏ p : Fin K × Fin K, ((x p) ! : ℝ)) := hprod_theta_eq
    exact le_of_mul_le_mul_right hmul_le hprod_fac_pos
  · push Not at hX_le
    have hempty : ValSet = ∅ := by
      ext f
      simp only [ValSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      intro hall
      have hsum_le : X ≤ m₀ := by
        calc
          X = ∑ p : Fin K × Fin K, x p := rfl
          _ ≤ ∑ p : Fin K × Fin K, absResCellCard A' B' f p :=
            Finset.sum_le_sum fun p _ => hall p
          _ = m₀ := sum_absResCellCard_eq hdom hA_disj hA_union hB_disj hB_union f
      omega
    change (ValSet.card : ℝ) ≤ _
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (Nat.cast_nonneg _)
      (Finset.prod_nonneg fun p _ =>
        div_nonneg (pow_nonneg (absTheta_nonneg A' B' m₀ p) _) (Nat.cast_nonneg _))

/-! ### 4. Conditional Residual Attachment Bounds Across All Three Regimes -/

theorem prod_ite_zero_eq {ι : Type*} (s : Finset ι) (P : ι → Prop)
    [∀ i, Decidable (P i)] (g : ι → ℝ) :
    (∏ i ∈ s, if P i then g i else 0) =
      if (∀ i ∈ s, P i) then (∏ i ∈ s, g i) else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ih]
    by_cases hPa : P a
    · by_cases hPs : ∀ i ∈ s, P i
      · have hall : ∀ i ∈ insert a s, P i :=
          fun i hi => (Finset.mem_insert.mp hi).elim (fun h => h ▸ hPa) (hPs i)
        rw [ite_eq_left_of_eq_true _ _ (eq_true hPa),
          ite_eq_left_of_eq_true _ _ (eq_true hPs),
          ite_eq_left_of_eq_true _ _ (eq_true hall), Finset.prod_insert ha]
      · have hnall : ¬ ∀ i ∈ insert a s, P i :=
          fun h => hPs (fun i hi => h i (Finset.mem_insert_of_mem hi))
        rw [ite_eq_left_of_eq_true _ _ (eq_true hPa),
          ite_eq_right_of_eq_false _ _ (eq_false hPs),
          ite_eq_right_of_eq_false _ _ (eq_false hnall), mul_zero]
    · have hnall : ¬ ∀ i ∈ insert a s, P i :=
        fun h => hPa (h a (Finset.mem_insert_self a s))
      rw [ite_eq_right_of_eq_false _ _ (eq_false hPa),
        ite_eq_right_of_eq_false _ _ (eq_false hnall), zero_mul]

/-- Truncated residual cell moment `q_p = ∑_{x=2}^{R₀} g(x) * θ_p^x / x!`. -/
noncomputable def absQWeight {n K : ℕ} (A' B' : Fin K → Finset (Fin n)) (m₀ R₀ : ℕ)
    (p : Fin K × Fin K) : ℝ :=
  ∑ x ∈ Finset.Icc 2 R₀, localCellReward x * (absTheta A' B' m₀ p) ^ x / (x ! : ℝ)

theorem absQWeight_nonneg {n K : ℕ} (A' B' : Fin K → Finset (Fin n)) (m₀ R₀ : ℕ)
    (p : Fin K × Fin K) :
    0 ≤ absQWeight A' B' m₀ R₀ p :=
  Finset.sum_nonneg fun x _ =>
    div_nonneg
      (mul_nonneg (localCellReward_pos x).le (pow_nonneg (absTheta_nonneg A' B' m₀ p) x))
      (Nat.cast_nonneg _)

/-- **Proposition 9.4 (`arXiv:2608.30604`) — Generating-Function Residual Attachment Bound**:
For any `0 < m₀`, partial block matching `M`, and `E₀ = Finset.univ \ M`, summing
`(∏_{p ∈ E₀} g(r'_p(f))) * #{F ⊆ M ∪ H_res(f) | IsEvenOverlapSubgraph F}` over residual bijections
with `r'_p(f) ≤ R₀` on `E₀` is bounded by `m₀! * exp(2 * ∑_{p ∈ E₀} absQWeight A' B' m₀ R₀ p)`. -/
theorem absResSum_intrinsic_le_exp {n K m₀ R₀ : ℕ} {U_dom U_cod : Finset (Fin n)}
    {A' B' : Fin K → Finset (Fin n)}
    {M : Finset (Fin K × Fin K)}
    (hM : IsBlockMatching K M)
    (hm₀_pos : 0 < m₀)
    (hdom : U_dom.card = m₀)
    (hcod : U_cod.card = m₀)
    (hA_disj : (Set.univ : Set (Fin K)).PairwiseDisjoint A')
    (hA_union : Finset.univ.biUnion A' = U_dom)
    (hB_disj : (Set.univ : Set (Fin K)).PairwiseDisjoint B')
    (hB_union : Finset.univ.biUnion B' = U_cod) :
    (∑ f ∈ Finset.univ.filter (fun f : {u // u ∈ U_dom} ≃ {v // v ∈ U_cod} =>
        (∀ p ∈ M, absResCellCard A' B' f p = 0) ∧
        (∀ p ∈ Finset.univ \ M, absResCellCard A' B' f p ≤ R₀)),
      (∏ p ∈ Finset.univ \ M, localCellReward (absResCellCard A' B' f p)) *
        (((M ∪ (Finset.univ \ M).filter (fun p => 2 ≤ absResCellCard A' B' f p)).powerset.filter
          IsEvenOverlapSubgraph).card : ℝ)) ≤
      (m₀ ! : ℝ) * Real.exp (2 * ∑ p ∈ Finset.univ \ M, absQWeight A' B' m₀ R₀ p) := by
  let E₀ : Finset (Fin K × Fin K) := Finset.univ \ M
  let validBij := Finset.univ.filter (fun f : {u // u ∈ U_dom} ≃ {v // v ∈ U_cod} =>
    (∀ p ∈ M, absResCellCard A' B' f p = 0) ∧
    (∀ p ∈ E₀, absResCellCard A' B' f p ≤ R₀))
  let EvenAll := (M ∪ E₀).powerset.filter IsEvenOverlapSubgraph
  have hcard_even_eq : ∀ f ∈ validBij,
      (((M ∪ E₀.filter (fun p => 2 ≤ absResCellCard A' B' f p)).powerset.filter
          IsEvenOverlapSubgraph).card : ℝ) =
        ∑ F ∈ EvenAll, if (∀ p ∈ F \ M, 2 ≤ absResCellCard A' B' f p) then (1 : ℝ) else 0 := by
    intro f _
    have hset_eq :
        (M ∪ E₀.filter (fun p => 2 ≤ absResCellCard A' B' f p)).powerset.filter
            IsEvenOverlapSubgraph =
          EvenAll.filter (fun F => ∀ p ∈ F \ M, 2 ≤ absResCellCard A' B' f p) := by
      ext F
      simp only [EvenAll, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · rintro ⟨hsub, hev⟩
        refine ⟨⟨fun p hp => ?_, hev⟩, fun p hp => ?_⟩
        · rcases Finset.mem_union.mp (hsub hp) with h1 | h2
          · exact Finset.mem_union_left _ h1
          · exact Finset.mem_union_right _ (Finset.mem_filter.mp h2).1
        · rcases Finset.mem_sdiff.mp hp with ⟨hpF, hpM⟩
          rcases Finset.mem_union.mp (hsub hpF) with h1 | h2
          · exact False.elim (hpM h1)
          · exact (Finset.mem_filter.mp h2).2
      · rintro ⟨⟨hsub, hev⟩, hall⟩
        refine ⟨fun p hp => ?_, hev⟩
        by_cases hpM : p ∈ M
        · exact Finset.mem_union_left _ hpM
        · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨?_, ?_⟩)
          · rcases Finset.mem_union.mp (hsub hp) with h1 | h2
            · exact False.elim (hpM h1)
            · exact h2
          · exact hall p (Finset.mem_sdiff.mpr ⟨hp, hpM⟩)
    rw [hset_eq, Finset.card_filter]
    push_cast
    rfl
  have hlhs_swap :
      (∑ f ∈ validBij,
        (∏ p ∈ E₀, localCellReward (absResCellCard A' B' f p)) *
          (((M ∪ E₀.filter (fun p => 2 ≤ absResCellCard A' B' f p)).powerset.filter
            IsEvenOverlapSubgraph).card : ℝ)) =
      ∑ F ∈ EvenAll, ∑ f ∈ validBij,
        (∏ p ∈ E₀, localCellReward (absResCellCard A' B' f p)) *
          (if (∀ p ∈ F \ M, 2 ≤ absResCellCard A' B' f p) then (1 : ℝ) else 0) := by
    have hcongr : ∀ f ∈ validBij,
        (∏ p ∈ E₀, localCellReward (absResCellCard A' B' f p)) *
          (((M ∪ E₀.filter (fun p => 2 ≤ absResCellCard A' B' f p)).powerset.filter
            IsEvenOverlapSubgraph).card : ℝ) =
        ∑ F ∈ EvenAll,
          (∏ p ∈ E₀, localCellReward (absResCellCard A' B' f p)) *
            (if (∀ p ∈ F \ M, 2 ≤ absResCellCard A' B' f p) then (1 : ℝ) else 0) := by
      intro f hf
      rw [hcard_even_eq f hf, Finset.mul_sum]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_comm]
  rw [hlhs_swap]
  -- Bound each `F ∈ EvenAll` via `Finset.prod_univ_sum` and Lemma 6.2
  have hF_bound : ∀ F ∈ EvenAll,
      (∑ f ∈ validBij,
        (∏ p ∈ E₀, localCellReward (absResCellCard A' B' f p)) *
          (if (∀ p ∈ F \ M, 2 ≤ absResCellCard A' B' f p) then (1 : ℝ) else 0)) ≤
      (m₀ ! : ℝ) *
        ((∏ p ∈ E₀, (1 + absQWeight A' B' m₀ R₀ p)) *
          (∏ p ∈ F \ M, absQWeight A' B' m₀ R₀ p)) := by
    intro F hF
    let S : Finset (Fin K × Fin K) := F \ M
    have hS_sub : S ⊆ E₀ := by
      have hF_sub : F ⊆ M ∪ E₀ := Finset.mem_powerset.mp (Finset.mem_filter.mp hF).1
      intro p hp
      rcases Finset.mem_sdiff.mp hp with ⟨hpF, hpM⟩
      rcases Finset.mem_union.mp (hF_sub hpF) with h1 | h2
      · exact False.elim (hpM h1)
      · exact h2
    let box (p : Fin K × Fin K) : Finset ℕ :=
      if p ∈ S then Finset.Icc 2 R₀
      else if p ∈ E₀ then insert 0 (Finset.Icc 3 R₀)
      else {0}
    have hpoint : ∀ f ∈ validBij,
        (∏ p ∈ E₀, localCellReward (absResCellCard A' B' f p)) *
          (if (∀ p ∈ S, 2 ≤ absResCellCard A' B' f p) then (1 : ℝ) else 0) ≤
        ∑ x ∈ Fintype.piFinset box,
          if (∀ p : Fin K × Fin K, x p ≤ absResCellCard A' B' f p) then
            (∏ p : Fin K × Fin K, localCellReward (x p))
          else 0 := by
      intro f hf
      have hfE₀ : ∀ p ∈ E₀, absResCellCard A' B' f p ≤ R₀ := (Finset.mem_filter.mp hf).2.2
      set r := absResCellCard A' B' f
      have hite_prod :
          (if (∀ p ∈ S, 2 ≤ r p) then (1 : ℝ) else 0) =
            ∏ p ∈ S, if 2 ≤ r p then (1 : ℝ) else 0 := by
        rw [prod_ite_zero_eq S (fun p => 2 ≤ r p) (fun _ => (1 : ℝ)), Finset.prod_const_one]
        split_ifs <;> rfl
      have hlhs_univ :
          (∏ p ∈ E₀, localCellReward (r p)) * (∏ p ∈ S, if 2 ≤ r p then (1 : ℝ) else 0) =
            ∏ p : Fin K × Fin K,
              ((if p ∈ E₀ then localCellReward (r p) else 1) *
                (if p ∈ S then (if 2 ≤ r p then (1 : ℝ) else 0) else 1)) := by
        simp only [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter]
      have hfactor_le : ∀ p : Fin K × Fin K,
          ((if p ∈ E₀ then localCellReward (r p) else 1) *
            (if p ∈ S then (if 2 ≤ r p then (1 : ℝ) else 0) else 1)) ≤
          ∑ x ∈ box p, if x ≤ r p then localCellReward x else 0 := by
        intro p
        have hsum_nn : ∀ t : Finset ℕ,
            0 ≤ ∑ x ∈ t, if x ≤ r p then localCellReward x else 0 :=
          fun t => Finset.sum_nonneg fun x _ => by
            split_ifs
            · exact (localCellReward_pos x).le
            · norm_num
        by_cases hpS : p ∈ S
        · have hpE₀ : p ∈ E₀ := hS_sub hpS
          have hr_hi : r p ≤ R₀ := hfE₀ p hpE₀
          simp only [box, hpS, hpE₀, ↓reduceIte]
          by_cases h2 : 2 ≤ r p
          · simp only [h2, ↓reduceIte, mul_one]
            have hmem : r p ∈ Finset.Icc 2 R₀ := Finset.mem_Icc.mpr ⟨h2, hr_hi⟩
            have hsingle := Finset.single_le_sum
              (f := fun x => if x ≤ r p then localCellReward x else 0)
              (fun x _ => by split_ifs; exact (localCellReward_pos x).le; norm_num) hmem
            simpa only [le_rfl, ↓reduceIte] using hsingle
          · simp only [h2, ↓reduceIte, mul_zero]
            exact hsum_nn _
        · by_cases hpE₀ : p ∈ E₀
          · have hr_hi : r p ≤ R₀ := hfE₀ p hpE₀
            simp only [box, hpS, hpE₀, ↓reduceIte, mul_one]
            by_cases hr2 : r p ≤ 2
            · rw [localCellReward_eq_one_of_le_two hr2]
              have h0_mem : (0 : ℕ) ∈ insert 0 (Finset.Icc 3 R₀) :=
                Finset.mem_insert_self 0 _
              have hsingle := Finset.single_le_sum
                (f := fun x => if x ≤ r p then localCellReward x else 0)
                (fun x _ => by split_ifs; exact (localCellReward_pos x).le; norm_num) h0_mem
              simpa only [Nat.zero_le, ↓reduceIte,
                localCellReward_eq_one_of_le_two (by omega : 0 ≤ 2)] using hsingle
            · push Not at hr2
              have hmem : r p ∈ insert 0 (Finset.Icc 3 R₀) :=
                Finset.mem_insert_of_mem (Finset.mem_Icc.mpr ⟨by omega, hr_hi⟩)
              have hsingle := Finset.single_le_sum
                (f := fun x => if x ≤ r p then localCellReward x else 0)
                (fun x _ => by split_ifs; exact (localCellReward_pos x).le; norm_num) hmem
              simpa only [le_rfl, ↓reduceIte] using hsingle
          · simp only [box, hpS, hpE₀, ↓reduceIte, mul_one, Finset.sum_singleton,
              Nat.zero_le, localCellReward_eq_one_of_le_two (by omega : 0 ≤ 2), le_rfl]
      have hprod_step :
          ∏ p : Fin K × Fin K,
            ((if p ∈ E₀ then localCellReward (r p) else 1) *
              (if p ∈ S then (if 2 ≤ r p then (1 : ℝ) else 0) else 1)) ≤
          ∏ p : Fin K × Fin K, (∑ x ∈ box p, if x ≤ r p then localCellReward x else 0) := by
        refine prod_le_prod_real Finset.univ (fun p _ => ?_) (fun p _ => hfactor_le p)
        refine mul_nonneg ?_ ?_
        · split_ifs
          · exact (localCellReward_pos _).le
          · norm_num
        · split_ifs <;> norm_num
      rw [hite_prod, hlhs_univ]
      refine hprod_step.trans_eq ?_
      rw [Finset.prod_univ_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [prod_ite_zero_eq Finset.univ (fun p => x p ≤ r p) (fun p => localCellReward (x p))]
      simp only [Finset.mem_univ, forall_true_left]
    -- Sum `hpoint` over `f ∈ validBij`, swap with `x`, apply Lemma 6.2, and refactor
    have hsum_x :
        (∑ f ∈ validBij, ∑ x ∈ Fintype.piFinset box,
          if (∀ p : Fin K × Fin K, x p ≤ absResCellCard A' B' f p) then
            (∏ p : Fin K × Fin K, localCellReward (x p))
          else 0) ≤
        (m₀ ! : ℝ) *
          ∏ p : Fin K × Fin K,
            ∑ x ∈ box p, localCellReward x * (absTheta A' B' m₀ p) ^ x / (x ! : ℝ) := by
      rw [Finset.sum_comm]
      have hterm_x : ∀ x ∈ Fintype.piFinset box,
          (∑ f ∈ validBij,
            if (∀ p : Fin K × Fin K, x p ≤ absResCellCard A' B' f p) then
              (∏ p : Fin K × Fin K, localCellReward (x p))
            else 0) ≤
          (m₀ ! : ℝ) *
            ∏ p : Fin K × Fin K,
              (localCellReward (x p) * (absTheta A' B' m₀ p) ^ (x p) / ((x p) ! : ℝ)) := by
        intro x _
        have hsub_univ :
            (∑ f ∈ validBij,
              if (∀ p : Fin K × Fin K, x p ≤ absResCellCard A' B' f p) then
                (∏ p : Fin K × Fin K, localCellReward (x p))
              else 0) ≤
            ∑ f : {u // u ∈ U_dom} ≃ {v // v ∈ U_cod},
              if (∀ p : Fin K × Fin K, x p ≤ absResCellCard A' B' f p) then
                (∏ p : Fin K × Fin K, localCellReward (x p))
              else 0 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun f _ _ => ?_
          split_ifs
          · exact Finset.prod_nonneg fun p _ => (localCellReward_pos (x p)).le
          · norm_num
        have heval_univ :
            (∑ f : {u // u ∈ U_dom} ≃ {v // v ∈ U_cod},
              if (∀ p : Fin K × Fin K, x p ≤ absResCellCard A' B' f p) then
                (∏ p : Fin K × Fin K, localCellReward (x p))
              else 0) =
            ((Finset.univ.filter (fun f : {u // u ∈ U_dom} ≃ {v // v ∈ U_cod} =>
              ∀ p : Fin K × Fin K, x p ≤ absResCellCard A' B' f p)).card : ℝ) *
              (∏ p : Fin K × Fin K, localCellReward (x p)) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
        have hlem62 := card_prescribed_absResBij_le hm₀_pos hdom hcod hA_disj hA_union
          hB_disj hB_union x
        have hrew_prod :
            ((m₀ ! : ℝ) *
                ∏ p : Fin K × Fin K, (absTheta A' B' m₀ p) ^ (x p) / ((x p) ! : ℝ)) *
              (∏ p : Fin K × Fin K, localCellReward (x p)) =
            (m₀ ! : ℝ) *
              ∏ p : Fin K × Fin K,
                (localCellReward (x p) * (absTheta A' B' m₀ p) ^ (x p) / ((x p) ! : ℝ)) := by
          rw [mul_assoc, ← Finset.prod_mul_distrib]
          congr 1
          refine Finset.prod_congr rfl fun p _ => ?_
          ring
        calc
          (∑ f ∈ validBij, _) ≤ _ := hsub_univ
          _ = _ := heval_univ
          _ ≤ ((m₀ ! : ℝ) *
                ∏ p : Fin K × Fin K, (absTheta A' B' m₀ p) ^ (x p) / ((x p) ! : ℝ)) *
              (∏ p : Fin K × Fin K, localCellReward (x p)) :=
            mul_le_mul_of_nonneg_right hlem62
              (Finset.prod_nonneg fun p _ => (localCellReward_pos (x p)).le)
          _ = _ := hrew_prod
      calc
        (∑ x ∈ Fintype.piFinset box, _)
            ≤ ∑ x ∈ Fintype.piFinset box,
                (m₀ ! : ℝ) *
                  ∏ p : Fin K × Fin K,
                    (localCellReward (x p) * (absTheta A' B' m₀ p) ^ (x p) / ((x p) ! : ℝ)) :=
          Finset.sum_le_sum hterm_x
        _ = (m₀ ! : ℝ) *
              ∑ x ∈ Fintype.piFinset box,
                ∏ p : Fin K × Fin K,
                  (localCellReward (x p) * (absTheta A' B' m₀ p) ^ (x p) / ((x p) ! : ℝ)) :=
          (Finset.mul_sum _ _ _).symm
        _ = (m₀ ! : ℝ) *
              ∏ p : Fin K × Fin K,
                ∑ x ∈ box p, localCellReward x * (absTheta A' B' m₀ p) ^ x / (x ! : ℝ) := by
          congr 1
          symm
          rw [Finset.prod_univ_sum]
    have hprod_box_le :
        (∏ p : Fin K × Fin K,
            ∑ x ∈ box p, localCellReward x * (absTheta A' B' m₀ p) ^ x / (x ! : ℝ)) ≤
          (∏ p ∈ E₀, (1 + absQWeight A' B' m₀ R₀ p)) *
            (∏ p ∈ S, absQWeight A' B' m₀ R₀ p) := by
      have hrhs_univ :
          (∏ p ∈ E₀, (1 + absQWeight A' B' m₀ R₀ p)) *
              (∏ p ∈ S, absQWeight A' B' m₀ R₀ p) =
            ∏ p : Fin K × Fin K,
              ((if p ∈ E₀ then 1 + absQWeight A' B' m₀ R₀ p else 1) *
                (if p ∈ S then absQWeight A' B' m₀ R₀ p else 1)) := by
        simp only [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter]
      rw [hrhs_univ]
      refine prod_le_prod_real Finset.univ
        (fun p _ => Finset.sum_nonneg fun x _ =>
          div_nonneg (mul_nonneg (localCellReward_pos x).le
            (pow_nonneg (absTheta_nonneg A' B' m₀ p) x)) (Nat.cast_nonneg _))
        fun p _ => ?_
      have hq_nn : 0 ≤ absQWeight A' B' m₀ R₀ p := absQWeight_nonneg A' B' m₀ R₀ p
      by_cases hpS : p ∈ S
      · have hpE₀ : p ∈ E₀ := hS_sub hpS
        simp only [box, hpS, hpE₀, ↓reduceIte]
        change absQWeight A' B' m₀ R₀ p ≤
          (1 + absQWeight A' B' m₀ R₀ p) * absQWeight A' B' m₀ R₀ p
        nlinarith
      · by_cases hpE₀ : p ∈ E₀
        · simp only [box, hpS, hpE₀, ↓reduceIte, mul_one]
          have h0_not : (0 : ℕ) ∉ Finset.Icc 3 R₀ := by simp
          rw [Finset.sum_insert h0_not]
          have h0_eval :
              localCellReward 0 * (absTheta A' B' m₀ p) ^ 0 / ((0 ! : ℕ) : ℝ) = 1 := by
            rw [localCellReward_eq_one_of_le_two (by omega : 0 ≤ 2)]
            norm_num
          rw [h0_eval]
          refine add_le_add_right ?_ 1
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (fun x hx => Finset.mem_Icc.mpr ⟨by linarith [(Finset.mem_Icc.mp hx).1],
              (Finset.mem_Icc.mp hx).2⟩)
            fun x _ _ => div_nonneg (mul_nonneg (localCellReward_pos x).le
              (pow_nonneg (absTheta_nonneg A' B' m₀ p) x)) (Nat.cast_nonneg _)
        · simp only [box, hpS, hpE₀, ↓reduceIte, mul_one, Finset.sum_singleton]
          rw [localCellReward_eq_one_of_le_two (by omega : 0 ≤ 2)]
          norm_num
    exact (Finset.sum_le_sum hpoint).trans
      (hsum_x.trans (mul_le_mul_of_nonneg_left hprod_box_le (Nat.cast_nonneg _)))
  -- Sum `hF_bound` over `F ∈ EvenAll` and invoke Lemma 9.3 (`sum_evenSubgraphs_prod_sdiff_le`)
  have hexp_bound :
      (∏ p ∈ E₀, (1 + absQWeight A' B' m₀ R₀ p)) *
          (∑ F ∈ EvenAll, ∏ p ∈ F \ M, absQWeight A' B' m₀ R₀ p) ≤
        Real.exp (2 * ∑ p ∈ E₀, absQWeight A' B' m₀ R₀ p) := by
    have h1 : (∏ p ∈ E₀, (1 + absQWeight A' B' m₀ R₀ p)) ≤
        Real.exp (∑ p ∈ E₀, absQWeight A' B' m₀ R₀ p) :=
      prod_one_add_le_exp_sum E₀ (fun p _ => absQWeight_nonneg A' B' m₀ R₀ p)
    have h2 : (∑ F ∈ EvenAll, ∏ p ∈ F \ M, absQWeight A' B' m₀ R₀ p) ≤
        Real.exp (∑ p ∈ E₀, absQWeight A' B' m₀ R₀ p) :=
      (sum_evenSubgraphs_prod_sdiff_le hM (fun p _ => absQWeight_nonneg A' B' m₀ R₀ p)).trans h1
    calc
      (∏ p ∈ E₀, (1 + absQWeight A' B' m₀ R₀ p)) *
          (∑ F ∈ EvenAll, ∏ p ∈ F \ M, absQWeight A' B' m₀ R₀ p)
          ≤ Real.exp (∑ p ∈ E₀, absQWeight A' B' m₀ R₀ p) *
              Real.exp (∑ p ∈ E₀, absQWeight A' B' m₀ R₀ p) :=
        mul_le_mul h1 h2
          (Finset.sum_nonneg fun F _ =>
            Finset.prod_nonneg fun p _ => absQWeight_nonneg A' B' m₀ R₀ p)
          (Real.exp_pos _).le
      _ = Real.exp (2 * ∑ p ∈ E₀, absQWeight A' B' m₀ R₀ p) := by
        rw [← Real.exp_add, two_mul]
  calc
    (∑ F ∈ EvenAll, ∑ f ∈ validBij, _)
        ≤ ∑ F ∈ EvenAll,
            (m₀ ! : ℝ) *
              ((∏ p ∈ E₀, (1 + absQWeight A' B' m₀ R₀ p)) *
                (∏ p ∈ F \ M, absQWeight A' B' m₀ R₀ p)) :=
      Finset.sum_le_sum hF_bound
    _ = (m₀ ! : ℝ) *
          ((∏ p ∈ E₀, (1 + absQWeight A' B' m₀ R₀ p)) *
            (∑ F ∈ EvenAll, ∏ p ∈ F \ M, absQWeight A' B' m₀ R₀ p)) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (m₀ ! : ℝ) * Real.exp (2 * ∑ p ∈ E₀, absQWeight A' B' m₀ R₀ p) :=
      mul_le_mul_of_nonneg_left hexp_bound (Nat.cast_nonneg _)

theorem two_mul_choose_two (k : ℕ) : 2 * k.choose 2 = k * (k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases k with _ | k
    · simp
    · rw [show (k + 1 + 1).choose 2 = (k + 1).choose 1 + (k + 1).choose 2 from
        Nat.choose_succ_succ (k + 1) 1, Nat.choose_one_right, mul_add, ih]
      simp only [Nat.add_sub_cancel]
      ring

theorem two_mul_choose_two_sub_one_eq {x : ℕ} (hx : 2 ≤ x) :
    2 * (x.choose 2 - 1) = (x - 2) * (x + 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hx
  have h1 : 1 ≤ (2 + d).choose 2 := by simpa using Nat.choose_le_choose 2 (Nat.le_add_right 2 d)
  have h2 := two_mul_choose_two (2 + d)
  have hid : (2 + d - 2) * (2 + d + 1) + 2 = (2 + d) * (2 + d - 1) := by
    rw [show 2 + d - 2 = d by omega, show 2 + d - 1 = d + 1 by omega]
    ring
  omega

/-- **Master Uniform Residual Sum Bound Across `m₀ = 0`, Complementary, and Intrinsic Regimes**:
Under the asymptotic high-cap hypotheses (`98 ≤ U`, `R₀ = U / 2`, `4 * 10^10 ≤ L`, `n = exp L`,
`U ≤ 3 * L`, `2^U ≤ n^2`, and `exp 12 * U^12 ≤ 2^(U / 3)`), the conditional residual sum is at
most `m₀! * exp(n / L^5)` uniformly in `m₀` and `(A', B')`. -/
theorem absResSum_le_master {n K m₀ U R₀ : ℕ} {L : ℝ}
    {U_dom U_cod : Finset (Fin n)}
    {A' B' : Fin K → Finset (Fin n)}
    {M : Finset (Fin K × Fin K)}
    (hM : IsBlockMatching K M)
    (hdom : U_dom.card = m₀)
    (hcod : U_cod.card = m₀)
    (hA_disj : (Set.univ : Set (Fin K)).PairwiseDisjoint A')
    (hA_union : Finset.univ.biUnion A' = U_dom)
    (hB_disj : (Set.univ : Set (Fin K)).PairwiseDisjoint B')
    (hB_union : Finset.univ.biUnion B' = U_cod)
    (hA_cap : ∀ a : Fin K, (A' a).card ≤ U)
    (hB_cap : ∀ b : Fin K, (B' b).card ≤ U)
    (hU_lo : 98 ≤ U)
    (hR₀ : R₀ = U / 2)
    (hL_big : (4 * 10 ^ 10 : ℝ) ≤ L)
    (hn_exp : (n : ℝ) = Real.exp L)
    (hU_hi : (U : ℝ) ≤ 3 * L)
    (h2U_hi : (2 : ℝ) ^ U ≤ (n : ℝ) ^ 2)
    (h2U3_lo : Real.exp 12 * (U : ℝ) ^ 12 ≤ (2 : ℝ) ^ (U / 3)) :
    (∑ f ∈ Finset.univ.filter (fun f : {u // u ∈ U_dom} ≃ {v // v ∈ U_cod} =>
        (∀ p ∈ M, absResCellCard A' B' f p = 0) ∧
        (∀ p ∈ Finset.univ \ M, absResCellCard A' B' f p ≤ R₀)),
      (∏ p ∈ Finset.univ \ M, localCellReward (absResCellCard A' B' f p)) *
        (((M ∪ (Finset.univ \ M).filter (fun p => 2 ≤ absResCellCard A' B' f p)).powerset.filter
          IsEvenOverlapSubgraph).card : ℝ)) ≤
      (m₀ ! : ℝ) * Real.exp ((n : ℝ) / L ^ 5) := by
  let E₀ : Finset (Fin K × Fin K) := Finset.univ \ M
  let validBij := Finset.univ.filter (fun f : {u // u ∈ U_dom} ≃ {v // v ∈ U_cod} =>
    (∀ p ∈ M, absResCellCard A' B' f p = 0) ∧
    (∀ p ∈ E₀, absResCellCard A' B' f p ≤ R₀))
  have hL_pos : 0 < L := by linarith only [hL_big]
  have hn_pos : 0 < (n : ℝ) := by rw [hn_exp]; exact Real.exp_pos L
  rcases Nat.eq_zero_or_pos m₀ with rfl | hm₀_pos
  · -- Regime 1: `m₀ = 0`
    have hterm_le_one : ∀ f ∈ validBij,
        (∏ p ∈ E₀, localCellReward (absResCellCard A' B' f p)) *
          (((M ∪ E₀.filter (fun p => 2 ≤ absResCellCard A' B' f p)).powerset.filter
            IsEvenOverlapSubgraph).card : ℝ) ≤ 1 := by
      intro f _
      have hsum0 := sum_absResCellCard_eq hdom hA_disj hA_union hB_disj hB_union f
      have hall0 : ∀ p : Fin K × Fin K, absResCellCard A' B' f p = 0 := fun p =>
        Nat.eq_zero_of_le_zero
          ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)).trans hsum0.le)
      have hprod1 : (∏ p ∈ E₀, localCellReward (absResCellCard A' B' f p)) = 1 := by
        refine Finset.prod_eq_one fun p _ => ?_
        rw [hall0 p]
        exact localCellReward_eq_one_of_le_two (by omega)
      have hH_empty : E₀.filter (fun p => 2 ≤ absResCellCard A' B' f p) = ∅ := by
        ext p
        simp [hall0]
      rw [hprod1, one_mul, hH_empty]
      have hcard_le1 : ((M ∪ ∅).powerset.filter IsEvenOverlapSubgraph).card ≤ 1 := by
        simpa using card_evenSubgraphs_union_le (H := ∅) hM
      exact_mod_cast hcard_le1
    have hcard_valid : validBij.card ≤ 1 := by
      calc
        validBij.card ≤ (Finset.univ : Finset ({u // u ∈ U_dom} ≃ {v // v ∈ U_cod})).card :=
          Finset.card_le_card (Finset.subset_univ _)
        _ = 0 ! := by rw [Finset.card_univ, card_equiv_finset_eq_factorial hdom hcod]
        _ = 1 := rfl
    calc
      (∑ f ∈ validBij, _) ≤ ∑ _f ∈ validBij, (1 : ℝ) := Finset.sum_le_sum hterm_le_one
      _ = (validBij.card : ℝ) := by simp
      _ ≤ 1 := by exact_mod_cast hcard_valid
      _ ≤ (0 ! : ℝ) * Real.exp ((n : ℝ) / L ^ 5) := by
        simp only [Nat.factorial_zero, Nat.cast_one, one_mul]
        exact Real.one_le_exp (div_nonneg hn_pos.le (pow_nonneg hL_pos.le 5))
  · -- `0 < m₀`: split into Complementary (`m₀^3 < 2^U`) vs. Intrinsic (`2^U ≤ m₀^3`)
    by_cases hcomp : (m₀ : ℝ) ^ 3 < (2 : ℝ) ^ U
    · -- Regime 2: Complementary regime `(m₀ : ℝ) ^ 3 < (2 : ℝ) ^ U`
      have hterm_comp : ∀ f ∈ validBij,
          (∏ p ∈ E₀, localCellReward (absResCellCard A' B' f p)) *
            (((M ∪ E₀.filter (fun p => 2 ≤ absResCellCard A' B' f p)).powerset.filter
              IsEvenOverlapSubgraph).card : ℝ) ≤
          Real.exp ((U : ℝ) * (m₀ : ℝ)) := by
        intro f hf
        have hfE₀ : ∀ p ∈ E₀, absResCellCard A' B' f p ≤ R₀ := (Finset.mem_filter.mp hf).2.2
        set r := absResCellCard A' B' f
        let H_res := E₀.filter (fun p => 2 ≤ r p)
        have hprod_eq :
            (∏ p ∈ E₀, localCellReward (r p)) =
              (2 : ℝ) ^ (∑ p ∈ H_res, ((r p).choose 2 - 1)) := by
          have hsub : (∏ p ∈ H_res, localCellReward (r p)) = ∏ p ∈ E₀, localCellReward (r p) := by
            refine Finset.prod_subset (Finset.filter_subset _ E₀) fun p hpE₀ hpH => ?_
            have hlt : r p < 2 := by
              by_contra hge
              exact hpH (Finset.mem_filter.mpr ⟨hpE₀, by omega⟩)
            exact localCellReward_eq_one_of_le_two (by omega)
          rw [← hsub]
          exact prod_pow_eq_pow_sum_real H_res (2 : ℝ) (fun p => (r p).choose 2 - 1)
        have hcyc_le :
            (((M ∪ H_res).powerset.filter IsEvenOverlapSubgraph).card : ℝ) ≤
              (2 : ℝ) ^ H_res.card := by
          exact_mod_cast card_evenSubgraphs_union_le hM
        have hexp_sum :
            (∑ p ∈ H_res, ((r p).choose 2 - 1)) + H_res.card =
              ∑ p ∈ H_res, (r p).choose 2 := by
          have hones : H_res.card = ∑ _p ∈ H_res, 1 := by simp
          rw [hones, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun p hp => ?_
          have h2 : 2 ≤ r p := (Finset.mem_filter.mp hp).2
          have h1 : 1 ≤ (r p).choose 2 := by simpa using Nat.choose_le_choose 2 h2
          exact Nat.sub_add_cancel h1
        have hsum_ch_le : ∑ p ∈ H_res, (r p).choose 2 ≤ U * m₀ := by
          have hch_p : ∀ p ∈ H_res, (r p).choose 2 ≤ U * r p := by
            intro p hp
            have hpE₀ : p ∈ E₀ := (Finset.mem_filter.mp hp).1
            have hrU : r p ≤ U := (hfE₀ p hpE₀).trans (by omega)
            have h2 := two_mul_choose_two (r p)
            have hle1 : r p - 1 ≤ U := by omega
            calc
              (r p).choose 2 ≤ 2 * (r p).choose 2 := by omega
              _ = r p * (r p - 1) := h2
              _ ≤ r p * U := Nat.mul_le_mul_left _ hle1
              _ = U * r p := mul_comm _ _
          calc
            ∑ p ∈ H_res, (r p).choose 2 ≤ ∑ p ∈ H_res, U * r p := Finset.sum_le_sum hch_p
            _ ≤ ∑ p : Fin K × Fin K, U * r p :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                fun _ _ _ => Nat.zero_le _
            _ = U * ∑ p : Fin K × Fin K, r p := (Finset.mul_sum _ _ _).symm
            _ = U * m₀ := by
              rw [sum_absResCellCard_eq hdom hA_disj hA_union hB_disj hB_union f]
        have h2_le_e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        calc
          (∏ p ∈ E₀, localCellReward (r p)) *
              (((M ∪ H_res).powerset.filter IsEvenOverlapSubgraph).card : ℝ)
              ≤ (2 : ℝ) ^ (∑ p ∈ H_res, ((r p).choose 2 - 1)) * (2 : ℝ) ^ H_res.card := by
            rw [hprod_eq]
            exact mul_le_mul_of_nonneg_left hcyc_le (pow_nonneg (by norm_num) _)
          _ = (2 : ℝ) ^ (∑ p ∈ H_res, (r p).choose 2) := by rw [← pow_add, hexp_sum]
          _ ≤ (2 : ℝ) ^ (U * m₀) := pow_le_pow_right₀ (by norm_num) hsum_ch_le
          _ ≤ (Real.exp 1) ^ (U * m₀) := pow_le_pow_left₀ (by norm_num) h2_le_e _
          _ = Real.exp ((U : ℝ) * (m₀ : ℝ)) := by
            rw [← Real.exp_nat_mul]
            push_cast
            ring_nf
      have hcard_valid : (validBij.card : ℝ) ≤ (m₀ ! : ℝ) := by
        have hle : validBij.card ≤ m₀ ! := by
          calc
            validBij.card ≤ (Finset.univ : Finset ({u // u ∈ U_dom} ≃ {v // v ∈ U_cod})).card :=
              Finset.card_le_card (Finset.subset_univ _)
            _ = m₀ ! := by rw [Finset.card_univ, card_equiv_finset_eq_factorial hdom hcod]
        exact_mod_cast hle
      have hUm₀_le : (U : ℝ) * (m₀ : ℝ) ≤ (n : ℝ) / L ^ 5 := by
        have h3L_18 : 3 * L ≤ Real.exp (L / 18) := by
          have h2 := pow_div_factorial_le_exp (by positivity : 0 ≤ L / 18) 2
          have hfac2 : ((2 ! : ℕ) : ℝ) = 2 := by norm_num
          rw [hfac2] at h2
          have hquad : 3 * L ≤ (L / 18) ^ 2 / 2 := by nlinarith [hL_big]
          exact hquad.trans h2
        have h27L18_le_n : 27 * L ^ 18 ≤ (n : ℝ) := by
          have hpow18 : (3 * L) ^ 18 ≤ (Real.exp (L / 18)) ^ 18 :=
            pow_le_pow_left₀ (by positivity) h3L_18 18
          have hexp18 : (Real.exp (L / 18)) ^ 18 = (n : ℝ) := by
            rw [← Real.exp_nat_mul, hn_exp]
            congr 1
            ring
          rw [hexp18] at hpow18
          have hcoef : 27 * L ^ 18 ≤ (3 * L) ^ 18 := by
            have hc : (27 : ℝ) ≤ 3 ^ 18 := by norm_num
            calc
              27 * L ^ 18 ≤ (3 : ℝ) ^ 18 * L ^ 18 :=
                mul_le_mul_of_nonneg_right hc (pow_nonneg hL_pos.le 18)
              _ = (3 * L) ^ 18 := (mul_pow 3 L 18).symm
          exact hcoef.trans hpow18
        have hcube_le : ((U : ℝ) * (m₀ : ℝ)) ^ 3 ≤ ((n : ℝ) / L ^ 5) ^ 3 := by
          have hU3 : (U : ℝ) ^ 3 ≤ 27 * L ^ 3 := by
            calc
              (U : ℝ) ^ 3 ≤ (3 * L) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg U) hU_hi 3
              _ = 27 * L ^ 3 := by ring
          have hm₀3 : (m₀ : ℝ) ^ 3 ≤ (n : ℝ) ^ 2 := hcomp.le.trans h2U_hi
          have hlhs3 : ((U : ℝ) * (m₀ : ℝ)) ^ 3 ≤ 27 * L ^ 3 * (n : ℝ) ^ 2 := by
            rw [mul_pow]
            exact mul_le_mul hU3 hm₀3 (pow_nonneg (Nat.cast_nonneg m₀) 3) (by positivity)
          rw [div_pow, ← pow_mul, le_div_iff₀ (pow_pos hL_pos 15)]
          calc
            ((U : ℝ) * (m₀ : ℝ)) ^ 3 * L ^ 15
                ≤ (27 * L ^ 3 * (n : ℝ) ^ 2) * L ^ 15 :=
              mul_le_mul_of_nonneg_right hlhs3 (pow_nonneg hL_pos.le 15)
            _ = (27 * L ^ 18) * (n : ℝ) ^ 2 := by ring
            _ ≤ (n : ℝ) * (n : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_right h27L18_le_n (sq_nonneg (n : ℝ))
            _ = (n : ℝ) ^ 3 := by ring
        exact (pow_le_pow_iff_left₀ (mul_nonneg (Nat.cast_nonneg U) (Nat.cast_nonneg m₀))
          (div_nonneg hn_pos.le (pow_nonneg hL_pos.le 5)) (by norm_num : 3 ≠ 0)).mp hcube_le
      calc
        (∑ f ∈ validBij, _) ≤ ∑ _f ∈ validBij, Real.exp ((U : ℝ) * (m₀ : ℝ)) :=
          Finset.sum_le_sum hterm_comp
        _ = (validBij.card : ℝ) * Real.exp ((U : ℝ) * (m₀ : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (m₀ ! : ℝ) * Real.exp ((n : ℝ) / L ^ 5) :=
          mul_le_mul hcard_valid (Real.exp_le_exp.mpr hUm₀_le)
            (Real.exp_pos _).le (Nat.cast_nonneg _)
    · -- Regime 3: Intrinsic regime `(2 : ℝ) ^ U ≤ (m₀ : ℝ) ^ 3`
      push Not at hcomp
      have hintr := absResSum_intrinsic_le_exp (R₀ := R₀) hM hm₀_pos hdom hcod
        hA_disj hA_union hB_disj hB_union
      refine hintr.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Nat.cast_nonneg _))
      have hm₀_r_pos : 0 < (m₀ : ℝ) := Nat.cast_pos.mpr hm₀_pos
      have h2U_m₀6 : (2 : ℝ) ^ (2 * U) ≤ (m₀ : ℝ) ^ 6 := by
        have hsq := pow_le_pow_left₀ (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) U) hcomp 2
        calc
          (2 : ℝ) ^ (2 * U) = ((2 : ℝ) ^ U) ^ 2 := by rw [mul_comm 2 U, pow_mul]
          _ ≤ ((m₀ : ℝ) ^ 3) ^ 2 := hsq
          _ = (m₀ : ℝ) ^ 6 := by ring
      -- Bound `absQWeight A' B' m₀ R₀ p ≤ U * (absTheta A' B' m₀ p)^2` for every `p`
      have hq_le : ∀ p : Fin K × Fin K,
          absQWeight A' B' m₀ R₀ p ≤ (U : ℝ) * (absTheta A' B' m₀ p) ^ 2 := by
        intro p
        set θ : ℝ := absTheta A' B' m₀ p
        have hθ0 : 0 ≤ θ := absTheta_nonneg A' B' m₀ p
        have hθ_cap : θ ≤ (Real.exp 2 * (U : ℝ) ^ 2) / (m₀ : ℝ) := by
          dsimp [θ, absTheta]
          refine div_le_div_of_nonneg_right ?_ hm₀_r_pos.le
          have ha : ((A' p.1).card : ℝ) ≤ (U : ℝ) := by exact_mod_cast hA_cap p.1
          have hb : ((B' p.2).card : ℝ) ≤ (U : ℝ) := by exact_mod_cast hB_cap p.2
          have hab : ((A' p.1).card : ℝ) * ((B' p.2).card : ℝ) ≤ (U : ℝ) ^ 2 := by
            rw [sq]
            exact mul_le_mul ha hb (Nat.cast_nonneg _) (Nat.cast_nonneg _)
          calc
            Real.exp 2 * ((A' p.1).card : ℝ) * ((B' p.2).card : ℝ)
                = Real.exp 2 * (((A' p.1).card : ℝ) * ((B' p.2).card : ℝ)) := by ring
            _ ≤ Real.exp 2 * (U : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_left hab (Real.exp_pos 2).le
        have hbase6_le1 : (2 : ℝ) ^ (3 * R₀ + 3) * θ ^ 6 ≤ 1 := by
          have hθ6 : θ ^ 6 ≤ (Real.exp 12 * (U : ℝ) ^ 12) / (m₀ : ℝ) ^ 6 := by
            have hp6 := pow_le_pow_left₀ hθ0 hθ_cap 6
            refine hp6.trans_eq ?_
            rw [div_pow, mul_pow, ← Real.exp_nat_mul]
            congr 1
            ring_nf
          have hexp_sum_le : (3 * R₀ + 3) + U / 3 ≤ 2 * U := by omega
          have h2_split :
              (2 : ℝ) ^ (3 * R₀ + 3) * (2 : ℝ) ^ (U / 3) ≤ (2 : ℝ) ^ (2 * U) := by
            rw [← pow_add]
            exact pow_le_pow_right₀ (by norm_num) hexp_sum_le
          calc
            (2 : ℝ) ^ (3 * R₀ + 3) * θ ^ 6
                ≤ (2 : ℝ) ^ (3 * R₀ + 3) * ((Real.exp 12 * (U : ℝ) ^ 12) / (m₀ : ℝ) ^ 6) :=
              mul_le_mul_of_nonneg_left hθ6 (pow_nonneg (by norm_num) _)
            _ ≤ (2 : ℝ) ^ (3 * R₀ + 3) * ((2 : ℝ) ^ (U / 3) / (m₀ : ℝ) ^ 6) :=
              mul_le_mul_of_nonneg_left
                (div_le_div_of_nonneg_right h2U3_lo (pow_nonneg hm₀_r_pos.le 6))
                (pow_nonneg (by norm_num) _)
            _ = ((2 : ℝ) ^ (3 * R₀ + 3) * (2 : ℝ) ^ (U / 3)) / (m₀ : ℝ) ^ 6 :=
              mul_div_assoc' _ _ _
            _ ≤ (2 : ℝ) ^ (2 * U) / (m₀ : ℝ) ^ 6 :=
              div_le_div_of_nonneg_right h2_split (pow_nonneg hm₀_r_pos.le 6)
            _ ≤ 1 := (div_le_one (pow_pos hm₀_r_pos 6)).mpr h2U_m₀6
        have hterm_le : ∀ x ∈ Finset.Icc 2 R₀,
            localCellReward x * θ ^ x / (x ! : ℝ) ≤ θ ^ 2 := by
          intro x hx
          rcases Finset.mem_Icc.mp hx with ⟨hx2, hxR₀⟩
          have hrew_le1 : localCellReward x * θ ^ (x - 2) ≤ 1 := by
            have h6_le1 : (localCellReward x * θ ^ (x - 2)) ^ 6 ≤ 1 ^ 6 := by
              rw [one_pow, mul_pow]
              unfold localCellReward
              rw [← pow_mul, ← pow_mul]
              have hexp6 : 6 * (x.choose 2 - 1) ≤ (3 * R₀ + 3) * (x - 2) := by
                have hch := two_mul_choose_two_sub_one_eq hx2
                have hx1 : x + 1 ≤ R₀ + 1 := by omega
                calc
                  6 * (x.choose 2 - 1) = 3 * (2 * (x.choose 2 - 1)) := by ring
                  _ = 3 * ((x - 2) * (x + 1)) := by rw [hch]
                  _ ≤ 3 * ((x - 2) * (R₀ + 1)) :=
                    Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left (x - 2) hx1)
                  _ = (3 * R₀ + 3) * (x - 2) := by ring
              calc
                (2 : ℝ) ^ ((x.choose 2 - 1) * 6) * θ ^ ((x - 2) * 6)
                    = (2 : ℝ) ^ (6 * (x.choose 2 - 1)) * (θ ^ 6) ^ (x - 2) := by
                  rw [mul_comm (x.choose 2 - 1) 6, mul_comm (x - 2) 6, pow_mul θ 6 (x - 2)]
                _ ≤ (2 : ℝ) ^ ((3 * R₀ + 3) * (x - 2)) * (θ ^ 6) ^ (x - 2) :=
                  mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hexp6)
                    (pow_nonneg (pow_nonneg hθ0 6) _)
                _ = ((2 : ℝ) ^ (3 * R₀ + 3) * θ ^ 6) ^ (x - 2) := by
                  rw [pow_mul, mul_pow]
                _ ≤ 1 ^ (x - 2) :=
                  pow_le_pow_left₀ (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg hθ0 6))
                    hbase6_le1 _
                _ = 1 := one_pow _
            exact (pow_le_pow_iff_left₀
              (mul_nonneg (localCellReward_pos x).le (pow_nonneg hθ0 _))
              zero_le_one (by norm_num : 6 ≠ 0)).mp h6_le1
          have hfac_ge1 : (1 : ℝ) ≤ (x ! : ℝ) := by
            exact_mod_cast Nat.factorial_pos x
          have hx_split : θ ^ x = θ ^ 2 * θ ^ (x - 2) := by
            rw [← pow_add, show 2 + (x - 2) = x by omega]
          calc
            localCellReward x * θ ^ x / (x ! : ℝ)
                ≤ localCellReward x * θ ^ x / 1 :=
              div_le_div_of_nonneg_left
                (mul_nonneg (localCellReward_pos x).le (pow_nonneg hθ0 x))
                zero_lt_one hfac_ge1
            _ = θ ^ 2 * (localCellReward x * θ ^ (x - 2)) := by rw [div_one, hx_split]; ring
            _ ≤ θ ^ 2 * 1 := mul_le_mul_of_nonneg_left hrew_le1 (sq_nonneg θ)
            _ = θ ^ 2 := mul_one _
        have hcard_icc : ((Finset.Icc 2 R₀).card : ℝ) ≤ (U : ℝ) := by
          have hc : (Finset.Icc 2 R₀).card ≤ U := by
            rw [Nat.card_Icc]
            omega
          exact_mod_cast hc
        calc
          absQWeight A' B' m₀ R₀ p
              ≤ ∑ _x ∈ Finset.Icc 2 R₀, θ ^ 2 := Finset.sum_le_sum hterm_le
          _ = ((Finset.Icc 2 R₀).card : ℝ) * θ ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (U : ℝ) * θ ^ 2 := mul_le_mul_of_nonneg_right hcard_icc (sq_nonneg θ)
      -- Sum `absQWeight` over `E₀`
      have hsum_theta_sq :
          ∑ p : Fin K × Fin K, (absTheta A' B' m₀ p) ^ 2 ≤ Real.exp 4 * (U : ℝ) ^ 2 := by
        have hrow_sq : ∑ a : Fin K, ((A' a).card : ℝ) ^ 2 ≤ (U : ℝ) * (m₀ : ℝ) := by
          have hsum_a : ∑ a : Fin K, ((A' a).card : ℝ) = (m₀ : ℝ) := by
            exact_mod_cast sum_block_cards_eq hdom hA_disj hA_union
          calc
            ∑ a : Fin K, ((A' a).card : ℝ) ^ 2
                ≤ ∑ a : Fin K, (U : ℝ) * ((A' a).card : ℝ) := by
              refine Finset.sum_le_sum fun a _ => ?_
              have ha : ((A' a).card : ℝ) ≤ (U : ℝ) := by exact_mod_cast hA_cap a
              rw [sq]
              exact mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _)
            _ = (U : ℝ) * ∑ a : Fin K, ((A' a).card : ℝ) := (Finset.mul_sum _ _ _).symm
            _ = (U : ℝ) * (m₀ : ℝ) := by rw [hsum_a]
        have hcol_sq : ∑ b : Fin K, ((B' b).card : ℝ) ^ 2 ≤ (U : ℝ) * (m₀ : ℝ) := by
          have hsum_b : ∑ b : Fin K, ((B' b).card : ℝ) = (m₀ : ℝ) := by
            exact_mod_cast sum_block_cards_eq hcod hB_disj hB_union
          calc
            ∑ b : Fin K, ((B' b).card : ℝ) ^ 2
                ≤ ∑ b : Fin K, (U : ℝ) * ((B' b).card : ℝ) := by
              refine Finset.sum_le_sum fun b _ => ?_
              have hb : ((B' b).card : ℝ) ≤ (U : ℝ) := by exact_mod_cast hB_cap b
              rw [sq]
              exact mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg _)
            _ = (U : ℝ) * ∑ b : Fin K, ((B' b).card : ℝ) := (Finset.mul_sum _ _ _).symm
            _ = (U : ℝ) * (m₀ : ℝ) := by rw [hsum_b]
        have hexp2_sq : (Real.exp 2) ^ 2 = Real.exp 4 := by
          rw [← Real.exp_nat_mul]
          norm_num
        have hprod_sum :
            ∑ p : Fin K × Fin K, (absTheta A' B' m₀ p) ^ 2 =
              (Real.exp 4 / (m₀ : ℝ) ^ 2) *
                ((∑ a : Fin K, ((A' a).card : ℝ) ^ 2) *
                  (∑ b : Fin K, ((B' b).card : ℝ) ^ 2)) := by
          have hrew : ∀ p : Fin K × Fin K,
              (absTheta A' B' m₀ p) ^ 2 =
                (Real.exp 4 / (m₀ : ℝ) ^ 2) *
                  (((A' p.1).card : ℝ) ^ 2 * ((B' p.2).card : ℝ) ^ 2) := by
            intro p
            unfold absTheta
            rw [div_pow, mul_pow, mul_pow, hexp2_sq]
            ring
          simp_rw [hrew, ← Finset.mul_sum]
          congr 1
          rw [Fintype.sum_prod_type
            (fun p : Fin K × Fin K => ((A' p.1).card : ℝ) ^ 2 * ((B' p.2).card : ℝ) ^ 2)]
          simp_rw [← Finset.mul_sum]
          rw [← Finset.sum_mul]
        rw [hprod_sum]
        calc
          (Real.exp 4 / (m₀ : ℝ) ^ 2) *
              ((∑ a : Fin K, ((A' a).card : ℝ) ^ 2) *
                (∑ b : Fin K, ((B' b).card : ℝ) ^ 2))
              ≤ (Real.exp 4 / (m₀ : ℝ) ^ 2) * (((U : ℝ) * (m₀ : ℝ)) * ((U : ℝ) * (m₀ : ℝ))) := by
            refine mul_le_mul_of_nonneg_left ?_
              (div_nonneg (Real.exp_pos 4).le (sq_nonneg (m₀ : ℝ)))
            exact mul_le_mul hrow_sq hcol_sq
              (Finset.sum_nonneg fun _ _ => sq_nonneg _)
              (mul_nonneg (Nat.cast_nonneg U) hm₀_r_pos.le)
          _ = Real.exp 4 * (U : ℝ) ^ 2 := by
            field_simp [hm₀_r_pos.ne']
      have h2q_sum :
          2 * ∑ p ∈ E₀, absQWeight A' B' m₀ R₀ p ≤ 2 * Real.exp 4 * (U : ℝ) ^ 3 := by
        have hsub_u :
            ∑ p ∈ E₀, absQWeight A' B' m₀ R₀ p ≤
              ∑ p : Fin K × Fin K, (U : ℝ) * (absTheta A' B' m₀ p) ^ 2 := by
          calc
            ∑ p ∈ E₀, absQWeight A' B' m₀ R₀ p
                ≤ ∑ p ∈ E₀, (U : ℝ) * (absTheta A' B' m₀ p) ^ 2 :=
              Finset.sum_le_sum fun p _ => hq_le p
            _ ≤ ∑ p : Fin K × Fin K, (U : ℝ) * (absTheta A' B' m₀ p) ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                fun p _ _ => mul_nonneg (Nat.cast_nonneg U) (sq_nonneg _)
        rw [← Finset.mul_sum] at hsub_u
        have hm := mul_le_mul_of_nonneg_left hsum_theta_sq (Nat.cast_nonneg U)
        linarith [hsub_u, hm, show (U : ℝ) * (Real.exp 4 * (U : ℝ) ^ 2) =
          Real.exp 4 * (U : ℝ) ^ 3 by ring]
      -- Finally `2 * Real.exp 4 * U^3 ≤ n / L^5`
      have h2L_16 : 2 * L ≤ Real.exp (L / 16) := by
        have h2 := pow_div_factorial_le_exp (by positivity : 0 ≤ L / 16) 2
        have hfac2 : ((2 ! : ℕ) : ℝ) = 2 := by norm_num
        rw [hfac2] at h2
        have hquad : 2 * L ≤ (L / 16) ^ 2 / 2 := by nlinarith [hL_big]
        exact hquad.trans h2
      have h54L8_le : 54 * L ^ 8 ≤ Real.exp (L - 4) := by
        have hpow8 : (2 * L) ^ 8 ≤ (Real.exp (L / 16)) ^ 8 :=
          pow_le_pow_left₀ (by positivity) h2L_16 8
        have hexp8 : (Real.exp (L / 16)) ^ 8 = Real.exp (L / 2) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
        rw [hexp8] at hpow8
        have hcoef : 54 * L ^ 8 ≤ (2 * L) ^ 8 := by
          have hc : (54 : ℝ) ≤ 2 ^ 8 := by norm_num
          calc
            54 * L ^ 8 ≤ (2 : ℝ) ^ 8 * L ^ 8 :=
              mul_le_mul_of_nonneg_right hc (pow_nonneg hL_pos.le 8)
            _ = (2 * L) ^ 8 := (mul_pow 2 L 8).symm
        have hexp_half : Real.exp (L / 2) ≤ Real.exp (L - 4) :=
          Real.exp_le_exp.mpr (by linarith only [hL_big])
        exact (hcoef.trans hpow8).trans hexp_half
      have hU3_le : 2 * Real.exp 4 * (U : ℝ) ^ 3 ≤ (n : ℝ) / L ^ 5 := by
        rw [hn_exp, le_div_iff₀ (pow_pos hL_pos 5)]
        have hU3 : (U : ℝ) ^ 3 ≤ 27 * L ^ 3 := by
          calc
            (U : ℝ) ^ 3 ≤ (3 * L) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg U) hU_hi 3
            _ = 27 * L ^ 3 := by ring
        calc
          2 * Real.exp 4 * (U : ℝ) ^ 3 * L ^ 5
              ≤ 2 * Real.exp 4 * (27 * L ^ 3) * L ^ 5 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hU3 (mul_nonneg (by norm_num) (Real.exp_pos 4).le))
              (pow_nonneg hL_pos.le 5)
          _ = (54 * L ^ 8) * Real.exp 4 := by ring
          _ ≤ Real.exp (L - 4) * Real.exp 4 :=
            mul_le_mul_of_nonneg_right h54L8_le (Real.exp_pos 4).le
          _ = Real.exp L := by
            rw [← Real.exp_add]
            congr 1
            ring
      exact h2q_sum.trans hU3_le

/-! ### 5. High-Cell Fiber Conditioning on `Equiv.Perm (Fin n)` and Master Second-Moment Theorem -/

theorem sum_biUnion_le_of_nonneg {ι α : Type*} [DecidableEq α]
    (s : Finset ι) (t : ι → Finset α) {f : α → ℝ}
    (hf : ∀ i ∈ s, ∀ x ∈ t i, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hunion : ∑ x ∈ t a ∪ s.biUnion t, f x ≤
        ∑ x ∈ t a, f x + ∑ x ∈ s.biUnion t, f x := by
      have hid := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
      have hinter_nn : 0 ≤ ∑ x ∈ t a ∩ s.biUnion t, f x :=
        Finset.sum_nonneg fun x hx =>
          hf a (Finset.mem_insert_self a s) x (Finset.mem_inter.mp hx).1
      linarith
    have hih := ih (fun i hi x hx => hf i (Finset.mem_insert_of_mem hi) x hx)
    linarith

/-- High-cell Datum on a single matched cell `(S_row, S_col)` of multiplicity `k`. -/
abbrev CellHighDatum {n : ℕ} (S_row S_col : Finset (Fin n)) (k : ℕ) : Type :=
  Σ (ST : {S // S ∈ S_row.powersetCard k} × {T // T ∈ S_col.powersetCard k}),
    ({u // u ∈ ST.1.1} ≃ {v // v ∈ ST.2.1})

/-- Joint high-cell realization choice across all edges `p ∈ M`. -/
abbrev HighChoice {n K : ℕ} (A B : Fin K → Finset (Fin n))
    (M : Finset (Fin K × Fin K)) (j : Fin K × Fin K → ℕ) : Type :=
  ∀ p : {p // p ∈ M}, CellHighDatum (A p.1.1) (B p.1.2) (j p.1)

def cDom {n K : ℕ} {A B : Fin K → Finset (Fin n)}
    {M : Finset (Fin K × Fin K)} {j : Fin K × Fin K → ℕ}
    (c : HighChoice A B M j) (p : {p // p ∈ M}) : Finset (Fin n) :=
  (c p).1.1.1

def cCod {n K : ℕ} {A B : Fin K → Finset (Fin n)}
    {M : Finset (Fin K × Fin K)} {j : Fin K × Fin K → ℕ}
    (c : HighChoice A B M j) (p : {p // p ∈ M}) : Finset (Fin n) :=
  (c p).1.2.1

def cEquiv {n K : ℕ} {A B : Fin K → Finset (Fin n)}
    {M : Finset (Fin K × Fin K)} {j : Fin K × Fin K → ℕ}
    (c : HighChoice A B M j) (p : {p // p ∈ M}) :
    {u // u ∈ cDom c p} ≃ {v // v ∈ cCod c p} :=
  (c p).2

def usedDom {n K : ℕ} {A B : Fin K → Finset (Fin n)}
    {M : Finset (Fin K × Fin K)} {j : Fin K × Fin K → ℕ}
    (c : HighChoice A B M j) : Finset (Fin n) :=
  Finset.univ.biUnion (cDom c)

def usedCod {n K : ℕ} {A B : Fin K → Finset (Fin n)}
    {M : Finset (Fin K × Fin K)} {j : Fin K × Fin K → ℕ}
    (c : HighChoice A B M j) : Finset (Fin n) :=
  Finset.univ.biUnion (cCod c)

def remDom {n K : ℕ} {A B : Fin K → Finset (Fin n)}
    {M : Finset (Fin K × Fin K)} {j : Fin K × Fin K → ℕ}
    (c : HighChoice A B M j) : Finset (Fin n) :=
  Finset.univ \ usedDom c

def remCod {n K : ℕ} {A B : Fin K → Finset (Fin n)}
    {M : Finset (Fin K × Fin K)} {j : Fin K × Fin K → ℕ}
    (c : HighChoice A B M j) : Finset (Fin n) :=
  Finset.univ \ usedCod c

/-- Predicate stating that `π : Equiv.Perm (Fin n)` extends all local bijections in `c`. -/
def MatchesChoice {n K : ℕ} {A B : Fin K → Finset (Fin n)}
    {M : Finset (Fin K × Fin K)} {j : Fin K × Fin K → ℕ}
    (c : HighChoice A B M j) (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ p : {p // p ∈ M}, ∀ u : {u // u ∈ cDom c p}, π u.1 = (cEquiv c p u).1

theorem card_cellHighDatum {n : ℕ} (S_row S_col : Finset (Fin n)) (k : ℕ) :
    Fintype.card (CellHighDatum S_row S_col k) =
      S_row.card.choose k * S_col.card.choose k * k ! := by
  unfold CellHighDatum
  rw [Fintype.card_sigma]
  have hfiber : ∀ ST : {S // S ∈ S_row.powersetCard k} × {T // T ∈ S_col.powersetCard k},
      Fintype.card ({u // u ∈ ST.1.1} ≃ {v // v ∈ ST.2.1}) = k ! := by
    intro ST
    have h1 : ST.1.1.card = k := (Finset.mem_powersetCard.mp ST.1.2).2
    have h2 : ST.2.1.card = k := (Finset.mem_powersetCard.mp ST.2.2).2
    exact card_equiv_finset_eq_factorial h1 h2
  simp_rw [hfiber]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_coe, Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_powersetCard, smul_eq_mul]

theorem card_highChoice {n K : ℕ} (A B : Fin K → Finset (Fin n))
    (M : Finset (Fin K × Fin K)) (j : Fin K × Fin K → ℕ) :
    Fintype.card (HighChoice A B M j) =
      ∏ p ∈ M, ((A p.1).card.choose (j p) * (B p.2).card.choose (j p) * (j p) !) := by
  unfold HighChoice
  rw [Fintype.card_pi]
  simp_rw [card_cellHighDatum]
  rw [Finset.univ_eq_attach,
    Finset.prod_attach M (fun p => (A p.1).card.choose (j p) * (B p.2).card.choose (j p) * (j p) !)]

theorem cast_choose_mul_choose_mul_factorial (s t k : ℕ) :
    ((s.choose k * t.choose k * k ! : ℕ) : ℝ) =
      ((s.descFactorial k : ℝ) * (t.descFactorial k : ℝ)) / (k ! : ℝ) := by
  have hk_ne : (k ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [eq_div_iff hk_ne]
  have hnat : (s.choose k * t.choose k * k !) * k ! = s.descFactorial k * t.descFactorial k := by
    rw [Nat.descFactorial_eq_factorial_mul_choose s k,
      Nat.descFactorial_eq_factorial_mul_choose t k]
    ring
  exact_mod_cast hnat

theorem inv_factorial_mul_sub_factorial {n J : ℕ} (hJ : J ≤ n) :
    ((n ! : ℝ))⁻¹ * ((n - J) ! : ℝ) = ((n.descFactorial J : ℝ))⁻¹ := by
  have hn_fac : n ! = n.descFactorial J * (n - J) ! := by
    have hsplit := descFactorial_add_eq n J (n - J)
    rw [Nat.add_sub_of_le hJ, Nat.descFactorial_self, Nat.descFactorial_self] at hsplit
    exact hsplit
  have hsub_ne : ((n - J) ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hdesc_ne : (n.descFactorial J : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (descFactorial_pos_of_le hJ).ne'
  have hcast : (n ! : ℝ) = (n.descFactorial J : ℝ) * ((n - J) ! : ℝ) := by exact_mod_cast hn_fac
  rw [hcast]
  field_simp [hsub_ne, hdesc_ne]

theorem pairwiseDisjoint_cDom {n K : ℕ} {A B : Fin K → Finset (Fin n)}
    (hA_disj : (Set.univ : Set (Fin K)).PairwiseDisjoint A)
    {M : Finset (Fin K × Fin K)} (hM : IsBlockMatching K M)
    {j : Fin K × Fin K → ℕ} (c : HighChoice A B M j) :
    (Set.univ : Set {p // p ∈ M}).PairwiseDisjoint (cDom c) := by
  intro p₁ _ p₂ _ hne
  have hfst_ne : p₁.1.1 ≠ p₂.1.1 := fun hf =>
    hne (Subtype.ext (hM.1 p₁.1 p₁.2 p₂.1 p₂.2 hf))
  have hsub1 : cDom c p₁ ⊆ A p₁.1.1 := (Finset.mem_powersetCard.mp (c p₁).1.1.2).1
  have hsub2 : cDom c p₂ ⊆ A p₂.1.1 := (Finset.mem_powersetCard.mp (c p₂).1.1.2).1
  exact Finset.disjoint_left.mpr fun x hx1 hx2 =>
    Finset.disjoint_left.mp (hA_disj trivial trivial hfst_ne) (hsub1 hx1) (hsub2 hx2)

theorem pairwiseDisjoint_cCod {n K : ℕ} {A B : Fin K → Finset (Fin n)}
    (hB_disj : (Set.univ : Set (Fin K)).PairwiseDisjoint B)
    {M : Finset (Fin K × Fin K)} (hM : IsBlockMatching K M)
    {j : Fin K × Fin K → ℕ} (c : HighChoice A B M j) :
    (Set.univ : Set {p // p ∈ M}).PairwiseDisjoint (cCod c) := by
  intro p₁ _ p₂ _ hne
  have hsnd_ne : p₁.1.2 ≠ p₂.1.2 := fun hs =>
    hne (Subtype.ext (hM.2 p₁.1 p₁.2 p₂.1 p₂.2 hs))
  have hsub1 : cCod c p₁ ⊆ B p₁.1.2 := (Finset.mem_powersetCard.mp (c p₁).1.2.2).1
  have hsub2 : cCod c p₂ ⊆ B p₂.1.2 := (Finset.mem_powersetCard.mp (c p₂).1.2.2).1
  exact Finset.disjoint_left.mpr fun y hy1 hy2 =>
    Finset.disjoint_left.mp (hB_disj trivial trivial hsnd_ne) (hsub1 hy1) (hsub2 hy2)

theorem card_usedDom_eq {n K : ℕ} {A B : Fin K → Finset (Fin n)}
    (hA_disj : (Set.univ : Set (Fin K)).PairwiseDisjoint A)
    {M : Finset (Fin K × Fin K)} (hM : IsBlockMatching K M)
    {j : Fin K × Fin K → ℕ} (c : HighChoice A B M j) :
    (usedDom c).card = ∑ p ∈ M, j p := by
  have hdisj : ((Finset.univ : Finset {p // p ∈ M}) : Set {p // p ∈ M}).PairwiseDisjoint
      (cDom c) :=
    fun p₁ _ p₂ _ hne => pairwiseDisjoint_cDom hA_disj hM c trivial trivial hne
  unfold usedDom
  rw [Finset.card_biUnion hdisj]
  have hcards : ∀ p : {p // p ∈ M}, (cDom c p).card = j p.1 :=
    fun p => (Finset.mem_powersetCard.mp (c p).1.1.2).2
  simp_rw [hcards]
  rw [Finset.univ_eq_attach, Finset.sum_attach M j]

theorem card_usedCod_eq {n K : ℕ} {A B : Fin K → Finset (Fin n)}
    (hB_disj : (Set.univ : Set (Fin K)).PairwiseDisjoint B)
    {M : Finset (Fin K × Fin K)} (hM : IsBlockMatching K M)
    {j : Fin K × Fin K → ℕ} (c : HighChoice A B M j) :
    (usedCod c).card = ∑ p ∈ M, j p := by
  have hdisj : ((Finset.univ : Finset {p // p ∈ M}) : Set {p // p ∈ M}).PairwiseDisjoint
      (cCod c) :=
    fun p₁ _ p₂ _ hne => pairwiseDisjoint_cCod hB_disj hM c trivial trivial hne
  unfold usedCod
  rw [Finset.card_biUnion hdisj]
  have hcards : ∀ p : {p // p ∈ M}, (cCod c p).card = j p.1 :=
    fun p => (Finset.mem_powersetCard.mp (c p).1.2.2).2
  simp_rw [hcards]
  rw [Finset.univ_eq_attach, Finset.sum_attach M j]

theorem card_remDom_eq {n K : ℕ} {A B : Fin K → Finset (Fin n)}
    (hA_disj : (Set.univ : Set (Fin K)).PairwiseDisjoint A)
    {M : Finset (Fin K × Fin K)} (hM : IsBlockMatching K M)
    {j : Fin K × Fin K → ℕ} (c : HighChoice A B M j) :
    (remDom c).card = n - ∑ p ∈ M, j p := by
  unfold remDom
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
    card_usedDom_eq hA_disj hM c]

theorem card_remCod_eq {n K : ℕ} {A B : Fin K → Finset (Fin n)}
    (hB_disj : (Set.univ : Set (Fin K)).PairwiseDisjoint B)
    {M : Finset (Fin K × Fin K)} (hM : IsBlockMatching K M)
    {j : Fin K × Fin K → ℕ} (c : HighChoice A B M j) :
    (remCod c).card = n - ∑ p ∈ M, j p := by
  unfold remCod
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
    card_usedCod_eq hB_disj hM c]

theorem map_usedDom_eq_usedCod {n K : ℕ} {A B : Fin K → Finset (Fin n)}
    (hA_disj : (Set.univ : Set (Fin K)).PairwiseDisjoint A)
    (hB_disj : (Set.univ : Set (Fin K)).PairwiseDisjoint B)
    {M : Finset (Fin K × Fin K)} (hM : IsBlockMatching K M)
    {j : Fin K × Fin K → ℕ} (c : HighChoice A B M j)
    {π : Equiv.Perm (Fin n)} (hmatch : MatchesChoice c π) :
    (usedDom c).map π.toEmbedding = usedCod c := by
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    rcases Finset.mem_map.mp hy with ⟨x, hx, rfl⟩
    rcases Finset.mem_biUnion.mp hx with ⟨p, _, hxp⟩
    have hπx : π x = (cEquiv c p ⟨x, hxp⟩).1 := hmatch p ⟨x, hxp⟩
    rw [Equiv.coe_toEmbedding, hπx]
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ p, (cEquiv c p ⟨x, hxp⟩).2⟩
  · rw [Finset.card_map, card_usedDom_eq hA_disj hM c, card_usedCod_eq hB_disj hM c]

/-- Restriction of a `MatchesChoice c π` permutation to a bijection `remDom c ≃ remCod c`. -/
def restrictRem {n K : ℕ} {A B : Fin K → Finset (Fin n)}
    (hA_disj : (Set.univ : Set (Fin K)).PairwiseDisjoint A)
    (hB_disj : (Set.univ : Set (Fin K)).PairwiseDisjoint B)
    {M : Finset (Fin K × Fin K)} (hM : IsBlockMatching K M)
    {j : Fin K × Fin K → ℕ} (c : HighChoice A B M j)
    (π : Equiv.Perm (Fin n)) (hmatch : MatchesChoice c π) :
    {u // u ∈ remDom c} ≃ {v // v ∈ remCod c} :=
  have hmap := map_usedDom_eq_usedCod hA_disj hB_disj hM c hmatch
  { toFun := fun u =>
      ⟨π u.1, by
        have hu_not : u.1 ∉ usedDom c := (Finset.mem_sdiff.mp u.2).2
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hv_in => ?_⟩
        rw [← hmap] at hv_in
        rcases Finset.mem_map.mp hv_in with ⟨x, hx, heq⟩
        exact hu_not ((π.injective heq) ▸ hx)⟩
    invFun := fun v =>
      ⟨π.symm v.1, by
        have hv_not : v.1 ∉ usedCod c := (Finset.mem_sdiff.mp v.2).2
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hu_in => ?_⟩
        apply hv_not
        rw [← hmap]
        exact Finset.mem_map.mpr ⟨π.symm v.1, hu_in, π.apply_symm_apply v.1⟩⟩
    left_inv := fun u => Subtype.ext (π.symm_apply_apply u.1)
    right_inv := fun v => Subtype.ext (π.apply_symm_apply v.1) }

/-- Row/column sum bounds and high-cell extraction on `Equiv.Perm (Fin n)`. -/
theorem sum_row_cellCard_le (n : ℕ) (π : Equiv.Perm (Fin n)) (a : Fin (kCoSeed n)) :
    ∑ b : Fin (kCoSeed n), cellCard n π (a, b) ≤ (canonicalBlocks n a).card := by
  have hdisj : ((Finset.univ : Finset (Fin (kCoSeed n))) : Set (Fin (kCoSeed n))).PairwiseDisjoint
      (fun b => cellSet n π (a, b)) := by
    intro b₁ _ b₂ _ hne
    refine Finset.disjoint_left.mpr fun x hx₁ hx₂ => ?_
    exact Finset.disjoint_left.mp (pairwiseDisjoint_canonicalBlocks n trivial trivial hne)
      (Finset.mem_filter.mp hx₁).2 (Finset.mem_filter.mp hx₂).2
  have hsub : Finset.univ.biUnion (fun b => cellSet n π (a, b)) ⊆ canonicalBlocks n a := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨b, _, hxb⟩
    exact (Finset.mem_filter.mp hxb).1
  unfold cellCard
  rw [← Finset.card_biUnion hdisj]
  exact Finset.card_le_card hsub

theorem sum_col_cellCard_le (n : ℕ) (π : Equiv.Perm (Fin n)) (b : Fin (kCoSeed n)) :
    ∑ a : Fin (kCoSeed n), cellCard n π (a, b) ≤ (canonicalBlocks n b).card := by
  let mapped (a : Fin (kCoSeed n)) : Finset (Fin n) := (cellSet n π (a, b)).map π.toEmbedding
  have hdisj : ((Finset.univ : Finset (Fin (kCoSeed n))) : Set (Fin (kCoSeed n))).PairwiseDisjoint
      mapped := by
    intro a₁ _ a₂ _ hne
    refine Finset.disjoint_left.mpr fun y hy₁ hy₂ => ?_
    rcases Finset.mem_map.mp hy₁ with ⟨x₁, hx₁, rfl⟩
    rcases Finset.mem_map.mp hy₂ with ⟨x₂, hx₂, heq⟩
    cases π.toEmbedding.injective heq
    exact Finset.disjoint_left.mp (pairwiseDisjoint_canonicalBlocks n trivial trivial hne)
      (Finset.mem_filter.mp hx₁).1 (Finset.mem_filter.mp hx₂).1
  have hsub : Finset.univ.biUnion mapped ⊆ canonicalBlocks n b := by
    intro y hy
    rcases Finset.mem_biUnion.mp hy with ⟨a, _, hya⟩
    rcases Finset.mem_map.mp hya with ⟨x, hx, rfl⟩
    exact (Finset.mem_filter.mp hx).2
  have hcard_eq : ∀ a : Fin (kCoSeed n), cellCard n π (a, b) = (mapped a).card :=
    fun a => (Finset.card_map _).symm
  simp_rw [hcard_eq]
  rw [← Finset.card_biUnion hdisj]
  exact Finset.card_le_card hsub

theorem cellCard_le_min (n : ℕ) (π : Equiv.Perm (Fin n))
    (p : Fin (kCoSeed n) × Fin (kCoSeed n)) :
    cellCard n π p ≤ min (canonicalBlocks n p.1).card (canonicalBlocks n p.2).card := by
  refine le_min ?_ ?_
  · exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ p.2)).trans
      (sum_row_cellCard_le n π p.1)
  · exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ p.1)).trans
      (sum_col_cellCard_le n π p.2)

/-- High-cell matching `M(π) = {p | highThresh n + 1 ≤ cellCard n π p}` of `π : Equiv.Perm (Fin n)`. -/
noncomputable def permHighMatching (n : ℕ) (π : Equiv.Perm (Fin n)) :
    Finset (Fin (kCoSeed n) × Fin (kCoSeed n)) :=
  Finset.univ.filter (fun p => highThresh n + 1 ≤ cellCard n π p)

/-- High-cell multiplicity vector `j(π)` equal to `cellCard n π p` on `permHighMatching n π` and `0` elsewhere. -/
noncomputable def permHighMult (n : ℕ) (π : Equiv.Perm (Fin n))
    (p : Fin (kCoSeed n) × Fin (kCoSeed n)) : ℕ :=
  if highThresh n + 1 ≤ cellCard n π p then cellCard n π p else 0

theorem permHighMatching_mem_blockMatchings {n : ℕ}
    (hK : ∑ i : Fin 4, witnessCounts n i = kCoSeed n)
    (hn : ∑ i : Fin 4, witnessSize n i * witnessCounts n i = n)
    (π : Equiv.Perm (Fin n)) :
    permHighMatching n π ∈ blockMatchings n := by
  rw [mem_blockMatchings_iff]
  have hlt := highCap_lt_two_mul_highThresh_succ n
  constructor
  · intro p₁ hp₁ p₂ hp₂ hfst
    by_contra hne
    have hsnd_ne : p₁.2 ≠ p₂.2 := fun hs => hne (Prod.ext hfst hs)
    have hc₁ : highThresh n + 1 ≤ cellCard n π (p₁.1, p₁.2) := (Finset.mem_filter.mp hp₁).2
    have hc₂ : highThresh n + 1 ≤ cellCard n π (p₁.1, p₂.2) := by
      rw [show (p₁.1, p₂.2) = p₂ from Prod.ext hfst rfl]
      exact (Finset.mem_filter.mp hp₂).2
    have hpair_le :
        cellCard n π (p₁.1, p₁.2) + cellCard n π (p₁.1, p₂.2) ≤
          ∑ b : Fin (kCoSeed n), cellCard n π (p₁.1, b) := by
      have hpair : ∑ b ∈ ({p₁.2, p₂.2} : Finset (Fin (kCoSeed n))), cellCard n π (p₁.1, b) =
          cellCard n π (p₁.1, p₁.2) + cellCard n π (p₁.1, p₂.2) :=
        Finset.sum_pair hsnd_ne
      rw [← hpair]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => Nat.zero_le _
    have hrow_cap : ∑ b : Fin (kCoSeed n), cellCard n π (p₁.1, b) ≤ highCap n := by
      calc
        ∑ b : Fin (kCoSeed n), cellCard n π (p₁.1, b)
            ≤ (canonicalBlocks n p₁.1).card := sum_row_cellCard_le n π p₁.1
        _ = seedBlockSize n p₁.1 := card_canonicalBlocks_eq hK hn p₁.1
        _ ≤ highCap n := seedBlockSize_le_highCap n p₁.1
    omega
  · intro p₁ hp₁ p₂ hp₂ hsnd
    by_contra hne
    have hfst_ne : p₁.1 ≠ p₂.1 := fun hf => hne (Prod.ext hf hsnd)
    have hc₁ : highThresh n + 1 ≤ cellCard n π (p₁.1, p₁.2) := (Finset.mem_filter.mp hp₁).2
    have hc₂ : highThresh n + 1 ≤ cellCard n π (p₂.1, p₁.2) := by
      rw [show (p₂.1, p₁.2) = p₂ from Prod.ext rfl hsnd]
      exact (Finset.mem_filter.mp hp₂).2
    have hpair_le :
        cellCard n π (p₁.1, p₁.2) + cellCard n π (p₂.1, p₁.2) ≤
          ∑ a : Fin (kCoSeed n), cellCard n π (a, p₁.2) := by
      have hpair : ∑ a ∈ ({p₁.1, p₂.1} : Finset (Fin (kCoSeed n))), cellCard n π (a, p₁.2) =
          cellCard n π (p₁.1, p₁.2) + cellCard n π (p₂.1, p₁.2) :=
        Finset.sum_pair hfst_ne
      rw [← hpair]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => Nat.zero_le _
    have hcol_cap : ∑ a : Fin (kCoSeed n), cellCard n π (a, p₁.2) ≤ highCap n := by
      calc
        ∑ a : Fin (kCoSeed n), cellCard n π (a, p₁.2)
            ≤ (canonicalBlocks n p₁.2).card := sum_col_cellCard_le n π p₁.2
        _ = seedBlockSize n p₁.2 := card_canonicalBlocks_eq hK hn p₁.2
        _ ≤ highCap n := seedBlockSize_le_highCap n p₁.2
    omega

theorem permHighMult_mem_highMultBox {n : ℕ}
    (hK : ∑ i : Fin 4, witnessCounts n i = kCoSeed n)
    (hn : ∑ i : Fin 4, witnessSize n i * witnessCounts n i = n)
    (π : Equiv.Perm (Fin n)) :
    permHighMult n π ∈ highMultBox n (permHighMatching n π) := by
  rw [mem_highMultBox_iff]
  constructor
  · intro p hp
    have hge : highThresh n + 1 ≤ cellCard n π p := (Finset.mem_filter.mp hp).2
    rw [show permHighMult n π p = cellCard n π p from ite_eq_left_of_eq_true _ _ (eq_true hge)]
    refine ⟨hge, ?_⟩
    calc
      cellCard n π p ≤ min (canonicalBlocks n p.1).card (canonicalBlocks n p.2).card :=
        cellCard_le_min n π p
      _ = cellMinSize n p := by
        unfold cellMinSize
        rw [card_canonicalBlocks_eq hK hn p.1, card_canonicalBlocks_eq hK hn p.2]
  · intro p hp
    have hn_ge : ¬ highThresh n + 1 ≤ cellCard n π p := by
      simpa [permHighMatching] using hp
    exact ite_eq_right_of_eq_false _ _ (eq_false hn_ge)

/-- Fiber of permutations with prescribed high-cell matching `M` and multiplicity vector `j`. -/
noncomputable def permFiber (n : ℕ)
    (M : Finset (Fin (kCoSeed n) × Fin (kCoSeed n)))
    (j : Fin (kCoSeed n) × Fin (kCoSeed n) → ℕ) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
    permHighMatching n π = M ∧ permHighMult n π = j)

/-- Fiberwise bound for fixed `(M, j)` reducing `(n!)⁻¹ * ∑_{π ∈ permFiber n M j} overlapPairFactor`
to `highSkeletonWeight n M j * exp(n / L^5)`. -/
theorem inv_nfac_mul_sum_permFiber_le {n : ℕ} {L : ℝ}
    (hK : ∑ i : Fin 4, witnessCounts n i = kCoSeed n)
    (hn : ∑ i : Fin 4, witnessSize n i * witnessCounts n i = n)
    (hU_lo : 98 ≤ highCap n)
    (hL_big : (4 * 10 ^ 10 : ℝ) ≤ L)
    (hn_exp : (n : ℝ) = Real.exp L)
    (hU_hi : (highCap n : ℝ) ≤ 3 * L)
    (h2U_hi : (2 : ℝ) ^ (highCap n) ≤ (n : ℝ) ^ 2)
    (h2U3_lo : Real.exp 12 * (highCap n : ℝ) ^ 12 ≤ (2 : ℝ) ^ (highCap n / 3))
    {M : Finset (Fin (kCoSeed n) × Fin (kCoSeed n))}
    (hM : IsBlockMatching (kCoSeed n) M)
    {j : Fin (kCoSeed n) × Fin (kCoSeed n) → ℕ}
    (hj : j ∈ highMultBox n M) :
    ((n ! : ℝ))⁻¹ *
      (∑ π ∈ permFiber n M j,
        overlapPairFactor (canonicalBlocks n) (permBlock n π.symm)) ≤
      highSkeletonWeight n M j * Real.exp ((n : ℝ) / L ^ 5) := by
  classical
  have hA_disj := pairwiseDisjoint_canonicalBlocks n
  have hA_union := biUnion_canonicalBlocks_eq_univ hK hn
  have hR₀_ge1 : 1 ≤ highThresh n := by
    unfold highThresh
    omega
  set J : ℕ := ∑ p ∈ M, j p
  have hJ_le_n : J ≤ n := sum_highMult_le_n hK hn hM hj
  set m₀ : ℕ := n - J
  let ChoiceType := HighChoice (canonicalBlocks n) (canonicalBlocks n) M j
  let fiberChoice (c : ChoiceType) : Finset (Equiv.Perm (Fin n)) :=
    (permFiber n M j).filter (MatchesChoice c)
  -- Every `π ∈ permFiber n M j` matches some `c : ChoiceType`
  have hcover : permFiber n M j ⊆ Finset.univ.biUnion fiberChoice := by
    intro π hπ
    rcases (Finset.mem_filter.mp hπ).2 with ⟨hM_π, hj_π⟩
    let c : ChoiceType := fun p =>
      have hp_hi : highThresh n + 1 ≤ cellCard n π p.1 := by
        have hp_mem : p.1 ∈ permHighMatching n π := hM_π.symm ▸ p.2
        exact (Finset.mem_filter.mp hp_mem).2
      have hcard_p : (cellSet n π p.1).card = j p.1 := by
        rw [← hj_π]
        unfold permHighMult
        rw [ite_eq_left_of_eq_true _ _ (eq_true hp_hi)]
        rfl
      have hdom_mem : cellSet n π p.1 ∈ (canonicalBlocks n p.1.1).powersetCard (j p.1) :=
        Finset.mem_powersetCard.mpr ⟨Finset.filter_subset _ _, hcard_p⟩
      have hcod_mem : (cellSet n π p.1).map π.toEmbedding ∈
          (canonicalBlocks n p.1.2).powersetCard (j p.1) := by
        refine Finset.mem_powersetCard.mpr ⟨?_, by rw [Finset.card_map, hcard_p]⟩
        intro y hy
        rcases Finset.mem_map.mp hy with ⟨x, hx, rfl⟩
        exact (Finset.mem_filter.mp hx).2
      ⟨(⟨cellSet n π p.1, hdom_mem⟩, ⟨(cellSet n π p.1).map π.toEmbedding, hcod_mem⟩),
        { toFun := fun u => ⟨π u.1, Finset.mem_map.mpr ⟨u.1, u.2, rfl⟩⟩
          invFun := fun v =>
            ⟨π.symm v.1, by
              rcases Finset.mem_map.mp v.2 with ⟨x, hx, heq⟩
              have hx_eq : π.symm v.1 = x := by
                rw [← heq]
                exact π.symm_apply_apply x
              rwa [hx_eq]⟩
          left_inv := fun u => Subtype.ext (π.symm_apply_apply u.1)
          right_inv := fun v => Subtype.ext (π.apply_symm_apply v.1) }⟩
    exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ c, Finset.mem_filter.mpr ⟨hπ, fun _ _ => rfl⟩⟩
  have hopf_nn : ∀ π : Equiv.Perm (Fin n),
      0 ≤ overlapPairFactor (canonicalBlocks n) (permBlock n π.symm) := by
    intro π
    rw [overlapPairFactor_canonical_eq]
    exact mul_nonneg (Finset.prod_nonneg fun p _ => (localCellReward_pos _).le)
      (Nat.cast_nonneg _)
  -- Bound each `fiberChoice c` by injecting into residual bijections on `remDom c ≃ remCod c`
  have hchoice_bound : ∀ c : ChoiceType,
      (∑ π ∈ fiberChoice c,
        overlapPairFactor (canonicalBlocks n) (permBlock n π.symm)) ≤
      (∏ p ∈ M, localCellReward (j p)) *
        ((m₀ ! : ℝ) * Real.exp ((n : ℝ) / L ^ 5)) := by
    intro c
    let resRow (a : Fin (kCoSeed n)) : Finset (Fin n) := canonicalBlocks n a ∩ remDom c
    let resCol (b : Fin (kCoSeed n)) : Finset (Fin n) := canonicalBlocks n b ∩ remCod c
    have hdom_c : (remDom c).card = m₀ := card_remDom_eq hA_disj hM c
    have hcod_c : (remCod c).card = m₀ := card_remCod_eq hA_disj hM c
    have hresRow_disj : (Set.univ : Set (Fin (kCoSeed n))).PairwiseDisjoint resRow := by
      intro a₁ _ a₂ _ hne
      exact Finset.disjoint_left.mpr fun x hx₁ hx₂ =>
        Finset.disjoint_left.mp (hA_disj trivial trivial hne)
          (Finset.mem_inter.mp hx₁).1 (Finset.mem_inter.mp hx₂).1
    have hresCol_disj : (Set.univ : Set (Fin (kCoSeed n))).PairwiseDisjoint resCol := by
      intro b₁ _ b₂ _ hne
      exact Finset.disjoint_left.mpr fun y hy₁ hy₂ =>
        Finset.disjoint_left.mp (hA_disj trivial trivial hne)
          (Finset.mem_inter.mp hy₁).1 (Finset.mem_inter.mp hy₂).1
    have hresRow_union : Finset.univ.biUnion resRow = remDom c := by
      ext x
      simp only [resRow, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_inter]
      constructor
      · rintro ⟨_, _, hx_rem⟩
        exact hx_rem
      · intro hx_rem
        have hx_all : x ∈ Finset.univ.biUnion (canonicalBlocks n) := by
          rw [hA_union]
          exact Finset.mem_univ x
        rcases Finset.mem_biUnion.mp hx_all with ⟨a, _, ha⟩
        exact ⟨a, ha, hx_rem⟩
    have hresCol_union : Finset.univ.biUnion resCol = remCod c := by
      ext y
      simp only [resCol, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_inter]
      constructor
      · rintro ⟨_, _, hy_rem⟩
        exact hy_rem
      · intro hy_rem
        have hy_all : y ∈ Finset.univ.biUnion (canonicalBlocks n) := by
          rw [hA_union]
          exact Finset.mem_univ y
        rcases Finset.mem_biUnion.mp hy_all with ⟨b, _, hb⟩
        exact ⟨b, hb, hy_rem⟩
    have hresRow_cap : ∀ a : Fin (kCoSeed n), (resRow a).card ≤ highCap n := by
      intro a
      calc
        (resRow a).card ≤ (canonicalBlocks n a).card := Finset.card_le_card Finset.inter_subset_left
        _ = seedBlockSize n a := card_canonicalBlocks_eq hK hn a
        _ ≤ highCap n := seedBlockSize_le_highCap n a
    have hresCol_cap : ∀ b : Fin (kCoSeed n), (resCol b).card ≤ highCap n := by
      intro b
      calc
        (resCol b).card ≤ (canonicalBlocks n b).card := Finset.card_le_card Finset.inter_subset_left
        _ = seedBlockSize n b := card_canonicalBlocks_eq hK hn b
        _ ≤ highCap n := seedBlockSize_le_highCap n b
    let E₀ : Finset (Fin (kCoSeed n) × Fin (kCoSeed n)) := Finset.univ \ M
    let validRes := Finset.univ.filter (fun f : {u // u ∈ remDom c} ≃ {v // v ∈ remCod c} =>
      (∀ p ∈ M, absResCellCard resRow resCol f p = 0) ∧
      (∀ p ∈ E₀, absResCellCard resRow resCol f p ≤ highThresh n))
    let resTerm (f : {u // u ∈ remDom c} ≃ {v // v ∈ remCod c}) : ℝ :=
      (∏ p ∈ E₀, localCellReward (absResCellCard resRow resCol f p)) *
        (((M ∪ E₀.filter (fun p => 2 ≤ absResCellCard resRow resCol f p)).powerset.filter
          IsEvenOverlapSubgraph).card : ℝ)
    let toRes (π_sub : {π // π ∈ fiberChoice c}) :
        {u // u ∈ remDom c} ≃ {v // v ∈ remCod c} :=
      restrictRem hA_disj hA_disj hM c π_sub.1 (Finset.mem_filter.mp π_sub.2).2
    have htoRes_inj : Function.Injective toRes := by
      intro π₁ π₂ heq
      apply Subtype.ext
      apply Equiv.ext
      intro x
      have hm₁ : MatchesChoice c π₁.1 := (Finset.mem_filter.mp π₁.2).2
      have hm₂ : MatchesChoice c π₂.1 := (Finset.mem_filter.mp π₂.2).2
      by_cases hx_used : x ∈ usedDom c
      · rcases Finset.mem_biUnion.mp hx_used with ⟨p, _, hxp⟩
        rw [hm₁ p ⟨x, hxp⟩, hm₂ p ⟨x, hxp⟩]
      · have hx_rem : x ∈ remDom c := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx_used⟩
        exact congrArg Subtype.val (Equiv.congr_fun heq ⟨x, hx_rem⟩)
    -- Relate `cellCard n π_sub.1 q` to `absResCellCard resRow resCol (toRes π_sub) q`
    have hcell_split : ∀ (π_sub : {π // π ∈ fiberChoice c})
        (q : Fin (kCoSeed n) × Fin (kCoSeed n)),
        cellCard n π_sub.1 q =
          (if q ∈ M then j q else 0) + absResCellCard resRow resCol (toRes π_sub) q := by
      intro π_sub q
      have hm : MatchesChoice c π_sub.1 := (Finset.mem_filter.mp π_sub.2).2
      let S₁ : Finset (Fin n) := cellSet n π_sub.1 q ∩ usedDom c
      let S₂ : Finset (Fin n) := cellSet n π_sub.1 q ∩ remDom c
      have hdisj12 : Disjoint S₁ S₂ :=
        Finset.disjoint_left.mpr fun x hx₁ hx₂ =>
          (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx₂).2).2 (Finset.mem_inter.mp hx₁).2
      have hunion12 : S₁ ∪ S₂ = cellSet n π_sub.1 q := by
        ext x
        simp only [S₁, S₂, remDom, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
          Finset.mem_univ, true_and]
        tauto
      have hcard_S₂ : S₂.card = absResCellCard resRow resCol (toRes π_sub) q := by
        have hmap_S₂ :
            (absResCellSet resRow resCol (toRes π_sub) q).map
                (Function.Embedding.subtype _) = S₂ := by
          ext x
          simp only [absResCellSet, S₂, cellSet, resRow, resCol, Finset.mem_map,
            Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
            Function.Embedding.coe_subtype]
          constructor
          · rintro ⟨u, ⟨⟨hx_row, _⟩, ⟨hπ_col, _⟩⟩, rfl⟩
            exact ⟨⟨hx_row, hπ_col⟩, u.2⟩
          · rintro ⟨⟨hx_row, hπ_col⟩, hx_rem⟩
            refine ⟨⟨x, hx_rem⟩, ⟨⟨hx_row, hx_rem⟩, ⟨hπ_col, ?_⟩⟩, rfl⟩
            exact (toRes π_sub ⟨x, hx_rem⟩).2
        rw [← hmap_S₂, Finset.card_map]
        rfl
      have hcard_S₁ : S₁.card = if q ∈ M then j q else 0 := by
        by_cases hqM : q ∈ M
        · simp only [hqM, ↓reduceIte]
          have hS₁_eq : S₁ = cDom c ⟨q, hqM⟩ := by
            ext x
            simp only [S₁, cellSet, Finset.mem_inter, Finset.mem_filter]
            constructor
            · rintro ⟨⟨hx_a, _⟩, hx_used⟩
              rcases Finset.mem_biUnion.mp hx_used with ⟨p, _, hxp⟩
              have hsub_p : cDom c p ⊆ canonicalBlocks n p.1.1 :=
                (Finset.mem_powersetCard.mp (c p).1.1.2).1
              have hfst_eq : p.1.1 = q.1 := by
                by_contra hne
                exact Finset.disjoint_left.mp (hA_disj trivial trivial hne) (hsub_p hxp) hx_a
              have hp_eq : p = ⟨q, hqM⟩ :=
                Subtype.ext (hM.1 p.1 p.2 q hqM hfst_eq)
              rwa [← hp_eq]
            · intro hxq
              have hsub_q : cDom c ⟨q, hqM⟩ ⊆ canonicalBlocks n q.1 :=
                (Finset.mem_powersetCard.mp (c ⟨q, hqM⟩).1.1.2).1
              have hsub_cod : cCod c ⟨q, hqM⟩ ⊆ canonicalBlocks n q.2 :=
                (Finset.mem_powersetCard.mp (c ⟨q, hqM⟩).1.2.2).1
              have hπx : π_sub.1 x = (cEquiv c ⟨q, hqM⟩ ⟨x, hxq⟩).1 := hm ⟨q, hqM⟩ ⟨x, hxq⟩
              refine ⟨⟨hsub_q hxq, ?_⟩,
                Finset.mem_biUnion.mpr ⟨⟨q, hqM⟩, Finset.mem_univ _, hxq⟩⟩
              rw [hπx]
              exact hsub_cod (cEquiv c ⟨q, hqM⟩ ⟨x, hxq⟩).2
          rw [hS₁_eq]
          exact (Finset.mem_powersetCard.mp (c ⟨q, hqM⟩).1.1.2).2
        · simp only [hqM, ↓reduceIte]
          rw [Finset.card_eq_zero]
          ext x
          simp only [S₁, cellSet, Finset.mem_inter, Finset.mem_filter, Finset.notMem_empty,
            iff_false]
          rintro ⟨⟨hx_a, hπ_b⟩, hx_used⟩
          rcases Finset.mem_biUnion.mp hx_used with ⟨p, _, hxp⟩
          have hsub_dom : cDom c p ⊆ canonicalBlocks n p.1.1 :=
            (Finset.mem_powersetCard.mp (c p).1.1.2).1
          have hsub_cod : cCod c p ⊆ canonicalBlocks n p.1.2 :=
            (Finset.mem_powersetCard.mp (c p).1.2.2).1
          have hfst_eq : p.1.1 = q.1 := by
            by_contra hne
            exact Finset.disjoint_left.mp (hA_disj trivial trivial hne) (hsub_dom hxp) hx_a
          have hπx : π_sub.1 x ∈ canonicalBlocks n p.1.2 := by
            rw [hm p ⟨x, hxp⟩]
            exact hsub_cod (cEquiv c p ⟨x, hxp⟩).2
          have hsnd_eq : p.1.2 = q.2 := by
            by_contra hne
            exact Finset.disjoint_left.mp (hA_disj trivial trivial hne) hπx hπ_b
          exact hqM (Prod.ext hfst_eq hsnd_eq ▸ p.2)
      unfold cellCard
      rw [← hunion12, Finset.card_union_of_disjoint hdisj12, hcard_S₁, hcard_S₂]
    have htoRes_mem : ∀ π_sub : {π // π ∈ fiberChoice c}, toRes π_sub ∈ validRes := by
      intro π_sub
      rcases (Finset.mem_filter.mp (Finset.mem_filter.mp π_sub.2).1).2 with ⟨hM_π, hj_π⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro p hpM
        have hsp := hcell_split π_sub p
        simp only [hpM, ↓reduceIte] at hsp
        have hp_hi : highThresh n + 1 ≤ cellCard n π_sub.1 p := by
          have hp_in : p ∈ permHighMatching n π_sub.1 := hM_π.symm ▸ hpM
          exact (Finset.mem_filter.mp hp_in).2
        have hjp_eq : cellCard n π_sub.1 p = j p := by
          rw [← hj_π]
          simp only [permHighMult, hp_hi, ↓reduceIte]
        omega
      · intro p hpE₀
        have hp_notM : p ∉ M := (Finset.mem_sdiff.mp hpE₀).2
        have hsp := hcell_split π_sub p
        simp only [hp_notM, ↓reduceIte, zero_add] at hsp
        have hp_not_in : p ∉ permHighMatching n π_sub.1 := by rwa [hM_π]
        have hle : ¬ highThresh n + 1 ≤ cellCard n π_sub.1 p := by
          simpa [permHighMatching] using hp_not_in
        omega
    have hopf_eq : ∀ π_sub : {π // π ∈ fiberChoice c},
        overlapPairFactor (canonicalBlocks n) (permBlock n π_sub.1.symm) =
          (∏ p ∈ M, localCellReward (j p)) * resTerm (toRes π_sub) := by
      intro π_sub
      have hvalid := Finset.mem_filter.mp (htoRes_mem π_sub)
      have h0M := hvalid.2.1
      have hjM := (mem_highMultBox_iff.mp hj).1
      rw [overlapPairFactor_canonical_eq]
      have hcard_on_M : ∀ p ∈ M, cellCard n π_sub.1 p = j p := by
        intro p hpM
        have hsp := hcell_split π_sub p
        simp only [hpM, ↓reduceIte, h0M p hpM, add_zero] at hsp
        exact hsp
      have hcard_on_E₀ : ∀ p ∈ E₀,
          cellCard n π_sub.1 p = absResCellCard resRow resCol (toRes π_sub) p := by
        intro p hpE₀
        have hp_notM : p ∉ M := (Finset.mem_sdiff.mp hpE₀).2
        have hsp := hcell_split π_sub p
        simp only [hp_notM, ↓reduceIte, zero_add] at hsp
        exact hsp
      have hprod_split :
          (∏ p : Fin (kCoSeed n) × Fin (kCoSeed n), localCellReward (cellCard n π_sub.1 p)) =
            (∏ p ∈ M, localCellReward (j p)) *
              (∏ p ∈ E₀, localCellReward (absResCellCard resRow resCol (toRes π_sub) p)) := by
        have huniv_u : (Finset.univ : Finset (Fin (kCoSeed n) × Fin (kCoSeed n))) = M ∪ E₀ :=
          (Finset.union_sdiff_of_subset (Finset.subset_univ M)).symm
        have hdisj_u : Disjoint M E₀ :=
          Finset.disjoint_left.mpr fun _ hm1 hm2 => (Finset.mem_sdiff.mp hm2).2 hm1
        rw [huniv_u, Finset.prod_union hdisj_u]
        congr 1
        · exact Finset.prod_congr rfl fun p hp => by rw [hcard_on_M p hp]
        · exact Finset.prod_congr rfl fun p hp => by rw [hcard_on_E₀ p hp]
      have hheavy_eq :
          permHeavyPairs n π_sub.1 =
            M ∪ E₀.filter (fun p => 2 ≤ absResCellCard resRow resCol (toRes π_sub) p) := by
        ext p
        by_cases hpM : p ∈ M
        · have hj2 : 2 ≤ j p := by
            have := (hjM p hpM).1
            omega
          simp only [permHeavyPairs, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_union, hpM, true_or, iff_true, hcard_on_M p hpM]
          exact hj2
        · have hpE₀ : p ∈ E₀ := Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, hpM⟩
          simp only [permHeavyPairs, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_union, hpM, false_or, hpE₀, hcard_on_E₀ p hpE₀]
      rw [hprod_split, hheavy_eq]
      dsimp [resTerm]
      ring
    -- Inject `fiberChoice c` into `validRes` and apply `absResSum_le_master`
    have himg_sub : (Finset.univ : Finset {π // π ∈ fiberChoice c}).image toRes ⊆ validRes := by
      intro f hf
      rcases Finset.mem_image.mp hf with ⟨π_sub, _, rfl⟩
      exact htoRes_mem π_sub
    have hinj_on : Set.InjOn toRes
        ((Finset.univ : Finset {π // π ∈ fiberChoice c}) : Set _) :=
      fun _ _ _ _ h => htoRes_inj h
    have hmaster := absResSum_le_master hM hdom_c hcod_c hresRow_disj hresRow_union
      hresCol_disj hresCol_union hresRow_cap hresCol_cap hU_lo rfl hL_big hn_exp
      hU_hi h2U_hi h2U3_lo
    calc
      (∑ π ∈ fiberChoice c,
          overlapPairFactor (canonicalBlocks n) (permBlock n π.symm))
          = ∑ π_sub : {π // π ∈ fiberChoice c},
              overlapPairFactor (canonicalBlocks n) (permBlock n π_sub.1.symm) := by
        rw [Finset.univ_eq_attach,
          Finset.sum_attach (fiberChoice c)
            (fun π => overlapPairFactor (canonicalBlocks n) (permBlock n π.symm))]
      _ = ∑ π_sub : {π // π ∈ fiberChoice c},
            (∏ p ∈ M, localCellReward (j p)) * resTerm (toRes π_sub) :=
        Finset.sum_congr rfl fun π_sub _ => hopf_eq π_sub
      _ = (∏ p ∈ M, localCellReward (j p)) *
            ∑ π_sub : {π // π ∈ fiberChoice c}, resTerm (toRes π_sub) :=
        (Finset.mul_sum _ _ _).symm
      _ = (∏ p ∈ M, localCellReward (j p)) *
            ∑ f ∈ (Finset.univ : Finset {π // π ∈ fiberChoice c}).image toRes, resTerm f := by
        rw [Finset.sum_image hinj_on]
      _ ≤ (∏ p ∈ M, localCellReward (j p)) * ∑ f ∈ validRes, resTerm f := by
        refine mul_le_mul_of_nonneg_left ?_
          (Finset.prod_nonneg fun p _ => (localCellReward_pos _).le)
        refine Finset.sum_le_sum_of_subset_of_nonneg himg_sub fun f _ _ => ?_
        exact mul_nonneg (Finset.prod_nonneg fun p _ => (localCellReward_pos _).le)
          (Nat.cast_nonneg _)
      _ ≤ (∏ p ∈ M, localCellReward (j p)) *
            ((m₀ ! : ℝ) * Real.exp ((n : ℝ) / L ^ 5)) :=
        mul_le_mul_of_nonneg_left hmaster
          (Finset.prod_nonneg fun p _ => (localCellReward_pos _).le)
  -- Sum over `c : ChoiceType` and simplify to `highSkeletonWeight n M j * exp(n / L^5)`
  have hcard_choice_real :
      (Fintype.card ChoiceType : ℝ) * (∏ p ∈ M, localCellReward (j p)) =
        ∏ p ∈ M,
          (((seedBlockSize n p.1).descFactorial (j p) : ℝ) *
            ((seedBlockSize n p.2).descFactorial (j p) : ℝ) /
            ((j p) ! : ℝ)) * localCellReward (j p) := by
    have hc_nat := card_highChoice (canonicalBlocks n) (canonicalBlocks n) M j
    have hc_real :
        (Fintype.card ChoiceType : ℝ) =
          ∏ p ∈ M,
            (((seedBlockSize n p.1).descFactorial (j p) : ℝ) *
              ((seedBlockSize n p.2).descFactorial (j p) : ℝ) /
              ((j p) ! : ℝ)) := by
      dsimp [ChoiceType]
      rw [hc_nat, Nat.cast_prod]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [card_canonicalBlocks_eq hK hn p.1, card_canonicalBlocks_eq hK hn p.2]
      exact cast_choose_mul_choose_mul_factorial _ _ _
    rw [hc_real, ← Finset.prod_mul_distrib]
  have hskel_id :
      ((n ! : ℝ))⁻¹ *
        ((Fintype.card ChoiceType : ℝ) *
          ((∏ p ∈ M, localCellReward (j p)) *
            ((m₀ ! : ℝ) * Real.exp ((n : ℝ) / L ^ 5)))) =
      highSkeletonWeight n M j * Real.exp ((n : ℝ) / L ^ 5) := by
    have hinv_fac : ((n ! : ℝ))⁻¹ * (m₀ ! : ℝ) = ((n.descFactorial J : ℝ))⁻¹ :=
      inv_factorial_mul_sub_factorial hJ_le_n
    calc
      ((n ! : ℝ))⁻¹ *
          ((Fintype.card ChoiceType : ℝ) *
            ((∏ p ∈ M, localCellReward (j p)) *
              ((m₀ ! : ℝ) * Real.exp ((n : ℝ) / L ^ 5))))
          = (((Fintype.card ChoiceType : ℝ) * (∏ p ∈ M, localCellReward (j p))) *
              (((n ! : ℝ))⁻¹ * (m₀ ! : ℝ))) * Real.exp ((n : ℝ) / L ^ 5) := by ring
      _ = ((∏ p ∈ M,
              (((seedBlockSize n p.1).descFactorial (j p) : ℝ) *
                ((seedBlockSize n p.2).descFactorial (j p) : ℝ) /
                ((j p) ! : ℝ)) * localCellReward (j p)) *
            ((n.descFactorial J : ℝ))⁻¹) * Real.exp ((n : ℝ) / L ^ 5) := by
        rw [hcard_choice_real, hinv_fac]
      _ = highSkeletonWeight n M j * Real.exp ((n : ℝ) / L ^ 5) := by
        unfold highSkeletonWeight
        rw [← div_eq_mul_inv]
  have hsum_fiber :
      (∑ π ∈ permFiber n M j,
        overlapPairFactor (canonicalBlocks n) (permBlock n π.symm)) ≤
      (Fintype.card ChoiceType : ℝ) *
        ((∏ p ∈ M, localCellReward (j p)) *
          ((m₀ ! : ℝ) * Real.exp ((n : ℝ) / L ^ 5))) := by
    calc
      (∑ π ∈ permFiber n M j,
          overlapPairFactor (canonicalBlocks n) (permBlock n π.symm))
          ≤ ∑ π ∈ Finset.univ.biUnion fiberChoice,
              overlapPairFactor (canonicalBlocks n) (permBlock n π.symm) :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover fun π _ _ => hopf_nn π
      _ ≤ ∑ c : ChoiceType, ∑ π ∈ fiberChoice c,
            overlapPairFactor (canonicalBlocks n) (permBlock n π.symm) :=
        sum_biUnion_le_of_nonneg Finset.univ fiberChoice (fun _ _ π _ => hopf_nn π)
      _ ≤ ∑ _c : ChoiceType,
            (∏ p ∈ M, localCellReward (j p)) *
              ((m₀ ! : ℝ) * Real.exp ((n : ℝ) / L ^ 5)) :=
        Finset.sum_le_sum fun c _ => hchoice_bound c
      _ = (Fintype.card ChoiceType : ℝ) *
            ((∏ p ∈ M, localCellReward (j p)) *
              ((m₀ ! : ℝ) * Real.exp ((n : ℝ) / L ^ 5))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    ((n ! : ℝ))⁻¹ *
        (∑ π ∈ permFiber n M j,
          overlapPairFactor (canonicalBlocks n) (permBlock n π.symm))
        ≤ ((n ! : ℝ))⁻¹ *
            ((Fintype.card ChoiceType : ℝ) *
              ((∏ p ∈ M, localCellReward (j p)) *
                ((m₀ ! : ℝ) * Real.exp ((n : ℝ) / L ^ 5)))) :=
      mul_le_mul_of_nonneg_left hsum_fiber (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = highSkeletonWeight n M j * Real.exp ((n : ℝ) / L ^ 5) := hskel_id

/-- **Petkov's Unconditional Subcritical Second-Moment Theorem (`arXiv:2608.30604`, Sections 7–9)**:
There exists a deterministic nonnegative sequence `η : ℕ → ℝ` with `η n → 0` such that eventually
`secondMomentRatio n ≤ Real.exp (η n * (n : ℝ) / (Real.log (n : ℝ)) ^ 4)`. -/
theorem eventually_secondMomentRatio_subcritical :
    ∃ η : ℕ → ℝ, (∀ n, 0 ≤ η n) ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,
        secondMomentRatio n ≤ Real.exp (η n * (n : ℝ) / (Real.log (n : ℝ)) ^ 4) := by
  obtain ⟨η_hi, hη_hi_nn, hη_hi_0, hev_hi⟩ := eventually_sum_highSkeletonWeight_le
  let η_res : ℕ → ℝ := fun n => if n ≤ 2 then 0 else 1 / Real.log (n : ℝ)
  let η : ℕ → ℝ := fun n => η_hi n + η_res n
  have hη_res_nn : ∀ n, 0 ≤ η_res n := by
    intro n
    dsimp [η_res]
    split_ifs with h
    · norm_num
    · have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
      exact div_nonneg zero_le_one (Real.log_pos hn1).le
  have hη_nn : ∀ n, 0 ≤ η n := fun n => add_nonneg (hη_hi_nn n) (hη_res_nn n)
  have hL : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll_div_L : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact h0.comp hL
  have hη_res_0 : Tendsto η_res atTop (𝓝 0) := by
    have hdiv : Tendsto (fun n : ℕ => 1 / Real.log (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hL
    refine hdiv.congr' ?_
    filter_upwards [eventually_ge_atTop 3] with n hn3
    dsimp [η_res]
    split_ifs with h
    · omega
    · rfl
  have hη_0 : Tendsto η atTop (𝓝 0) := by
    simpa [η] using hη_hi_0.add hη_res_0
  refine ⟨η, hη_nn, hη_0, ?_⟩
  filter_upwards [eventually_alphaNat_regime, eventually_witnessCounts_spec, hev_hi,
    tendsto_alphaNat_atTop.eventually_ge_atTop 100,
    hL.eventually_ge_atTop (4 * 10 ^ 10 : ℝ),
    hll_div_L.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16))] with
      n ⟨hn16, _, _, hqα, _, hhi⟩ ⟨hK, hn, _, _, _⟩ hhi_sum
      hα100 hL_big hrat16
  set L : ℝ := Real.log (n : ℝ)
  set q : ℝ := Real.log 2
  have hL_big' : (4 * 10 ^ 10 : ℝ) ≤ L := hL_big
  have hL_pos : 0 < L := by linarith only [hL_big']
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn_exp : (n : ℝ) = Real.exp L := (Real.exp_log hn_pos).symm
  have hq_bounds : (0.69 : ℝ) ≤ q ∧ q ≤ 0.70 := by
    dsimp [q]; constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
  -- Verify numeric high-cap hypotheses `hU_lo`, `hU_hi`, `h2U_hi`, `h2U3_lo`
  have hU_lo : 98 ≤ highCap n := by
    unfold highCap witnessSize
    omega
  have hα_le_3L : (alphaNat n : ℝ) ≤ 3 * L := by
    have hm : 0.69 * (alphaNat n : ℝ) ≤ q * (alphaNat n : ℝ) :=
      mul_le_mul_of_nonneg_right hq_bounds.1 (Nat.cast_nonneg _)
    change q * (alphaNat n : ℝ) ≤ 2 * L at hhi
    linarith only [hhi, hm, hL_pos]
  have hU_le_α : (highCap n : ℝ) ≤ (alphaNat n : ℝ) := by
    exact_mod_cast (Nat.sub_le (alphaNat n) 2 : highCap n ≤ alphaNat n)
  have hU_hi : (highCap n : ℝ) ≤ 3 * L := hU_le_α.trans hα_le_3L
  have h2U_hi : (2 : ℝ) ^ (highCap n) ≤ (n : ℝ) ^ 2 := by
    have h2eq : (2 : ℝ) ^ (highCap n) = Real.exp ((highCap n : ℝ) * q) := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul]
    have hn2_eq : (n : ℝ) ^ 2 = Real.exp (2 * L) := by
      rw [hn_exp, sq, ← Real.exp_add, two_mul]
    rw [h2eq, hn2_eq]
    apply Real.exp_le_exp.mpr
    change q * (alphaNat n : ℝ) ≤ 2 * L at hhi
    have hm := mul_le_mul_of_nonneg_right hU_le_α (by linarith only [hq_bounds.1])
    linarith only [hm, hhi]
  have hac_le : |alphaConst| ≤ 1 := by
    unfold alphaConst
    have hq_gt : Real.exp (-0.4) ≤ q := by
      rw [Real.exp_neg]
      have he01 : (1.1 : ℝ) ≤ Real.exp 0.1 := by linarith [Real.add_one_le_exp (0.1 : ℝ)]
      have he04 : (1.1 : ℝ) ^ 4 ≤ Real.exp 0.4 := by
        calc
          (1.1 : ℝ) ^ 4 ≤ (Real.exp 0.1) ^ 4 := pow_le_pow_left₀ (by norm_num) he01 4
          _ = Real.exp 0.4 := by rw [← Real.exp_nat_mul]; norm_num
      have hinv : (Real.exp 0.4)⁻¹ ≤ ((1.1 : ℝ) ^ 4)⁻¹ := inv_anti₀ (by positivity) he04
      linarith [hq_bounds.1, hinv]
    have hlo_q := Real.log_le_log (Real.exp_pos _) hq_gt
    rw [Real.log_exp] at hlo_q
    have hhi_q : Real.log q ≤ 0 := Real.log_nonpos (by linarith [hq_bounds.1]) (by linarith [hq_bounds.2])
    rw [abs_le]
    constructor <;> dsimp [q] at hlo_q hhi_q hq_bounds ⊢ <;> linarith
  have hqα_ge : (7 / 4 : ℝ) * L + 10 ≤ q * (alphaNat n : ℝ) := by
    have hll_le : Real.log L ≤ (1 / 16 : ℝ) * L := (div_le_iff₀ hL_pos).mp hrat16
    have hc_lo := (abs_le.mp hac_le).1
    have hδ := phaseDelta_mem_Icc n
    have hqδ : q * phaseDelta n ≤ 1 := by
      calc
        q * phaseDelta n ≤ 0.70 * 1 := mul_le_mul hq_bounds.2 hδ.2 hδ.1 (by norm_num)
        _ ≤ 1 := by norm_num
    change q * (alphaNat n : ℝ) = 2 * L - 2 * Real.log L + 2 * alphaConst - q * phaseDelta n at hqα
    linarith only [hqα, hll_le, hc_lo, hqδ, hL_big']
  have h2U3_lo : Real.exp 12 * (highCap n : ℝ) ^ 12 ≤ (2 : ℝ) ^ (highCap n / 3) := by
    have h3L_24 : 3 * L ≤ Real.exp (L / 24) := by
      have h2 := pow_div_factorial_le_exp (by positivity : 0 ≤ L / 24) 2
      have hfac2 : ((2 ! : ℕ) : ℝ) = 2 := by norm_num
      rw [hfac2] at h2
      have hquad : 3 * L ≤ (L / 24) ^ 2 / 2 := by nlinarith [hL_big']
      exact hquad.trans h2
    have hU12_le : (highCap n : ℝ) ^ 12 ≤ Real.exp (L / 2) := by
      calc
        (highCap n : ℝ) ^ 12 ≤ (3 * L) ^ 12 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hU_hi 12
        _ ≤ (Real.exp (L / 24)) ^ 12 := pow_le_pow_left₀ (by positivity) h3L_24 12
        _ = Real.exp (L / 2) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
    have hdiv3_nat : alphaNat n - 4 ≤ 3 * (highCap n / 3) := by
      unfold highCap witnessSize
      omega
    have hdiv3_r : (alphaNat n : ℝ) - 4 ≤ 3 * ((highCap n / 3 : ℕ) : ℝ) := by
      have hc : ((alphaNat n - 4 : ℕ) : ℝ) ≤ ((3 * (highCap n / 3) : ℕ) : ℝ) := by
        exact_mod_cast hdiv3_nat
      rw [Nat.cast_sub (by omega)] at hc
      push_cast at hc
      linarith
    have hpow2_ge : Real.exp (12 + L / 2) ≤ (2 : ℝ) ^ (highCap n / 3) := by
      have h2eq : (2 : ℝ) ^ (highCap n / 3) = Real.exp (((highCap n / 3 : ℕ) : ℝ) * q) := by
        rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul]
      rw [h2eq]
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_right hdiv3_r (by linarith only [hq_bounds.1])
      linarith only [hm, hqα_ge, hq_bounds.2, hL_big']
    calc
      Real.exp 12 * (highCap n : ℝ) ^ 12
          ≤ Real.exp 12 * Real.exp (L / 2) :=
        mul_le_mul_of_nonneg_left hU12_le (Real.exp_pos 12).le
      _ = Real.exp (12 + L / 2) := (Real.exp_add 12 (L / 2)).symm
      _ ≤ (2 : ℝ) ^ (highCap n / 3) := hpow2_ge
  -- Partition `Equiv.Perm (Fin n)` into `permFiber n M j` over `M ∈ blockMatchings n`, `j ∈ highMultBox n M`
  have hperm_cover :
      (Finset.univ : Finset (Equiv.Perm (Fin n))) ⊆
        (blockMatchings n).biUnion (fun M => (highMultBox n M).biUnion (permFiber n M)) := by
    intro π _
    exact Finset.mem_biUnion.mpr ⟨permHighMatching n π,
      permHighMatching_mem_blockMatchings hK hn π,
      Finset.mem_biUnion.mpr ⟨permHighMult n π,
        permHighMult_mem_highMultBox hK hn π,
        Finset.mem_filter.mpr ⟨Finset.mem_univ π, rfl, rfl⟩⟩⟩
  have hopf_nn : ∀ π : Equiv.Perm (Fin n),
      0 ≤ overlapPairFactor (canonicalBlocks n) (permBlock n π.symm) := by
    intro π
    rw [overlapPairFactor_canonical_eq]
    exact mul_nonneg (Finset.prod_nonneg fun p _ => (localCellReward_pos _).le)
      (Nat.cast_nonneg _)
  have hsum_all :
      secondMomentRatio n ≤
        (∑ M ∈ blockMatchings n, ∑ j ∈ highMultBox n M, highSkeletonWeight n M j) *
          Real.exp ((n : ℝ) / L ^ 5) := by
    rw [secondMomentRatio_eq_single_perm_sum]
    have hbi1 :
        (∑ π : Equiv.Perm (Fin n),
            overlapPairFactor (canonicalBlocks n) (permBlock n π.symm)) ≤
          ∑ M ∈ blockMatchings n, ∑ j ∈ highMultBox n M, ∑ π ∈ permFiber n M j,
            overlapPairFactor (canonicalBlocks n) (permBlock n π.symm) := by
      calc
        (∑ π : Equiv.Perm (Fin n),
            overlapPairFactor (canonicalBlocks n) (permBlock n π.symm))
            ≤ ∑ π ∈ (blockMatchings n).biUnion
                (fun M => (highMultBox n M).biUnion (permFiber n M)),
                overlapPairFactor (canonicalBlocks n) (permBlock n π.symm) :=
          Finset.sum_le_sum_of_subset_of_nonneg hperm_cover fun π _ _ => hopf_nn π
        _ ≤ ∑ M ∈ blockMatchings n,
              ∑ π ∈ (highMultBox n M).biUnion (permFiber n M),
                overlapPairFactor (canonicalBlocks n) (permBlock n π.symm) :=
          sum_biUnion_le_of_nonneg (blockMatchings n) _ (fun _ _ π _ => hopf_nn π)
        _ ≤ ∑ M ∈ blockMatchings n, ∑ j ∈ highMultBox n M, ∑ π ∈ permFiber n M j,
              overlapPairFactor (canonicalBlocks n) (permBlock n π.symm) :=
          Finset.sum_le_sum fun M _ =>
            sum_biUnion_le_of_nonneg (highMultBox n M) _ (fun _ _ π _ => hopf_nn π)
    calc
      ((n ! : ℝ))⁻¹ *
          (∑ π : Equiv.Perm (Fin n),
            overlapPairFactor (canonicalBlocks n) (permBlock n π.symm))
          ≤ ((n ! : ℝ))⁻¹ *
              (∑ M ∈ blockMatchings n, ∑ j ∈ highMultBox n M, ∑ π ∈ permFiber n M j,
                overlapPairFactor (canonicalBlocks n) (permBlock n π.symm)) :=
        mul_le_mul_of_nonneg_left hbi1 (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = ∑ M ∈ blockMatchings n, ∑ j ∈ highMultBox n M,
            ((n ! : ℝ))⁻¹ *
              (∑ π ∈ permFiber n M j,
                overlapPairFactor (canonicalBlocks n) (permBlock n π.symm)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun M _ => ?_
        rw [Finset.mul_sum]
      _ ≤ ∑ M ∈ blockMatchings n, ∑ j ∈ highMultBox n M,
            highSkeletonWeight n M j * Real.exp ((n : ℝ) / L ^ 5) := by
        refine Finset.sum_le_sum fun M hM => Finset.sum_le_sum fun j hj => ?_
        exact inv_nfac_mul_sum_permFiber_le hK hn hU_lo hL_big' hn_exp hU_hi h2U_hi h2U3_lo
          (mem_blockMatchings_iff.mp hM) hj
      _ = (∑ M ∈ blockMatchings n, ∑ j ∈ highMultBox n M, highSkeletonWeight n M j) *
            Real.exp ((n : ℝ) / L ^ 5) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun M _ => ?_
        rw [Finset.sum_mul]
  have hη_eq :
      η_hi n * (n : ℝ) / L ^ 4 + (n : ℝ) / L ^ 5 = η n * (n : ℝ) / L ^ 4 := by
    dsimp [η, η_res]
    split_ifs with h
    · omega
    · change η_hi n * (n : ℝ) / L ^ 4 + (n : ℝ) / L ^ 5 =
        (η_hi n + 1 / L) * (n : ℝ) / L ^ 4
      field_simp [hL_pos.ne']
  calc
    secondMomentRatio n
        ≤ (∑ M ∈ blockMatchings n, ∑ j ∈ highMultBox n M, highSkeletonWeight n M j) *
            Real.exp ((n : ℝ) / L ^ 5) := hsum_all
    _ ≤ Real.exp (η_hi n * (n : ℝ) / L ^ 4) * Real.exp ((n : ℝ) / L ^ 5) :=
      mul_le_mul_of_nonneg_right hhi_sum (Real.exp_pos _).le
    _ = Real.exp (η n * (n : ℝ) / L ^ 4) := by
      rw [← Real.exp_add, hη_eq]

end JSP000506

