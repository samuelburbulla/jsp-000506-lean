import JSP000506.PartA

/-!
# Section 6: Signed 4-Size Cocoloring Witness and Exact Signed-Overlap Cycle-Space Identity

This module formalizes Section 6 of Samuil Petkov's *A Full-Sequence Quantitative Gap Between the
Chromatic and Cochromatic Numbers of a Random Graph* (`arXiv:2608.30604`):

1. **Canonical 4-Size Block Partition (`canonicalBlocks`) and Permutation Witness (`permSignedWitness`)**:
   Constructs the canonical `kCoSeed n`-block family on `Fin n` with block-size multiplicities
   `witnessCounts n : Fin 4 → ℕ`, defines both the permutation-summed witness `permSignedWitness`
   and the symmetry-normalized unordered signed witness `unordSignedWitness`, and proves:
   - `cocolorable_of_permSignedWitness_pos` / `cocolorable_of_unordSignedWitness_pos`: positivity
     deterministically implies `Cocolorable G (kCoSeed n)` (`ζ(G) ≤ kCoSeed n`).
   - `eventually_expectGnpHalf_unordSignedWitness_supercritical`: `𝔼[Z_n] ≥ exp(100 n / (log n)^2)`.
   - `secondMomentRatio_unord_eq_perm`: scale invariance `𝔼[Z_n^2] / (𝔼[Z_n])^2 = 𝔼[W_n^2] / (𝔼[W_n])^2`.

2. **Exact Signed-Overlap Pair Probability with Binary Cycle-Space Factor (`signed_overlap_pair_prob_eq`)**:
   Proves Lemma 6.1 of `arXiv:2608.30604` unconditionally: for any two pairwise-disjoint `K`-block
   families `A, B : Fin K → Finset (Fin n)`, summing the joint signed realization probability over all
   sign pairs `(σ, τ) ∈ {false, true}^K × {false, true}^K` yields
   `4^K * 2^{-(∑_i C(|A_i|, 2) + ∑_j C(|B_j|, 2))} * 2^{∑_{p ∈ M} (C(r_p, 2) - 1)} * #{H ⊆ M | IsEvenOverlapSubgraph H}`,
   where `M = heavyOverlapPairs A B = {(i, j) | |A_i ∩ B_j| ≥ 2}` and `#{H ⊆ M | IsEvenOverlapSubgraph H}`
   is the cardinality (`2^β`) of the binary cycle space (even-degree subgraphs) of `M`.

3. **Exact Normalized Second-Moment Expansion (`secondMomentRatio_eq_overlap_sum`)**:
   Expresses `secondMomentRatio n = 𝔼[W_n^2] / (𝔼[W_n])^2` directly as the uniform permutation
   average of the overlap-gain × binary-cycle-space factor.
-/

open Filter SimpleGraph Finset
open scoped Topology BigOperators Nat

namespace JSP000506

/-! ### 1. Canonical Interval Partition on `Fin n` -/

private lemma card_filter_interval {K a len : ℕ} (hle : a + len ≤ K) :
    (Finset.univ.filter (fun r : Fin K => a ≤ r.val ∧ r.val < a + len)).card = len := by
  have hlen : len = (Finset.univ : Finset (Fin len)).card := by simp
  conv_rhs => rw [hlen]
  refine Finset.card_bij (fun (r : Fin K) hr => (⟨r.val - a, ?_⟩ : Fin len)) ?_ ?_ ?_
  · rcases (Finset.mem_filter.mp hr).2 with ⟨h1, h2⟩
    omega
  · intro _ _
    exact Finset.mem_univ _
  · intro r₁ hr₁ r₂ hr₂ heq
    rcases (Finset.mem_filter.mp hr₁).2 with ⟨h₁, _⟩
    rcases (Finset.mem_filter.mp hr₂).2 with ⟨h₂, _⟩
    have hval : r₁.val - a = r₂.val - a := congrArg Fin.val heq
    exact Fin.ext (by omega)
  · intro i _
    have hi : i.val < len := i.isLt
    refine ⟨⟨a + i.val, by omega⟩, ?_, Fin.ext (by dsimp; omega)⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by dsimp; omega, by dsimp; omega⟩

/-- Assigns each block index `r : Fin (kCoSeed n)` to one of the 4 size classes in cumulative order. -/
noncomputable def seedBlockType (n : ℕ) (r : Fin (kCoSeed n)) : Fin 4 :=
  if r.val < witnessCounts n 0 then 0
  else if r.val < witnessCounts n 0 + witnessCounts n 1 then 1
  else if r.val < witnessCounts n 0 + witnessCounts n 1 + witnessCounts n 2 then 2
  else 3

/-- Target vertex cardinality of block `r : Fin (kCoSeed n)`. -/
noncomputable def seedBlockSize (n : ℕ) (r : Fin (kCoSeed n)) : ℕ :=
  witnessSize n (seedBlockType n r)

/-- Starting vertex index of block `r : Fin (kCoSeed n)` in `Fin n`. -/
noncomputable def seedBlockStart (n : ℕ) (r : Fin (kCoSeed n)) : ℕ :=
  ∑ q ∈ Finset.univ.filter (fun q : Fin (kCoSeed n) => q.val < r.val), seedBlockSize n q

/-- Canonical interval block `r : Fin (kCoSeed n)` in `Fin n`. -/
noncomputable def canonicalBlocks (n : ℕ) (r : Fin (kCoSeed n)) : Finset (Fin n) :=
  Finset.univ.filter (fun v : Fin n =>
    seedBlockStart n r ≤ v.val ∧ v.val < seedBlockStart n r + seedBlockSize n r)

lemma seedBlockStart_add_le_of_lt {n : ℕ} {r₁ r₂ : Fin (kCoSeed n)} (hlt : r₁.val < r₂.val) :
    seedBlockStart n r₁ + seedBlockSize n r₁ ≤ seedBlockStart n r₂ := by
  let S₁ := Finset.univ.filter (fun q : Fin (kCoSeed n) => q.val < r₁.val)
  let S₂ := Finset.univ.filter (fun q : Fin (kCoSeed n) => q.val < r₂.val)
  have hr₁_not : r₁ ∉ S₁ := by simp [S₁]
  have hsub : insert r₁ S₁ ⊆ S₂ := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq₁
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
    · have hq_lt : q.val < r₁.val := (Finset.mem_filter.mp hq₁).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq_lt.trans hlt⟩
  calc
    seedBlockStart n r₁ + seedBlockSize n r₁
        = seedBlockSize n r₁ + ∑ q ∈ S₁, seedBlockSize n q := add_comm _ _
    _ = ∑ q ∈ insert r₁ S₁, seedBlockSize n q := (Finset.sum_insert hr₁_not).symm
    _ ≤ ∑ q ∈ S₂, seedBlockSize n q :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _
    _ = seedBlockStart n r₂ := rfl

/-- `canonicalBlocks n` is unconditionally pairwise disjoint for every `n : ℕ`. -/
theorem pairwiseDisjoint_canonicalBlocks (n : ℕ) :
    (Set.univ : Set (Fin (kCoSeed n))).PairwiseDisjoint (canonicalBlocks n) := by
  intro r₁ _ r₂ _ hne
  exact Finset.disjoint_left.mpr fun v hv₁ hv₂ => by
    have h₁ := (Finset.mem_filter.mp hv₁).2
    have h₂ := (Finset.mem_filter.mp hv₂).2
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · have hle := seedBlockStart_add_le_of_lt hlt
      omega
    · have hle := seedBlockStart_add_le_of_lt hgt
      omega

/-- Exact multiplicity of each block type `j : Fin 4` when `∑ j, witnessCounts n j = kCoSeed n`. -/
theorem card_seedBlockType_eq {n : ℕ}
    (hK : ∑ j : Fin 4, witnessCounts n j = kCoSeed n) (j : Fin 4) :
    (Finset.univ.filter (fun r : Fin (kCoSeed n) => seedBlockType n r = j)).card =
      witnessCounts n j := by
  have hsum4 : witnessCounts n 0 + witnessCounts n 1 + witnessCounts n 2 + witnessCounts n 3 =
      kCoSeed n := by
    have hexp : ∑ i : Fin 4, witnessCounts n i =
        witnessCounts n 0 + witnessCounts n 1 + witnessCounts n 2 + witnessCounts n 3 := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      change witnessCounts n 0 + (witnessCounts n 1 + (witnessCounts n 2 + witnessCounts n 3)) = _
      omega
    omega
  fin_cases j
  · change (Finset.univ.filter (fun r : Fin (kCoSeed n) => seedBlockType n r = 0)).card =
      witnessCounts n 0
    have hset : Finset.univ.filter (fun r : Fin (kCoSeed n) => seedBlockType n r = 0) =
        Finset.univ.filter (fun r : Fin (kCoSeed n) =>
          0 ≤ r.val ∧ r.val < 0 + witnessCounts n 0) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold seedBlockType
      constructor <;> intro h
      · split_ifs at h <;> omega
      · split_ifs <;> first | rfl | omega
    rw [hset]
    exact card_filter_interval (by omega)
  · change (Finset.univ.filter (fun r : Fin (kCoSeed n) => seedBlockType n r = 1)).card =
      witnessCounts n 1
    have hset : Finset.univ.filter (fun r : Fin (kCoSeed n) => seedBlockType n r = 1) =
        Finset.univ.filter (fun r : Fin (kCoSeed n) =>
          witnessCounts n 0 ≤ r.val ∧ r.val < witnessCounts n 0 + witnessCounts n 1) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold seedBlockType
      constructor <;> intro h
      · split_ifs at h <;> omega
      · split_ifs <;> first | rfl | omega
    rw [hset]
    exact card_filter_interval (by omega)
  · change (Finset.univ.filter (fun r : Fin (kCoSeed n) => seedBlockType n r = 2)).card =
      witnessCounts n 2
    have hset : Finset.univ.filter (fun r : Fin (kCoSeed n) => seedBlockType n r = 2) =
        Finset.univ.filter (fun r : Fin (kCoSeed n) =>
          witnessCounts n 0 + witnessCounts n 1 ≤ r.val ∧
            r.val < (witnessCounts n 0 + witnessCounts n 1) + witnessCounts n 2) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold seedBlockType
      constructor <;> intro h
      · split_ifs at h <;> omega
      · split_ifs <;> first | rfl | omega
    rw [hset]
    exact card_filter_interval (by omega)
  · change (Finset.univ.filter (fun r : Fin (kCoSeed n) => seedBlockType n r = 3)).card =
      witnessCounts n 3
    have hset : Finset.univ.filter (fun r : Fin (kCoSeed n) => seedBlockType n r = 3) =
        Finset.univ.filter (fun r : Fin (kCoSeed n) =>
          witnessCounts n 0 + witnessCounts n 1 + witnessCounts n 2 ≤ r.val ∧
            r.val < (witnessCounts n 0 + witnessCounts n 1 + witnessCounts n 2) +
              witnessCounts n 3) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold seedBlockType
      constructor <;> intro h
      · have hr := r.isLt
        split_ifs at h <;> omega
      · split_ifs <;> first | rfl | omega
    rw [hset]
    exact card_filter_interval (by omega)

private lemma sum_seedBlockType_comp {n : ℕ}
    (hK : ∑ j : Fin 4, witnessCounts n j = kCoSeed n) (f : Fin 4 → ℕ) :
    ∑ r : Fin (kCoSeed n), f (seedBlockType n r) =
      ∑ j : Fin 4, witnessCounts n j * f j := by
  have huniv : (Finset.univ : Finset (Fin (kCoSeed n))) =
      Finset.univ.biUnion (fun j : Fin 4 =>
        Finset.univ.filter (fun r : Fin (kCoSeed n) => seedBlockType n r = j)) := by
    ext r
    simp
  have hdisj : ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint
      (fun j : Fin 4 => Finset.univ.filter (fun r : Fin (kCoSeed n) => seedBlockType n r = j)) := by
    intro j₁ _ j₂ _ hne
    exact Finset.disjoint_left.mpr fun r hr₁ hr₂ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr₁ hr₂
      exact hne (hr₁.symm.trans hr₂)
  conv_lhs => rw [huniv]
  rw [Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hconst : ∀ r ∈ Finset.univ.filter (fun r : Fin (kCoSeed n) => seedBlockType n r = j),
      f (seedBlockType n r) = f j := fun _ hr => by rw [(Finset.mem_filter.mp hr).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, card_seedBlockType_eq hK j]

private lemma prod_seedBlockType_comp {n : ℕ}
    (hK : ∑ j : Fin 4, witnessCounts n j = kCoSeed n) (f : Fin 4 → ℝ) :
    ∏ r : Fin (kCoSeed n), f (seedBlockType n r) =
      ∏ j : Fin 4, (f j) ^ (witnessCounts n j) := by
  have huniv : (Finset.univ : Finset (Fin (kCoSeed n))) =
      Finset.univ.biUnion (fun j : Fin 4 =>
        Finset.univ.filter (fun r : Fin (kCoSeed n) => seedBlockType n r = j)) := by
    ext r
    simp
  have hdisj : ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint
      (fun j : Fin 4 => Finset.univ.filter (fun r : Fin (kCoSeed n) => seedBlockType n r = j)) := by
    intro j₁ _ j₂ _ hne
    exact Finset.disjoint_left.mpr fun r hr₁ hr₂ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr₁ hr₂
      exact hne (hr₁.symm.trans hr₂)
  conv_lhs => rw [huniv]
  rw [Finset.prod_biUnion hdisj]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hconst : ∀ r ∈ Finset.univ.filter (fun r : Fin (kCoSeed n) => seedBlockType n r = j),
      f (seedBlockType n r) = f j := fun _ hr => by rw [(Finset.mem_filter.mp hr).2]
  rw [Finset.prod_congr rfl hconst, Finset.prod_const, card_seedBlockType_eq hK j]

/-- Exact block cardinalities `(canonicalBlocks n r).card = seedBlockSize n r` under the profile
equations. -/
theorem card_canonicalBlocks_eq {n : ℕ}
    (hK : ∑ j : Fin 4, witnessCounts n j = kCoSeed n)
    (hn : ∑ j : Fin 4, witnessSize n j * witnessCounts n j = n)
    (r : Fin (kCoSeed n)) :
    (canonicalBlocks n r).card = seedBlockSize n r := by
  have hsum_all : ∑ q : Fin (kCoSeed n), seedBlockSize n q = n := by
    unfold seedBlockSize
    rw [sum_seedBlockType_comp hK (witnessSize n)]
    calc
      ∑ j : Fin 4, witnessCounts n j * witnessSize n j
          = ∑ j : Fin 4, witnessSize n j * witnessCounts n j :=
        Finset.sum_congr rfl fun j _ => mul_comm _ _
      _ = n := hn
  have hle_n : seedBlockStart n r + seedBlockSize n r ≤ n := by
    let S := Finset.univ.filter (fun q : Fin (kCoSeed n) => q.val < r.val)
    have hr_not : r ∉ S := by simp [S]
    calc
      seedBlockStart n r + seedBlockSize n r
          = seedBlockSize n r + ∑ q ∈ S, seedBlockSize n q := add_comm _ _
      _ = ∑ q ∈ insert r S, seedBlockSize n q := (Finset.sum_insert hr_not).symm
      _ ≤ ∑ q : Fin (kCoSeed n), seedBlockSize n q :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => Nat.zero_le _
      _ = n := hsum_all
  exact card_filter_interval hle_n

/-- `canonicalBlocks n` partitions `Fin n` completely under the profile equations. -/
theorem biUnion_canonicalBlocks_eq_univ {n : ℕ}
    (hK : ∑ j : Fin 4, witnessCounts n j = kCoSeed n)
    (hn : ∑ j : Fin 4, witnessSize n j * witnessCounts n j = n) :
    Finset.univ.biUnion (canonicalBlocks n) = Finset.univ := by
  have hdisj : ((Finset.univ : Finset (Fin (kCoSeed n))) : Set (Fin (kCoSeed n))).PairwiseDisjoint
      (canonicalBlocks n) :=
    fun r₁ _ r₂ _ hne => pairwiseDisjoint_canonicalBlocks n trivial trivial hne
  apply Finset.eq_univ_of_card
  rw [Finset.card_biUnion hdisj]
  simp_rw [card_canonicalBlocks_eq hK hn]
  unfold seedBlockSize
  rw [sum_seedBlockType_comp hK (witnessSize n)]
  calc
    ∑ j : Fin 4, witnessCounts n j * witnessSize n j
        = ∑ j : Fin 4, witnessSize n j * witnessCounts n j :=
      Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ = n := hn
    _ = Fintype.card (Fin n) := (Fintype.card_fin n).symm

/-! ### 2. Permutation-Indexed and Unordered Signed 4-Size Witnesses -/

/-- Transported canonical block `π(canonicalBlocks n r)` for `π : Equiv.Perm (Fin n)`. -/
noncomputable def permBlock (n : ℕ) (π : Equiv.Perm (Fin n)) (r : Fin (kCoSeed n)) :
    Finset (Fin n) :=
  (canonicalBlocks n r).map π.toEmbedding

@[simp]
theorem card_permBlock (n : ℕ) (π : Equiv.Perm (Fin n)) (r : Fin (kCoSeed n)) :
    (permBlock n π r).card = (canonicalBlocks n r).card :=
  Finset.card_map _

theorem pairwiseDisjoint_permBlock (n : ℕ) (π : Equiv.Perm (Fin n)) :
    (Set.univ : Set (Fin (kCoSeed n))).PairwiseDisjoint (permBlock n π) := by
  intro r₁ _ r₂ _ hne
  exact Finset.disjoint_left.mpr fun v hv₁ hv₂ => by
    rcases Finset.mem_map.mp hv₁ with ⟨u₁, hu₁, rfl⟩
    rcases Finset.mem_map.mp hv₂ with ⟨u₂, hu₂, heq⟩
    cases π.toEmbedding.injective heq
    exact Finset.disjoint_left.mp (pairwiseDisjoint_canonicalBlocks n trivial trivial hne) hu₁ hu₂

/-- Permutation-summed signed 4-size witness `W_n(G)` summing over all `π ∈ S_n` and `σ ∈ {I, K}^K`. -/
noncomputable def permSignedWitness (n : ℕ) (G : SimpleGraph (Fin n)) : ℝ := by
  classical
  exact ∑ π : Equiv.Perm (Fin n), ∑ σ : Fin (kCoSeed n) → Bool,
    if ∀ r : Fin (kCoSeed n), SatisfiesSign G (σ r) (permBlock n π r : Set (Fin n))
    then (1 : ℝ) else 0

/-- Symmetry factor `(∏_{j=0}^3 κ_j!) * (∏_{r=1}^K |B_r|!)` relating ordered and unordered blocks. -/
noncomputable def witnessSymmetryFactor (n : ℕ) : ℝ :=
  (∏ j : Fin 4, ((witnessCounts n j) ! : ℝ)) *
    (∏ r : Fin (kCoSeed n), ((canonicalBlocks n r).card ! : ℝ))

/-- Unordered signed 4-size witness `Z_n(G) = W_n(G) / witnessSymmetryFactor n`. -/
noncomputable def unordSignedWitness (n : ℕ) (G : SimpleGraph (Fin n)) : ℝ :=
  permSignedWitness n G / witnessSymmetryFactor n

theorem witnessSymmetryFactor_pos (n : ℕ) : 0 < witnessSymmetryFactor n := by
  unfold witnessSymmetryFactor
  exact mul_pos
    (Finset.prod_pos fun _ _ => Nat.cast_pos.mpr (Nat.factorial_pos _))
    (Finset.prod_pos fun _ _ => Nat.cast_pos.mpr (Nat.factorial_pos _))

theorem permSignedWitness_nonneg (n : ℕ) (G : SimpleGraph (Fin n)) :
    0 ≤ permSignedWitness n G := by
  classical
  unfold permSignedWitness
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num

theorem unordSignedWitness_nonneg (n : ℕ) (G : SimpleGraph (Fin n)) :
    0 ≤ unordSignedWitness n G :=
  div_nonneg (permSignedWitness_nonneg n G) (witnessSymmetryFactor_pos n).le

theorem unordSignedWitness_pos_iff (n : ℕ) (G : SimpleGraph (Fin n)) :
    0 < unordSignedWitness n G ↔ 0 < permSignedWitness n G :=
  div_pos_iff_of_pos_right (witnessSymmetryFactor_pos n)

/-- **Deterministic Cocolorability from `permSignedWitness > 0`**:
Whenever the 4-size profile equations hold and `0 < permSignedWitness n G`, `G` is `kCoSeed n`-cocolorable
(hence `cochromaticNumber G ≤ kCoSeed n`). -/
theorem cocolorable_of_permSignedWitness_pos {n : ℕ}
    (hK : ∑ j : Fin 4, witnessCounts n j = kCoSeed n)
    (hn : ∑ j : Fin 4, witnessSize n j * witnessCounts n j = n)
    {G : SimpleGraph (Fin n)} (hpos : 0 < permSignedWitness n G) :
    Cocolorable G (kCoSeed n) := by
  classical
  unfold permSignedWitness at hpos
  have hex : ∃ π : Equiv.Perm (Fin n), ∃ σ : Fin (kCoSeed n) → Bool,
      ∀ r : Fin (kCoSeed n), SatisfiesSign G (σ r) (permBlock n π r : Set (Fin n)) := by
    by_contra hall
    push Not at hall
    have hzero : (∑ π : Equiv.Perm (Fin n), ∑ σ : Fin (kCoSeed n) → Bool,
        if ∀ r : Fin (kCoSeed n), SatisfiesSign G (σ r) (permBlock n π r : Set (Fin n))
        then (1 : ℝ) else 0) = 0 := by
      refine Finset.sum_eq_zero fun π _ => Finset.sum_eq_zero fun σ _ => ?_
      rcases hall π σ with ⟨r, hr⟩
      have hnot : ¬ ∀ r' : Fin (kCoSeed n),
          SatisfiesSign G (σ r') (permBlock n π r' : Set (Fin n)) := fun hall' => hr (hall' r)
      simp [hnot]
    linarith
  rcases hex with ⟨π, σ, hvalid⟩
  have hcover : ∀ v : Fin n, ∃ r : Fin (kCoSeed n), v ∈ permBlock n π r := by
    intro v
    have hmem_univ : π.symm v ∈ Finset.univ.biUnion (canonicalBlocks n) := by
      rw [biUnion_canonicalBlocks_eq_univ hK hn]
      exact Finset.mem_univ _
    rcases Finset.mem_biUnion.mp hmem_univ with ⟨r, _, hr⟩
    refine ⟨r, Finset.mem_map.mpr ⟨π.symm v, hr, ?_⟩⟩
    simp
  simpa using cocolorable_of_signed_cover G (permBlock n π) σ hcover hvalid

theorem cocolorable_of_unordSignedWitness_pos {n : ℕ}
    (hK : ∑ j : Fin 4, witnessCounts n j = kCoSeed n)
    (hn : ∑ j : Fin 4, witnessSize n j * witnessCounts n j = n)
    {G : SimpleGraph (Fin n)} (hpos : 0 < unordSignedWitness n G) :
    Cocolorable G (kCoSeed n) :=
  cocolorable_of_permSignedWitness_pos hK hn ((unordSignedWitness_pos_iff n G).mp hpos)

/-- Exact first moment of `permSignedWitness n` under `G(n, 1/2)`. -/
theorem expectGnpHalf_permSignedWitness (n : ℕ) :
    expectGnpHalf n (permSignedWitness n) =
      (n ! : ℝ) * (2 : ℝ) ^ (kCoSeed n) *
        (2⁻¹ : ℝ) ^ (∑ r : Fin (kCoSeed n), (canonicalBlocks n r).card.choose 2) := by
  classical
  have hfun : permSignedWitness n = fun G =>
      ∑ π : Equiv.Perm (Fin n), ∑ σ : Fin (kCoSeed n) → Bool,
        {H | ∀ r ∈ (Finset.univ : Finset (Fin (kCoSeed n))),
          SatisfiesSign H (σ r) (permBlock n π r : Set (Fin n))}.indicator (fun _ => (1 : ℝ)) G := by
    funext G
    unfold permSignedWitness
    refine Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun σ _ => ?_
    by_cases h : ∀ r : Fin (kCoSeed n), SatisfiesSign G (σ r) (permBlock n π r : Set (Fin n)) <;>
      simp [Set.indicator, h]
  rw [hfun, expectGnpHalf_sum]
  have hinner : ∀ π : Equiv.Perm (Fin n),
      expectGnpHalf n (fun G => ∑ σ : Fin (kCoSeed n) → Bool,
        {H | ∀ r ∈ (Finset.univ : Finset (Fin (kCoSeed n))),
          SatisfiesSign H (σ r) (permBlock n π r : Set (Fin n))}.indicator (fun _ => (1 : ℝ)) G) =
      (2 : ℝ) ^ (kCoSeed n) *
        (2⁻¹ : ℝ) ^ (∑ r : Fin (kCoSeed n), (canonicalBlocks n r).card.choose 2) := by
    intro π
    rw [expectGnpHalf_sum]
    have hdisj : ((Finset.univ : Finset (Fin (kCoSeed n))) : Set (Fin (kCoSeed n))).PairwiseDisjoint
        (permBlock n π) :=
      fun r₁ _ r₂ _ hne => pairwiseDisjoint_permBlock n π trivial trivial hne
    have hterm : ∀ σ : Fin (kCoSeed n) → Bool,
        expectGnpHalf n (fun G =>
          {H | ∀ r ∈ (Finset.univ : Finset (Fin (kCoSeed n))),
            SatisfiesSign H (σ r) (permBlock n π r : Set (Fin n))}.indicator (fun _ => (1 : ℝ)) G) =
        (2⁻¹ : ℝ) ^ (∑ r : Fin (kCoSeed n), (canonicalBlocks n r).card.choose 2) := by
      intro σ
      rw [expectGnpHalf_indicator_one,
        probGnpHalf_disjoint_satisfiesSign n Finset.univ (permBlock n π) σ hdisj]
      simp_rw [card_permBlock]
    rw [Finset.sum_congr rfl fun σ _ => hterm σ, Finset.sum_const, nsmul_eq_mul]
    simp [Fintype.card_bool, Fintype.card_fin]
  rw [Finset.sum_congr rfl fun π _ => hinner π, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  ring

theorem expectGnpHalf_permSignedWitness_pos (n : ℕ) :
    0 < expectGnpHalf n (permSignedWitness n) := by
  rw [expectGnpHalf_permSignedWitness]
  have hnfac : (0 : ℝ) < (n ! : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  positivity

/-- **Supercritical First Moment of `unordSignedWitness` (`arXiv:2608.30604`, Section 4 / Section 6)**:
Eventually `𝔼[Z_n] ≥ exp(100 * n / (log n)^2)`. -/
theorem eventually_expectGnpHalf_unordSignedWitness_supercritical :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (100 * (n : ℝ) / (Real.log (n : ℝ)) ^ 2) ≤
        expectGnpHalf n (unordSignedWitness n) := by
  filter_upwards [eventually_witnessCounts_spec] with n ⟨hK, hn, _, _, hlog_fm⟩
  unfold unordSignedWitness
  have hdiv : expectGnpHalf n (fun G => permSignedWitness n G / witnessSymmetryFactor n) =
      expectGnpHalf n (permSignedWitness n) / witnessSymmetryFactor n := by
    simp_rw [div_eq_mul_inv, mul_comm _ (witnessSymmetryFactor n)⁻¹]
    rw [expectGnpHalf_mul_const, mul_comm]
  rw [hdiv, expectGnpHalf_permSignedWitness]
  -- Rewrite `witnessSymmetryFactor n` and the edge-exponent sum in terms of `witnessCounts`
  have hprod_cards : ∏ r : Fin (kCoSeed n), ((canonicalBlocks n r).card ! : ℝ) =
      ∏ j : Fin 4, ((witnessSize n j) ! : ℝ) ^ (witnessCounts n j) := by
    simp_rw [card_canonicalBlocks_eq hK hn]
    unfold seedBlockSize
    exact prod_seedBlockType_comp hK (fun j => ((witnessSize n j) ! : ℝ))
  have hsum_choose : ∑ r : Fin (kCoSeed n), (canonicalBlocks n r).card.choose 2 =
      ∑ j : Fin 4, witnessCounts n j * (witnessSize n j).choose 2 := by
    simp_rw [card_canonicalBlocks_eq hK hn]
    unfold seedBlockSize
    exact sum_seedBlockType_comp hK (fun j => (witnessSize n j).choose 2)
  have hsym_eq : witnessSymmetryFactor n =
      Real.exp ((∑ j : Fin 4, Real.log ((witnessCounts n j) ! : ℝ)) +
        ∑ j : Fin 4, (witnessCounts n j : ℝ) * Real.log ((witnessSize n j) ! : ℝ)) := by
    unfold witnessSymmetryFactor
    rw [hprod_cards, Real.exp_add, Real.exp_sum, Real.exp_sum]
    congr 1
    · refine Finset.prod_congr rfl fun j _ => ?_
      exact (Real.exp_log (Nat.cast_pos.mpr (Nat.factorial_pos _))).symm
    · refine Finset.prod_congr rfl fun j _ => ?_
      rw [Real.exp_nat_mul, Real.exp_log (Nat.cast_pos.mpr (Nat.factorial_pos _))]
  have hnum_eq :
      (n ! : ℝ) * (2 : ℝ) ^ (kCoSeed n) *
        (2⁻¹ : ℝ) ^ (∑ r : Fin (kCoSeed n), (canonicalBlocks n r).card.choose 2) =
      Real.exp (Real.log (n ! : ℝ) + (kCoSeed n : ℝ) * Real.log 2 -
        ∑ j : Fin 4, (witnessCounts n j : ℝ) *
          (Real.log 2 * ((witnessSize n j).choose 2 : ℝ))) := by
    rw [hsum_choose]
    have hnfac : (n ! : ℝ) = Real.exp (Real.log (n ! : ℝ)) :=
      (Real.exp_log (Nat.cast_pos.mpr (Nat.factorial_pos n))).symm
    have h2K : (2 : ℝ) ^ (kCoSeed n) = Real.exp ((kCoSeed n : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    have h2edge : (2⁻¹ : ℝ) ^ (∑ j : Fin 4, witnessCounts n j * (witnessSize n j).choose 2) =
        Real.exp (-(∑ j : Fin 4, (witnessCounts n j : ℝ) *
          (Real.log 2 * ((witnessSize n j).choose 2 : ℝ)))) := by
      rw [show -(∑ j : Fin 4, (witnessCounts n j : ℝ) *
            (Real.log 2 * ((witnessSize n j).choose 2 : ℝ))) =
          ((∑ j : Fin 4, witnessCounts n j * (witnessSize n j).choose 2 : ℕ) : ℝ) *
            Real.log (2⁻¹) by
            rw [Real.log_inv, Nat.cast_sum]
            simp_rw [Nat.cast_mul]
            rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun j _ => by ring,
        Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [hnfac, h2K, h2edge, Real.log_exp, ← Real.exp_add, ← Real.exp_add, sub_eq_add_neg]
  rw [hnum_eq, hsym_eq, ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  have hsplit :
      ∑ j : Fin 4, (witnessCounts n j : ℝ) *
        (Real.log ((witnessSize n j) ! : ℝ) + Real.log 2 * ((witnessSize n j).choose 2 : ℝ)) =
      (∑ j : Fin 4, (witnessCounts n j : ℝ) * Real.log ((witnessSize n j) ! : ℝ)) +
        (∑ j : Fin 4, (witnessCounts n j : ℝ) *
          (Real.log 2 * ((witnessSize n j).choose 2 : ℝ))) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
  linarith only [hlog_fm, hsplit]

/-- Normalized second-moment ratio `𝔼[W_n^2] / (𝔼[W_n])^2` of the signed 4-size witness. -/
noncomputable def secondMomentRatio (n : ℕ) : ℝ :=
  expectGnpHalf n (fun G => (permSignedWitness n G) ^ 2) /
    (expectGnpHalf n (permSignedWitness n)) ^ 2

/-- Scale invariance of the normalized second moment between `unordSignedWitness` and `permSignedWitness`. -/
theorem secondMomentRatio_unord_eq_perm (n : ℕ) :
    expectGnpHalf n (fun G => (unordSignedWitness n G) ^ 2) /
      (expectGnpHalf n (unordSignedWitness n)) ^ 2 = secondMomentRatio n := by
  unfold unordSignedWitness secondMomentRatio
  have hc_ne : witnessSymmetryFactor n ≠ 0 := (witnessSymmetryFactor_pos n).ne'
  have h1 : expectGnpHalf n (fun G => (permSignedWitness n G / witnessSymmetryFactor n) ^ 2) =
      (witnessSymmetryFactor n)⁻¹ ^ 2 * expectGnpHalf n (fun G => (permSignedWitness n G) ^ 2) := by
    have hfun : (fun G => (permSignedWitness n G / witnessSymmetryFactor n) ^ 2) =
        fun G => (witnessSymmetryFactor n)⁻¹ ^ 2 * (permSignedWitness n G) ^ 2 := by
      funext G
      ring
    rw [hfun, expectGnpHalf_mul_const]
  have h2 : expectGnpHalf n (fun G => permSignedWitness n G / witnessSymmetryFactor n) =
      (witnessSymmetryFactor n)⁻¹ * expectGnpHalf n (permSignedWitness n) := by
    have hfun : (fun G => permSignedWitness n G / witnessSymmetryFactor n) =
        fun G => (witnessSymmetryFactor n)⁻¹ * permSignedWitness n G := by
      funext G
      ring
    rw [hfun, expectGnpHalf_mul_const]
  rw [h1, h2, mul_pow, mul_div_mul_left _ _ (pow_ne_zero 2 (inv_ne_zero hc_ne))]

/-! ### 3. Exact Signed-Overlap Pair Probability & Binary Cycle-Space Factor (Lemma 6.1) -/

lemma satisfiesSign_mono {V : Type*} {G : SimpleGraph V} {b : Bool} {s t : Set V}
    (h : SatisfiesSign G b s) (hst : t ⊆ s) : SatisfiesSign G b t := by
  cases b <;> exact fun _ hu _ hv huv => h (hst hu) (hst hv) huv

lemma subsetPairs_inter {n : ℕ} (S T : Finset (Fin n)) :
    subsetPairs S ∩ subsetPairs T = subsetPairs (S ∩ T) := by
  ext e
  simp only [Finset.mem_inter, mem_subsetPairs]
  exact ⟨fun ⟨hS, hT⟩ v hv => ⟨hS v hv, hT v hv⟩,
    fun h => ⟨fun v hv => (h v hv).1, fun v hv => (h v hv).2⟩⟩

lemma subsetPairs_eq_empty_of_lt_two {n : ℕ} {S : Finset (Fin n)} (h : S.card < 2) :
    subsetPairs S = ∅ := by
  rw [← Finset.card_eq_zero, card_subsetPairs]
  exact Nat.choose_eq_zero_of_lt h

/-- Set of heavy overlap index pairs `M(A, B) = {(i, j) ∈ Fin K × Fin K | |A_i ∩ B_j| ≥ 2}`. -/
def heavyOverlapPairs {n K : ℕ} (A B : Fin K → Finset (Fin n)) : Finset (Fin K × Fin K) :=
  Finset.univ.filter (fun p : Fin K × Fin K => 2 ≤ (A p.1 ∩ B p.2).card)

/-- Even-degree bipartite subgraph predicate characterizing the binary cycle space `ker(∂)` on `M`. -/
def IsEvenOverlapSubgraph {K : ℕ} (H : Finset (Fin K × Fin K)) : Prop :=
  (∀ i : Fin K, Even (H.filter (fun p => p.1 = i)).card) ∧
  (∀ j : Fin K, Even (H.filter (fun p => p.2 = j)).card)

private def boolSign (b : Bool) : ℝ :=
  if b then 1 else -1

private lemma prod_one_add_eq_sum_powerset {α : Type*} [DecidableEq α]
    (M : Finset α) (f : α → ℝ) :
    (∏ p ∈ M, (1 + f p)) = ∑ H ∈ M.powerset, ∏ p ∈ H, f p := by
  induction M using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
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
    rw [Finset.prod_insert ha, ih, Finset.powerset_insert,
      Finset.sum_union hdisj, Finset.sum_image hinj]
    have himg : (∑ H ∈ s.powerset, ∏ p ∈ insert a H, f p) =
        f a * ∑ H ∈ s.powerset, ∏ p ∈ H, f p := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun H hH => ?_
      have haH : a ∉ H := fun h => ha (Finset.mem_powerset.mp hH h)
      exact Finset.prod_insert haH
    rw [himg]
    ring

private lemma sum_prod_pi_general {β : Type*} [Fintype β] :
    ∀ (K : ℕ) (g : Fin K → β → ℝ),
      (∑ σ : Fin K → β, ∏ i : Fin K, g i (σ i)) = ∏ i : Fin K, ∑ b : β, g i b := by
  intro K
  induction K with
  | zero =>
    intro g
    have huniq : (Finset.univ : Finset (Fin 0 → β)).card = 1 := by simp
    rcases Finset.card_eq_one.mp huniq with ⟨σ₀, hσ₀⟩
    rw [hσ₀, Finset.sum_singleton, Finset.univ_eq_empty, Finset.prod_empty, Finset.prod_empty]
  | succ K ih =>
    intro g
    let e : (β × (Fin K → β)) ≃ (Fin (K + 1) → β) :=
      { toFun := fun p => Fin.cases p.1 p.2
        invFun := fun σ => (σ 0, fun i => σ i.succ)
        left_inv := fun ⟨b, σ'⟩ => by ext <;> simp
        right_inv := fun σ => by
          funext r
          cases r using Fin.cases <;> simp }
    rw [← Equiv.sum_comp e, Fintype.sum_prod_type, Fin.prod_univ_succ]
    have hstep : ∀ b : β,
        (∑ σ' : Fin K → β, ∏ r : Fin (K + 1), g r (e (b, σ') r)) =
          g 0 b * ∏ i : Fin K, ∑ b' : β, g i.succ b' := by
      intro b
      have hprod : ∀ σ' : Fin K → β,
          (∏ r : Fin (K + 1), g r (e (b, σ') r)) = g 0 b * ∏ i : Fin K, g i.succ (σ' i) := by
        intro σ'
        rw [Fin.prod_univ_succ]
        simp [e]
      simp_rw [hprod, ← Finset.mul_sum, ih (fun i b' => g i.succ b')]
    simp_rw [hstep, ← Finset.sum_mul]

private lemma sum_boolSign_pow (m : ℕ) :
    (∑ b : Bool, (boolSign b) ^ m) = if Even m then 2 else 0 := by
  have hsum : (∑ b : Bool, (boolSign b) ^ m) = (-1 : ℝ) ^ m + (1 : ℝ) ^ m := by
    simp [boolSign]
    ring
  rw [hsum, one_pow]
  by_cases hm : Even m
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hm)]
    rcases hm with ⟨t, rfl⟩
    have hneg1 : (-1 : ℝ) ^ (t + t) = 1 := by
      rw [← two_mul, pow_mul]
      norm_num
    linarith
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hm)]
    rcases Nat.not_even_iff_odd.mp hm with ⟨t, rfl⟩
    have hneg1 : (-1 : ℝ) ^ (2 * t + 1) = -1 := by
      rw [pow_add, pow_mul]
      norm_num
    linarith

/-- **Walsh–Hadamard / Binary Cycle-Space Counting Identity**:
For any bipartite edge set `M : Finset (Fin K × Fin K)`, the number of sign assignments
`(σ, τ) : (Fin K → Bool) × (Fin K → Bool)` satisfying `σ p.1 = τ p.2` on every `p ∈ M` equals
`4^K * 2^{-|M|} * #{H ⊆ M | IsEvenOverlapSubgraph H}`. -/
theorem card_compatible_signs_eq_evenSubgraphs {K : ℕ} (M : Finset (Fin K × Fin K)) :
    (∑ σ : Fin K → Bool, ∑ τ : Fin K → Bool,
      if ∀ p ∈ M, σ p.1 = τ p.2 then (1 : ℝ) else 0) =
    (4 : ℝ) ^ K * (2⁻¹ : ℝ) ^ M.card *
      ((by classical exact (M.powerset.filter IsEvenOverlapSubgraph).card : ℕ) : ℝ) := by
  classical
  have hchar : ∀ (σ τ : Fin K → Bool),
      (if ∀ p ∈ M, σ p.1 = τ p.2 then (1 : ℝ) else 0) =
        (2⁻¹ : ℝ) ^ M.card * ∏ p ∈ M, (1 + boolSign (σ p.1) * boolSign (τ p.2)) := by
    intro σ τ
    have hpair : ∀ (b₁ b₂ : Bool),
        ((1 + boolSign b₁ * boolSign b₂) / 2 : ℝ) = if b₁ = b₂ then 1 else 0 := by
      intro b₁ b₂
      cases b₁ <;> cases b₂ <;> norm_num [boolSign]
    have hprod_div : (∏ p ∈ M, ((1 + boolSign (σ p.1) * boolSign (τ p.2)) / 2 : ℝ)) =
        (2⁻¹ : ℝ) ^ M.card * ∏ p ∈ M, (1 + boolSign (σ p.1) * boolSign (τ p.2)) := by
      simp_rw [div_eq_inv_mul]
      rw [Finset.prod_mul_distrib, Finset.prod_const]
    rw [← hprod_div]
    simp_rw [hpair]
    by_cases hall : ∀ p ∈ M, σ p.1 = τ p.2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hall)]
      exact (Finset.prod_eq_one fun p hp => by simp [hall p hp]).symm
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hall)]
      push Not at hall
      rcases hall with ⟨p₀, hp₀, hne⟩
      exact (Finset.prod_eq_zero hp₀ (by simp [hne])).symm
  simp_rw [hchar, prod_one_add_eq_sum_powerset, ← Finset.mul_sum]
  -- Swap `∑ σ, ∑ τ, ∑ H ∈ M.powerset` into `∑ H ∈ M.powerset`
  have hswap :
      (∑ σ : Fin K → Bool, ∑ τ : Fin K → Bool, ∑ H ∈ M.powerset,
        ∏ p ∈ H, (boolSign (σ p.1) * boolSign (τ p.2))) =
      ∑ H ∈ M.powerset,
        (∑ σ : Fin K → Bool, ∏ p ∈ H, boolSign (σ p.1)) *
        (∑ τ : Fin K → Bool, ∏ p ∈ H, boolSign (τ p.2)) := by
    simp_rw [Finset.prod_mul_distrib]
    conv_lhs =>
      arg 2; ext σ
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun H _ => ?_
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [hswap]
  -- Evaluate left and right Walsh character sums
  have hleft : ∀ H : Finset (Fin K × Fin K),
      (∑ σ : Fin K → Bool, ∏ p ∈ H, boolSign (σ p.1)) =
        if ∀ i : Fin K, Even (H.filter (fun p => p.1 = i)).card then (2 : ℝ) ^ K else 0 := by
    intro H
    have hpart : ∀ σ : Fin K → Bool,
        (∏ p ∈ H, boolSign (σ p.1)) =
          ∏ i : Fin K, (boolSign (σ i)) ^ (H.filter (fun p => p.1 = i)).card := by
      intro σ
      have huniv : H = Finset.univ.biUnion (fun i : Fin K => H.filter (fun p => p.1 = i)) := by
        ext p
        simp
      have hdisj : ((Finset.univ : Finset (Fin K)) : Set (Fin K)).PairwiseDisjoint
          (fun i : Fin K => H.filter (fun p => p.1 = i)) := by
        intro i₁ _ i₂ _ hne
        exact Finset.disjoint_left.mpr fun p hp₁ hp₂ =>
          hne ((Finset.mem_filter.mp hp₁).2.symm.trans (Finset.mem_filter.mp hp₂).2)
      conv_lhs => rw [huniv]
      rw [Finset.prod_biUnion hdisj]
      refine Finset.prod_congr rfl fun i _ => ?_
      have hconst : ∀ p ∈ H.filter (fun p => p.1 = i), boolSign (σ p.1) = boolSign (σ i) :=
        fun p hp => by rw [(Finset.mem_filter.mp hp).2]
      rw [Finset.prod_congr rfl hconst, Finset.prod_const]
    simp_rw [hpart]
    rw [sum_prod_pi_general K (fun i b => (boolSign b) ^ (H.filter (fun p => p.1 = i)).card)]
    simp_rw [sum_boolSign_pow]
    by_cases hev : ∀ i : Fin K, Even (H.filter (fun p => p.1 = i)).card
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hev)]
      have hconst : ∀ i ∈ (Finset.univ : Finset (Fin K)),
          (if Even (H.filter (fun p => p.1 = i)).card then (2 : ℝ) else 0) = 2 :=
        fun i _ => ite_eq_left_of_eq_true _ _ (eq_true (hev i))
      rw [Finset.prod_congr rfl hconst, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hev)]
      push Not at hev
      rcases hev with ⟨i₀, hi₀⟩
      exact Finset.prod_eq_zero (Finset.mem_univ i₀) (ite_eq_right_of_eq_false _ _ (eq_false hi₀))
  have hright : ∀ H : Finset (Fin K × Fin K),
      (∑ τ : Fin K → Bool, ∏ p ∈ H, boolSign (τ p.2)) =
        if ∀ j : Fin K, Even (H.filter (fun p => p.2 = j)).card then (2 : ℝ) ^ K else 0 := by
    intro H
    have hpart : ∀ τ : Fin K → Bool,
        (∏ p ∈ H, boolSign (τ p.2)) =
          ∏ j : Fin K, (boolSign (τ j)) ^ (H.filter (fun p => p.2 = j)).card := by
      intro τ
      have huniv : H = Finset.univ.biUnion (fun j : Fin K => H.filter (fun p => p.2 = j)) := by
        ext p
        simp
      have hdisj : ((Finset.univ : Finset (Fin K)) : Set (Fin K)).PairwiseDisjoint
          (fun j : Fin K => H.filter (fun p => p.2 = j)) := by
        intro j₁ _ j₂ _ hne
        exact Finset.disjoint_left.mpr fun p hp₁ hp₂ =>
          hne ((Finset.mem_filter.mp hp₁).2.symm.trans (Finset.mem_filter.mp hp₂).2)
      conv_lhs => rw [huniv]
      rw [Finset.prod_biUnion hdisj]
      refine Finset.prod_congr rfl fun j _ => ?_
      have hconst : ∀ p ∈ H.filter (fun p => p.2 = j), boolSign (τ p.2) = boolSign (τ j) :=
        fun p hp => by rw [(Finset.mem_filter.mp hp).2]
      rw [Finset.prod_congr rfl hconst, Finset.prod_const]
    simp_rw [hpart]
    rw [sum_prod_pi_general K (fun j b => (boolSign b) ^ (H.filter (fun p => p.2 = j)).card)]
    simp_rw [sum_boolSign_pow]
    by_cases hev : ∀ j : Fin K, Even (H.filter (fun p => p.2 = j)).card
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hev)]
      have hconst : ∀ j ∈ (Finset.univ : Finset (Fin K)),
          (if Even (H.filter (fun p => p.2 = j)).card then (2 : ℝ) else 0) = 2 :=
        fun j _ => ite_eq_left_of_eq_true _ _ (eq_true (hev j))
      rw [Finset.prod_congr rfl hconst, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hev)]
      push Not at hev
      rcases hev with ⟨j₀, hj₀⟩
      exact Finset.prod_eq_zero (Finset.mem_univ j₀) (ite_eq_right_of_eq_false _ _ (eq_false hj₀))
  simp_rw [hleft, hright]
  have hprod_ite : ∀ H : Finset (Fin K × Fin K),
      (if ∀ i : Fin K, Even (H.filter (fun p => p.1 = i)).card then (2 : ℝ) ^ K else 0) *
      (if ∀ j : Fin K, Even (H.filter (fun p => p.2 = j)).card then (2 : ℝ) ^ K else 0) =
      if IsEvenOverlapSubgraph H then (4 : ℝ) ^ K else 0 := by
    intro H
    unfold IsEvenOverlapSubgraph
    by_cases h1 : ∀ i : Fin K, Even (H.filter (fun p => p.1 = i)).card <;>
      by_cases h2 : ∀ j : Fin K, Even (H.filter (fun p => p.2 = j)).card
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true h2),
        ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, h2⟩), ← mul_pow]
      norm_num
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_right_of_eq_false _ _ (eq_false h2),
        ite_eq_right_of_eq_false _ _ (eq_false (fun h => h2 h.2)), mul_zero]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), zero_mul,
        ite_eq_right_of_eq_false _ _ (eq_false (fun h => h1 h.1))]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), zero_mul,
        ite_eq_right_of_eq_false _ _ (eq_false (fun h => h1 h.1))]
  simp_rw [hprod_ite]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Lemma 6.1 (`arXiv:2608.30604`) — Exact Signed-Overlap Pair Probability with Cycle-Space Factor**:
For any two pairwise-disjoint `K`-block families `A, B : Fin K → Finset (Fin n)`,
`∑_{σ, τ} ℙ(G realizes (A, σ) and (B, τ))` equals the product of:
- the independent baseline `4^K * 2^{-(∑_i C(|A_i|, 2) + ∑_j C(|B_j|, 2))}`,
- the quadratic heavy-overlap gain `2^{∑_{p ∈ M} (C(|A_{p.1} ∩ B_{p.2}|, 2) - 1)}`, and
- the binary cycle-space cardinality `#{H ⊆ M | IsEvenOverlapSubgraph H}` (`= 2^β`). -/
theorem signed_overlap_pair_prob_eq {n K : ℕ} (A B : Fin K → Finset (Fin n))
    (hA : (Set.univ : Set (Fin K)).PairwiseDisjoint A)
    (hB : (Set.univ : Set (Fin K)).PairwiseDisjoint B) :
    (∑ σ : Fin K → Bool, ∑ τ : Fin K → Bool,
      probGnpHalf n {G |
        (∀ i : Fin K, SatisfiesSign G (σ i) (A i : Set (Fin n))) ∧
        (∀ j : Fin K, SatisfiesSign G (τ j) (B j : Set (Fin n)))}) =
    ((4 : ℝ) ^ K *
      (2⁻¹ : ℝ) ^ (∑ i : Fin K, (A i).card.choose 2 + ∑ j : Fin K, (B j).card.choose 2)) *
    ((2 : ℝ) ^ (∑ p ∈ heavyOverlapPairs A B, ((A p.1 ∩ B p.2).card.choose 2 - 1)) *
      ((by classical exact ((heavyOverlapPairs A B).powerset.filter IsEvenOverlapSubgraph).card : ℕ) : ℝ)) := by
  classical
  let EA : Finset (OffDiagSym2 n) := Finset.univ.biUnion (fun i : Fin K => subsetPairs (A i))
  let EB : Finset (OffDiagSym2 n) := Finset.univ.biUnion (fun j : Fin K => subsetPairs (B j))
  let M : Finset (Fin K × Fin K) := heavyOverlapPairs A B
  have hEA_disj : ((Finset.univ : Finset (Fin K)) : Set (Fin K)).PairwiseDisjoint
      (fun i => subsetPairs (A i)) :=
    fun i₁ _ i₂ _ hne => disjoint_subsetPairs (hA trivial trivial hne)
  have hEB_disj : ((Finset.univ : Finset (Fin K)) : Set (Fin K)).PairwiseDisjoint
      (fun j => subsetPairs (B j)) :=
    fun j₁ _ j₂ _ hne => disjoint_subsetPairs (hB trivial trivial hne)
  have hEA_card : EA.card = ∑ i : Fin K, (A i).card.choose 2 := by
    rw [Finset.card_biUnion hEA_disj]
    exact Finset.sum_congr rfl fun i _ => card_subsetPairs (A i)
  have hEB_card : EB.card = ∑ j : Fin K, (B j).card.choose 2 := by
    rw [Finset.card_biUnion hEB_disj]
    exact Finset.sum_congr rfl fun j _ => card_subsetPairs (B j)
  -- Identify `EA ∩ EB` with the disjoint union of `subsetPairs (A p.1 ∩ B p.2)` over `p ∈ M`
  have hInter_eq : EA ∩ EB = M.biUnion (fun p => subsetPairs (A p.1 ∩ B p.2)) := by
    ext e
    simp only [EA, EB, M, heavyOverlapPairs, Finset.mem_inter, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
      have he_inter : e ∈ subsetPairs (A i ∩ B j) := by
        rw [← subsetPairs_inter]
        exact Finset.mem_inter.mpr ⟨hi, hj⟩
      have hcard_ge2 : 2 ≤ (A i ∩ B j).card := by
        by_contra hlt
        rw [subsetPairs_eq_empty_of_lt_two (not_le.mp hlt)] at he_inter
        exact Finset.notMem_empty e he_inter
      exact ⟨(i, j), hcard_ge2, he_inter⟩
    · rintro ⟨⟨i, j⟩, _, he⟩
      rw [← subsetPairs_inter] at he
      rcases Finset.mem_inter.mp he with ⟨hi, hj⟩
      exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  have hM_disj : (M : Set (Fin K × Fin K)).PairwiseDisjoint
      (fun p => subsetPairs (A p.1 ∩ B p.2)) := by
    intro p₁ _ p₂ _ hne
    exact disjoint_subsetPairs <| Finset.disjoint_left.mpr fun v hv₁ hv₂ => by
      rcases Finset.mem_inter.mp hv₁ with ⟨hA₁, hB₁⟩
      rcases Finset.mem_inter.mp hv₂ with ⟨hA₂, hB₂⟩
      by_cases hi : p₁.1 = p₂.1
      · have hj : p₁.2 ≠ p₂.2 := fun hj => hne (Prod.ext hi hj)
        exact Finset.disjoint_left.mp (hB trivial trivial hj) hB₁ hB₂
      · exact Finset.disjoint_left.mp (hA trivial trivial hi) hA₁ hA₂
  have hInter_card : (EA ∩ EB).card = ∑ p ∈ M, (A p.1 ∩ B p.2).card.choose 2 := by
    rw [hInter_eq, Finset.card_biUnion hM_disj]
    exact Finset.sum_congr rfl fun p _ => card_subsetPairs (A p.1 ∩ B p.2)
  -- Evaluate single-pair probability for fixed `(σ, τ)`
  have hsingle : ∀ (σ τ : Fin K → Bool),
      probGnpHalf n {G |
        (∀ i : Fin K, SatisfiesSign G (σ i) (A i : Set (Fin n))) ∧
        (∀ j : Fin K, SatisfiesSign G (τ j) (B j : Set (Fin n)))} =
      (if ∀ p ∈ M, σ p.1 = τ p.2 then (1 : ℝ) else 0) * (2⁻¹ : ℝ) ^ (EA ∪ EB).card := by
    intro σ τ
    by_cases hcomp : ∀ p ∈ M, σ p.1 = τ p.2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hcomp), one_mul]
      let η : OffDiagSym2 n → Bool := fun e =>
        if h : ∃ i : Fin K, e ∈ subsetPairs (A i) then σ (Classical.choose h)
        else if h' : ∃ j : Fin K, e ∈ subsetPairs (B j) then τ (Classical.choose h')
        else false
      have hηA : ∀ (i : Fin K), ∀ e ∈ subsetPairs (A i), η e = σ i := by
        intro i e he
        have hex : ∃ i' : Fin K, e ∈ subsetPairs (A i') := ⟨i, he⟩
        simp only [η, dite_eq_left_of_eq_true (eq_true hex)]
        have hspec := Classical.choose_spec hex
        by_cases hii : Classical.choose hex = i
        · rw [hii]
        · exact False.elim (Finset.disjoint_left.mp (hEA_disj (Finset.mem_univ _)
            (Finset.mem_univ _) hii) hspec he)
      have hηB : ∀ (j : Fin K), ∀ e ∈ subsetPairs (B j), η e = τ j := by
        intro j e he
        by_cases hexA : ∃ i : Fin K, e ∈ subsetPairs (A i)
        · rcases hexA with ⟨i, hi⟩
          rw [hηA i e hi]
          have he_inter : e ∈ subsetPairs (A i ∩ B j) := by
            rw [← subsetPairs_inter]
            exact Finset.mem_inter.mpr ⟨hi, he⟩
          have hpM : (i, j) ∈ M := by
            simp only [M, heavyOverlapPairs, Finset.mem_filter, Finset.mem_univ, true_and]
            by_contra hlt
            rw [subsetPairs_eq_empty_of_lt_two (not_le.mp hlt)] at he_inter
            exact Finset.notMem_empty e he_inter
          exact hcomp (i, j) hpM
        · have hexB : ∃ j' : Fin K, e ∈ subsetPairs (B j') := ⟨j, he⟩
          simp only [η, hexA, ↓reduceDIte, dite_eq_left_of_eq_true (eq_true hexB)]
          have hspec := Classical.choose_spec hexB
          by_cases hjj : Classical.choose hexB = j
          · rw [hjj]
          · exact False.elim (Finset.disjoint_left.mp (hEB_disj (Finset.mem_univ _)
              (Finset.mem_univ _) hjj) hspec he)
      have hevent : {G : SimpleGraph (Fin n) |
          (∀ i : Fin K, SatisfiesSign G (σ i) (A i : Set (Fin n))) ∧
          (∀ j : Fin K, SatisfiesSign G (τ j) (B j : Set (Fin n)))} =
          {G : SimpleGraph (Fin n) |
            ∀ e ∈ EA ∪ EB, (edgeConfigEquiv n).symm G e = η e} := by
        ext G
        simp only [Set.mem_ofPred_eq, EA, EB, Finset.mem_union, Finset.mem_biUnion,
          Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hGA, hGB⟩ e (⟨i, hi⟩ | ⟨j, hj⟩)
          · rw [hηA i e hi]
            exact (satisfiesSign_iff_subsetPairs G (σ i) (A i)).mp (hGA i) e hi
          · rw [hηB j e hj]
            exact (satisfiesSign_iff_subsetPairs G (τ j) (B j)).mp (hGB j) e hj
        · intro hG
          refine ⟨fun i => ?_, fun j => ?_⟩
          · rw [satisfiesSign_iff_subsetPairs]
            intro e hi
            rw [← hηA i e hi]
            exact hG e (Or.inl ⟨i, hi⟩)
          · rw [satisfiesSign_iff_subsetPairs]
            intro e hj
            rw [← hηB j e hj]
            exact hG e (Or.inr ⟨j, hj⟩)
      rw [hevent, probGnpHalf_prescribed_edges]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hcomp), zero_mul]
      push Not at hcomp
      rcases hcomp with ⟨p₀, hp₀, hne⟩
      have hcard2 : 2 ≤ (A p₀.1 ∩ B p₀.2).card := (Finset.mem_filter.mp hp₀).2
      have hempty : {G : SimpleGraph (Fin n) |
          (∀ i : Fin K, SatisfiesSign G (σ i) (A i : Set (Fin n))) ∧
          (∀ j : Fin K, SatisfiesSign G (τ j) (B j : Set (Fin n)))} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro G ⟨hGA, hGB⟩
        have h1 : SatisfiesSign G (σ p₀.1) ((A p₀.1 ∩ B p₀.2 : Finset (Fin n)) : Set (Fin n)) :=
          satisfiesSign_mono (hGA p₀.1) (by rw [Finset.coe_inter]; exact Set.inter_subset_left)
        have h2 : SatisfiesSign G (τ p₀.2) ((A p₀.1 ∩ B p₀.2 : Finset (Fin n)) : Set (Fin n)) :=
          satisfiesSign_mono (hGB p₀.2) (by rw [Finset.coe_inter]; exact Set.inter_subset_right)
        exact hne (satisfiesSign_unique_of_two_le_card hcard2 h1 h2)
      rw [hempty, probGnpHalf_empty]
  simp_rw [hsingle, ← Finset.sum_mul]
  rw [card_compatible_signs_eq_evenSubgraphs M]
  -- Combine powers of `2` cleanly using `(EA ∪ EB).card + M.card + ∑_{p ∈ M} (C(r_p, 2) - 1) = EA.card + EB.card`
  have hchoose_ge1 : ∀ p ∈ M, 1 ≤ (A p.1 ∩ B p.2).card.choose 2 := by
    intro p hp
    have h2 : 2 ≤ (A p.1 ∩ B p.2).card := (Finset.mem_filter.mp hp).2
    simpa using Nat.choose_le_choose 2 h2
  have hsum_sub1 : (∑ p ∈ M, ((A p.1 ∩ B p.2).card.choose 2 - 1)) + M.card = (EA ∩ EB).card := by
    have hM_ones : M.card = ∑ _p ∈ M, 1 := by simp
    rw [hInter_card, hM_ones, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => Nat.sub_add_cancel (hchoose_ge1 p hp)
  have hexp_eq :
      (EA ∪ EB).card + M.card + (∑ p ∈ M, ((A p.1 ∩ B p.2).card.choose 2 - 1)) =
        ∑ i : Fin K, (A i).card.choose 2 + ∑ j : Fin K, (B j).card.choose 2 := by
    have hu := Finset.card_union_add_card_inter EA EB
    omega
  have hpow_id :
      (2⁻¹ : ℝ) ^ (∑ i : Fin K, (A i).card.choose 2 + ∑ j : Fin K, (B j).card.choose 2) *
        (2 : ℝ) ^ (∑ p ∈ M, ((A p.1 ∩ B p.2).card.choose 2 - 1)) =
      (2⁻¹ : ℝ) ^ M.card * (2⁻¹ : ℝ) ^ (EA ∪ EB).card := by
    rw [← hexp_eq, pow_add, pow_add, mul_assoc]
    have hcancel : (2⁻¹ : ℝ) ^ (∑ p ∈ M, ((A p.1 ∩ B p.2).card.choose 2 - 1)) *
        (2 : ℝ) ^ (∑ p ∈ M, ((A p.1 ∩ B p.2).card.choose 2 - 1)) = 1 := by
      rw [← mul_pow]
      norm_num
    rw [hcancel, mul_one, mul_comm]
  calc
    (4 : ℝ) ^ K * (2⁻¹ : ℝ) ^ M.card *
        (((M.powerset.filter IsEvenOverlapSubgraph).card : ℕ) : ℝ) *
        (2⁻¹ : ℝ) ^ (EA ∪ EB).card
        = (4 : ℝ) ^ K * ((2⁻¹ : ℝ) ^ M.card * (2⁻¹ : ℝ) ^ (EA ∪ EB).card) *
            (((M.powerset.filter IsEvenOverlapSubgraph).card : ℕ) : ℝ) := by ring
    _ = (4 : ℝ) ^ K *
          ((2⁻¹ : ℝ) ^ (∑ i : Fin K, (A i).card.choose 2 + ∑ j : Fin K, (B j).card.choose 2) *
            (2 : ℝ) ^ (∑ p ∈ M, ((A p.1 ∩ B p.2).card.choose 2 - 1))) *
          (((M.powerset.filter IsEvenOverlapSubgraph).card : ℕ) : ℝ) := by rw [← hpow_id]
    _ = _ := by ring

/-- Pairwise overlap weight `2^{∑_{p ∈ M} (C(r_p, 2) - 1)} * #{H ⊆ M | IsEvenOverlapSubgraph H}`
between two `K`-block families `A, B`. -/
noncomputable def overlapPairFactor {n K : ℕ} (A B : Fin K → Finset (Fin n)) : ℝ := by
  classical
  exact (2 : ℝ) ^ (∑ p ∈ heavyOverlapPairs A B, ((A p.1 ∩ B p.2).card.choose 2 - 1)) *
    (((heavyOverlapPairs A B).powerset.filter IsEvenOverlapSubgraph).card : ℝ)

/-- **Exact Normalized Second-Moment Expansion (`arXiv:2608.30604`, Section 6)**:
`secondMomentRatio n` equals the uniform average over `(π₁, π₂) ∈ S_n × S_n` of
`overlapPairFactor (permBlock n π₁) (permBlock n π₂)`. -/
theorem secondMomentRatio_eq_overlap_sum (n : ℕ) :
    secondMomentRatio n =
      ((n ! : ℝ) ^ 2)⁻¹ *
        ∑ π₁ : Equiv.Perm (Fin n), ∑ π₂ : Equiv.Perm (Fin n),
          overlapPairFactor (permBlock n π₁) (permBlock n π₂) := by
  classical
  unfold secondMomentRatio
  -- Expand `(permSignedWitness n G) ^ 2` as a sum over `π₁, π₂, σ, τ`
  have hsq_fun : (fun G => (permSignedWitness n G) ^ 2) = fun G =>
      ∑ π₁ : Equiv.Perm (Fin n), ∑ π₂ : Equiv.Perm (Fin n),
        ∑ σ : Fin (kCoSeed n) → Bool, ∑ τ : Fin (kCoSeed n) → Bool,
          {H | (∀ i : Fin (kCoSeed n), SatisfiesSign H (σ i) (permBlock n π₁ i : Set (Fin n))) ∧
               (∀ j : Fin (kCoSeed n), SatisfiesSign H (τ j) (permBlock n π₂ j : Set (Fin n)))}.indicator
            (fun _ => (1 : ℝ)) G := by
    funext G
    unfold permSignedWitness
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun π₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun π₂ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    by_cases h1 : ∀ i : Fin (kCoSeed n), SatisfiesSign G (σ i) (permBlock n π₁ i : Set (Fin n)) <;>
      by_cases h2 : ∀ j : Fin (kCoSeed n), SatisfiesSign G (τ j) (permBlock n π₂ j : Set (Fin n)) <;>
      simp [Set.indicator, h1, h2]
  rw [hsq_fun, expectGnpHalf_sum]
  set E₀ : ℕ := ∑ r : Fin (kCoSeed n), (canonicalBlocks n r).card.choose 2
  have hpair_eval : ∀ (π₁ π₂ : Equiv.Perm (Fin n)),
      expectGnpHalf n (fun G =>
        ∑ σ : Fin (kCoSeed n) → Bool, ∑ τ : Fin (kCoSeed n) → Bool,
          {H | (∀ i : Fin (kCoSeed n), SatisfiesSign H (σ i) (permBlock n π₁ i : Set (Fin n))) ∧
               (∀ j : Fin (kCoSeed n), SatisfiesSign H (τ j) (permBlock n π₂ j : Set (Fin n)))}.indicator
            (fun _ => (1 : ℝ)) G) =
      ((4 : ℝ) ^ (kCoSeed n) * (2⁻¹ : ℝ) ^ (E₀ + E₀)) *
        overlapPairFactor (permBlock n π₁) (permBlock n π₂) := by
    intro π₁ π₂
    rw [expectGnpHalf_sum]
    have hinner : ∀ σ : Fin (kCoSeed n) → Bool,
        expectGnpHalf n (fun G => ∑ τ : Fin (kCoSeed n) → Bool,
          {H | (∀ i : Fin (kCoSeed n), SatisfiesSign H (σ i) (permBlock n π₁ i : Set (Fin n))) ∧
               (∀ j : Fin (kCoSeed n), SatisfiesSign H (τ j) (permBlock n π₂ j : Set (Fin n)))}.indicator
            (fun _ => (1 : ℝ)) G) =
        ∑ τ : Fin (kCoSeed n) → Bool,
          probGnpHalf n {G |
            (∀ i : Fin (kCoSeed n), SatisfiesSign G (σ i) (permBlock n π₁ i : Set (Fin n))) ∧
            (∀ j : Fin (kCoSeed n), SatisfiesSign G (τ j) (permBlock n π₂ j : Set (Fin n)))} := by
      intro σ
      rw [expectGnpHalf_sum]
      refine Finset.sum_congr rfl fun τ _ => expectGnpHalf_indicator_one n _
    simp_rw [hinner]
    rw [signed_overlap_pair_prob_eq (permBlock n π₁) (permBlock n π₂)
      (pairwiseDisjoint_permBlock n π₁) (pairwiseDisjoint_permBlock n π₂)]
    simp_rw [card_permBlock]
    rfl
  have houter : ∀ π₁ : Equiv.Perm (Fin n),
      expectGnpHalf n (fun G => ∑ π₂ : Equiv.Perm (Fin n),
        ∑ σ : Fin (kCoSeed n) → Bool, ∑ τ : Fin (kCoSeed n) → Bool,
          {H | (∀ i : Fin (kCoSeed n), SatisfiesSign H (σ i) (permBlock n π₁ i : Set (Fin n))) ∧
               (∀ j : Fin (kCoSeed n), SatisfiesSign H (τ j) (permBlock n π₂ j : Set (Fin n)))}.indicator
            (fun _ => (1 : ℝ)) G) =
      ((4 : ℝ) ^ (kCoSeed n) * (2⁻¹ : ℝ) ^ (E₀ + E₀)) *
        ∑ π₂ : Equiv.Perm (Fin n), overlapPairFactor (permBlock n π₁) (permBlock n π₂) := by
    intro π₁
    rw [expectGnpHalf_sum, Finset.sum_congr rfl fun π₂ _ => hpair_eval π₁ π₂, ← Finset.mul_sum]
  simp_rw [houter, ← Finset.mul_sum]
  rw [expectGnpHalf_permSignedWitness]
  have hexp_sq :
      ((n ! : ℝ) * (2 : ℝ) ^ (kCoSeed n) * (2⁻¹ : ℝ) ^ E₀) ^ 2 =
        ((n ! : ℝ) ^ 2) * ((4 : ℝ) ^ (kCoSeed n) * (2⁻¹ : ℝ) ^ (E₀ + E₀)) := by
    have h4 : ((2 : ℝ) ^ (kCoSeed n)) ^ 2 = (4 : ℝ) ^ (kCoSeed n) := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [mul_pow, mul_pow, h4, pow_add, sq ((2⁻¹ : ℝ) ^ E₀)]
    ring
  rw [hexp_sq]
  have hpos_base : (0 : ℝ) < (4 : ℝ) ^ (kCoSeed n) * (2⁻¹ : ℝ) ^ (E₀ + E₀) := by positivity
  have hnfac_ne : ((n ! : ℝ) ^ 2) ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
  rw [div_mul_eq_div_div_swap, mul_div_cancel_left₀ _ hpos_base.ne', div_eq_inv_mul]

end JSP000506
