import Mathlib.Data.Fintype.CardEmbedding
import JSP000506.Diag

/-!
# Section 8: Canonical High-Cell Skeletons, Deficit Sums, and Endpoint-Table Reduction

This module formalizes Section 8 of Samuil Petkov's *A Full-Sequence Quantitative Gap Between the
Chromatic and Cochromatic Numbers of a Random Graph* (`arXiv:2608.30604`), establishing the
phase-uniform subcritical bound on the sum of canonical high-cell skeleton weights
`∑_{M ∈ blockMatchings n} ∑_{j ∈ highMultBox n M} highSkeletonWeight n M j ≤ exp(η_hi(n) * n / (log n)^4)`
with `η_hi(n) → 0`:

1. **High-Cell Thresholds and Block Matchings (`highCap`, `highThresh`, `IsBlockMatching`)**:
   Defines `U = highCap n = witnessSize n 0` (`α_n - 2`) and `R_0 = highThresh n = ⌊U / 2⌋`.
   Because every canonical block has cardinality `≤ U < 2 * (R_0 + 1)`, cells exceeding `R_0`
   have at most one entry per row and column (`IsBlockMatching`).
2. **Deficit Geometric Decay (`sum_highMultBox_highSkeletonWeight_le`)**:
   For any block matching `M` and feasible multiplicity vector `j ∈ highMultBox n M`, compares
   `highSkeletonWeight n M j` directly to `fullSkeletonWeight n M` via the quadratic binomial drop
   `C(m_p, 2) - C(j_p, 2) ≥ (m_p - j_p) * (3 α_n / 4 - 4)`, summing over `highMultBox n M`.
3. **Exact `4 × 4` Type-Table Counting and Squared Comparison (`tableWeight_sq_le`)**:
   Injects ordered realizations of matchings with `4 × 4` endpoint-type table `L` into row/column
   class embeddings via `Fintype.card_embedding_eq`, proves Lemma 8.6 comparing `(tableWeight n L)^2`
   against `diagWeight n (typeTableRow L) * diagWeight n (typeTableCol L)`, applies AM-GM and the
   4-variable multinomial identity, and invokes Section 7 (`eventually_sum_diagWeight_le`).
-/

open Filter SimpleGraph Finset
open scoped Topology BigOperators Nat

namespace JSP000506

/-! ### 1. General Falling-Factorial, Exponential, and Binomial-Gap Helpers -/

/-- Multiplicative splitting `(a)_{b + c} = (a)_b * (a - b)_c` for all `a, b, c : ℕ`. -/
theorem descFactorial_add_eq (a b c : ℕ) :
    a.descFactorial (b + c) = a.descFactorial b * (a - b).descFactorial c := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [← add_assoc, Nat.descFactorial_succ, ih, Nat.descFactorial_succ, Nat.sub_sub]
    ring

/-- Polynomial lower bound `t ^ m / m! ≤ exp t` for all `0 ≤ t` and `m : ℕ`. -/
theorem pow_div_factorial_le_exp {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    t ^ m / (m ! : ℝ) ≤ Real.exp t := by
  have hsingle : t ^ m / (m ! : ℝ) ≤ ∑ k ∈ Finset.range (m + 1), t ^ k / (k ! : ℝ) :=
    Finset.single_le_sum (fun k _ => div_nonneg (pow_nonneg ht k) (Nat.cast_nonneg _))
      (Finset.mem_range.mpr (Nat.lt_succ_self m))
  exact hsingle.trans (Real.sum_le_exp_of_nonneg ht (m + 1))

/-- Elementary AM-GM corollary: if `0 ≤ w`, `0 ≤ X`, `0 ≤ Y`, and `w ^ 2 ≤ X * Y`,
then `w ≤ (X + Y) / 2`. -/
theorem le_half_add_of_sq_le_mul {w X Y : ℝ}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hsq : w ^ 2 ≤ X * Y) :
    w ≤ (X + Y) / 2 := by
  by_contra hlt
  push Not at hlt
  nlinarith [sq_nonneg (X - Y)]

/-- Exact binomial-two gap lower bound: whenever `1 ≤ j ≤ m` and `2 * q ≤ m + j - 1`,
`j.choose 2 + (m - j) * q ≤ m.choose 2`. -/
theorem choose_two_add_sub_mul_le {j m q : ℕ}
    (hj1 : 1 ≤ j) (hjm : j ≤ m) (hq : 2 * q ≤ m + j - 1) :
    j.choose 2 + (m - j) * q ≤ m.choose 2 := by
  suffices hreal : ((j.choose 2 + (m - j) * q : ℕ) : ℝ) ≤ (m.choose 2 : ℝ) by
    exact_mod_cast hreal
  push_cast
  rw [cast_choose_two j, cast_choose_two m, Nat.cast_sub hjm]
  have hq_r : 2 * (q : ℝ) ≤ (m : ℝ) + (j : ℝ) - 1 := by
    have hc : ((2 * q : ℕ) : ℝ) ≤ ((m + j - 1 : ℕ) : ℝ) := by exact_mod_cast hq
    rw [Nat.cast_sub (by omega)] at hc
    push_cast at hc
    linarith
  have hdiff_nonneg : 0 ≤ (m : ℝ) - (j : ℝ) := sub_nonneg.mpr (by exact_mod_cast hjm)
  have hm_prod := mul_le_mul_of_nonneg_left hq_r hdiff_nonneg
  have hid : (m : ℝ) * ((m : ℝ) - 1) - (j : ℝ) * ((j : ℝ) - 1) =
      ((m : ℝ) - (j : ℝ)) * ((m : ℝ) + (j : ℝ) - 1) := by ring
  linarith

/-! ### 2. High-Cell Parameters, Block Matchings, and Canonical Skeleton Weights -/

/-- Maximum block size `U = witnessSize n 0 = alphaNat n - 2` of the 4-size profile. -/
noncomputable def highCap (n : ℕ) : ℕ :=
  witnessSize n 0

/-- Canonical high-overlap threshold `R_0 = ⌊U / 2⌋`. -/
noncomputable def highThresh (n : ℕ) : ℕ :=
  highCap n / 2

theorem witnessSize_le_highCap (n : ℕ) (i : Fin 4) :
    witnessSize n i ≤ highCap n := by
  unfold highCap witnessSize
  omega

theorem seedBlockSize_le_highCap (n : ℕ) (r : Fin (kCoSeed n)) :
    seedBlockSize n r ≤ highCap n :=
  witnessSize_le_highCap n (seedBlockType n r)

theorem highCap_lt_two_mul_highThresh_succ (n : ℕ) :
    highCap n < 2 * (highThresh n + 1) := by
  unfold highThresh
  omega

/-- A subset `M` of `Fin K × Fin K` is a partial block matching if every row and every column
is incident to at most one edge of `M`. -/
def IsBlockMatching (K : ℕ) (M : Finset (Fin K × Fin K)) : Prop :=
  (∀ p₁ ∈ M, ∀ p₂ ∈ M, p₁.1 = p₂.1 → p₁ = p₂) ∧
  (∀ p₁ ∈ M, ∀ p₂ ∈ M, p₁.2 = p₂.2 → p₁ = p₂)

/-- Finite family of all partial block matchings on `Fin (kCoSeed n) × Fin (kCoSeed n)`. -/
noncomputable def blockMatchings (n : ℕ) :
    Finset (Finset (Fin (kCoSeed n) × Fin (kCoSeed n))) := by
  classical
  exact (Finset.univ : Finset (Fin (kCoSeed n) × Fin (kCoSeed n))).powerset.filter
    (IsBlockMatching (kCoSeed n))

@[simp]
theorem mem_blockMatchings_iff {n : ℕ}
    {M : Finset (Fin (kCoSeed n) × Fin (kCoSeed n))} :
    M ∈ blockMatchings n ↔ IsBlockMatching (kCoSeed n) M := by
  classical
  simp [blockMatchings]

theorem card_le_of_isBlockMatching {K : ℕ} {M : Finset (Fin K × Fin K)}
    (hM : IsBlockMatching K M) :
    M.card ≤ K := by
  have hinj : Set.InjOn Prod.fst (M : Set (Fin K × Fin K)) :=
    fun p₁ hp₁ p₂ hp₂ heq => hM.1 p₁ hp₁ p₂ hp₂ heq
  calc
    M.card = (M.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset (Fin K)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = K := Fintype.card_fin K

/-- Maximum possible intersection cardinality `m_p = min(s_{p.1}, s_{p.2})` of cell `p`. -/
noncomputable def cellMinSize (n : ℕ) (p : Fin (kCoSeed n) × Fin (kCoSeed n)) : ℕ :=
  min (seedBlockSize n p.1) (seedBlockSize n p.2)

theorem cellMinSize_le_highCap (n : ℕ) (p : Fin (kCoSeed n) × Fin (kCoSeed n)) :
    cellMinSize n p ≤ highCap n :=
  (min_le_left _ _).trans (seedBlockSize_le_highCap n p.1)

theorem sum_seedBlockSize_eq_n {n : ℕ}
    (hK : ∑ i : Fin 4, witnessCounts n i = kCoSeed n)
    (hn : ∑ i : Fin 4, witnessSize n i * witnessCounts n i = n) :
    ∑ r : Fin (kCoSeed n), seedBlockSize n r = n := by
  have hdisj : ((Finset.univ : Finset (Fin (kCoSeed n))) : Set (Fin (kCoSeed n))).PairwiseDisjoint
      (canonicalBlocks n) :=
    fun r₁ _ r₂ _ hne => pairwiseDisjoint_canonicalBlocks n trivial trivial hne
  have huniv := biUnion_canonicalBlocks_eq_univ hK hn
  have hcard : (Finset.univ.biUnion (canonicalBlocks n)).card = n := by
    rw [huniv, Finset.card_univ, Fintype.card_fin]
  rw [Finset.card_biUnion hdisj] at hcard
  simp_rw [card_canonicalBlocks_eq hK hn] at hcard
  exact hcard

theorem sum_cellMinSize_le_n {n : ℕ}
    (hK : ∑ i : Fin 4, witnessCounts n i = kCoSeed n)
    (hn : ∑ i : Fin 4, witnessSize n i * witnessCounts n i = n)
    {M : Finset (Fin (kCoSeed n) × Fin (kCoSeed n))}
    (hM : IsBlockMatching (kCoSeed n) M) :
    ∑ p ∈ M, cellMinSize n p ≤ n := by
  have hinj : Set.InjOn Prod.fst (M : Set (Fin (kCoSeed n) × Fin (kCoSeed n))) :=
    fun p₁ hp₁ p₂ hp₂ heq => hM.1 p₁ hp₁ p₂ hp₂ heq
  calc
    ∑ p ∈ M, cellMinSize n p
        ≤ ∑ p ∈ M, seedBlockSize n p.1 :=
      Finset.sum_le_sum fun p _ => min_le_left _ _
    _ = ∑ r ∈ M.image Prod.fst, seedBlockSize n r :=
      (Finset.sum_image hinj).symm
    _ ≤ ∑ r : Fin (kCoSeed n), seedBlockSize n r :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => Nat.zero_le _
    _ = n := sum_seedBlockSize_eq_n hK hn

/-- Box of feasible high-multiplicity vectors `j` supported on a block matching `M`:
`R_0 + 1 ≤ j p ≤ cellMinSize n p` for `p ∈ M` and `j p = 0` for `p ∉ M`. -/
noncomputable def highMultBox (n : ℕ)
    (M : Finset (Fin (kCoSeed n) × Fin (kCoSeed n))) :
    Finset (Fin (kCoSeed n) × Fin (kCoSeed n) → ℕ) :=
  Fintype.piFinset (fun p : Fin (kCoSeed n) × Fin (kCoSeed n) =>
    if p ∈ M then Finset.Icc (highThresh n + 1) (cellMinSize n p) else {0})

theorem mem_highMultBox_iff {n : ℕ}
    {M : Finset (Fin (kCoSeed n) × Fin (kCoSeed n))}
    {j : Fin (kCoSeed n) × Fin (kCoSeed n) → ℕ} :
    j ∈ highMultBox n M ↔
      (∀ p ∈ M, highThresh n + 1 ≤ j p ∧ j p ≤ cellMinSize n p) ∧
      (∀ p ∉ M, j p = 0) := by
  simp only [highMultBox, Fintype.mem_piFinset]
  constructor
  · intro h
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · have hp' := h p
      simp only [hp, ↓reduceIte, Finset.mem_Icc] at hp'
      exact hp'
    · have hp' := h p
      simp only [hp, ↓reduceIte, Finset.mem_singleton] at hp'
      exact hp'
  · rintro ⟨h1, h2⟩ p
    by_cases hp : p ∈ M
    · simp only [hp, ↓reduceIte, Finset.mem_Icc]
      exact h1 p hp
    · simp only [hp, ↓reduceIte, Finset.mem_singleton]
      exact h2 p hp

theorem sum_highMult_le_n {n : ℕ}
    (hK : ∑ i : Fin 4, witnessCounts n i = kCoSeed n)
    (hn : ∑ i : Fin 4, witnessSize n i * witnessCounts n i = n)
    {M : Finset (Fin (kCoSeed n) × Fin (kCoSeed n))}
    (hM : IsBlockMatching (kCoSeed n) M)
    {j : Fin (kCoSeed n) × Fin (kCoSeed n) → ℕ}
    (hj : j ∈ highMultBox n M) :
    ∑ p ∈ M, j p ≤ n := by
  have hjM := (mem_highMultBox_iff.mp hj).1
  exact (Finset.sum_le_sum fun p hp => (hjM p hp).2).trans (sum_cellMinSize_le_n hK hn hM)

/-- Canonical high-skeleton weight `w_n(M, j)` (`(8.3)` of `arXiv:2608.30604`). -/
noncomputable def highSkeletonWeight (n : ℕ)
    (M : Finset (Fin (kCoSeed n) × Fin (kCoSeed n)))
    (j : Fin (kCoSeed n) × Fin (kCoSeed n) → ℕ) : ℝ :=
  (∏ p ∈ M,
    (((seedBlockSize n p.1).descFactorial (j p) : ℝ) *
      ((seedBlockSize n p.2).descFactorial (j p) : ℝ) /
      ((j p) ! : ℝ)) * localCellReward (j p)) /
  (n.descFactorial (∑ p ∈ M, j p) : ℝ)

theorem highSkeletonWeight_nonneg (n : ℕ)
    (M : Finset (Fin (kCoSeed n) × Fin (kCoSeed n)))
    (j : Fin (kCoSeed n) × Fin (kCoSeed n) → ℕ) :
    0 ≤ highSkeletonWeight n M j := by
  unfold highSkeletonWeight
  refine div_nonneg (Finset.prod_nonneg fun p _ => ?_) (Nat.cast_nonneg _)
  exact mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)) (localCellReward_pos _).le

/-- Full-saturation multiplicity profile `m_p = cellMinSize n p` on `M` and `0` off `M`. -/
noncomputable def fullMultiplicity (n : ℕ)
    (M : Finset (Fin (kCoSeed n) × Fin (kCoSeed n)))
    (p : Fin (kCoSeed n) × Fin (kCoSeed n)) : ℕ :=
  if p ∈ M then cellMinSize n p else 0

/-- Full-saturation skeleton weight `w_n^{\mathrm{full}}(M) = w_n(M, m)`. -/
noncomputable def fullSkeletonWeight (n : ℕ)
    (M : Finset (Fin (kCoSeed n) × Fin (kCoSeed n))) : ℝ :=
  highSkeletonWeight n M (fullMultiplicity n M)

theorem fullSkeletonWeight_nonneg (n : ℕ)
    (M : Finset (Fin (kCoSeed n) × Fin (kCoSeed n))) :
    0 ≤ fullSkeletonWeight n M :=
  highSkeletonWeight_nonneg n M (fullMultiplicity n M)

/-! ### 3. Subsection 8.2: Per-Edge Deficit Decay and Sum over `highMultBox n M` -/

/-- Deficit decay ratio `ρ_def(n) = n * alphaNat n / 2 ^ (3 * alphaNat n / 4 - 4)`. -/
noncomputable def deficitRatio (n : ℕ) : ℝ :=
  ((n : ℝ) * (alphaNat n : ℝ)) / (2 : ℝ) ^ (3 * alphaNat n / 4 - 4)

theorem deficitRatio_nonneg (n : ℕ) : 0 ≤ deficitRatio n := by
  unfold deficitRatio
  positivity

/-- Pointwise deficit bound: for any matching `M` and `j ∈ highMultBox n M`,
`highSkeletonWeight n M j ≤ fullSkeletonWeight n M * ∏ p ∈ M, (deficitRatio n) ^ (cellMinSize n p - j p)`. -/
theorem highSkeletonWeight_le_full_mul_prod_deficit {n : ℕ}
    (hK : ∑ i : Fin 4, witnessCounts n i = kCoSeed n)
    (hn : ∑ i : Fin 4, witnessSize n i * witnessCounts n i = n)
    (hα40 : 40 ≤ alphaNat n)
    {M : Finset (Fin (kCoSeed n) × Fin (kCoSeed n))}
    (hM : IsBlockMatching (kCoSeed n) M)
    {j : Fin (kCoSeed n) × Fin (kCoSeed n) → ℕ}
    (hj : j ∈ highMultBox n M) :
    highSkeletonWeight n M j ≤
      fullSkeletonWeight n M *
        ∏ p ∈ M, (deficitRatio n) ^ (cellMinSize n p - j p) := by
  have hjM := (mem_highMultBox_iff.mp hj).1
  set J : ℕ := ∑ p ∈ M, j p
  set M_sum : ℕ := ∑ p ∈ M, cellMinSize n p
  set H : ℕ := ∑ p ∈ M, (cellMinSize n p - j p)
  have hM_le_n : M_sum ≤ n := sum_cellMinSize_le_n hK hn hM
  have hJH_eq : J + H = M_sum := by
    dsimp [J, H, M_sum]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p hp => Nat.add_sub_of_le (hjM p hp).2
  have hJ_le_n : J ≤ n := by omega
  have hdesc_n_pos : 0 < (n.descFactorial M_sum : ℝ) :=
    Nat.cast_pos.mpr (descFactorial_pos_of_le hM_le_n)
  have hdesc_J_pos : 0 < (n.descFactorial J : ℝ) :=
    Nat.cast_pos.mpr (descFactorial_pos_of_le hJ_le_n)
  have hinv_J_le :
      ((n.descFactorial J : ℝ))⁻¹ ≤
        ((n : ℝ) ^ H) / (n.descFactorial M_sum : ℝ) := by
    rw [inv_le_iff_one_le_mul₀ hdesc_J_pos, div_mul_eq_mul_div, le_div_iff₀ hdesc_n_pos, one_mul]
    have hsplit_nat : n.descFactorial M_sum = n.descFactorial J * (n - J).descFactorial H := by
      rw [← hJH_eq]
      exact descFactorial_add_eq n J H
    have hrem_le : (n - J).descFactorial H ≤ n ^ H :=
      (descFactorial_le_pow (n - J) H).trans (Nat.pow_le_pow_left (Nat.sub_le n J) H)
    have hnat : n.descFactorial M_sum ≤ n ^ H * n.descFactorial J := by
      rw [hsplit_nat, mul_comm (n.descFactorial J)]
      exact Nat.mul_le_mul_right _ hrem_le
    exact_mod_cast hnat
  set qExp : ℕ := 3 * alphaNat n / 4 - 4
  have hcell_bound : ∀ p ∈ M,
      (((seedBlockSize n p.1).descFactorial (j p) : ℝ) *
        ((seedBlockSize n p.2).descFactorial (j p) : ℝ) /
        ((j p) ! : ℝ)) * localCellReward (j p) ≤
      ((((seedBlockSize n p.1).descFactorial (cellMinSize n p) : ℝ) *
        ((seedBlockSize n p.2).descFactorial (cellMinSize n p) : ℝ) /
        ((cellMinSize n p) ! : ℝ)) * localCellReward (cellMinSize n p)) *
      (((alphaNat n : ℝ) / (2 : ℝ) ^ qExp) ^ (cellMinSize n p - j p)) := by
    intro p hp
    set s : ℕ := seedBlockSize n p.1
    set t : ℕ := seedBlockSize n p.2
    set m : ℕ := cellMinSize n p
    set h : ℕ := m - j p
    have hjp_lo : highThresh n + 1 ≤ j p := (hjM p hp).1
    have hjp_hi : j p ≤ m := (hjM p hp).2
    have hm_ge : alphaNat n - 5 ≤ m := by
      have hs_ge : alphaNat n - 5 ≤ s := by
        dsimp [s, seedBlockSize, witnessSize]
        have := (seedBlockType n p.1).isLt
        omega
      have ht_ge : alphaNat n - 5 ≤ t := by
        dsimp [t, seedBlockSize, witnessSize]
        have := (seedBlockType n p.2).isLt
        omega
      exact le_min hs_ge ht_ge
    have hjp_ge2 : 2 ≤ j p := by
      dsimp [highThresh, highCap, witnessSize] at hjp_lo
      omega
    have hm_ge2 : 2 ≤ m := hjp_ge2.trans hjp_hi
    have hs_desc_le : s.descFactorial (j p) ≤ s.descFactorial m := by
      have hadd : j p + h = m := Nat.add_sub_of_le hjp_hi
      have hm_le_s : m ≤ s := min_le_left s t
      have hpos : 1 ≤ (s - j p).descFactorial h := descFactorial_pos_of_le (by omega)
      calc
        s.descFactorial (j p) ≤ s.descFactorial (j p) * (s - j p).descFactorial h :=
          Nat.le_mul_of_pos_right _ hpos
        _ = s.descFactorial (j p + h) := (descFactorial_add_eq s (j p) h).symm
        _ = s.descFactorial m := by rw [hadd]
    have ht_desc_le : t.descFactorial (j p) ≤ t.descFactorial m := by
      have hadd : j p + h = m := Nat.add_sub_of_le hjp_hi
      have hm_le_t : m ≤ t := min_le_right s t
      have hpos : 1 ≤ (t - j p).descFactorial h := descFactorial_pos_of_le (by omega)
      calc
        t.descFactorial (j p) ≤ t.descFactorial (j p) * (t - j p).descFactorial h :=
          Nat.le_mul_of_pos_right _ hpos
        _ = t.descFactorial (j p + h) := (descFactorial_add_eq t (j p) h).symm
        _ = t.descFactorial m := by rw [hadd]
    have hfac_inv :
        ((j p) ! : ℝ)⁻¹ ≤ ((alphaNat n : ℝ) ^ h) / ((m ! : ℝ)) := by
      have hfac_id : m.descFactorial h * (j p) ! = m ! := by
        have hsub : m - h = j p := by omega
        have hid := descFactorial_mul_factorial_sub (Nat.sub_le m (j p))
        change m.descFactorial h * (m - h) ! = m ! at hid
        rwa [hsub] at hid
      have hm_le_α : m ≤ alphaNat n := by
        calc
          m ≤ highCap n := cellMinSize_le_highCap n p
          _ = alphaNat n - 2 := rfl
          _ ≤ alphaNat n := Nat.sub_le (alphaNat n) 2
      have hdesc_pow : m.descFactorial h ≤ (alphaNat n) ^ h :=
        (descFactorial_le_pow m h).trans (Nat.pow_le_pow_left hm_le_α h)
      have hnat : m ! ≤ (alphaNat n) ^ h * (j p) ! := by
        rw [← hfac_id]
        exact Nat.mul_le_mul_right _ hdesc_pow
      have hjp_pos : (0 : ℝ) < ((j p) ! : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
      have hm_pos : (0 : ℝ) < (m ! : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
      rw [inv_le_iff_one_le_mul₀ hjp_pos, div_mul_eq_mul_div, le_div_iff₀ hm_pos, one_mul]
      exact_mod_cast hnat
    have hrew_le :
        localCellReward (j p) ≤ localCellReward m / ((2 : ℝ) ^ qExp) ^ h := by
      rw [localCellReward_eq_div_two_of_two_le hjp_ge2,
        localCellReward_eq_div_two_of_two_le hm_ge2, ← pow_mul]
      have h2q : 2 * qExp ≤ m + j p - 1 := by
        dsimp [qExp]
        dsimp [highThresh, highCap, witnessSize] at hjp_lo
        omega
      have hch := choose_two_add_sub_mul_le (by omega) hjp_hi h2q
      have hpow : (2 : ℝ) ^ ((j p).choose 2) * (2 : ℝ) ^ (qExp * h) ≤ (2 : ℝ) ^ (m.choose 2) := by
        rw [mul_comm qExp h, ← pow_add]
        exact pow_le_pow_right₀ (by norm_num) hch
      rw [le_div_iff₀ (pow_pos (by norm_num) _)]
      linarith
    calc
      (((s.descFactorial (j p) : ℝ) * (t.descFactorial (j p) : ℝ) / ((j p) ! : ℝ)) *
          localCellReward (j p))
          = ((s.descFactorial (j p) : ℝ) * (t.descFactorial (j p) : ℝ)) *
              ((j p) ! : ℝ)⁻¹ * localCellReward (j p) := by ring
      _ ≤ ((s.descFactorial m : ℝ) * (t.descFactorial m : ℝ)) *
            (((alphaNat n : ℝ) ^ h) / (m ! : ℝ)) *
            (localCellReward m / ((2 : ℝ) ^ qExp) ^ h) := by
          refine mul_le_mul (mul_le_mul ?_ hfac_inv (inv_nonneg.mpr (Nat.cast_nonneg _))
            (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
            hrew_le (localCellReward_pos _).le
            (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
              (div_nonneg (pow_nonneg (Nat.cast_nonneg _) h) (Nat.cast_nonneg _)))
          exact mul_le_mul (by exact_mod_cast hs_desc_le) (by exact_mod_cast ht_desc_le)
            (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      _ = ((((s.descFactorial m : ℝ) * (t.descFactorial m : ℝ) / (m ! : ℝ)) *
            localCellReward m)) *
          (((alphaNat n : ℝ) / (2 : ℝ) ^ qExp) ^ h) := by
          rw [div_pow]
          ring
  have hprod_le :
      (∏ p ∈ M,
        (((seedBlockSize n p.1).descFactorial (j p) : ℝ) *
          ((seedBlockSize n p.2).descFactorial (j p) : ℝ) /
          ((j p) ! : ℝ)) * localCellReward (j p)) ≤
      (∏ p ∈ M,
        ((((seedBlockSize n p.1).descFactorial (cellMinSize n p) : ℝ) *
          ((seedBlockSize n p.2).descFactorial (cellMinSize n p) : ℝ) /
          ((cellMinSize n p) ! : ℝ)) * localCellReward (cellMinSize n p))) *
      (∏ p ∈ M, ((alphaNat n : ℝ) / (2 : ℝ) ^ qExp) ^ (cellMinSize n p - j p)) := by
    exact (prod_le_prod_real M
      (fun p _ => mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)) (localCellReward_pos _).le)
      hcell_bound).trans_eq Finset.prod_mul_distrib
  have hfull_eq :
      fullSkeletonWeight n M =
        (∏ p ∈ M,
          ((((seedBlockSize n p.1).descFactorial (cellMinSize n p) : ℝ) *
            ((seedBlockSize n p.2).descFactorial (cellMinSize n p) : ℝ) /
            ((cellMinSize n p) ! : ℝ)) * localCellReward (cellMinSize n p))) /
        (n.descFactorial M_sum : ℝ) := by
    unfold fullSkeletonWeight highSkeletonWeight
    have hsum_eq : (∑ p ∈ M, fullMultiplicity n M p) = M_sum :=
      Finset.sum_congr rfl fun p hp => by simp [fullMultiplicity, hp]
    have hprod_eq :
        (∏ p ∈ M,
          ((((seedBlockSize n p.1).descFactorial (fullMultiplicity n M p) : ℝ) *
            ((seedBlockSize n p.2).descFactorial (fullMultiplicity n M p) : ℝ) /
            ((fullMultiplicity n M p) ! : ℝ)) * localCellReward (fullMultiplicity n M p))) =
        (∏ p ∈ M,
          ((((seedBlockSize n p.1).descFactorial (cellMinSize n p) : ℝ) *
            ((seedBlockSize n p.2).descFactorial (cellMinSize n p) : ℝ) /
            ((cellMinSize n p) ! : ℝ)) * localCellReward (cellMinSize n p))) :=
      Finset.prod_congr rfl fun p hp => by simp [fullMultiplicity, hp]
    rw [hsum_eq, hprod_eq]
  have hpow_n : (n : ℝ) ^ H = ∏ p ∈ M, (n : ℝ) ^ (cellMinSize n p - j p) :=
    (prod_pow_eq_pow_sum_real M (n : ℝ) (fun p => cellMinSize n p - j p)).symm
  unfold highSkeletonWeight
  rw [div_eq_mul_inv]
  calc
    (∏ p ∈ M,
        (((seedBlockSize n p.1).descFactorial (j p) : ℝ) *
          ((seedBlockSize n p.2).descFactorial (j p) : ℝ) /
          ((j p) ! : ℝ)) * localCellReward (j p)) *
      ((n.descFactorial J : ℝ))⁻¹
        ≤ ((∏ p ∈ M,
            ((((seedBlockSize n p.1).descFactorial (cellMinSize n p) : ℝ) *
              ((seedBlockSize n p.2).descFactorial (cellMinSize n p) : ℝ) /
              ((cellMinSize n p) ! : ℝ)) * localCellReward (cellMinSize n p))) *
          (∏ p ∈ M, ((alphaNat n : ℝ) / (2 : ℝ) ^ qExp) ^ (cellMinSize n p - j p))) *
          (((n : ℝ) ^ H) / (n.descFactorial M_sum : ℝ)) := by
        refine mul_le_mul hprod_le hinv_J_le (inv_nonneg.mpr (Nat.cast_nonneg _)) ?_
        refine mul_nonneg (Finset.prod_nonneg fun p _ => ?_)
          (Finset.prod_nonneg fun p _ =>
            pow_nonneg (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)) _)
        exact mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          (Nat.cast_nonneg _)) (localCellReward_pos _).le
    _ = fullSkeletonWeight n M *
          ((n : ℝ) ^ H *
            ∏ p ∈ M, ((alphaNat n : ℝ) / (2 : ℝ) ^ qExp) ^ (cellMinSize n p - j p)) := by
        rw [hfull_eq]
        ring
    _ = fullSkeletonWeight n M *
          ∏ p ∈ M, (deficitRatio n) ^ (cellMinSize n p - j p) := by
        rw [hpow_n, ← Finset.prod_mul_distrib]
        congr 1
        refine Finset.prod_congr rfl fun p _ => ?_
        rw [← mul_pow]
        congr 1
        unfold deficitRatio
        ring

/-- Summing `highSkeletonWeight n M j` over `j ∈ highMultBox n M` loses at most
`Real.exp ((kCoSeed n : ℝ) * (alphaNat n : ℝ) * deficitRatio n)` whenever `deficitRatio n ≤ 1`. -/
theorem sum_highMultBox_highSkeletonWeight_le {n : ℕ}
    (hK : ∑ i : Fin 4, witnessCounts n i = kCoSeed n)
    (hn : ∑ i : Fin 4, witnessSize n i * witnessCounts n i = n)
    (hα40 : 40 ≤ alphaNat n)
    (hρ1 : deficitRatio n ≤ 1)
    {M : Finset (Fin (kCoSeed n) × Fin (kCoSeed n))}
    (hM : IsBlockMatching (kCoSeed n) M) :
    ∑ j ∈ highMultBox n M, highSkeletonWeight n M j ≤
      Real.exp ((kCoSeed n : ℝ) * (alphaNat n : ℝ) * deficitRatio n) *
        fullSkeletonWeight n M := by
  classical
  set ρ : ℝ := deficitRatio n
  have hρ0 : 0 ≤ ρ := deficitRatio_nonneg n
  let tBox : Fin (kCoSeed n) × Fin (kCoSeed n) → Finset ℕ := fun p =>
    if p ∈ M then Finset.Icc (highThresh n + 1) (cellMinSize n p) else {0}
  let gFactor : Fin (kCoSeed n) × Fin (kCoSeed n) → ℕ → ℝ := fun p x =>
    if p ∈ M then ρ ^ (cellMinSize n p - x) else 1
  have hprod_ext : ∀ j : Fin (kCoSeed n) × Fin (kCoSeed n) → ℕ,
      (∏ p ∈ M, ρ ^ (cellMinSize n p - j p)) =
        ∏ p : Fin (kCoSeed n) × Fin (kCoSeed n), gFactor p (j p) := by
    intro j
    simp only [gFactor, Finset.prod_ite_mem, Finset.univ_inter]
  have hsum_pi :
      ∑ j ∈ highMultBox n M, ∏ p ∈ M, ρ ^ (cellMinSize n p - j p) =
        ∏ p ∈ M, ∑ x ∈ Finset.Icc (highThresh n + 1) (cellMinSize n p),
          ρ ^ (cellMinSize n p - x) := by
    simp_rw [hprod_ext]
    change ∑ j ∈ Fintype.piFinset tBox, ∏ p, gFactor p (j p) = _
    rw [← Finset.prod_univ_sum]
    have hfactor : ∀ p : Fin (kCoSeed n) × Fin (kCoSeed n),
        (∑ x ∈ tBox p, gFactor p x) =
          if p ∈ M then
            ∑ x ∈ Finset.Icc (highThresh n + 1) (cellMinSize n p), ρ ^ (cellMinSize n p - x)
          else 1 := by
      intro p
      by_cases hp : p ∈ M
      · simp [tBox, gFactor, hp]
      · simp [tBox, gFactor, hp]
    simp_rw [hfactor]
    simp [Finset.prod_ite_mem]
  have hinner_le : ∀ p ∈ M,
      ∑ x ∈ Finset.Icc (highThresh n + 1) (cellMinSize n p), ρ ^ (cellMinSize n p - x) ≤
        Real.exp ((alphaNat n : ℝ) * ρ) := by
    intro p _
    set m : ℕ := cellMinSize n p
    have hm_mem : m ∈ Finset.Icc (highThresh n + 1) m := by
      rw [Finset.mem_Icc]
      refine ⟨?_, le_rfl⟩
      have hs_ge : alphaNat n - 5 ≤ seedBlockSize n p.1 := by
        dsimp [seedBlockSize, witnessSize]
        have := (seedBlockType n p.1).isLt
        omega
      have ht_ge : alphaNat n - 5 ≤ seedBlockSize n p.2 := by
        dsimp [seedBlockSize, witnessSize]
        have := (seedBlockType n p.2).isLt
        omega
      have hm_ge : alphaNat n - 5 ≤ m := le_min hs_ge ht_ge
      dsimp [highThresh, highCap, witnessSize]
      omega
    rw [← Finset.add_sum_erase _ _ hm_mem]
    simp only [Nat.sub_self, pow_zero]
    let S := (Finset.Icc (highThresh n + 1) m).erase m
    have hS_sub : S ⊆ Finset.range m := by
      intro x hx
      rcases Finset.mem_erase.mp hx with ⟨hne, hx_icc⟩
      have hx_le : x ≤ m := (Finset.mem_Icc.mp hx_icc).2
      exact Finset.mem_range.mpr (lt_of_le_of_ne hx_le hne)
    have hS_card : S.card ≤ alphaNat n := by
      calc
        S.card ≤ (Finset.range m).card := Finset.card_le_card hS_sub
        _ = m := Finset.card_range m
        _ ≤ highCap n := cellMinSize_le_highCap n p
        _ ≤ alphaNat n := Nat.sub_le (alphaNat n) 2
    have hS_term : ∀ x ∈ S, ρ ^ (m - x) ≤ ρ := by
      intro x hx
      have hx_lt : x < m := Finset.mem_range.mp (hS_sub hx)
      exact pow_le_of_le_one hρ0 hρ1 (by omega : m - x ≠ 0)
    have hsum_S : ∑ x ∈ S, ρ ^ (m - x) ≤ (alphaNat n : ℝ) * ρ := by
      calc
        ∑ x ∈ S, ρ ^ (m - x) ≤ ∑ _x ∈ S, ρ := Finset.sum_le_sum hS_term
        _ = (S.card : ℝ) * ρ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (alphaNat n : ℝ) * ρ := mul_le_mul_of_nonneg_right (by exact_mod_cast hS_card) hρ0
    calc
      1 + ∑ x ∈ S, ρ ^ (m - x) ≤ 1 + (alphaNat n : ℝ) * ρ := by linarith
      _ ≤ Real.exp ((alphaNat n : ℝ) * ρ) := by
        linarith [Real.add_one_le_exp ((alphaNat n : ℝ) * ρ)]
  have hprod_exp :
      ∏ p ∈ M, ∑ x ∈ Finset.Icc (highThresh n + 1) (cellMinSize n p),
        ρ ^ (cellMinSize n p - x) ≤
      Real.exp ((kCoSeed n : ℝ) * (alphaNat n : ℝ) * ρ) := by
    calc
      ∏ p ∈ M, ∑ x ∈ Finset.Icc (highThresh n + 1) (cellMinSize n p),
          ρ ^ (cellMinSize n p - x)
          ≤ ∏ _p ∈ M, Real.exp ((alphaNat n : ℝ) * ρ) :=
        prod_le_prod_real M
          (fun p _ => Finset.sum_nonneg fun _ _ => pow_nonneg hρ0 _) hinner_le
      _ = (Real.exp ((alphaNat n : ℝ) * ρ)) ^ M.card := Finset.prod_const _
      _ ≤ (Real.exp ((alphaNat n : ℝ) * ρ)) ^ (kCoSeed n) :=
        pow_le_pow_right₀ (Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) hρ0))
          (card_le_of_isBlockMatching hM)
      _ = Real.exp ((kCoSeed n : ℝ) * (alphaNat n : ℝ) * ρ) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  calc
    ∑ j ∈ highMultBox n M, highSkeletonWeight n M j
        ≤ ∑ j ∈ highMultBox n M,
            fullSkeletonWeight n M * ∏ p ∈ M, ρ ^ (cellMinSize n p - j p) :=
      Finset.sum_le_sum fun j hj =>
        highSkeletonWeight_le_full_mul_prod_deficit hK hn hα40 hM hj
    _ = fullSkeletonWeight n M *
          ∑ j ∈ highMultBox n M, ∏ p ∈ M, ρ ^ (cellMinSize n p - j p) :=
      (Finset.mul_sum _ _ _).symm
    _ = fullSkeletonWeight n M *
          ∏ p ∈ M, ∑ x ∈ Finset.Icc (highThresh n + 1) (cellMinSize n p),
            ρ ^ (cellMinSize n p - x) := by rw [hsum_pi]
    _ ≤ fullSkeletonWeight n M * Real.exp ((kCoSeed n : ℝ) * (alphaNat n : ℝ) * ρ) :=
      mul_le_mul_of_nonneg_left hprod_exp (fullSkeletonWeight_nonneg n M)
    _ = Real.exp ((kCoSeed n : ℝ) * (alphaNat n : ℝ) * ρ) * fullSkeletonWeight n M :=
      mul_comm _ _

/-! ### 4. Multinomial Identity on `Fin d` and `4 × 4` Endpoint-Table Reduction -/

/-- Discrete simplex `{k : Fin d → ℕ | ∑ j, k j = m}` inside `{0, ..., m}^d`. -/
def simplexFin (d m : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset (fun _ : Fin d => Finset.range (m + 1))).filter
    (fun k => ∑ j : Fin d, k j = m)

theorem mem_simplexFin_iff {d m : ℕ} {k : Fin d → ℕ} :
    k ∈ simplexFin d m ↔ ∑ j : Fin d, k j = m := by
  simp only [simplexFin, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨fun j => ?_, h⟩⟩
  have hle : k j ≤ ∑ i : Fin d, k i :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  omega

/-- Exact `d`-variable multinomial identity proved directly from `add_pow`. -/
theorem multinomial_fin_eq (d : ℕ) :
    ∀ (m : ℕ) (a : Fin d → ℝ),
      ∑ k ∈ simplexFin d m,
        ((m ! : ℝ) / ∏ j : Fin d, ((k j) ! : ℝ)) * ∏ j : Fin d, (a j) ^ (k j) =
      (∑ j : Fin d, a j) ^ m := by
  induction d with
  | zero =>
    intro m a
    rcases m with _ | m
    · have h0 : simplexFin 0 0 = {Fin.elim0} := by
        ext k
        rw [mem_simplexFin_iff, Finset.mem_singleton]
        simp [Subsingleton.elim k Fin.elim0]
      rw [h0]
      simp
    · have hemp : simplexFin 0 (m + 1) = ∅ := by
        ext k
        simp [mem_simplexFin_iff]
      rw [hemp]
      simp [zero_pow (Nat.succ_ne_zero m)]
  | succ d ih =>
    intro m a
    let consNat (k₀ : ℕ) : (Fin d → ℕ) → (Fin (d + 1) → ℕ) := fun f => Fin.cons k₀ f
    have hpart :
        simplexFin (d + 1) m =
          (Finset.range (m + 1)).biUnion
            (fun k₀ => (simplexFin d (m - k₀)).image (consNat k₀)) := by
      ext k
      simp only [mem_simplexFin_iff, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
      constructor
      · intro hsum
        rw [Fin.sum_univ_succ] at hsum
        let k' : Fin d → ℕ := fun j => k j.succ
        have hk'_sum : ∑ j : Fin d, k' j = m - k 0 := by
          change ∑ j : Fin d, k j.succ = m - k 0
          omega
        refine ⟨k 0, by omega, k', hk'_sum, ?_⟩
        exact Fin.cons_self_tail k
      · rintro ⟨k₀, hk₀_lt, k', hk', rfl⟩
        dsimp [consNat]
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, hk']
        omega
    have hdisj : ((Finset.range (m + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
        (fun k₀ => (simplexFin d (m - k₀)).image (consNat k₀)) := by
      intro k₁ _ k₂ _ hne
      refine Finset.disjoint_left.mpr fun k hk₁ hk₂ => hne ?_
      rcases Finset.mem_image.mp hk₁ with ⟨f₁, _, rfl⟩
      rcases Finset.mem_image.mp hk₂ with ⟨f₂, _, heq⟩
      have h0 := congrFun heq 0
      simpa [consNat] using h0.symm
    rw [hpart, Finset.sum_biUnion hdisj]
    have hslice : ∀ k₀ ∈ Finset.range (m + 1),
        ∑ k ∈ (simplexFin d (m - k₀)).image (consNat k₀),
          ((m ! : ℝ) / ∏ j : Fin (d + 1), ((k j) ! : ℝ)) * ∏ j : Fin (d + 1), (a j) ^ (k j) =
        (a 0) ^ k₀ * (∑ j : Fin d, a j.succ) ^ (m - k₀) * (m.choose k₀ : ℝ) := by
      intro k₀ hk₀
      have hk₀_le : k₀ ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk₀)
      have hinj : Set.InjOn (consNat k₀) (simplexFin d (m - k₀)) := by
        intro f₁ _ f₂ _ heq
        funext j
        simpa [consNat] using congrFun heq j.succ
      rw [Finset.sum_image hinj]
      have hterm : ∀ k' ∈ simplexFin d (m - k₀),
          ((m ! : ℝ) / ∏ j : Fin (d + 1), ((consNat k₀ k' j) ! : ℝ)) *
            ∏ j : Fin (d + 1), (a j) ^ (consNat k₀ k' j) =
          ((m.choose k₀ : ℝ) * (a 0) ^ k₀) *
            ((((m - k₀) ! : ℝ) / ∏ j : Fin d, ((k' j) ! : ℝ)) *
              ∏ j : Fin d, (a j.succ) ^ (k' j)) := by
        intro k' _
        dsimp [consNat]
        rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        have hch : (m.choose k₀ : ℝ) * (k₀ ! : ℝ) * ((m - k₀) ! : ℝ) = (m ! : ℝ) := by
          exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk₀_le
        have hk0_ne : (k₀ ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
        have hprod_ne : (∏ j : Fin d, ((k' j) ! : ℝ)) ≠ 0 :=
          (Finset.prod_pos fun j _ => Nat.cast_pos.mpr (Nat.factorial_pos _)).ne'
        rw [← hch]
        field_simp [hk0_ne, hprod_ne]
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ih (m - k₀) (fun j => a j.succ)]
      ring
    rw [Finset.sum_congr rfl hslice, ← add_pow (a 0) (∑ j : Fin d, a j.succ) m,
      Fin.sum_univ_succ]

/-- `4 × 4` endpoint-type multiplicity table `L(i, j)` of a partial block matching `M`. -/
noncomputable def matchingTypeTable (n : ℕ)
    (M : Finset (Fin (kCoSeed n) × Fin (kCoSeed n)))
    (q : Fin 4 × Fin 4) : ℕ :=
  (M.filter (fun p => (seedBlockType n p.1, seedBlockType n p.2) = q)).card

/-- Row-marginal profile `r_i = ∑_{j : Fin 4} L(i, j)` of a `4 × 4` table `L`. -/
def typeTableRow (L : Fin 4 × Fin 4 → ℕ) (i : Fin 4) : ℕ :=
  ∑ j : Fin 4, L (i, j)

/-- Column-marginal profile `c_j = ∑_{i : Fin 4} L(i, j)` of a `4 × 4` table `L`. -/
def typeTableCol (L : Fin 4 × Fin 4 → ℕ) (j : Fin 4) : ℕ :=
  ∑ i : Fin 4, L (i, j)

/-- Finite box of valid `4 × 4` endpoint-type tables whose row and column marginals lie in `diagBox n`. -/
noncomputable def validTypeTables (n : ℕ) : Finset (Fin 4 × Fin 4 → ℕ) :=
  (Fintype.piFinset (fun q : Fin 4 × Fin 4 =>
    Finset.range (witnessCounts n q.1 + 1))).filter
    (fun L => typeTableRow L ∈ diagBox n ∧ typeTableCol L ∈ diagBox n)

theorem mem_validTypeTables_iff {n : ℕ} {L : Fin 4 × Fin 4 → ℕ} :
    L ∈ validTypeTables n ↔
      typeTableRow L ∈ diagBox n ∧ typeTableCol L ∈ diagBox n := by
  simp only [validTypeTables, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨fun q => ?_, h⟩⟩
  have hle1 : L q ≤ typeTableRow L q.1 := by
    rcases q with ⟨i, j⟩
    exact Finset.single_le_sum (f := fun j' => L (i, j')) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
  have hle2 : typeTableRow L q.1 ≤ witnessCounts n q.1 := (mem_diagBox_iff.mp h.1) q.1
  omega

theorem matchingTypeTable_mem_validTypeTables {n : ℕ}
    (hK : ∑ i : Fin 4, witnessCounts n i = kCoSeed n)
    {M : Finset (Fin (kCoSeed n) × Fin (kCoSeed n))}
    (hM : IsBlockMatching (kCoSeed n) M) :
    matchingTypeTable n M ∈ validTypeTables n := by
  rw [mem_validTypeTables_iff, mem_diagBox_iff, mem_diagBox_iff]
  refine ⟨fun i => ?_, fun j => ?_⟩
  · have hrow_eq : typeTableRow (matchingTypeTable n M) i =
        (M.filter (fun p => seedBlockType n p.1 = i)).card := by
      unfold typeTableRow matchingTypeTable
      have hpart : M.filter (fun p => seedBlockType n p.1 = i) =
          Finset.univ.biUnion (fun j : Fin 4 =>
            M.filter (fun p => (seedBlockType n p.1, seedBlockType n p.2) = (i, j))) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and, Prod.mk.injEq]
        exact ⟨fun h => ⟨seedBlockType n p.2, h.1, h.2, rfl⟩,
          fun ⟨_, hpM, hi, _⟩ => ⟨hpM, hi⟩⟩
      have hdisj : ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint
          (fun j : Fin 4 =>
            M.filter (fun p => (seedBlockType n p.1, seedBlockType n p.2) = (i, j))) := by
        intro j₁ _ j₂ _ hne
        refine Finset.disjoint_left.mpr fun p hp₁ hp₂ => hne ?_
        have h1 := (Prod.mk.inj (Finset.mem_filter.mp hp₁).2).2
        have h2 := (Prod.mk.inj (Finset.mem_filter.mp hp₂).2).2
        exact h1.symm.trans h2
      rw [hpart, Finset.card_biUnion hdisj]
    rw [hrow_eq, ← card_seedBlockType_eq hK i]
    have hinj : Set.InjOn Prod.fst
        ((M.filter (fun p => seedBlockType n p.1 = i)) :
          Set (Fin (kCoSeed n) × Fin (kCoSeed n))) :=
      fun p₁ hp₁ p₂ hp₂ heq =>
        hM.1 p₁ (Finset.mem_filter.mp hp₁).1 p₂ (Finset.mem_filter.mp hp₂).1 heq
    rw [← Finset.card_image_of_injOn hinj]
    refine Finset.card_le_card fun r hr => ?_
    rcases Finset.mem_image.mp hr with ⟨p, hp, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
  · have hcol_eq : typeTableCol (matchingTypeTable n M) j =
        (M.filter (fun p => seedBlockType n p.2 = j)).card := by
      unfold typeTableCol matchingTypeTable
      have hpart : M.filter (fun p => seedBlockType n p.2 = j) =
          Finset.univ.biUnion (fun i : Fin 4 =>
            M.filter (fun p => (seedBlockType n p.1, seedBlockType n p.2) = (i, j))) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and, Prod.mk.injEq]
        exact ⟨fun h => ⟨seedBlockType n p.1, h.1, rfl, h.2⟩,
          fun ⟨_, hpM, _, hj⟩ => ⟨hpM, hj⟩⟩
      have hdisj : ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint
          (fun i : Fin 4 =>
            M.filter (fun p => (seedBlockType n p.1, seedBlockType n p.2) = (i, j))) := by
        intro i₁ _ i₂ _ hne
        refine Finset.disjoint_left.mpr fun p hp₁ hp₂ => hne ?_
        have h1 := (Prod.mk.inj (Finset.mem_filter.mp hp₁).2).1
        have h2 := (Prod.mk.inj (Finset.mem_filter.mp hp₂).2).1
        exact h1.symm.trans h2
      rw [hpart, Finset.card_biUnion hdisj]
    rw [hcol_eq, ← card_seedBlockType_eq hK j]
    have hinj : Set.InjOn Prod.snd
        ((M.filter (fun p => seedBlockType n p.2 = j)) :
          Set (Fin (kCoSeed n) × Fin (kCoSeed n))) :=
      fun p₁ hp₁ p₂ hp₂ heq =>
        hM.2 p₁ (Finset.mem_filter.mp hp₁).1 p₂ (Finset.mem_filter.mp hp₂).1 heq
    rw [← Finset.card_image_of_injOn hinj]
    refine Finset.card_le_card fun r hr => ?_
    rcases Finset.mem_image.mp hr with ⟨p, hp, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩

/-- Exact counting bound for block matchings realizing a `4 × 4` endpoint-type table `L`:
`#{M ∈ blockMatchings n | matchingTypeTable n M = L} * ∏ q, (L q)! ≤
  (∏ i, (κ_i)_{r_i}) * (∏ j, (κ_j)_{c_j})`. -/
theorem card_matchings_with_table_mul_le {n : ℕ}
    (hK : ∑ i : Fin 4, witnessCounts n i = kCoSeed n)
    (L : Fin 4 × Fin 4 → ℕ) :
    ((blockMatchings n).filter (fun M => matchingTypeTable n M = L)).card *
      (∏ q : Fin 4 × Fin 4, (L q) !) ≤
    (∏ i : Fin 4, (witnessCounts n i).descFactorial (typeTableRow L i)) *
      (∏ j : Fin 4, (witnessCounts n j).descFactorial (typeTableCol L j)) := by
  classical
  let MatSet := (blockMatchings n).filter (fun M => matchingTypeTable n M = L)
  let SliceM (M : Finset (Fin (kCoSeed n) × Fin (kCoSeed n))) (q : Fin 4 × Fin 4) :=
    M.filter (fun p => (seedBlockType n p.1, seedBlockType n p.2) = q)
  let RowBlock (i : Fin 4) :=
    {r : Fin (kCoSeed n) // r ∈ Finset.univ.filter (fun r => seedBlockType n r = i)}
  let IdxRow (i : Fin 4) := Σ j : Fin 4, Fin (L (i, j))
  let IdxCol (j : Fin 4) := Σ i : Fin 4, Fin (L (i, j))
  let LHS := Σ M : {M // M ∈ MatSet},
    ∀ q : Fin 4 × Fin 4, Fin (L q) ≃ {p // p ∈ SliceM M.1 q}
  let RHS := (∀ i : Fin 4, IdxRow i ↪ RowBlock i) × (∀ j : Fin 4, IdxCol j ↪ RowBlock j)
  let embMap : LHS → RHS := fun ⟨⟨M, hM_mem⟩, e⟩ =>
    have hM : IsBlockMatching (kCoSeed n) M :=
      mem_blockMatchings_iff.mp (Finset.mem_filter.mp hM_mem).1
    (fun i =>
      { toFun := fun ⟨j, t⟩ =>
          ⟨(e (i, j) t).1.1, by
            have hp := (Finset.mem_filter.mp (e (i, j) t).2).2
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Prod.mk.inj hp).1⟩⟩
        inj' := by
          rintro ⟨j₁, t₁⟩ ⟨j₂, t₂⟩ heq
          have hfst : (e (i, j₁) t₁).1.1 = (e (i, j₂) t₂).1.1 := congrArg Subtype.val heq
          have hp₁_mem := Finset.mem_filter.mp (e (i, j₁) t₁).2
          have hp₂_mem := Finset.mem_filter.mp (e (i, j₂) t₂).2
          have hp_eq : (e (i, j₁) t₁).1 = (e (i, j₂) t₂).1 :=
            hM.1 _ hp₁_mem.1 _ hp₂_mem.1 hfst
          have hj_eq : j₁ = j₂ := by
            have h1 := (Prod.mk.inj hp₁_mem.2).2
            have h2 := (Prod.mk.inj hp₂_mem.2).2
            rw [← h1, ← h2, hp_eq]
          subst hj_eq
          have ht_eq : t₁ = t₂ := (e (i, j₁)).injective (Subtype.ext hp_eq)
          subst ht_eq
          rfl },
     fun j =>
      { toFun := fun ⟨i, t⟩ =>
          ⟨(e (i, j) t).1.2, by
            have hp := (Finset.mem_filter.mp (e (i, j) t).2).2
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Prod.mk.inj hp).2⟩⟩
        inj' := by
          rintro ⟨i₁, t₁⟩ ⟨i₂, t₂⟩ heq
          have hsnd : (e (i₁, j) t₁).1.2 = (e (i₂, j) t₂).1.2 := congrArg Subtype.val heq
          have hp₁_mem := Finset.mem_filter.mp (e (i₁, j) t₁).2
          have hp₂_mem := Finset.mem_filter.mp (e (i₂, j) t₂).2
          have hp_eq : (e (i₁, j) t₁).1 = (e (i₂, j) t₂).1 :=
            hM.2 _ hp₁_mem.1 _ hp₂_mem.1 hsnd
          have hi_eq : i₁ = i₂ := by
            have h1 := (Prod.mk.inj hp₁_mem.2).1
            have h2 := (Prod.mk.inj hp₂_mem.2).1
            rw [← h1, ← h2, hp_eq]
          subst hi_eq
          have ht_eq : t₁ = t₂ := (e (i₁, j)).injective (Subtype.ext hp_eq)
          subst ht_eq
          rfl })
  have hemb_inj : Function.Injective embMap := by
    rintro ⟨⟨M₁, hM₁⟩, e₁⟩ ⟨⟨M₂, hM₂⟩, e₂⟩ hemb
    have hrow := (Prod.mk.inj hemb).1
    have hcol := (Prod.mk.inj hemb).2
    have he_val : ∀ (q : Fin 4 × Fin 4) (t : Fin (L q)),
        (e₁ q t).1 = (e₂ q t).1 := by
      rintro ⟨i, j⟩ t
      have h1 : (e₁ (i, j) t).1.1 = (e₂ (i, j) t).1.1 :=
        congrArg Subtype.val (DFunLike.congr_fun (congrFun hrow i) ⟨j, t⟩)
      have h2 : (e₁ (i, j) t).1.2 = (e₂ (i, j) t).1.2 :=
        congrArg Subtype.val (DFunLike.congr_fun (congrFun hcol j) ⟨i, t⟩)
      exact Prod.ext h1 h2
    have hM_eq : M₁ = M₂ := by
      ext p
      constructor
      · intro hp
        let q : Fin 4 × Fin 4 := (seedBlockType n p.1, seedBlockType n p.2)
        have hp_slice : p ∈ SliceM M₁ q := Finset.mem_filter.mpr ⟨hp, rfl⟩
        let t : Fin (L q) := (e₁ q).symm ⟨p, hp_slice⟩
        have ht1 : (e₁ q t).1 = p :=
          congrArg Subtype.val ((e₁ q).apply_symm_apply ⟨p, hp_slice⟩)
        have ht2 : p = (e₂ q t).1 := ht1.symm.trans (he_val q t)
        rw [ht2]
        exact (Finset.mem_filter.mp (e₂ q t).2).1
      · intro hp
        let q : Fin 4 × Fin 4 := (seedBlockType n p.1, seedBlockType n p.2)
        have hp_slice : p ∈ SliceM M₂ q := Finset.mem_filter.mpr ⟨hp, rfl⟩
        let t : Fin (L q) := (e₂ q).symm ⟨p, hp_slice⟩
        have ht2 : (e₂ q t).1 = p :=
          congrArg Subtype.val ((e₂ q).apply_symm_apply ⟨p, hp_slice⟩)
        have ht1 : p = (e₁ q t).1 := ht2.symm.trans (he_val q t).symm
        rw [ht1]
        exact (Finset.mem_filter.mp (e₁ q t).2).1
    subst hM_eq
    have he_eq : e₁ = e₂ := by
      funext q
      apply Equiv.ext
      intro t
      exact Subtype.ext (he_val q t)
    subst he_eq
    rfl
  have hcard_le := Fintype.card_le_of_injective embMap hemb_inj
  have hLHS : Fintype.card LHS = MatSet.card * ∏ q : Fin 4 × Fin 4, (L q) ! := by
    dsimp [LHS]
    rw [Fintype.card_sigma]
    have hfiber : ∀ M : {M // M ∈ MatSet},
        Fintype.card (∀ q : Fin 4 × Fin 4, Fin (L q) ≃ {p // p ∈ SliceM M.1 q}) =
          ∏ q : Fin 4 × Fin 4, (L q) ! := by
      intro M
      rw [Fintype.card_pi]
      refine Finset.prod_congr rfl fun q _ => ?_
      have hLM : matchingTypeTable n M.1 = L := (Finset.mem_filter.mp M.2).2
      have hcard_slice : (SliceM M.1 q).card = L q := by
        rw [← hLM]
        rfl
      let eqvSlice : {p // p ∈ SliceM M.1 q} ≃ Fin (L q) :=
        (SliceM M.1 q).equivFinOfCardEq hcard_slice
      rw [Fintype.card_congr (Equiv.equivCongr (Equiv.refl _) eqvSlice),
        Fintype.card_perm, Fintype.card_fin]
    simp_rw [hfiber]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
  have hRHS : Fintype.card RHS =
      (∏ i : Fin 4, (witnessCounts n i).descFactorial (typeTableRow L i)) *
        (∏ j : Fin 4, (witnessCounts n j).descFactorial (typeTableCol L j)) := by
    have hRHS_row :
        ∏ i : Fin 4, Fintype.card (IdxRow i ↪ RowBlock i) =
          ∏ i : Fin 4, (witnessCounts n i).descFactorial (typeTableRow L i) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Fintype.card_embedding_eq]
      have hrb : Fintype.card (RowBlock i) = witnessCounts n i := by
        dsimp [RowBlock]
        rw [Fintype.card_coe, card_seedBlockType_eq hK i]
      have hir : Fintype.card (IdxRow i) = typeTableRow L i := by
        dsimp [IdxRow, typeTableRow]
        simp
      rw [hrb, hir]
    have hRHS_col :
        ∏ j : Fin 4, Fintype.card (IdxCol j ↪ RowBlock j) =
          ∏ j : Fin 4, (witnessCounts n j).descFactorial (typeTableCol L j) := by
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Fintype.card_embedding_eq]
      have hrb : Fintype.card (RowBlock j) = witnessCounts n j := by
        dsimp [RowBlock]
        rw [Fintype.card_coe, card_seedBlockType_eq hK j]
      have hic : Fintype.card (IdxCol j) = typeTableCol L j := by
        dsimp [IdxCol, typeTableCol]
        simp
      rw [hrb, hic]
    dsimp [RHS]
    rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_pi, hRHS_row, hRHS_col]
  rwa [hLHS, hRHS] at hcard_le

/-! ### 5. Endpoint-Table Weights, Squared Comparison (Lemma 8.6), and Master Section 8 Bound -/

/-- Per-cell full-saturation factor `(max u_i u_j)_{min u_i u_j} * localCellReward (min u_i u_j)`. -/
noncomputable def cellFullFactor (n : ℕ) (q : Fin 4 × Fin 4) : ℝ :=
  (((max (witnessSize n q.1) (witnessSize n q.2)).descFactorial
      (min (witnessSize n q.1) (witnessSize n q.2)) : ℝ)) *
    localCellReward (min (witnessSize n q.1) (witnessSize n q.2))

/-- Total minimum-size vertex support `M(L) = ∑_{q : Fin 4 × Fin 4} L q * min(u_{q.1}, u_{q.2})`. -/
noncomputable def tableMinMass (n : ℕ) (L : Fin 4 × Fin 4 → ℕ) : ℕ :=
  ∑ q : Fin 4 × Fin 4, L q * min (witnessSize n q.1) (witnessSize n q.2)

/-- Table-grouped full-saturation weight `W_n(L)`. -/
noncomputable def tableWeight (n : ℕ) (L : Fin 4 × Fin 4 → ℕ) : ℝ :=
  (((∏ i : Fin 4, ((witnessCounts n i).descFactorial (typeTableRow L i) : ℝ)) *
      (∏ j : Fin 4, ((witnessCounts n j).descFactorial (typeTableCol L j) : ℝ))) /
    (∏ q : Fin 4 × Fin 4, ((L q) ! : ℝ))) *
  ((∏ q : Fin 4 × Fin 4, (cellFullFactor n q) ^ (L q)) /
    (n.descFactorial (tableMinMass n L) : ℝ))

theorem tableWeight_nonneg (n : ℕ) (L : Fin 4 × Fin 4 → ℕ) :
    0 ≤ tableWeight n L := by
  unfold tableWeight cellFullFactor
  refine mul_nonneg (div_nonneg (mul_nonneg ?_ ?_) ?_) (div_nonneg ?_ (Nat.cast_nonneg _))
  · exact Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
  · exact Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
  · exact Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
  · exact Finset.prod_nonneg fun _ _ =>
      pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (localCellReward_pos _).le) _

/-- `fullSkeletonWeight n M` depends on `M` only through `L = matchingTypeTable n M`. -/
theorem fullSkeletonWeight_eq_of_table {n : ℕ}
    {M : Finset (Fin (kCoSeed n) × Fin (kCoSeed n))}
    {L : Fin 4 × Fin 4 → ℕ}
    (hL : matchingTypeTable n M = L) :
    fullSkeletonWeight n M =
      (∏ q : Fin 4 × Fin 4, (cellFullFactor n q) ^ (L q)) /
        (n.descFactorial (tableMinMass n L) : ℝ) := by
  classical
  have hpart : M = Finset.univ.biUnion
      (fun q : Fin 4 × Fin 4 =>
        M.filter (fun p => (seedBlockType n p.1, seedBlockType n p.2) = q)) := by
    ext p
    simp
  have hdisj : ((Finset.univ : Finset (Fin 4 × Fin 4)) : Set (Fin 4 × Fin 4)).PairwiseDisjoint
      (fun q : Fin 4 × Fin 4 =>
        M.filter (fun p => (seedBlockType n p.1, seedBlockType n p.2) = q)) := by
    intro q₁ _ q₂ _ hne
    refine Finset.disjoint_left.mpr fun p hp₁ hp₂ => hne ?_
    exact (Finset.mem_filter.mp hp₁).2.symm.trans (Finset.mem_filter.mp hp₂).2
  have hsum_eq : (∑ p ∈ M, fullMultiplicity n M p) = tableMinMass n L := by
    have h1 : (∑ p ∈ M, fullMultiplicity n M p) = ∑ p ∈ M, cellMinSize n p :=
      Finset.sum_congr rfl fun p hp => by simp [fullMultiplicity, hp]
    rw [h1]
    conv_lhs => rw [hpart]
    rw [Finset.sum_biUnion hdisj]
    unfold tableMinMass
    refine Finset.sum_congr rfl fun q _ => ?_
    have hconst : ∀ p ∈ M.filter (fun p => (seedBlockType n p.1, seedBlockType n p.2) = q),
        cellMinSize n p = min (witnessSize n q.1) (witnessSize n q.2) := by
      intro p hp
      have hq := (Finset.mem_filter.mp hp).2
      dsimp [cellMinSize, seedBlockSize]
      rw [← (Prod.mk.inj hq).1, ← (Prod.mk.inj hq).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, ← hL]
    rfl
  have hcell_simp : ∀ a b : ℕ,
      ((a.descFactorial (min a b) : ℝ) * (b.descFactorial (min a b) : ℝ) /
        (((min a b) ! : ℝ))) =
      ((max a b).descFactorial (min a b) : ℝ) := by
    intro a b
    rcases le_total a b with hab | hba
    · rw [min_eq_left hab, max_eq_right hab, Nat.descFactorial_self]
      have hne : (a ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)
      field_simp [hne]
    · rw [min_eq_right hba, max_eq_left hba, Nat.descFactorial_self]
      have hne : (b ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero b)
      field_simp [hne]
  have hprod_eq :
      (∏ p ∈ M,
        ((((seedBlockSize n p.1).descFactorial (fullMultiplicity n M p) : ℝ) *
          ((seedBlockSize n p.2).descFactorial (fullMultiplicity n M p) : ℝ) /
          ((fullMultiplicity n M p) ! : ℝ)) * localCellReward (fullMultiplicity n M p))) =
      ∏ q : Fin 4 × Fin 4, (cellFullFactor n q) ^ (L q) := by
    have h1 :
        (∏ p ∈ M,
          ((((seedBlockSize n p.1).descFactorial (fullMultiplicity n M p) : ℝ) *
            ((seedBlockSize n p.2).descFactorial (fullMultiplicity n M p) : ℝ) /
            ((fullMultiplicity n M p) ! : ℝ)) * localCellReward (fullMultiplicity n M p))) =
        ∏ p ∈ M,
          ((((seedBlockSize n p.1).descFactorial (cellMinSize n p) : ℝ) *
            ((seedBlockSize n p.2).descFactorial (cellMinSize n p) : ℝ) /
            ((cellMinSize n p) ! : ℝ)) * localCellReward (cellMinSize n p)) :=
      Finset.prod_congr rfl fun p hp => by simp [fullMultiplicity, hp]
    rw [h1]
    conv_lhs => rw [hpart]
    rw [Finset.prod_biUnion hdisj]
    refine Finset.prod_congr rfl fun q _ => ?_
    have hconst : ∀ p ∈ M.filter (fun p => (seedBlockType n p.1, seedBlockType n p.2) = q),
        ((((seedBlockSize n p.1).descFactorial (cellMinSize n p) : ℝ) *
          ((seedBlockSize n p.2).descFactorial (cellMinSize n p) : ℝ) /
          ((cellMinSize n p) ! : ℝ)) * localCellReward (cellMinSize n p)) =
        cellFullFactor n q := by
      intro p hp
      have hq := (Finset.mem_filter.mp hp).2
      dsimp [cellMinSize, seedBlockSize, cellFullFactor]
      rw [(Prod.mk.inj hq).1, (Prod.mk.inj hq).2, hcell_simp]
    rw [Finset.prod_congr rfl hconst, Finset.prod_const, ← hL]
    rfl
  unfold fullSkeletonWeight highSkeletonWeight
  rw [hsum_eq, hprod_eq]

/-- Summing `fullSkeletonWeight n M` over `M ∈ blockMatchings n` is bounded by summing
`tableWeight n L` over `L ∈ validTypeTables n`. -/
theorem sum_blockMatchings_fullSkeletonWeight_le {n : ℕ}
    (hK : ∑ i : Fin 4, witnessCounts n i = kCoSeed n) :
    ∑ M ∈ blockMatchings n, fullSkeletonWeight n M ≤
      ∑ L ∈ validTypeTables n, tableWeight n L := by
  classical
  have hpart : blockMatchings n =
      (validTypeTables n).biUnion
        (fun L => (blockMatchings n).filter (fun M => matchingTypeTable n M = L)) := by
    ext M
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    exact ⟨fun hM => ⟨matchingTypeTable n M,
        matchingTypeTable_mem_validTypeTables hK (mem_blockMatchings_iff.mp hM), hM, rfl⟩,
      fun ⟨_, _, hM, _⟩ => hM⟩
  have hdisj : ((validTypeTables n : Finset (Fin 4 × Fin 4 → ℕ)) :
      Set (Fin 4 × Fin 4 → ℕ)).PairwiseDisjoint
      (fun L => (blockMatchings n).filter (fun M => matchingTypeTable n M = L)) := by
    intro L₁ _ L₂ _ hne
    refine Finset.disjoint_left.mpr fun M h₁ h₂ => hne ?_
    exact (Finset.mem_filter.mp h₁).2.symm.trans (Finset.mem_filter.mp h₂).2
  conv_lhs => rw [hpart]
  rw [Finset.sum_biUnion hdisj]
  refine Finset.sum_le_sum fun L _ => ?_
  have hconst : ∀ M ∈ (blockMatchings n).filter (fun M => matchingTypeTable n M = L),
      fullSkeletonWeight n M =
        (∏ q : Fin 4 × Fin 4, (cellFullFactor n q) ^ (L q)) /
          (n.descFactorial (tableMinMass n L) : ℝ) :=
    fun M hM => fullSkeletonWeight_eq_of_table (Finset.mem_filter.mp hM).2
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  unfold tableWeight
  refine mul_le_mul_of_nonneg_right ?_ (div_nonneg
    (Finset.prod_nonneg fun _ _ => pow_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (localCellReward_pos _).le) _)
    (Nat.cast_nonneg _))
  have hprod_pos : (0 : ℝ) < ∏ q : Fin 4 × Fin 4, ((L q) ! : ℝ) :=
    Finset.prod_pos fun _ _ => Nat.cast_pos.mpr (Nat.factorial_pos _)
  rw [le_div_iff₀ hprod_pos]
  exact_mod_cast card_matchings_with_table_mul_le hK L

/-- Size gap `|u_i - u_j| = max(u_i, u_j) - min(u_i, u_j)` of cell `q = (i, j)`. -/
noncomputable def uDiff (n : ℕ) (q : Fin 4 × Fin 4) : ℕ :=
  max (witnessSize n q.1) (witnessSize n q.2) - min (witnessSize n q.1) (witnessSize n q.2)

/-- Product of diagonal class weights `(u_i! g(u_i)) * (u_j! g(u_j))` at `q = (i, j)`. -/
noncomputable def cellDiagProd (n : ℕ) (q : Fin 4 × Fin 4) : ℝ :=
  (((witnessSize n q.1) ! : ℝ) * localCellReward (witnessSize n q.1)) *
    (((witnessSize n q.2) ! : ℝ) * localCellReward (witnessSize n q.2))

theorem cellDiagProd_pos (n : ℕ) (q : Fin 4 × Fin 4) : 0 < cellDiagProd n q := by
  unfold cellDiagProd
  exact mul_pos
    (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (localCellReward_pos _))
    (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (localCellReward_pos _))

/-- Squared off-diagonal penalty ratio `Q_{ij}^2` (`(8.17)` of `arXiv:2608.30604`). -/
noncomputable def cellRatioSq (n : ℕ) (q : Fin 4 × Fin 4) : ℝ :=
  ((n : ℝ) ^ (uDiff n q) * (cellFullFactor n q) ^ 2) / cellDiagProd n q

/-- Off-diagonal penalty factor `Q_{ij} = √(cellRatioSq n q)`. -/
noncomputable def cellRatio (n : ℕ) (q : Fin 4 × Fin 4) : ℝ :=
  Real.sqrt (cellRatioSq n q)

theorem cellRatio_nonneg (n : ℕ) (q : Fin 4 × Fin 4) : 0 ≤ cellRatio n q :=
  Real.sqrt_nonneg _

theorem cellRatio_sq_eq (n : ℕ) (q : Fin 4 × Fin 4) :
    (cellRatio n q) ^ 2 = cellRatioSq n q := by
  unfold cellRatio cellRatioSq
  exact Real.sq_sqrt (div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _))
    (cellDiagProd_pos n q).le)

theorem cellRatio_diag_eq_one (n : ℕ) (i : Fin 4) :
    cellRatio n (i, i) = 1 := by
  unfold cellRatio cellRatioSq cellFullFactor cellDiagProd uDiff
  simp only [max_self, min_self, Nat.sub_self, pow_zero, one_mul, Nat.descFactorial_self]
  have hpos : 0 < ((witnessSize n i) ! : ℝ) * localCellReward (witnessSize n i) :=
    mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (localCellReward_pos _)
  rw [← sq, div_self (sq_pos_of_pos hpos).ne', Real.sqrt_one]

/-- Off-diagonal bound on `cellRatioSq n q` for `q.1 ≠ q.2`. -/
theorem cellRatioSq_le_of_ne {n : ℕ}
    (hsize : ∀ i : Fin 4, 10 ≤ witnessSize n i)
    {q : Fin 4 × Fin 4} (hne : q.1 ≠ q.2) :
    cellRatioSq n q ≤
      (((n : ℝ) * (alphaNat n : ℝ)) / (2 : ℝ) ^ (alphaNat n - 5)) ^ (uDiff n q) := by
  set u1 : ℕ := witnessSize n q.1
  set u2 : ℕ := witnessSize n q.2
  set uMax : ℕ := max u1 u2
  set uMin : ℕ := min u1 u2
  set d : ℕ := uMax - uMin
  have huMin_ge10 : 10 ≤ uMin := le_min (hsize q.1) (hsize q.2)
  have huMax_ge10 : 10 ≤ uMax := (le_max_left u1 u2).trans' (hsize q.1)
  have huMin_ge_α5 : alphaNat n - 5 ≤ uMin := by
    have h1 : alphaNat n - 5 ≤ u1 := by
      dsimp [u1, witnessSize]; have := q.1.isLt; omega
    have h2 : alphaNat n - 5 ≤ u2 := by
      dsimp [u2, witnessSize]; have := q.2.isLt; omega
    exact le_min h1 h2
  have hd_pos : 1 ≤ d := by
    have hs0 := hsize 0
    unfold witnessSize at hs0
    have hval_ne : q.1.val ≠ q.2.val := Fin.val_ne_of_ne hne
    dsimp [d, uMax, uMin, u1, u2, witnessSize]
    have := q.1.isLt
    have := q.2.isLt
    omega
  have huMax_le_α : uMax ≤ alphaNat n := by
    have h1 : u1 ≤ alphaNat n := Nat.sub_le _ _
    have h2 : u2 ≤ alphaNat n := Nat.sub_le _ _
    exact max_le h1 h2
  have hprod_diag_eq :
      cellDiagProd n q =
        (((uMax ! : ℝ) * localCellReward uMax) * ((uMin ! : ℝ) * localCellReward uMin)) := by
    unfold cellDiagProd
    change (((u1 ! : ℝ) * localCellReward u1) * ((u2 ! : ℝ) * localCellReward u2)) = _
    rcases le_total u1 u2 with hle | hle
    · simp only [uMax, uMin, max_eq_right hle, min_eq_left hle]
      ring
    · simp only [uMax, uMin, max_eq_left hle, min_eq_right hle]
  have hdesc_le_fac : uMax.descFactorial uMin ≤ uMax ! := by
    have hid := descFactorial_mul_factorial_sub (min_le_max : uMin ≤ uMax)
    rw [← hid]
    exact Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)
  have hfac_ratio :
      ((uMax.descFactorial uMin : ℝ) ^ 2) / ((uMax ! : ℝ) * (uMin ! : ℝ)) ≤
        (alphaNat n : ℝ) ^ d := by
    have h1 : (uMax.descFactorial uMin : ℝ) ^ 2 ≤ (uMax ! : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hdesc_le_fac) 2
    have h2 : uMax ! = uMax.descFactorial d * uMin ! := by
      have hsub : uMax - d = uMin := by omega
      have hid := (descFactorial_mul_factorial_sub (Nat.sub_le uMax uMin)).symm
      change uMax ! = uMax.descFactorial d * (uMax - d) ! at hid
      rwa [hsub] at hid
    have h3 : uMax.descFactorial d ≤ (alphaNat n) ^ d :=
      (descFactorial_le_pow uMax d).trans (Nat.pow_le_pow_left huMax_le_α d)
    have hden_pos : 0 < (uMax ! : ℝ) * (uMin ! : ℝ) :=
      mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (Nat.cast_pos.mpr (Nat.factorial_pos _))
    rw [div_le_iff₀ hden_pos]
    have hnat : (uMax !) ^ 2 ≤ ((alphaNat n) ^ d) * (uMax ! * uMin !) := by
      calc
        (uMax !) ^ 2 = uMax ! * (uMax.descFactorial d * uMin !) := by rw [sq, ← h2]
        _ = uMax.descFactorial d * (uMax ! * uMin !) := by ring
        _ ≤ ((alphaNat n) ^ d) * (uMax ! * uMin !) := Nat.mul_le_mul_right _ h3
    exact h1.trans (by exact_mod_cast hnat)
  have hrew_ratio :
      (localCellReward uMin) ^ 2 / (localCellReward uMax * localCellReward uMin) ≤
        ((2 : ℝ) ^ (alphaNat n - 5))⁻¹ ^ d := by
    have hmin_pos : 0 < localCellReward uMin := localCellReward_pos uMin
    have hmax_pos : 0 < localCellReward uMax := localCellReward_pos uMax
    have hsimp : (localCellReward uMin) ^ 2 / (localCellReward uMax * localCellReward uMin) =
        localCellReward uMin / localCellReward uMax := by
      field_simp [hmin_pos.ne', hmax_pos.ne']
    rw [hsimp, localCellReward_eq_div_two_of_two_le (by omega),
      localCellReward_eq_div_two_of_two_le (by omega), inv_pow, ← pow_mul]
    have hdiv2 :
        ((2 : ℝ) ^ (uMin.choose 2) / 2) / ((2 : ℝ) ^ (uMax.choose 2) / 2) =
          (2 : ℝ) ^ (uMin.choose 2) / (2 : ℝ) ^ (uMax.choose 2) := by ring
    rw [hdiv2]
    have h2q : 2 * (alphaNat n - 5) ≤ uMax + uMin - 1 := by omega
    have hch := choose_two_add_sub_mul_le (by omega) (min_le_max : uMin ≤ uMax) h2q
    have hpow :
        (2 : ℝ) ^ (uMin.choose 2) * (2 : ℝ) ^ ((alphaNat n - 5) * d) ≤
          (2 : ℝ) ^ (uMax.choose 2) := by
      rw [mul_comm (alphaNat n - 5) d, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) hch
    rw [div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _),
      mul_comm ((2 : ℝ) ^ ((alphaNat n - 5) * d))⁻¹, ← div_eq_mul_inv,
      le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)]
    exact hpow
  unfold cellRatioSq cellFullFactor uDiff
  rw [hprod_diag_eq]
  change ((n : ℝ) ^ d * (((uMax.descFactorial uMin : ℝ) * localCellReward uMin) ^ 2)) /
      (((uMax ! : ℝ) * localCellReward uMax) * ((uMin ! : ℝ) * localCellReward uMin)) ≤ _
  have hsplit :
      ((n : ℝ) ^ d * (((uMax.descFactorial uMin : ℝ) * localCellReward uMin) ^ 2)) /
        (((uMax ! : ℝ) * localCellReward uMax) * ((uMin ! : ℝ) * localCellReward uMin)) =
      (n : ℝ) ^ d *
        (((uMax.descFactorial uMin : ℝ) ^ 2) / ((uMax ! : ℝ) * (uMin ! : ℝ))) *
        ((localCellReward uMin) ^ 2 / (localCellReward uMax * localCellReward uMin)) := by ring
  rw [hsplit]
  calc
    (n : ℝ) ^ d *
        (((uMax.descFactorial uMin : ℝ) ^ 2) / ((uMax ! : ℝ) * (uMin ! : ℝ))) *
        ((localCellReward uMin) ^ 2 / (localCellReward uMax * localCellReward uMin))
        ≤ (n : ℝ) ^ d * (alphaNat n : ℝ) ^ d * (((2 : ℝ) ^ (alphaNat n - 5))⁻¹ ^ d) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hfac_ratio (pow_nonneg (Nat.cast_nonneg n) d))
        hrew_ratio
        (div_nonneg (sq_nonneg _)
          (mul_nonneg (localCellReward_pos uMax).le (localCellReward_pos uMin).le))
        (mul_nonneg (pow_nonneg (Nat.cast_nonneg n) d)
          (pow_nonneg (Nat.cast_nonneg (alphaNat n)) d))
    _ = (((n : ℝ) * (alphaNat n : ℝ)) / (2 : ℝ) ^ (alphaNat n - 5)) ^ d := by
      rw [← mul_pow, ← mul_pow, div_eq_mul_inv]

/-- Row multinomial factor `∏_{i=0}^3 (r_i! / ∏_{j=0}^3 L(i, j)!)`. -/
noncomputable def rowMultinomial (L : Fin 4 × Fin 4 → ℕ) : ℝ :=
  ∏ i : Fin 4, (((typeTableRow L i) ! : ℝ) / ∏ j : Fin 4, ((L (i, j)) ! : ℝ))

/-- Column multinomial factor `∏_{j=0}^3 (c_j! / ∏_{i=0}^3 L(i, j)!)`. -/
noncomputable def colMultinomial (L : Fin 4 × Fin 4 → ℕ) : ℝ :=
  ∏ j : Fin 4, (((typeTableCol L j) ! : ℝ) / ∏ i : Fin 4, ((L (i, j)) ! : ℝ))

theorem rowMultinomial_nonneg (L : Fin 4 × Fin 4 → ℕ) : 0 ≤ rowMultinomial L :=
  Finset.prod_nonneg fun _ _ => div_nonneg (Nat.cast_nonneg _)
    (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)

theorem colMultinomial_nonneg (L : Fin 4 × Fin 4 → ℕ) : 0 ≤ colMultinomial L :=
  Finset.prod_nonneg fun _ _ => div_nonneg (Nat.cast_nonneg _)
    (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)

private lemma add_sub_min_eq_max_sub_min (a b : ℕ) :
    (a - min a b) + (b - min a b) = max a b - min a b := by
  omega

/-- **Lemma 8.6 (`arXiv:2608.30604`) — Squared Endpoint-Table Weight Comparison**:
For any valid table `L ∈ validTypeTables n` with `r = typeTableRow L` and `c = typeTableCol L`,
`(tableWeight n L) ^ 2 ≤ (diagWeight n r * rowMultinomial L * ∏ q, (cellRatio n q)^(L q)) *
  (diagWeight n c * colMultinomial L * ∏ q, (cellRatio n q)^(L q))`. -/
theorem tableWeight_sq_le {n : ℕ}
    (hn : ∑ i : Fin 4, witnessSize n i * witnessCounts n i = n)
    {L : Fin 4 × Fin 4 → ℕ}
    (hL : L ∈ validTypeTables n) :
    (tableWeight n L) ^ 2 ≤
      (diagWeight n (typeTableRow L) * rowMultinomial L *
          ∏ q : Fin 4 × Fin 4, (cellRatio n q) ^ (L q)) *
        (diagWeight n (typeTableCol L) * colMultinomial L *
          ∏ q : Fin 4 × Fin 4, (cellRatio n q) ^ (L q)) := by
  rcases mem_validTypeTables_iff.mp hL with ⟨hr_box, hc_box⟩
  set r := typeTableRow L
  set c := typeTableCol L
  have hr_mass_eq : diagMass n r = ∑ q : Fin 4 × Fin 4, L q * witnessSize n q.1 := by
    unfold diagMass
    dsimp [r, typeTableRow]
    simp_rw [Finset.mul_sum, mul_comm (witnessSize n _)]
    exact (Fintype.sum_prod_type (fun q : Fin 4 × Fin 4 => L q * witnessSize n q.1)).symm
  have hc_mass_eq : diagMass n c = ∑ q : Fin 4 × Fin 4, L q * witnessSize n q.2 := by
    unfold diagMass
    dsimp [c, typeTableCol]
    simp_rw [Finset.mul_sum, mul_comm (witnessSize n _)]
    rw [Finset.sum_comm]
    exact (Fintype.sum_prod_type (fun q : Fin 4 × Fin 4 => L q * witnessSize n q.2)).symm
  have hM_le_mr : tableMinMass n L ≤ diagMass n r := by
    rw [hr_mass_eq]
    exact Finset.sum_le_sum fun q _ => Nat.mul_le_mul_left _ (min_le_left _ _)
  have hM_le_mc : tableMinMass n L ≤ diagMass n c := by
    rw [hc_mass_eq]
    exact Finset.sum_le_sum fun q _ => Nat.mul_le_mul_left _ (min_le_right _ _)
  have hmr_le_n : diagMass n r ≤ n := diagMass_le_of_mem_diagBox hn hr_box
  have hmc_le_n : diagMass n c ≤ n := diagMass_le_of_mem_diagBox hn hc_box
  have hdiff_sum :
      (diagMass n r - tableMinMass n L) + (diagMass n c - tableMinMass n L) =
        ∑ q : Fin 4 × Fin 4, L q * uDiff n q := by
    have h1 : diagMass n r = tableMinMass n L +
        ∑ q : Fin 4 × Fin 4, L q * (witnessSize n q.1 - min (witnessSize n q.1) (witnessSize n q.2)) := by
      rw [hr_mass_eq]
      unfold tableMinMass
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← mul_add, Nat.add_sub_of_le (min_le_left _ _)]
    have h2 : diagMass n c = tableMinMass n L +
        ∑ q : Fin 4 × Fin 4, L q * (witnessSize n q.2 - min (witnessSize n q.1) (witnessSize n q.2)) := by
      rw [hc_mass_eq]
      unfold tableMinMass
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← mul_add, Nat.add_sub_of_le (min_le_right _ _)]
    have hsub1 : diagMass n r - tableMinMass n L =
        ∑ q : Fin 4 × Fin 4, L q * (witnessSize n q.1 - min (witnessSize n q.1) (witnessSize n q.2)) := by
      omega
    have hsub2 : diagMass n c - tableMinMass n L =
        ∑ q : Fin 4 × Fin 4, L q * (witnessSize n q.2 - min (witnessSize n q.1) (witnessSize n q.2)) := by
      omega
    rw [hsub1, hsub2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← mul_add, add_sub_min_eq_max_sub_min]
    rfl
  have hdesc_inv_sq :
      ((n.descFactorial (tableMinMass n L) : ℝ) ^ 2)⁻¹ ≤
        (∏ q : Fin 4 × Fin 4, ((n : ℝ) ^ (uDiff n q)) ^ (L q)) /
          ((n.descFactorial (diagMass n r) : ℝ) * (n.descFactorial (diagMass n c) : ℝ)) := by
    have hM_pos : 0 < (n.descFactorial (tableMinMass n L) : ℝ) :=
      Nat.cast_pos.mpr (descFactorial_pos_of_le (hM_le_mr.trans hmr_le_n))
    have hmr_pos : 0 < (n.descFactorial (diagMass n r) : ℝ) :=
      Nat.cast_pos.mpr (descFactorial_pos_of_le hmr_le_n)
    have hmc_pos : 0 < (n.descFactorial (diagMass n c) : ℝ) :=
      Nat.cast_pos.mpr (descFactorial_pos_of_le hmc_le_n)
    rw [inv_le_iff_one_le_mul₀ (sq_pos_of_pos hM_pos), div_mul_eq_mul_div,
      le_div_iff₀ (mul_pos hmr_pos hmc_pos), one_mul]
    have hsplit_r : n.descFactorial (diagMass n r) ≤
        n.descFactorial (tableMinMass n L) * n ^ (diagMass n r - tableMinMass n L) := by
      have heq : tableMinMass n L + (diagMass n r - tableMinMass n L) = diagMass n r :=
        Nat.add_sub_of_le hM_le_mr
      calc
        n.descFactorial (diagMass n r)
            = n.descFactorial (tableMinMass n L + (diagMass n r - tableMinMass n L)) := by rw [heq]
        _ = n.descFactorial (tableMinMass n L) *
              (n - tableMinMass n L).descFactorial (diagMass n r - tableMinMass n L) :=
          descFactorial_add_eq _ _ _
        _ ≤ n.descFactorial (tableMinMass n L) * n ^ (diagMass n r - tableMinMass n L) :=
          Nat.mul_le_mul_left _ ((descFactorial_le_pow _ _).trans
            (Nat.pow_le_pow_left (Nat.sub_le _ _) _))
    have hsplit_c : n.descFactorial (diagMass n c) ≤
        n.descFactorial (tableMinMass n L) * n ^ (diagMass n c - tableMinMass n L) := by
      have heq : tableMinMass n L + (diagMass n c - tableMinMass n L) = diagMass n c :=
        Nat.add_sub_of_le hM_le_mc
      calc
        n.descFactorial (diagMass n c)
            = n.descFactorial (tableMinMass n L + (diagMass n c - tableMinMass n L)) := by rw [heq]
        _ = n.descFactorial (tableMinMass n L) *
              (n - tableMinMass n L).descFactorial (diagMass n c - tableMinMass n L) :=
          descFactorial_add_eq _ _ _
        _ ≤ n.descFactorial (tableMinMass n L) * n ^ (diagMass n c - tableMinMass n L) :=
          Nat.mul_le_mul_left _ ((descFactorial_le_pow _ _).trans
            (Nat.pow_le_pow_left (Nat.sub_le _ _) _))
    have hmul_nat :
        n.descFactorial (diagMass n r) * n.descFactorial (diagMass n c) ≤
          n ^ (∑ q : Fin 4 × Fin 4, L q * uDiff n q) *
            (n.descFactorial (tableMinMass n L)) ^ 2 := by
      calc
        n.descFactorial (diagMass n r) * n.descFactorial (diagMass n c)
            ≤ (n.descFactorial (tableMinMass n L) * n ^ (diagMass n r - tableMinMass n L)) *
                (n.descFactorial (tableMinMass n L) * n ^ (diagMass n c - tableMinMass n L)) :=
          Nat.mul_le_mul hsplit_r hsplit_c
        _ = (n ^ (diagMass n r - tableMinMass n L) * n ^ (diagMass n c - tableMinMass n L)) *
              (n.descFactorial (tableMinMass n L)) ^ 2 := by
          ring
        _ = n ^ ((diagMass n r - tableMinMass n L) + (diagMass n c - tableMinMass n L)) *
              (n.descFactorial (tableMinMass n L)) ^ 2 := by
          rw [← pow_add]
        _ = n ^ (∑ q : Fin 4 × Fin 4, L q * uDiff n q) *
              (n.descFactorial (tableMinMass n L)) ^ 2 := by rw [hdiff_sum]
    have hpow_prod :
        (∏ q : Fin 4 × Fin 4, ((n : ℝ) ^ (uDiff n q)) ^ (L q)) =
          (n : ℝ) ^ (∑ q : Fin 4 × Fin 4, L q * uDiff n q) := by
      calc
        (∏ q : Fin 4 × Fin 4, ((n : ℝ) ^ (uDiff n q)) ^ (L q))
            = ∏ q : Fin 4 × Fin 4, (n : ℝ) ^ (L q * uDiff n q) := by
          refine Finset.prod_congr rfl fun q _ => ?_
          rw [← pow_mul, mul_comm]
        _ = (n : ℝ) ^ (∑ q : Fin 4 × Fin 4, L q * uDiff n q) :=
          prod_pow_eq_pow_sum_real Finset.univ (n : ℝ) (fun q => L q * uDiff n q)
    rw [hpow_prod]
    exact_mod_cast hmul_nat
  -- Exact algebraic factorizations connecting row/col products and `4 × 4` products
  have hprod_Lfac_row :
      ∏ i : Fin 4, ∏ j : Fin 4, ((L (i, j)) ! : ℝ) = ∏ q : Fin 4 × Fin 4, ((L q) ! : ℝ) :=
    (Fintype.prod_prod_type (fun q : Fin 4 × Fin 4 => ((L q) ! : ℝ))).symm
  have hprod_Lfac_col :
      ∏ j : Fin 4, ∏ i : Fin 4, ((L (i, j)) ! : ℝ) = ∏ q : Fin 4 × Fin 4, ((L q) ! : ℝ) := by
    rw [Finset.prod_comm]
    exact (Fintype.prod_prod_type (fun q : Fin 4 × Fin 4 => ((L q) ! : ℝ))).symm
  have hmult_id :
      ((∏ q : Fin 4 × Fin 4, ((L q) ! : ℝ)) ^ 2)⁻¹ =
        ((∏ i : Fin 4, ((r i) ! : ℝ))⁻¹ * (∏ j : Fin 4, ((c j) ! : ℝ))⁻¹) *
          rowMultinomial L * colMultinomial L := by
    unfold rowMultinomial colMultinomial
    rw [Finset.prod_div_distrib, Finset.prod_div_distrib, hprod_Lfac_row, hprod_Lfac_col]
    have hr_ne : (∏ i : Fin 4, ((r i) ! : ℝ)) ≠ 0 :=
      (Finset.prod_pos fun _ _ => Nat.cast_pos.mpr (Nat.factorial_pos _)).ne'
    have hc_ne : (∏ j : Fin 4, ((c j) ! : ℝ)) ≠ 0 :=
      (Finset.prod_pos fun _ _ => Nat.cast_pos.mpr (Nat.factorial_pos _)).ne'
    have hL_ne : (∏ q : Fin 4 × Fin 4, ((L q) ! : ℝ)) ≠ 0 :=
      (Finset.prod_pos fun _ _ => Nat.cast_pos.mpr (Nat.factorial_pos _)).ne'
    dsimp [r, c] at hr_ne hc_ne ⊢
    field_simp [hr_ne, hc_ne, hL_ne]
  have hdiag_cell_prod :
      (∏ i : Fin 4, (((witnessSize n i) ! : ℝ) * localCellReward (witnessSize n i)) ^ (r i)) *
        (∏ j : Fin 4, (((witnessSize n j) ! : ℝ) * localCellReward (witnessSize n j)) ^ (c j)) =
      ∏ q : Fin 4 × Fin 4, (cellDiagProd n q) ^ (L q) := by
    have h1 :
        ∏ i : Fin 4, (((witnessSize n i) ! : ℝ) * localCellReward (witnessSize n i)) ^ (r i) =
          ∏ q : Fin 4 × Fin 4,
            (((witnessSize n q.1) ! : ℝ) * localCellReward (witnessSize n q.1)) ^ (L q) := by
      rw [Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun i _ => ?_
      dsimp [r, typeTableRow]
      exact (prod_pow_eq_pow_sum_real Finset.univ _ (fun j => L (i, j))).symm
    have h2 :
        ∏ j : Fin 4, (((witnessSize n j) ! : ℝ) * localCellReward (witnessSize n j)) ^ (c j) =
          ∏ q : Fin 4 × Fin 4,
            (((witnessSize n q.2) ! : ℝ) * localCellReward (witnessSize n q.2)) ^ (L q) := by
      rw [Fintype.prod_prod_type, Finset.prod_comm]
      refine Finset.prod_congr rfl fun j _ => ?_
      dsimp [c, typeTableCol]
      exact (prod_pow_eq_pow_sum_real Finset.univ _ (fun i => L (i, j))).symm
    rw [h1, h2, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [← mul_pow]
    rfl
  have hcell_ratio_prod :
      (∏ q : Fin 4 × Fin 4, ((n : ℝ) ^ (uDiff n q)) ^ (L q)) *
        ((∏ q : Fin 4 × Fin 4, (cellFullFactor n q) ^ (L q)) ^ 2) =
      (∏ q : Fin 4 × Fin 4, (cellDiagProd n q) ^ (L q)) *
        ((∏ q : Fin 4 × Fin 4, (cellRatio n q) ^ (L q)) ^ 2) := by
    rw [sq (∏ q, (cellFullFactor n q) ^ (L q)), ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib, sq (∏ q, (cellRatio n q) ^ (L q)),
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun q _ => ?_
    have hdp_ne : (cellDiagProd n q) ^ (L q) ≠ 0 := (pow_pos (cellDiagProd_pos n q) _).ne'
    have hsq_q : (cellRatio n q) ^ (L q) * (cellRatio n q) ^ (L q) = (cellRatioSq n q) ^ (L q) := by
      rw [← mul_pow, ← sq, cellRatio_sq_eq]
    rw [hsq_q]
    unfold cellRatioSq
    rw [div_pow, mul_pow]
    calc
      ((n : ℝ) ^ (uDiff n q)) ^ (L q) * ((cellFullFactor n q) ^ (L q) * (cellFullFactor n q) ^ (L q))
          = ((n : ℝ) ^ (uDiff n q)) ^ (L q) * (((cellFullFactor n q) ^ 2) ^ (L q)) := by
        rw [← mul_pow, sq]
      _ = (cellDiagProd n q) ^ (L q) *
            ((((n : ℝ) ^ (uDiff n q)) ^ (L q) * ((cellFullFactor n q) ^ 2) ^ (L q)) /
              (cellDiagProd n q) ^ (L q)) := by
        field_simp [hdp_ne]
  -- Combine into `(tableWeight n L)^2 ≤ ...`
  unfold tableWeight
  have htw_sq :
      (((∏ i : Fin 4, ((witnessCounts n i).descFactorial (r i) : ℝ)) *
          (∏ j : Fin 4, ((witnessCounts n j).descFactorial (c j) : ℝ)) /
          (∏ q : Fin 4 × Fin 4, ((L q) ! : ℝ))) *
        ((∏ q : Fin 4 × Fin 4, (cellFullFactor n q) ^ (L q)) /
          (n.descFactorial (tableMinMass n L) : ℝ))) ^ 2 =
      ((∏ i : Fin 4, ((witnessCounts n i).descFactorial (r i) : ℝ) ^ 2) *
        (∏ j : Fin 4, ((witnessCounts n j).descFactorial (c j) : ℝ) ^ 2) *
        ((∏ q : Fin 4 × Fin 4, ((L q) ! : ℝ)) ^ 2)⁻¹ *
        ((∏ q : Fin 4 × Fin 4, (cellFullFactor n q) ^ (L q)) ^ 2)) *
      (((n.descFactorial (tableMinMass n L) : ℝ) ^ 2)⁻¹) := by
    simp_rw [Finset.prod_pow]
    ring
  change (((∏ i : Fin 4, ((witnessCounts n i).descFactorial (r i) : ℝ)) *
          (∏ j : Fin 4, ((witnessCounts n j).descFactorial (c j) : ℝ)) /
          (∏ q : Fin 4 × Fin 4, ((L q) ! : ℝ))) *
        ((∏ q : Fin 4 × Fin 4, (cellFullFactor n q) ^ (L q)) /
          (n.descFactorial (tableMinMass n L) : ℝ))) ^ 2 ≤ _
  rw [htw_sq]
  refine (mul_le_mul_of_nonneg_left hdesc_inv_sq ?_).trans ?_
  · refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) (sq_nonneg _)
    · exact Finset.prod_nonneg fun _ _ => sq_nonneg _
    · exact Finset.prod_nonneg fun _ _ => sq_nonneg _
    · exact inv_nonneg.mpr (sq_nonneg _)
  · rw [hmult_id]
    have hrearr :
        ((∏ i : Fin 4, ((witnessCounts n i).descFactorial (r i) : ℝ) ^ 2) *
          (∏ j : Fin 4, ((witnessCounts n j).descFactorial (c j) : ℝ) ^ 2) *
          (((∏ i : Fin 4, ((r i) ! : ℝ))⁻¹ * (∏ j : Fin 4, ((c j) ! : ℝ))⁻¹) *
            rowMultinomial L * colMultinomial L) *
          ((∏ q : Fin 4 × Fin 4, (cellFullFactor n q) ^ (L q)) ^ 2)) *
        ((∏ q : Fin 4 × Fin 4, ((n : ℝ) ^ (uDiff n q)) ^ (L q)) /
          ((n.descFactorial (diagMass n r) : ℝ) * (n.descFactorial (diagMass n c) : ℝ))) =
        (((∏ i : Fin 4, ((witnessCounts n i).descFactorial (r i) : ℝ) ^ 2) /
            (∏ i : Fin 4, ((r i) ! : ℝ))) *
          ((∏ j : Fin 4, ((witnessCounts n j).descFactorial (c j) : ℝ) ^ 2) /
            (∏ j : Fin 4, ((c j) ! : ℝ))) *
          rowMultinomial L * colMultinomial L /
          ((n.descFactorial (diagMass n r) : ℝ) * (n.descFactorial (diagMass n c) : ℝ))) *
        ((∏ q : Fin 4 × Fin 4, ((n : ℝ) ^ (uDiff n q)) ^ (L q)) *
          ((∏ q : Fin 4 × Fin 4, (cellFullFactor n q) ^ (L q)) ^ 2)) := by ring
    rw [hrearr, hcell_ratio_prod, ← hdiag_cell_prod]
    unfold diagWeight
    exact le_of_eq (by ring)

/-- Row-marginal multinomial sum over all tables `L` with `typeTableRow L = r`:
`∑_{L : row(L) = r} rowMultinomial L * ∏ q, Q(q)^{L(q)} = ∏_{i=0}^3 (∑_{j=0}^3 Q(i, j))^{r_i}`. -/
theorem sum_tables_with_row_eq (r : Fin 4 → ℕ) (Q : Fin 4 × Fin 4 → ℝ) :
    (∑ f ∈ Fintype.piFinset (fun i : Fin 4 => simplexFin 4 (r i)),
      ∏ i : Fin 4,
        ((((r i) ! : ℝ) / ∏ j : Fin 4, ((f i j) ! : ℝ)) *
          ∏ j : Fin 4, (Q (i, j)) ^ (f i j))) =
    ∏ i : Fin 4, (∑ j : Fin 4, Q (i, j)) ^ (r i) := by
  let g : Fin 4 → (Fin 4 → ℕ) → ℝ := fun i x =>
    (((r i) ! : ℝ) / ∏ j : Fin 4, ((x j) ! : ℝ)) * ∏ j : Fin 4, (Q (i, j)) ^ (x j)
  calc
    (∑ f ∈ Fintype.piFinset (fun i : Fin 4 => simplexFin 4 (r i)), ∏ i : Fin 4, g i (f i))
        = ∏ i : Fin 4, ∑ x ∈ simplexFin 4 (r i), g i x :=
      (Finset.prod_univ_sum (fun i : Fin 4 => simplexFin 4 (r i)) g).symm
    _ = ∏ i : Fin 4, (∑ j : Fin 4, Q (i, j)) ^ (r i) :=
      Finset.prod_congr rfl fun i _ => multinomial_fin_eq 4 (r i) (fun j => Q (i, j))

/-- Summing `rowMultinomial L * ∏ q, Q(q)^{L(q)}` over `{L ∈ validTypeTables n | typeTableRow L = r}`
is bounded by `∏ i : Fin 4, (∑ j : Fin 4, Q (i, j)) ^ (r i)` for nonnegative `Q`. -/
theorem sum_validTypeTables_row_le {n : ℕ}
    (r : Fin 4 → ℕ)
    {Q : Fin 4 × Fin 4 → ℝ} (hQ : ∀ q, 0 ≤ Q q) :
    ∑ L ∈ (validTypeTables n).filter (fun L => typeTableRow L = r),
      (rowMultinomial L * ∏ q : Fin 4 × Fin 4, (Q q) ^ (L q)) ≤
    ∏ i : Fin 4, (∑ j : Fin 4, Q (i, j)) ^ (r i) := by
  classical
  let curryMap : (Fin 4 × Fin 4 → ℕ) → (Fin 4 → Fin 4 → ℕ) := fun L i j => L (i, j)
  let hWeight : (Fin 4 → Fin 4 → ℕ) → ℝ := fun f =>
    ∏ i : Fin 4,
      ((((r i) ! : ℝ) / ∏ j : Fin 4, ((f i j) ! : ℝ)) *
        ∏ j : Fin 4, (Q (i, j)) ^ (f i j))
  have hinj : Set.InjOn curryMap
      ((validTypeTables n).filter (fun L => typeTableRow L = r)) := by
    intro L₁ _ L₂ _ heq
    funext ⟨i, j⟩
    exact congrFun (congrFun heq i) j
  have hsub : ((validTypeTables n).filter (fun L => typeTableRow L = r)).image curryMap ⊆
      Fintype.piFinset (fun i : Fin 4 => simplexFin 4 (r i)) := by
    intro f hf
    rcases Finset.mem_image.mp hf with ⟨L, hL_mem, rfl⟩
    have hrL : typeTableRow L = r := (Finset.mem_filter.mp hL_mem).2
    rw [Fintype.mem_piFinset]
    intro i
    rw [mem_simplexFin_iff]
    simpa [curryMap, typeTableRow] using congrFun hrL i
  have hterm_eq : ∀ L ∈ (validTypeTables n).filter (fun L => typeTableRow L = r),
      rowMultinomial L * (∏ q : Fin 4 × Fin 4, (Q q) ^ (L q)) = hWeight (curryMap L) := by
    intro L hL_mem
    have hrL : typeTableRow L = r := (Finset.mem_filter.mp hL_mem).2
    unfold rowMultinomial
    rw [hrL, Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  calc
    ∑ L ∈ (validTypeTables n).filter (fun L => typeTableRow L = r),
        (rowMultinomial L * ∏ q : Fin 4 × Fin 4, (Q q) ^ (L q))
        = ∑ L ∈ (validTypeTables n).filter (fun L => typeTableRow L = r),
            hWeight (curryMap L) := Finset.sum_congr rfl hterm_eq
    _ = ∑ f ∈ ((validTypeTables n).filter (fun L => typeTableRow L = r)).image curryMap,
          hWeight f := (Finset.sum_image hinj).symm
    _ ≤ ∑ f ∈ Fintype.piFinset (fun i : Fin 4 => simplexFin 4 (r i)), hWeight f := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun f _ _ => ?_
      exact Finset.prod_nonneg fun i _ =>
        mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _))
          (Finset.prod_nonneg fun j _ => pow_nonneg (hQ (i, j)) _)
    _ = ∏ i : Fin 4, (∑ j : Fin 4, Q (i, j)) ^ (r i) := sum_tables_with_row_eq r Q

/-- Column-symmetric bound over `{L ∈ validTypeTables n | typeTableCol L = c}`. -/
theorem sum_validTypeTables_col_le {n : ℕ}
    (c : Fin 4 → ℕ)
    {Q : Fin 4 × Fin 4 → ℝ} (hQ : ∀ q, 0 ≤ Q q) :
    ∑ L ∈ (validTypeTables n).filter (fun L => typeTableCol L = c),
      (colMultinomial L * ∏ q : Fin 4 × Fin 4, (Q q) ^ (L q)) ≤
    ∏ j : Fin 4, (∑ i : Fin 4, Q (i, j)) ^ (c j) := by
  classical
  let colCurry : (Fin 4 × Fin 4 → ℕ) → (Fin 4 → Fin 4 → ℕ) := fun L j i => L (i, j)
  let hWeight : (Fin 4 → Fin 4 → ℕ) → ℝ := fun f =>
    ∏ j : Fin 4,
      ((((c j) ! : ℝ) / ∏ i : Fin 4, ((f j i) ! : ℝ)) *
        ∏ i : Fin 4, (Q (i, j)) ^ (f j i))
  have hinj : Set.InjOn colCurry
      ((validTypeTables n).filter (fun L => typeTableCol L = c)) := by
    intro L₁ _ L₂ _ heq
    funext ⟨i, j⟩
    exact congrFun (congrFun heq j) i
  have hsub : ((validTypeTables n).filter (fun L => typeTableCol L = c)).image colCurry ⊆
      Fintype.piFinset (fun j : Fin 4 => simplexFin 4 (c j)) := by
    intro f hf
    rcases Finset.mem_image.mp hf with ⟨L, hL_mem, rfl⟩
    have hcL : typeTableCol L = c := (Finset.mem_filter.mp hL_mem).2
    rw [Fintype.mem_piFinset]
    intro j
    rw [mem_simplexFin_iff]
    simpa [colCurry, typeTableCol] using congrFun hcL j
  have hterm_eq : ∀ L ∈ (validTypeTables n).filter (fun L => typeTableCol L = c),
      colMultinomial L * (∏ q : Fin 4 × Fin 4, (Q q) ^ (L q)) = hWeight (colCurry L) := by
    intro L hL_mem
    have hcL : typeTableCol L = c := (Finset.mem_filter.mp hL_mem).2
    unfold colMultinomial
    rw [hcL, Fintype.prod_prod_type, Finset.prod_comm (f := fun i j => (Q (i, j)) ^ (L (i, j))),
      ← Finset.prod_mul_distrib]
  let Qswap : Fin 4 × Fin 4 → ℝ := fun q => Q (q.2, q.1)
  calc
    ∑ L ∈ (validTypeTables n).filter (fun L => typeTableCol L = c),
        (colMultinomial L * ∏ q : Fin 4 × Fin 4, (Q q) ^ (L q))
        = ∑ L ∈ (validTypeTables n).filter (fun L => typeTableCol L = c),
            hWeight (colCurry L) := Finset.sum_congr rfl hterm_eq
    _ = ∑ f ∈ ((validTypeTables n).filter (fun L => typeTableCol L = c)).image colCurry,
          hWeight f := (Finset.sum_image hinj).symm
    _ ≤ ∑ f ∈ Fintype.piFinset (fun j : Fin 4 => simplexFin 4 (c j)), hWeight f := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun f _ _ => ?_
      exact Finset.prod_nonneg fun j _ =>
        mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _))
          (Finset.prod_nonneg fun i _ => pow_nonneg (hQ (i, j)) _)
    _ = ∏ j : Fin 4, (∑ i : Fin 4, Q (i, j)) ^ (c j) := sum_tables_with_row_eq c Qswap

/-- **Master High-Cell Skeleton Sum Bound (`arXiv:2608.30604`, Section 8)**:
There exists a nonnegative sequence `η_hi : ℕ → ℝ` tending to `0` such that eventually
`∑ M ∈ blockMatchings n, ∑ j ∈ highMultBox n M, highSkeletonWeight n M j ≤
  Real.exp (η_hi n * (n : ℝ) / (Real.log (n : ℝ)) ^ 4)`. -/
theorem eventually_sum_highSkeletonWeight_le :
    ∃ η_hi : ℕ → ℝ,
      (∀ n, 0 ≤ η_hi n) ∧
      Tendsto η_hi atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∑ M ∈ blockMatchings n, ∑ j ∈ highMultBox n M, highSkeletonWeight n M j ≤
          Real.exp (η_hi n * (n : ℝ) / (Real.log (n : ℝ)) ^ 4) := by
  obtain ⟨η_pd, hη_pd_nonneg, hη_pd_tendsto, hev_pd⟩ := eventually_sum_diagWeight_le
  let η_extra : ℕ → ℝ := fun n => if n ≤ 2 then 0 else 2 / Real.log (n : ℝ)
  let η_hi : ℕ → ℝ := fun n => η_pd n + η_extra n
  have hη_extra_nonneg : ∀ n, 0 ≤ η_extra n := by
    intro n
    dsimp [η_extra]
    split_ifs with h
    · norm_num
    · have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
      exact div_nonneg (by norm_num) (Real.log_pos hn1).le
  have hη_hi_nonneg : ∀ n, 0 ≤ η_hi n :=
    fun n => add_nonneg (hη_pd_nonneg n) (hη_extra_nonneg n)
  have hL : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll_div_L : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact h0.comp hL
  have hη_extra_tendsto : Tendsto η_extra atTop (𝓝 0) := by
    have hdiv : Tendsto (fun n : ℕ => 2 / Real.log (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hL
    refine hdiv.congr' ?_
    filter_upwards [eventually_ge_atTop 3] with n hn3
    dsimp [η_extra]
    split_ifs with h
    · omega
    · rfl
  have hη_hi_tendsto : Tendsto η_hi atTop (𝓝 0) := by
    simpa using hη_pd_tendsto.add hη_extra_tendsto
  refine ⟨η_hi, hη_hi_nonneg, hη_hi_tendsto, ?_⟩
  filter_upwards [eventually_alphaNat_regime, eventually_witnessCounts_spec, hev_pd,
    tendsto_alphaNat_atTop.eventually_ge_atTop 100,
    hL.eventually_ge_atTop (4 * 10 ^ 10 : ℝ),
    hll_div_L.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16))] with
      n ⟨hn16, _, _, hqα, _, hhi⟩ ⟨hK, hn, hsize, _, _⟩ hpd_bound
      hα100 hL_big hrat16
  set L : ℝ := Real.log (n : ℝ)
  set q : ℝ := Real.log 2
  have hL_big' : (4 * 10 ^ 10 : ℝ) ≤ L := hL_big
  have hL_pos : 0 < L := by linarith only [hL_big']
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn_exp : (n : ℝ) = Real.exp L := (Real.exp_log hn_pos).symm
  have hq_bounds : (0.69 : ℝ) ≤ q ∧ q ≤ 0.70 := by
    dsimp [q]; constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
  -- `K ≤ n` and `alphaNat n ≤ 3 * L`
  have hK_le_n : kCoSeed n ≤ n := by
    calc
      kCoSeed n = ∑ i : Fin 4, witnessCounts n i := hK.symm
      _ ≤ ∑ i : Fin 4, witnessSize n i * witnessCounts n i := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hsi : 1 ≤ witnessSize n i := by have := hsize i; omega
        calc
          witnessCounts n i = 1 * witnessCounts n i := (one_mul _).symm
          _ ≤ witnessSize n i * witnessCounts n i := Nat.mul_le_mul_right _ hsi
      _ = n := hn
  have hα_le_3L : (alphaNat n : ℝ) ≤ 3 * L := by
    have hm : 0.69 * (alphaNat n : ℝ) ≤ q * (alphaNat n : ℝ) :=
      mul_le_mul_of_nonneg_right hq_bounds.1 (Nat.cast_nonneg _)
    change q * (alphaNat n : ℝ) ≤ 2 * L at hhi
    linarith only [hhi, hm, hL_pos]
  -- Lower bound `q * alphaNat n ≥ (7 / 4) * L + 10`
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
  -- Step 1: Bound `deficitRatio n` and `(kCoSeed n) * (alphaNat n) * deficitRatio n ≤ n / L^5`
  have hdef_exp : deficitRatio n ≤ 3 * L * Real.exp (-L / 4) := by
    unfold deficitRatio
    set qExp : ℕ := 3 * alphaNat n / 4 - 4
    have hqExp_ge : (3 / 4 : ℝ) * (alphaNat n : ℝ) - 5 ≤ (qExp : ℝ) := by
      have hdiv : 3 * alphaNat n - 3 ≤ 4 * (3 * alphaNat n / 4) := by omega
      have hsub : 20 ≤ 3 * alphaNat n / 4 := by omega
      have hc : (qExp : ℝ) = ((3 * alphaNat n / 4 : ℕ) : ℝ) - 4 := by
        dsimp [qExp]; rw [Nat.cast_sub (by omega)]; push_cast; rfl
      have hdiv_r : 3 * (alphaNat n : ℝ) - 3 ≤ 4 * ((3 * alphaNat n / 4 : ℕ) : ℝ) := by
        have h1 : ((3 * alphaNat n - 3 : ℕ) : ℝ) ≤ ((4 * (3 * alphaNat n / 4) : ℕ) : ℝ) := by
          exact_mod_cast hdiv
        rw [Nat.cast_sub (by omega)] at h1
        push_cast at h1
        linarith
      linarith
    have h2pow_ge : Real.exp ((5 / 4 : ℝ) * L) ≤ (2 : ℝ) ^ qExp := by
      have h2eq : (2 : ℝ) ^ qExp = Real.exp ((qExp : ℝ) * q) := by
        rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul]
      rw [h2eq]
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_right hqExp_ge (by linarith only [hq_bounds.1])
      linarith only [hm, hqα_ge, hq_bounds.2, hL_pos]
    calc
      ((n : ℝ) * (alphaNat n : ℝ)) / (2 : ℝ) ^ qExp
          ≤ ((n : ℝ) * (3 * L)) / (2 : ℝ) ^ qExp :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hα_le_3L hn_pos.le)
          (pow_nonneg (by norm_num) _)
      _ ≤ (Real.exp L * (3 * L)) / Real.exp ((5 / 4 : ℝ) * L) := by
        rw [← hn_exp]
        exact div_le_div_of_nonneg_left (mul_nonneg hn_pos.le (by linarith only [hL_pos]))
          (Real.exp_pos _) h2pow_ge
      _ = 3 * L * (Real.exp L / Real.exp ((5 / 4 : ℝ) * L)) := by ring
      _ = 3 * L * Real.exp (-L / 4) := by
        rw [← Real.exp_sub]
        congr 2
        ring
  have hexp_L4_poly : 12 * L ^ 7 ≤ Real.exp (L / 4) := by
    have h8 := pow_div_factorial_le_exp (by positivity : 0 ≤ L / 4) 8
    have hfac8 : ((8 ! : ℕ) : ℝ) = 40320 := by norm_num
    rw [hfac8] at h8
    have hcoef : 12 * L ^ 7 ≤ (L / 4) ^ 8 / 40320 := by
      have hbig : (12 * 4 ^ 8 * 40320 : ℝ) ≤ L := by linarith only [hL_big']
      have hm := mul_le_mul_of_nonneg_right hbig (pow_nonneg hL_pos.le 7)
      linarith [show (L / 4) ^ 8 / 40320 = L ^ 8 / (4 ^ 8 * 40320) by ring,
        show L * L ^ 7 = L ^ 8 by ring]
    exact hcoef.trans h8
  have hρ_le1 : deficitRatio n ≤ 1 := by
    refine hdef_exp.trans ?_
    have h3L_le : 3 * L ≤ Real.exp (L / 4) := by
      have hL7 : L ≤ L ^ 7 := by
        have h1 : (1 : ℝ) ≤ L ^ 6 := one_le_pow₀ (by linarith only [hL_big'])
        nlinarith [mul_le_mul_of_nonneg_left h1 hL_pos.le,
          show L * L ^ 6 = L ^ 7 by ring]
      linarith only [hexp_L4_poly, hL7, hL_pos]
    calc
      3 * L * Real.exp (-L / 4) ≤ Real.exp (L / 4) * Real.exp (-L / 4) :=
        mul_le_mul_of_nonneg_right h3L_le (Real.exp_pos _).le
      _ = 1 := by
        rw [← Real.exp_add]
        have hzero : L / 4 + -L / 4 = 0 := by ring
        rw [hzero, Real.exp_zero]
  have hdef_budget :
      (kCoSeed n : ℝ) * (alphaNat n : ℝ) * deficitRatio n ≤ (n : ℝ) / L ^ 5 := by
    have hK_r : (kCoSeed n : ℝ) ≤ Real.exp L := by rw [← hn_exp]; exact_mod_cast hK_le_n
    calc
      (kCoSeed n : ℝ) * (alphaNat n : ℝ) * deficitRatio n
          ≤ Real.exp L * (3 * L) * (3 * L * Real.exp (-L / 4)) := by
        refine mul_le_mul (mul_le_mul hK_r hα_le_3L (Nat.cast_nonneg _) (Real.exp_pos _).le)
          hdef_exp (deficitRatio_nonneg n) (by positivity)
      _ ≤ 12 * L ^ 2 * Real.exp ((3 / 4 : ℝ) * L) := by
        have hexp_mul : Real.exp L * Real.exp (-L / 4) = Real.exp ((3 / 4 : ℝ) * L) := by
          rw [← Real.exp_add]; congr 1; ring
        have h9_12 : 9 * L ^ 2 ≤ 12 * L ^ 2 :=
          mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg L)
        have hrew : Real.exp L * (3 * L) * (3 * L * Real.exp (-L / 4)) =
            9 * L ^ 2 * (Real.exp L * Real.exp (-L / 4)) := by ring
        rw [hrew, hexp_mul]
        exact mul_le_mul_of_nonneg_right h9_12 (Real.exp_pos _).le
      _ ≤ (n : ℝ) / L ^ 5 := by
        rw [hn_exp, le_div_iff₀ (by positivity)]
        have hm := mul_le_mul_of_nonneg_right hexp_L4_poly (Real.exp_pos ((3 / 4 : ℝ) * L)).le
        rw [← Real.exp_add] at hm
        have hadd : L / 4 + (3 / 4 : ℝ) * L = L := by ring
        rw [hadd] at hm
        have hl7 : 12 * L ^ 2 * Real.exp ((3 / 4 : ℝ) * L) * L ^ 5 =
            12 * L ^ 7 * Real.exp ((3 / 4 : ℝ) * L) := by ring
        linarith only [hm, hl7]
  -- Step 2: Bound off-diagonal `cellRatio n p ≤ Real.exp (-L / 6)` for `p.1 ≠ p.2`
  have htau_off : ∀ p : Fin 4 × Fin 4, p.1 ≠ p.2 → cellRatio n p ≤ Real.exp (-L / 6) := by
    intro p hne
    have hsq_le := cellRatioSq_le_of_ne hsize hne
    have hbase_le : ((n : ℝ) * (alphaNat n : ℝ)) / (2 : ℝ) ^ (alphaNat n - 5) ≤
        Real.exp (-L / 3) := by
      have h2pow_ge : Real.exp ((3 / 2 : ℝ) * L) ≤ (2 : ℝ) ^ (alphaNat n - 5) := by
        have h2eq : (2 : ℝ) ^ (alphaNat n - 5) = Real.exp (((alphaNat n - 5 : ℕ) : ℝ) * q) := by
          rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul]
        rw [h2eq]
        apply Real.exp_le_exp.mpr
        have hsub : ((alphaNat n - 5 : ℕ) : ℝ) * q = q * (alphaNat n : ℝ) - 5 * q := by
          rw [Nat.cast_sub (by omega)]
          push_cast
          ring
        linarith only [hsub, hqα_ge, hq_bounds.2, hL_big']
      have h3L_exp : 3 * L ≤ Real.exp (L / 6) := by
        have h2 := pow_div_factorial_le_exp (by positivity : 0 ≤ L / 6) 2
        have hfac2 : ((2 ! : ℕ) : ℝ) = 2 := by norm_num
        rw [hfac2] at h2
        have hquad : 3 * L ≤ (L / 6) ^ 2 / 2 := by nlinarith [hL_big']
        exact hquad.trans h2
      calc
        ((n : ℝ) * (alphaNat n : ℝ)) / (2 : ℝ) ^ (alphaNat n - 5)
            ≤ ((n : ℝ) * (3 * L)) / (2 : ℝ) ^ (alphaNat n - 5) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hα_le_3L hn_pos.le)
            (pow_nonneg (by norm_num) _)
        _ ≤ (Real.exp L * (3 * L)) / Real.exp ((3 / 2 : ℝ) * L) := by
          rw [← hn_exp]
          exact div_le_div_of_nonneg_left (mul_nonneg hn_pos.le (by linarith only [hL_pos]))
            (Real.exp_pos _) h2pow_ge
        _ = 3 * L * Real.exp (-L / 2) := by
          rw [show Real.exp L * (3 * L) / Real.exp ((3 / 2 : ℝ) * L) =
            3 * L * (Real.exp L / Real.exp ((3 / 2 : ℝ) * L)) by ring, ← Real.exp_sub]
          congr 2; ring
        _ ≤ Real.exp (L / 6) * Real.exp (-L / 2) :=
          mul_le_mul_of_nonneg_right h3L_exp (Real.exp_pos _).le
        _ = Real.exp (-L / 3) := by rw [← Real.exp_add]; congr 1; ring
    have hd_pos : 1 ≤ uDiff n p := by
      have hs0 := hsize 0
      unfold witnessSize at hs0
      have hval_ne : p.1.val ≠ p.2.val := Fin.val_ne_of_ne hne
      unfold uDiff witnessSize
      have := p.1.isLt
      have := p.2.isLt
      omega
    have hexp_le1 : Real.exp (-L / 3) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hL_pos])
    have hcsq : cellRatioSq n p ≤ (Real.exp (-L / 6)) ^ 2 := by
      calc
        cellRatioSq n p ≤ (Real.exp (-L / 3)) ^ (uDiff n p) :=
          hsq_le.trans (pow_le_pow_left₀
            (div_nonneg (mul_nonneg hn_pos.le (Nat.cast_nonneg _)) (pow_nonneg (by norm_num) _))
            hbase_le _)
        _ ≤ Real.exp (-L / 3) :=
          pow_le_of_le_one (Real.exp_pos _).le hexp_le1 (by omega : uDiff n p ≠ 0)
        _ = (Real.exp (-L / 6)) ^ 2 := by rw [sq, ← Real.exp_add]; congr 1; ring
    unfold cellRatio
    exact (Real.sqrt_le_iff).mpr ⟨(Real.exp_pos _).le, hcsq⟩
  -- Row and column 4-term sums of `cellRatio n` are `≤ 1 + 3 * exp(-L / 6)`
  have hrow_Q_sum : ∀ i : Fin 4, ∑ j : Fin 4, cellRatio n (i, j) ≤ 1 + 3 * Real.exp (-L / 6) := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), cellRatio_diag_eq_one]
    have hcard3 : ((Finset.univ : Finset (Fin 4)).erase i).card = 3 := by simp
    calc
      1 + ∑ j ∈ Finset.univ.erase i, cellRatio n (i, j)
          ≤ 1 + ∑ _j ∈ Finset.univ.erase i, Real.exp (-L / 6) := by
        refine add_le_add_right (Finset.sum_le_sum fun j hj => ?_) 1
        exact htau_off (i, j) (Finset.ne_of_mem_erase hj).symm
      _ = 1 + 3 * Real.exp (-L / 6) := by
        rw [Finset.sum_const, hcard3, nsmul_eq_mul]; push_cast; rfl
  have hcol_Q_sum : ∀ j : Fin 4, ∑ i : Fin 4, cellRatio n (i, j) ≤ 1 + 3 * Real.exp (-L / 6) := by
    intro j
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), cellRatio_diag_eq_one]
    have hcard3 : ((Finset.univ : Finset (Fin 4)).erase j).card = 3 := by simp
    calc
      1 + ∑ i ∈ Finset.univ.erase j, cellRatio n (i, j)
          ≤ 1 + ∑ _i ∈ Finset.univ.erase j, Real.exp (-L / 6) := by
        refine add_le_add_right (Finset.sum_le_sum fun i hi => ?_) 1
        exact htau_off (i, j) (Finset.ne_of_mem_erase hi)
      _ = 1 + 3 * Real.exp (-L / 6) := by
        rw [Finset.sum_const, hcard3, nsmul_eq_mul]; push_cast; rfl
  have h3K_tau_le : 3 * (kCoSeed n : ℝ) * Real.exp (-L / 6) ≤ (n : ℝ) / L ^ 5 := by
    have hK_r : (kCoSeed n : ℝ) ≤ Real.exp L := by rw [← hn_exp]; exact_mod_cast hK_le_n
    have h6 := pow_div_factorial_le_exp (by positivity : 0 ≤ L / 6) 6
    have hfac6 : ((6 ! : ℕ) : ℝ) = 720 := by norm_num
    rw [hfac6] at h6
    have hpoly6 : 3 * L ^ 5 ≤ Real.exp (L / 6) := by
      have hcoef : 3 * L ^ 5 ≤ (L / 6) ^ 6 / 720 := by
        have hbig : (3 * 6 ^ 6 * 720 : ℝ) ≤ L := by linarith only [hL_big']
        have hm := mul_le_mul_of_nonneg_right hbig (pow_nonneg hL_pos.le 5)
        linarith [show (L / 6) ^ 6 / 720 = L ^ 6 / (6 ^ 6 * 720) by ring,
          show L * L ^ 5 = L ^ 6 by ring]
      exact hcoef.trans h6
    rw [hn_exp, le_div_iff₀ (by positivity)]
    calc
      3 * (kCoSeed n : ℝ) * Real.exp (-L / 6) * L ^ 5
          ≤ 3 * Real.exp L * Real.exp (-L / 6) * L ^ 5 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK_r (by norm_num))
            (Real.exp_pos _).le) (by positivity)
      _ = (3 * L ^ 5) * Real.exp ((5 / 6 : ℝ) * L) := by
        have hexp_s : Real.exp L * Real.exp (-L / 6) = Real.exp ((5 / 6 : ℝ) * L) := by
          rw [← Real.exp_add]; congr 1; ring
        calc
          3 * Real.exp L * Real.exp (-L / 6) * L ^ 5
              = (3 * L ^ 5) * (Real.exp L * Real.exp (-L / 6)) := by ring
          _ = (3 * L ^ 5) * Real.exp ((5 / 6 : ℝ) * L) := by rw [hexp_s]
      _ ≤ Real.exp (L / 6) * Real.exp ((5 / 6 : ℝ) * L) :=
        mul_le_mul_of_nonneg_right hpoly6 (Real.exp_pos _).le
      _ = Real.exp L := by rw [← Real.exp_add]; congr 1; ring
  have hprod_v_le : ∀ v ∈ diagBox n,
      (1 + 3 * Real.exp (-L / 6)) ^ (∑ i : Fin 4, v i) ≤ Real.exp ((n : ℝ) / L ^ 5) := by
    intro v hv
    have hv_sum_le : ∑ i : Fin 4, v i ≤ kCoSeed n := by
      rw [← hK]
      exact Finset.sum_le_sum fun i _ => (mem_diagBox_iff.mp hv) i
    calc
      (1 + 3 * Real.exp (-L / 6)) ^ (∑ i : Fin 4, v i)
          ≤ (Real.exp (3 * Real.exp (-L / 6))) ^ (∑ i : Fin 4, v i) := by
        refine pow_le_pow_left₀ (by positivity) ?_ _
        linarith [Real.add_one_le_exp (3 * Real.exp (-L / 6))]
      _ ≤ (Real.exp (3 * Real.exp (-L / 6))) ^ (kCoSeed n) :=
        pow_le_pow_right₀ (Real.one_le_exp (by positivity)) hv_sum_le
      _ = Real.exp (3 * (kCoSeed n : ℝ) * Real.exp (-L / 6)) := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ Real.exp ((n : ℝ) / L ^ 5) := Real.exp_le_exp.mpr h3K_tau_le
  -- Step 3: AM-GM + row/col multinomial sums bound `∑_{L ∈ validTypeTables n} tableWeight n L`
  have hsum_tables :
      ∑ L ∈ validTypeTables n, tableWeight n L ≤
        Real.exp ((n : ℝ) / L ^ 5) * ∑ v ∈ diagBox n, diagWeight n v := by
    classical
    have hpoint_amgm : ∀ L ∈ validTypeTables n,
        tableWeight n L ≤
          (diagWeight n (typeTableRow L) *
              (rowMultinomial L * ∏ q : Fin 4 × Fin 4, (cellRatio n q) ^ (L q)) +
            diagWeight n (typeTableCol L) *
              (colMultinomial L * ∏ q : Fin 4 × Fin 4, (cellRatio n q) ^ (L q))) / 2 := by
      intro L hL_mem
      have hsq := tableWeight_sq_le hn hL_mem
      have hX0 : 0 ≤ diagWeight n (typeTableRow L) * rowMultinomial L *
          ∏ q : Fin 4 × Fin 4, (cellRatio n q) ^ (L q) :=
        mul_nonneg (mul_nonneg (diagWeight_nonneg _ _) (rowMultinomial_nonneg L))
          (Finset.prod_nonneg fun _ _ => pow_nonneg (cellRatio_nonneg _ _) _)
      have hY0 : 0 ≤ diagWeight n (typeTableCol L) * colMultinomial L *
          ∏ q : Fin 4 × Fin 4, (cellRatio n q) ^ (L q) :=
        mul_nonneg (mul_nonneg (diagWeight_nonneg _ _) (colMultinomial_nonneg L))
          (Finset.prod_nonneg fun _ _ => pow_nonneg (cellRatio_nonneg _ _) _)
      have hamgm := le_half_add_of_sq_le_mul hX0 hY0 hsq
      linarith only [hamgm, show
        diagWeight n (typeTableRow L) * rowMultinomial L *
          (∏ q : Fin 4 × Fin 4, (cellRatio n q) ^ (L q)) =
        diagWeight n (typeTableRow L) *
          (rowMultinomial L * ∏ q : Fin 4 × Fin 4, (cellRatio n q) ^ (L q)) by ring,
        show diagWeight n (typeTableCol L) * colMultinomial L *
          (∏ q : Fin 4 × Fin 4, (cellRatio n q) ^ (L q)) =
        diagWeight n (typeTableCol L) *
          (colMultinomial L * ∏ q : Fin 4 × Fin 4, (cellRatio n q) ^ (L q)) by ring]
    have hrow_total :
        ∑ L ∈ validTypeTables n,
          diagWeight n (typeTableRow L) *
            (rowMultinomial L * ∏ q : Fin 4 × Fin 4, (cellRatio n q) ^ (L q)) ≤
        Real.exp ((n : ℝ) / L ^ 5) * ∑ r ∈ diagBox n, diagWeight n r := by
      have hpart : validTypeTables n =
          (diagBox n).biUnion
            (fun r => (validTypeTables n).filter (fun L => typeTableRow L = r)) := by
        ext L
        simp only [Finset.mem_biUnion, Finset.mem_filter]
        exact ⟨fun hL => ⟨typeTableRow L, (mem_validTypeTables_iff.mp hL).1, hL, rfl⟩,
          fun ⟨_, _, hL, _⟩ => hL⟩
      have hdisj : ((diagBox n : Finset (Fin 4 → ℕ)) : Set (Fin 4 → ℕ)).PairwiseDisjoint
          (fun r => (validTypeTables n).filter (fun L => typeTableRow L = r)) := by
        intro r₁ _ r₂ _ hne
        refine Finset.disjoint_left.mpr fun L h₁ h₂ => hne ?_
        exact (Finset.mem_filter.mp h₁).2.symm.trans (Finset.mem_filter.mp h₂).2
      conv_lhs => rw [hpart]
      rw [Finset.sum_biUnion hdisj, Finset.mul_sum]
      refine Finset.sum_le_sum fun r hr => ?_
      have hconst : ∀ L ∈ (validTypeTables n).filter (fun L => typeTableRow L = r),
          diagWeight n (typeTableRow L) *
            (rowMultinomial L * ∏ q : Fin 4 × Fin 4, (cellRatio n q) ^ (L q)) =
          diagWeight n r *
            (rowMultinomial L * ∏ q : Fin 4 × Fin 4, (cellRatio n q) ^ (L q)) :=
        fun L hL => by rw [(Finset.mem_filter.mp hL).2]
      rw [Finset.sum_congr rfl hconst, ← Finset.mul_sum, mul_comm (Real.exp _)]
      refine mul_le_mul_of_nonneg_left ?_ (diagWeight_nonneg n r)
      calc
        ∑ L ∈ (validTypeTables n).filter (fun L => typeTableRow L = r),
            (rowMultinomial L * ∏ q : Fin 4 × Fin 4, (cellRatio n q) ^ (L q))
            ≤ ∏ i : Fin 4, (∑ j : Fin 4, cellRatio n (i, j)) ^ (r i) :=
          sum_validTypeTables_row_le r (cellRatio_nonneg n)
        _ ≤ ∏ i : Fin 4, (1 + 3 * Real.exp (-L / 6)) ^ (r i) :=
          prod_le_prod_real Finset.univ
            (fun i _ => pow_nonneg (Finset.sum_nonneg fun _ _ => cellRatio_nonneg _ _) _)
            (fun i _ => pow_le_pow_left₀
              (Finset.sum_nonneg fun _ _ => cellRatio_nonneg _ _) (hrow_Q_sum i) _)
        _ = (1 + 3 * Real.exp (-L / 6)) ^ (∑ i : Fin 4, r i) :=
          prod_pow_eq_pow_sum_real Finset.univ _ r
        _ ≤ Real.exp ((n : ℝ) / L ^ 5) := hprod_v_le r hr
    have hcol_total :
        ∑ L ∈ validTypeTables n,
          diagWeight n (typeTableCol L) *
            (colMultinomial L * ∏ q : Fin 4 × Fin 4, (cellRatio n q) ^ (L q)) ≤
        Real.exp ((n : ℝ) / L ^ 5) * ∑ c ∈ diagBox n, diagWeight n c := by
      have hpart : validTypeTables n =
          (diagBox n).biUnion
            (fun c => (validTypeTables n).filter (fun L => typeTableCol L = c)) := by
        ext L
        simp only [Finset.mem_biUnion, Finset.mem_filter]
        exact ⟨fun hL => ⟨typeTableCol L, (mem_validTypeTables_iff.mp hL).2, hL, rfl⟩,
          fun ⟨_, _, hL, _⟩ => hL⟩
      have hdisj : ((diagBox n : Finset (Fin 4 → ℕ)) : Set (Fin 4 → ℕ)).PairwiseDisjoint
          (fun c => (validTypeTables n).filter (fun L => typeTableCol L = c)) := by
        intro c₁ _ c₂ _ hne
        refine Finset.disjoint_left.mpr fun L h₁ h₂ => hne ?_
        exact (Finset.mem_filter.mp h₁).2.symm.trans (Finset.mem_filter.mp h₂).2
      conv_lhs => rw [hpart]
      rw [Finset.sum_biUnion hdisj, Finset.mul_sum]
      refine Finset.sum_le_sum fun c hc => ?_
      have hconst : ∀ L ∈ (validTypeTables n).filter (fun L => typeTableCol L = c),
          diagWeight n (typeTableCol L) *
            (colMultinomial L * ∏ q : Fin 4 × Fin 4, (cellRatio n q) ^ (L q)) =
          diagWeight n c *
            (colMultinomial L * ∏ q : Fin 4 × Fin 4, (cellRatio n q) ^ (L q)) :=
        fun L hL => by rw [(Finset.mem_filter.mp hL).2]
      rw [Finset.sum_congr rfl hconst, ← Finset.mul_sum, mul_comm (Real.exp _)]
      refine mul_le_mul_of_nonneg_left ?_ (diagWeight_nonneg n c)
      calc
        ∑ L ∈ (validTypeTables n).filter (fun L => typeTableCol L = c),
            (colMultinomial L * ∏ q : Fin 4 × Fin 4, (cellRatio n q) ^ (L q))
            ≤ ∏ j : Fin 4, (∑ i : Fin 4, cellRatio n (i, j)) ^ (c j) :=
          sum_validTypeTables_col_le c (cellRatio_nonneg n)
        _ ≤ ∏ j : Fin 4, (1 + 3 * Real.exp (-L / 6)) ^ (c j) :=
          prod_le_prod_real Finset.univ
            (fun j _ => pow_nonneg (Finset.sum_nonneg fun _ _ => cellRatio_nonneg _ _) _)
            (fun j _ => pow_le_pow_left₀
              (Finset.sum_nonneg fun _ _ => cellRatio_nonneg _ _) (hcol_Q_sum j) _)
        _ = (1 + 3 * Real.exp (-L / 6)) ^ (∑ j : Fin 4, c j) :=
          prod_pow_eq_pow_sum_real Finset.univ _ c
        _ ≤ Real.exp ((n : ℝ) / L ^ 5) := hprod_v_le c hc
    have hsum_half := Finset.sum_le_sum hpoint_amgm
    simp_rw [add_div] at hsum_half
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div] at hsum_half
    linarith only [hsum_half, hrow_total, hcol_total]
  -- Step 4: Combine deficit sum + matching sum + Section 7 `diagBox` sum
  have hη_eq :
      (n : ℝ) / L ^ 5 + ((n : ℝ) / L ^ 5 + η_pd n * (n : ℝ) / L ^ 4) =
        η_hi n * (n : ℝ) / L ^ 4 := by
    dsimp [η_hi, η_extra]
    split_ifs with h
    · omega
    · change (n : ℝ) / L ^ 5 + ((n : ℝ) / L ^ 5 + η_pd n * (n : ℝ) / L ^ 4) =
        (η_pd n + 2 / L) * (n : ℝ) / L ^ 4
      field_simp [hL_pos.ne']
      ring
  calc
    ∑ M ∈ blockMatchings n, ∑ j ∈ highMultBox n M, highSkeletonWeight n M j
        ≤ ∑ M ∈ blockMatchings n,
            Real.exp ((kCoSeed n : ℝ) * (alphaNat n : ℝ) * deficitRatio n) *
              fullSkeletonWeight n M :=
      Finset.sum_le_sum fun M hM =>
        sum_highMultBox_highSkeletonWeight_le hK hn (by omega) hρ_le1
          (mem_blockMatchings_iff.mp hM)
    _ = Real.exp ((kCoSeed n : ℝ) * (alphaNat n : ℝ) * deficitRatio n) *
          ∑ M ∈ blockMatchings n, fullSkeletonWeight n M :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp ((n : ℝ) / L ^ 5) * ∑ L ∈ validTypeTables n, tableWeight n L :=
      mul_le_mul (Real.exp_le_exp.mpr hdef_budget)
        (sum_blockMatchings_fullSkeletonWeight_le hK)
        (Finset.sum_nonneg fun M _ => fullSkeletonWeight_nonneg n M)
        (Real.exp_pos _).le
    _ ≤ Real.exp ((n : ℝ) / L ^ 5) *
          (Real.exp ((n : ℝ) / L ^ 5) * ∑ v ∈ diagBox n, diagWeight n v) :=
      mul_le_mul_of_nonneg_left hsum_tables (Real.exp_pos _).le
    _ ≤ Real.exp ((n : ℝ) / L ^ 5) *
          (Real.exp ((n : ℝ) / L ^ 5) * Real.exp (η_pd n * (n : ℝ) / L ^ 4)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpd_bound (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = Real.exp (η_hi n * (n : ℝ) / L ^ 4) := by
      rw [← Real.exp_add, ← Real.exp_add, hη_eq]

end JSP000506
