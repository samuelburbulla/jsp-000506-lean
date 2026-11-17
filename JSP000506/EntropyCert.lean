import JSP000506.Model
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Continuous Entropy Profiles and Petkov's Uniform `log(200 / 153)` Certificate

This module formalizes Sections 3 and 5.1 of `arXiv:2608.30604`:
1. Convergence, strict positivity, and global continuity of the partition functions `partFuncPlus`
   and `partFuncFour`.
2. Compactness reduction (`[-3, 10]`), attainment of dual minimizers, and `10`-Lipschitz continuity
   of `freeEnergyPlus` and `freeEnergyFour` on `[2.6, 4.1]`, establishing `ContinuousOn petkovA4 (Icc 0 1)`.
3. Existence and uniform positive lower bounds of the optimal 4-size Gibbs distribution `p_i*(T)`
   on `S_4 = {2, 3, 4, 5}`, plus the universal Gibbs upper bound on `S_+` for finite profiles.
4. **Lemma 5.1 (`petkovA4_uniform_margin`)**: For every `δ ∈ [0, 1]`,
   `petkovA4 δ ≥ log(200 / 153) + log(306 / 305) > log(200 / 153)` and `0 ≤ D_4(δ)`.
5. **Nonconstancy (`petkovA4_nonconstant`)**: `petkovA4` is nonconstant on `[0, 1]`, proved via the
   exact dyadic symmetry point `T = 7/2` (`δ_* = 2 / log 2 - 5/2 ∈ (0, 1)`) versus `δ = 1`.
-/

namespace JSP000506

open Finset Filter
open scoped Topology

/-! ### 1. Tilted Weights, Summability, Positivity, and Continuity -/

/-- Tilted Gaussian weight `w_i(λ) = exp(λ i - (log 2 / 2) i^2)` for `i : ℝ`. -/
noncomputable def tiltWeight (lam x : ℝ) : ℝ :=
  Real.exp (lam * x - (Real.log 2 / 2) * x ^ 2)

theorem tiltWeight_pos (lam x : ℝ) : 0 < tiltWeight lam x :=
  Real.exp_pos _

theorem partFuncPlus_eq_tsum (lam : ℝ) :
    partFuncPlus lam = ∑' k : ℕ, tiltWeight lam ((k : ℝ) - 1) :=
  rfl

theorem partFuncFour_eq_sum (lam : ℝ) :
    partFuncFour lam = ∑ i ∈ ({2, 3, 4, 5} : Finset ℤ), tiltWeight lam (i : ℝ) :=
  rfl

private lemma tiltWeight_le_geom {B : ℝ} (_hB : 0 ≤ B) {lam : ℝ} (hlam : |lam| ≤ B) (k : ℕ) :
    tiltWeight lam ((k : ℝ) - 1) ≤
      Real.exp ((B + 1) ^ 2 / (2 * Real.log 2) + 1) * (Real.exp (-1)) ^ k := by
  have hq : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set x : ℝ := (k : ℝ) - 1
  have hsq : 0 ≤ (Real.log 2 / 2) * (x - (lam + 1) / Real.log 2) ^ 2 := by positivity
  have hexp1 : lam * x - (Real.log 2 / 2) * x ^ 2 ≤
      (lam + 1) ^ 2 / (2 * Real.log 2) + 1 - (k : ℝ) := by
    have hid : lam * x - (Real.log 2 / 2) * x ^ 2 =
        (lam + 1) ^ 2 / (2 * Real.log 2) - x -
          (Real.log 2 / 2) * (x - (lam + 1) / Real.log 2) ^ 2 := by
      field_simp [hq.ne']
      ring
    have hx : x = (k : ℝ) - 1 := rfl
    linarith
  have hBsq : (lam + 1) ^ 2 ≤ (B + 1) ^ 2 := by
    have h1 := abs_le.mp hlam
    nlinarith
  have hexp2 : lam * x - (Real.log 2 / 2) * x ^ 2 ≤
      (B + 1) ^ 2 / (2 * Real.log 2) + 1 - (k : ℝ) := by
    have hdiv : (lam + 1) ^ 2 / (2 * Real.log 2) ≤ (B + 1) ^ 2 / (2 * Real.log 2) :=
      div_le_div_of_nonneg_right hBsq (by positivity)
    linarith
  calc
    tiltWeight lam x = Real.exp (lam * x - (Real.log 2 / 2) * x ^ 2) := rfl
    _ ≤ Real.exp ((B + 1) ^ 2 / (2 * Real.log 2) + 1 - (k : ℝ)) := Real.exp_le_exp.mpr hexp2
    _ = Real.exp ((B + 1) ^ 2 / (2 * Real.log 2) + 1) * (Real.exp (-1)) ^ k := by
      rw [← Real.exp_nat_mul, mul_neg_one, ← Real.exp_add]
      ring_nf

theorem summable_tiltWeight_plus (lam : ℝ) :
    Summable (fun k : ℕ => tiltWeight lam ((k : ℝ) - 1)) := by
  have hgeom : Summable (fun k : ℕ =>
      Real.exp ((|lam| + 1) ^ 2 / (2 * Real.log 2) + 1) * (Real.exp (-1)) ^ k) :=
    (summable_geometric_of_lt_one (Real.exp_pos (-1)).le
      (Real.exp_lt_one_iff.mpr (by norm_num))).mul_left _
  exact Summable.of_nonneg_of_le (fun k => (tiltWeight_pos lam _).le)
    (fun k => tiltWeight_le_geom (abs_nonneg lam) le_rfl k) hgeom

theorem partFuncPlus_pos (lam : ℝ) : 0 < partFuncPlus lam := by
  have h0 : tiltWeight lam ((1 : ℕ) - 1) ≤ partFuncPlus lam :=
    (summable_tiltWeight_plus lam).le_tsum 1 (fun k _ => (tiltWeight_pos lam _).le)
  exact (tiltWeight_pos lam _).trans_le h0

theorem partFuncFour_pos (lam : ℝ) : 0 < partFuncFour lam := by
  unfold partFuncFour
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) (by decide)

/-- Split `partFuncPlus lam` into low indices `{-1, 0, 1}`, core `S_4 = {2, 3, 4, 5}`, and high tail `i ≥ 6`. -/
noncomputable def lowWeightSum (lam : ℝ) : ℝ :=
  tiltWeight lam (-1) + tiltWeight lam 0 + tiltWeight lam 1

noncomputable def highWeightSum (lam : ℝ) : ℝ :=
  ∑' m : ℕ, tiltWeight lam ((m : ℝ) + 6)

theorem summable_highWeight (lam : ℝ) :
    Summable (fun m : ℕ => tiltWeight lam ((m : ℝ) + 6)) := by
  have heq : (fun m : ℕ => tiltWeight lam ((m : ℝ) + 6)) =
      fun m : ℕ => tiltWeight lam (((m + 7 : ℕ) : ℝ) - 1) := by
    funext m
    congr 1
    push_cast
    ring
  rw [heq]
  exact (summable_tiltWeight_plus lam).comp_injective (fun _ _ h => by omega)

theorem lowWeightSum_pos (lam : ℝ) : 0 < lowWeightSum lam := by
  unfold lowWeightSum
  linarith [tiltWeight_pos lam (-1), tiltWeight_pos lam 0, tiltWeight_pos lam 1]

theorem highWeightSum_pos (lam : ℝ) : 0 < highWeightSum lam := by
  have h0 : tiltWeight lam ((0 : ℕ) + 6) ≤ highWeightSum lam :=
    (summable_highWeight lam).le_tsum 0 (fun m _ => (tiltWeight_pos lam _).le)
  exact (tiltWeight_pos lam _).trans_le h0

theorem partFuncPlus_decomp (lam : ℝ) :
    partFuncPlus lam = lowWeightSum lam + partFuncFour lam + highWeightSum lam := by
  rw [partFuncPlus_eq_tsum, ← (summable_tiltWeight_plus lam).sum_add_tsum_nat_add 7]
  have hhead : ∑ k ∈ range 7, tiltWeight lam ((k : ℝ) - 1) =
      lowWeightSum lam + partFuncFour lam := by
    have h4 : ({2, 3, 4, 5} : Finset ℤ) =
        insert 2 (insert 3 (insert 4 {5})) := rfl
    rw [partFuncFour_eq_sum, h4]
    simp only [sum_range_succ, sum_range_zero, zero_add, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, sum_insert (by decide : (2 : ℤ) ∉ insert 3 (insert 4 ({5} : Finset ℤ))),
      sum_insert (by decide : (3 : ℤ) ∉ insert 4 ({5} : Finset ℤ)),
      sum_insert (by decide : (4 : ℤ) ∉ ({5} : Finset ℤ)), sum_singleton,
      Int.cast_ofNat, lowWeightSum]
    norm_num
    ring
  have htail : (∑' m : ℕ, tiltWeight lam (((m + 7 : ℕ) : ℝ) - 1)) = highWeightSum lam := by
    unfold highWeightSum
    refine tsum_congr fun m => ?_
    congr 1
    push_cast
    ring
  rw [hhead, htail]

theorem partFuncFour_le_partFuncPlus (lam : ℝ) :
    partFuncFour lam ≤ partFuncPlus lam := by
  rw [partFuncPlus_decomp]
  linarith [lowWeightSum_pos lam, highWeightSum_pos lam]

theorem continuous_partFuncPlus : Continuous partFuncPlus := by
  rw [continuous_iff_continuousAt]
  intro lam₀
  set B : ℝ := |lam₀| + 1
  have hB : 0 ≤ B := by positivity
  have hcontOn : ContinuousOn partFuncPlus (Set.Icc (-B) B) := by
    unfold partFuncPlus
    refine continuousOn_tsum
      (u := fun k : ℕ => Real.exp ((B + 1) ^ 2 / (2 * Real.log 2) + 1) * (Real.exp (-1)) ^ k)
      (fun k => by fun_prop) ?_ (fun k lam hlam => ?_)
    · exact (summable_geometric_of_lt_one (Real.exp_pos (-1)).le
        (Real.exp_lt_one_iff.mpr (by norm_num))).mul_left
          (Real.exp ((B + 1) ^ 2 / (2 * Real.log 2) + 1))
    · rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact tiltWeight_le_geom hB (abs_le.mpr hlam) k
  exact hcontOn.continuousAt
    (Icc_mem_nhds (by linarith [neg_abs_le lam₀]) (by linarith [le_abs_self lam₀]))

theorem continuous_partFuncFour : Continuous partFuncFour := by
  unfold partFuncFour
  fun_prop

/-! ### 2. Exact Dyadic Evaluation at `λ = (7/2) log 2` -/

private lemma partFuncFour_seven_halves_log_two :
    partFuncFour ((7 / 2 : ℝ) * Real.log 2) = 192 := by
  have h4 : ({2, 3, 4, 5} : Finset ℤ) = insert 2 (insert 3 (insert 4 {5})) := rfl
  rw [partFuncFour_eq_sum, h4]
  simp only [sum_insert (by decide : (2 : ℤ) ∉ insert 3 (insert 4 ({5} : Finset ℤ))),
    sum_insert (by decide : (3 : ℤ) ∉ insert 4 ({5} : Finset ℤ)),
    sum_insert (by decide : (4 : ℤ) ∉ ({5} : Finset ℤ)), sum_singleton,
    Int.cast_ofNat, tiltWeight]
  have h2 : (7 / 2 : ℝ) * Real.log 2 * 2 - Real.log 2 / 2 * 2 ^ 2 = (5 : ℕ) * Real.log 2 := by
    push_cast; ring
  have h3 : (7 / 2 : ℝ) * Real.log 2 * 3 - Real.log 2 / 2 * 3 ^ 2 = (6 : ℕ) * Real.log 2 := by
    push_cast; ring
  have h4' : (7 / 2 : ℝ) * Real.log 2 * 4 - Real.log 2 / 2 * 4 ^ 2 = (6 : ℕ) * Real.log 2 := by
    push_cast; ring
  have h5 : (7 / 2 : ℝ) * Real.log 2 * 5 - Real.log 2 / 2 * 5 ^ 2 = (5 : ℕ) * Real.log 2 := by
    push_cast; ring
  rw [h2, h3, h4', h5, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  norm_num

private lemma exp_pow_two_neg (m : ℕ) (c : ℝ) (hc : c = 6 * Real.log 2 - (m : ℝ) * Real.log 2) :
    Real.exp c = 64 * (2⁻¹ : ℝ) ^ m := by
  rw [hc, sub_eq_add_neg, Real.exp_add]
  have h6 : Real.exp (6 * Real.log 2) = 64 := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_num
  have hm : Real.exp (-((m : ℝ) * Real.log 2)) = (2⁻¹ : ℝ) ^ m := by
    rw [show -((m : ℝ) * Real.log 2) = (m : ℝ) * Real.log (2⁻¹) by rw [Real.log_inv]; ring,
      Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [h6, hm]

private lemma lowWeightSum_seven_halves_log_two :
    lowWeightSum ((7 / 2 : ℝ) * Real.log 2) = 64 * (145 / 1024) := by
  unfold lowWeightSum tiltWeight
  rw [exp_pow_two_neg 10 _ (by push_cast; ring),
      exp_pow_two_neg 6 _ (by push_cast; ring),
      exp_pow_two_neg 3 _ (by push_cast; ring)]
  norm_num

private lemma highWeightSum_seven_halves_log_two_le :
    highWeightSum ((7 / 2 : ℝ) * Real.log 2) ≤ 64 * (146 / 1024) := by
  let lam₀ : ℝ := (7 / 2 : ℝ) * Real.log 2
  rw [highWeightSum, ← (summable_highWeight lam₀).sum_add_tsum_nat_add 3]
  have hhead : ∑ m ∈ range 3, tiltWeight lam₀ ((m : ℝ) + 6) = 64 * (145 / 1024) := by
    simp only [sum_range_succ, sum_range_zero, zero_add, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, tiltWeight, lam₀]
    rw [exp_pow_two_neg 3 _ (by push_cast; ring),
        exp_pow_two_neg 6 _ (by push_cast; ring),
        exp_pow_two_neg 10 _ (by push_cast; ring)]
    norm_num
  have htail_term : ∀ j : ℕ, tiltWeight lam₀ (((j + 3 : ℕ) : ℝ) + 6) ≤
      64 * (1 / 32768 : ℝ) * (1 / 32 : ℝ) ^ j := by
    intro j
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hexp_le : lam₀ * (((j + 3 : ℕ) : ℝ) + 6) -
        Real.log 2 / 2 * (((j + 3 : ℕ) : ℝ) + 6) ^ 2 ≤
        6 * Real.log 2 - ((15 + 5 * j : ℕ) : ℝ) * Real.log 2 := by
      have hquad : 0 ≤ (((j : ℝ) ^ 2 + (j : ℝ)) / 2) * Real.log 2 := by positivity
      have hid : lam₀ * (((j + 3 : ℕ) : ℝ) + 6) -
          Real.log 2 / 2 * (((j + 3 : ℕ) : ℝ) + 6) ^ 2 =
          6 * Real.log 2 - ((15 + 5 * j : ℕ) : ℝ) * Real.log 2 -
            (((j : ℝ) ^ 2 + (j : ℝ)) / 2) * Real.log 2 := by
        dsimp [lam₀]
        push_cast
        ring
      linarith
    calc
      tiltWeight lam₀ (((j + 3 : ℕ) : ℝ) + 6)
          ≤ Real.exp (6 * Real.log 2 - ((15 + 5 * j : ℕ) : ℝ) * Real.log 2) :=
        Real.exp_le_exp.mpr hexp_le
      _ = 64 * (2⁻¹ : ℝ) ^ (15 + 5 * j) := exp_pow_two_neg (15 + 5 * j) _ rfl
      _ = 64 * (1 / 32768 : ℝ) * (1 / 32 : ℝ) ^ j := by
        rw [pow_add, pow_mul]
        norm_num
        ring
  have hgeom : Summable (fun j : ℕ => 64 * (1 / 32768 : ℝ) * (1 / 32 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have htail_le : (∑' j : ℕ, tiltWeight lam₀ (((j + 3 : ℕ) : ℝ) + 6)) ≤
      64 * (1 / 32768 : ℝ) * (1 - 1 / 32 : ℝ)⁻¹ := by
    calc
      (∑' j : ℕ, tiltWeight lam₀ (((j + 3 : ℕ) : ℝ) + 6))
          ≤ ∑' j : ℕ, 64 * (1 / 32768 : ℝ) * (1 / 32 : ℝ) ^ j :=
        ((summable_highWeight lam₀).comp_injective (fun _ _ h => by omega)).tsum_le_tsum
          htail_term hgeom
      _ = 64 * (1 / 32768 : ℝ) * (1 - 1 / 32 : ℝ)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  rw [hhead]
  linarith

private lemma partFuncPlus_seven_halves_log_two_le :
    partFuncPlus ((7 / 2 : ℝ) * Real.log 2) ≤ 192 * (1 + 291 / 3072) := by
  rw [partFuncPlus_decomp, lowWeightSum_seven_halves_log_two, partFuncFour_seven_halves_log_two]
  linarith [highWeightSum_seven_halves_log_two_le]

/-! ### 3. Compactness Reduction to `[-3, 10]` and `10`-Lipschitz Continuity -/

theorem targetDeficit_bounds {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    2.885 < targetDeficit δ ∧ targetDeficit δ < 3.886 := by
  unfold targetDeficit
  rcases hδ with ⟨h0, h1⟩
  have hq_lo := Real.log_two_gt_d9
  have hq_hi := Real.log_two_lt_d9
  have hdiv_lo : 2.885 < 2 / Real.log 2 := by
    rw [lt_div_iff₀ (by linarith)]
    nlinarith
  have hdiv_hi : 2 / Real.log 2 < 2.886 := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  constructor <;> linarith

theorem targetDeficit_mem_Icc {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    targetDeficit δ ∈ Set.Icc (2.6 : ℝ) 4.1 := by
  have hb := targetDeficit_bounds hδ
  exact ⟨by linarith, by linarith⟩

private lemma dualPlus_seven_halves_neg {T : ℝ} (hT : T ∈ Set.Icc (2.6 : ℝ) 4.1) :
    Real.log (partFuncPlus ((7 / 2 : ℝ) * Real.log 2)) -
      ((7 / 2 : ℝ) * Real.log 2) * T < 0 := by
  rcases hT with ⟨hT_lo, _⟩
  have hZ_lt : partFuncPlus ((7 / 2 : ℝ) * Real.log 2) < 256 := by
    linarith [partFuncPlus_seven_halves_log_two_le]
  have h256 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = (2 : ℝ) ^ (8 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlog : Real.log (partFuncPlus ((7 / 2 : ℝ) * Real.log 2)) < 8 * Real.log 2 := by
    rw [← h256]
    exact Real.log_lt_log (partFuncPlus_pos _) hZ_lt
  have hq : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

private lemma dualFour_seven_halves_neg {T : ℝ} (hT : T ∈ Set.Icc (2.6 : ℝ) 4.1) :
    Real.log (partFuncFour ((7 / 2 : ℝ) * Real.log 2)) -
      ((7 / 2 : ℝ) * Real.log 2) * T < 0 := by
  have hle : Real.log (partFuncFour ((7 / 2 : ℝ) * Real.log 2)) ≤
      Real.log (partFuncPlus ((7 / 2 : ℝ) * Real.log 2)) :=
    Real.log_le_log (partFuncFour_pos _) (partFuncFour_le_partFuncPlus _)
  linarith [dualPlus_seven_halves_neg hT]

private lemma dualPlus_pos_outside {T : ℝ} (hT : T ∈ Set.Icc (2.6 : ℝ) 4.1)
    {lam : ℝ} (hlam : lam ∉ Set.Icc (-3 : ℝ) 10) :
    0 < Real.log (partFuncPlus lam) - lam * T := by
  rcases hT with ⟨hT_lo, hT_hi⟩
  have hq_hi := Real.log_two_lt_d9
  by_cases hlt : lam < -3
  · have hw0 : 1 ≤ partFuncPlus lam := by
      rw [partFuncPlus_eq_tsum]
      have hle := (summable_tiltWeight_plus lam).le_tsum 1 (fun k _ => (tiltWeight_pos lam _).le)
      have h1 : (1 : ℝ) = tiltWeight lam (((1 : ℕ) : ℝ) - 1) := by
        unfold tiltWeight
        norm_num
      exact h1.trans_le hle
    have hlog : 0 ≤ Real.log (partFuncPlus lam) := Real.log_nonneg hw0
    nlinarith
  · have hgt : 10 < lam := by
      by_contra hle10
      exact hlam ⟨not_lt.mp hlt, not_lt.mp hle10⟩
    have hw5 : Real.exp (5 * lam - 25 / 2 * Real.log 2) ≤ partFuncPlus lam := by
      rw [partFuncPlus_eq_tsum]
      have hle := (summable_tiltWeight_plus lam).le_tsum 6 (fun k _ => (tiltWeight_pos lam _).le)
      have h6 : Real.exp (5 * lam - 25 / 2 * Real.log 2) =
          tiltWeight lam (((6 : ℕ) : ℝ) - 1) := by
        unfold tiltWeight
        congr 1
        norm_num
        ring
      exact h6.trans_le hle
    have hlog : 5 * lam - 25 / 2 * Real.log 2 ≤ Real.log (partFuncPlus lam) := by
      rw [← Real.log_exp (5 * lam - 25 / 2 * Real.log 2)]
      exact Real.log_le_log (Real.exp_pos _) hw5
    nlinarith

private lemma dualFour_pos_outside {T : ℝ} (hT : T ∈ Set.Icc (2.6 : ℝ) 4.1)
    {lam : ℝ} (hlam : lam ∉ Set.Icc (-3 : ℝ) 10) :
    0 < Real.log (partFuncFour lam) - lam * T := by
  rcases hT with ⟨hT_lo, hT_hi⟩
  have hq_hi := Real.log_two_lt_d9
  by_cases hlt : lam < -3
  · have hw2 : Real.exp (2 * lam - 2 * Real.log 2) ≤ partFuncFour lam := by
      rw [partFuncFour_eq_sum]
      have hmem : (2 : ℤ) ∈ ({2, 3, 4, 5} : Finset ℤ) := by decide
      have hle := Finset.single_le_sum (f := fun i : ℤ => tiltWeight lam (i : ℝ))
        (fun i _ => (tiltWeight_pos lam _).le) hmem
      have h2 : Real.exp (2 * lam - 2 * Real.log 2) = tiltWeight lam ((2 : ℤ) : ℝ) := by
        unfold tiltWeight
        congr 1
        norm_num
        ring
      exact h2.trans_le hle
    have hlog : 2 * lam - 2 * Real.log 2 ≤ Real.log (partFuncFour lam) := by
      rw [← Real.log_exp (2 * lam - 2 * Real.log 2)]
      exact Real.log_le_log (Real.exp_pos _) hw2
    nlinarith
  · have hgt : 10 < lam := by
      by_contra hle10
      exact hlam ⟨not_lt.mp hlt, not_lt.mp hle10⟩
    have hw5 : Real.exp (5 * lam - 25 / 2 * Real.log 2) ≤ partFuncFour lam := by
      rw [partFuncFour_eq_sum]
      have hmem : (5 : ℤ) ∈ ({2, 3, 4, 5} : Finset ℤ) := by decide
      have hle := Finset.single_le_sum (f := fun i : ℤ => tiltWeight lam (i : ℝ))
        (fun i _ => (tiltWeight_pos lam _).le) hmem
      have h5 : Real.exp (5 * lam - 25 / 2 * Real.log 2) = tiltWeight lam ((5 : ℤ) : ℝ) := by
        unfold tiltWeight
        congr 1
        norm_num
        ring
      exact h5.trans_le hle
    have hlog : 5 * lam - 25 / 2 * Real.log 2 ≤ Real.log (partFuncFour lam) := by
      rw [← Real.log_exp (5 * lam - 25 / 2 * Real.log 2)]
      exact Real.log_le_log (Real.exp_pos _) hw5
    nlinarith

/-- Attainment of the global dual minimizer for `freeEnergyPlus T` inside `[-3, 10]`. -/
theorem exists_min_dualPlus {T : ℝ} (hT : T ∈ Set.Icc (2.6 : ℝ) 4.1) :
    ∃ lam ∈ Set.Icc (-3 : ℝ) 10,
      freeEnergyPlus T = Real.log (partFuncPlus lam) - lam * T ∧
      ∀ μ : ℝ, Real.log (partFuncPlus lam) - lam * T ≤ Real.log (partFuncPlus μ) - μ * T := by
  let g : ℝ → ℝ := fun μ => Real.log (partFuncPlus μ) - μ * T
  have hcont : Continuous g :=
    (continuous_partFuncPlus.log fun μ => (partFuncPlus_pos μ).ne').sub
      (continuous_id.mul continuous_const)
  have hne : (Set.Icc (-3 : ℝ) 10).Nonempty := ⟨0, by norm_num⟩
  obtain ⟨lam, hlam_mem, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont.continuousOn
  have hlam₀_mem : (7 / 2 : ℝ) * Real.log 2 ∈ Set.Icc (-3 : ℝ) 10 := by
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_two_lt_d9
    constructor <;> linarith
  have hlam_neg : g lam < 0 :=
    (hmin hlam₀_mem).trans_lt (dualPlus_seven_halves_neg hT)
  have hall : ∀ μ : ℝ, g lam ≤ g μ := by
    intro μ
    by_cases hμ : μ ∈ Set.Icc (-3 : ℝ) 10
    · exact hmin hμ
    · exact hlam_neg.le.trans (dualPlus_pos_outside hT hμ).le
  refine ⟨lam, hlam_mem, ?_, hall⟩
  unfold freeEnergyPlus
  exact le_antisymm (ciInf_le ⟨g lam, Set.forall_mem_range.mpr hall⟩ lam) (le_ciInf hall)

/-- Attainment of the global dual minimizer for `freeEnergyFour T` inside `[-3, 10]`. -/
theorem exists_min_dualFour {T : ℝ} (hT : T ∈ Set.Icc (2.6 : ℝ) 4.1) :
    ∃ lam ∈ Set.Icc (-3 : ℝ) 10,
      freeEnergyFour T = Real.log (partFuncFour lam) - lam * T ∧
      ∀ μ : ℝ, Real.log (partFuncFour lam) - lam * T ≤ Real.log (partFuncFour μ) - μ * T := by
  let g : ℝ → ℝ := fun μ => Real.log (partFuncFour μ) - μ * T
  have hcont : Continuous g :=
    (continuous_partFuncFour.log fun μ => (partFuncFour_pos μ).ne').sub
      (continuous_id.mul continuous_const)
  have hne : (Set.Icc (-3 : ℝ) 10).Nonempty := ⟨0, by norm_num⟩
  obtain ⟨lam, hlam_mem, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont.continuousOn
  have hlam₀_mem : (7 / 2 : ℝ) * Real.log 2 ∈ Set.Icc (-3 : ℝ) 10 := by
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_two_lt_d9
    constructor <;> linarith
  have hlam_neg : g lam < 0 :=
    (hmin hlam₀_mem).trans_lt (dualFour_seven_halves_neg hT)
  have hall : ∀ μ : ℝ, g lam ≤ g μ := by
    intro μ
    by_cases hμ : μ ∈ Set.Icc (-3 : ℝ) 10
    · exact hmin hμ
    · exact hlam_neg.le.trans (dualFour_pos_outside hT hμ).le
  refine ⟨lam, hlam_mem, ?_, hall⟩
  unfold freeEnergyFour
  exact le_antisymm (ciInf_le ⟨g lam, Set.forall_mem_range.mpr hall⟩ lam) (le_ciInf hall)

theorem freeEnergyPlus_le_eval {T : ℝ} (hT : T ∈ Set.Icc (2.6 : ℝ) 4.1) (μ : ℝ) :
    freeEnergyPlus T ≤ Real.log (partFuncPlus μ) - μ * T := by
  rcases exists_min_dualPlus hT with ⟨lam, _, hfeq, hall⟩
  rw [hfeq]
  exact hall μ

theorem freeEnergyFour_le_eval {T : ℝ} (hT : T ∈ Set.Icc (2.6 : ℝ) 4.1) (μ : ℝ) :
    freeEnergyFour T ≤ Real.log (partFuncFour μ) - μ * T := by
  rcases exists_min_dualFour hT with ⟨lam, _, hfeq, hall⟩
  rw [hfeq]
  exact hall μ

/-- `10`-Lipschitz continuity of `freeEnergyPlus` on `[2.6, 4.1]`. -/
theorem abs_freeEnergyPlus_sub_le {T₁ T₂ : ℝ}
    (h₁ : T₁ ∈ Set.Icc (2.6 : ℝ) 4.1) (h₂ : T₂ ∈ Set.Icc (2.6 : ℝ) 4.1) :
    |freeEnergyPlus T₁ - freeEnergyPlus T₂| ≤ 10 * |T₁ - T₂| := by
  rcases exists_min_dualPlus h₁ with ⟨lam₁, hlam₁, hfeq₁, _⟩
  rcases exists_min_dualPlus h₂ with ⟨lam₂, hlam₂, hfeq₂, _⟩
  have hle1 : freeEnergyPlus T₁ - freeEnergyPlus T₂ ≤ lam₂ * (T₂ - T₁) := by
    have hu := freeEnergyPlus_le_eval h₁ lam₂
    linarith
  have hle2 : freeEnergyPlus T₂ - freeEnergyPlus T₁ ≤ lam₁ * (T₁ - T₂) := by
    have hu := freeEnergyPlus_le_eval h₂ lam₁
    linarith
  have habs1 : |lam₁| ≤ 10 := abs_le.mpr ⟨by linarith [hlam₁.1], hlam₁.2⟩
  have habs2 : |lam₂| ≤ 10 := abs_le.mpr ⟨by linarith [hlam₂.1], hlam₂.2⟩
  have hb1 : lam₂ * (T₂ - T₁) ≤ 10 * |T₁ - T₂| := by
    calc
      lam₂ * (T₂ - T₁) ≤ |lam₂ * (T₂ - T₁)| := le_abs_self _
      _ = |lam₂| * |T₁ - T₂| := by rw [abs_mul, abs_sub_comm]
      _ ≤ 10 * |T₁ - T₂| := mul_le_mul_of_nonneg_right habs2 (abs_nonneg _)
  have hb2 : lam₁ * (T₁ - T₂) ≤ 10 * |T₁ - T₂| := by
    calc
      lam₁ * (T₁ - T₂) ≤ |lam₁ * (T₁ - T₂)| := le_abs_self _
      _ = |lam₁| * |T₁ - T₂| := abs_mul _ _
      _ ≤ 10 * |T₁ - T₂| := mul_le_mul_of_nonneg_right habs1 (abs_nonneg _)
  rw [abs_le]
  constructor <;> linarith

/-- `10`-Lipschitz continuity of `freeEnergyFour` on `[2.6, 4.1]`. -/
theorem abs_freeEnergyFour_sub_le {T₁ T₂ : ℝ}
    (h₁ : T₁ ∈ Set.Icc (2.6 : ℝ) 4.1) (h₂ : T₂ ∈ Set.Icc (2.6 : ℝ) 4.1) :
    |freeEnergyFour T₁ - freeEnergyFour T₂| ≤ 10 * |T₁ - T₂| := by
  rcases exists_min_dualFour h₁ with ⟨lam₁, hlam₁, hfeq₁, _⟩
  rcases exists_min_dualFour h₂ with ⟨lam₂, hlam₂, hfeq₂, _⟩
  have hle1 : freeEnergyFour T₁ - freeEnergyFour T₂ ≤ lam₂ * (T₂ - T₁) := by
    have hu := freeEnergyFour_le_eval h₁ lam₂
    linarith
  have hle2 : freeEnergyFour T₂ - freeEnergyFour T₁ ≤ lam₁ * (T₁ - T₂) := by
    have hu := freeEnergyFour_le_eval h₂ lam₁
    linarith
  have habs1 : |lam₁| ≤ 10 := abs_le.mpr ⟨by linarith [hlam₁.1], hlam₁.2⟩
  have habs2 : |lam₂| ≤ 10 := abs_le.mpr ⟨by linarith [hlam₂.1], hlam₂.2⟩
  have hb1 : lam₂ * (T₂ - T₁) ≤ 10 * |T₁ - T₂| := by
    calc
      lam₂ * (T₂ - T₁) ≤ |lam₂ * (T₂ - T₁)| := le_abs_self _
      _ = |lam₂| * |T₁ - T₂| := by rw [abs_mul, abs_sub_comm]
      _ ≤ 10 * |T₁ - T₂| := mul_le_mul_of_nonneg_right habs2 (abs_nonneg _)
  have hb2 : lam₁ * (T₁ - T₂) ≤ 10 * |T₁ - T₂| := by
    calc
      lam₁ * (T₁ - T₂) ≤ |lam₁ * (T₁ - T₂)| := le_abs_self _
      _ = |lam₁| * |T₁ - T₂| := abs_mul _ _
      _ ≤ 10 * |T₁ - T₂| := mul_le_mul_of_nonneg_right habs1 (abs_nonneg _)
  rw [abs_le]
  constructor <;> linarith

theorem continuousOn_freeEnergyPlus :
    ContinuousOn freeEnergyPlus (Set.Icc (2.6 : ℝ) 4.1) := by
  rw [Metric.continuousOn_iff]
  intro T₁ h₁ ε hε
  refine ⟨ε / 11, by positivity, fun T₂ h₂ hdist => ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  calc
    |freeEnergyPlus T₂ - freeEnergyPlus T₁|
        ≤ 10 * |T₂ - T₁| := abs_freeEnergyPlus_sub_le h₂ h₁
    _ < 10 * (ε / 11) := mul_lt_mul_of_pos_left hdist (by norm_num)
    _ < ε := by linarith

theorem continuousOn_freeEnergyFour :
    ContinuousOn freeEnergyFour (Set.Icc (2.6 : ℝ) 4.1) := by
  rw [Metric.continuousOn_iff]
  intro T₁ h₁ ε hε
  refine ⟨ε / 11, by positivity, fun T₂ h₂ hdist => ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  calc
    |freeEnergyFour T₂ - freeEnergyFour T₁|
        ≤ 10 * |T₂ - T₁| := abs_freeEnergyFour_sub_le h₂ h₁
    _ < 10 * (ε / 11) := mul_lt_mul_of_pos_left hdist (by norm_num)
    _ < ε := by linarith

/-- Continuity of `petkovA4` on `[0, 1]`. -/
theorem continuousOn_petkovA4 : ContinuousOn petkovA4 (Set.Icc (0 : ℝ) 1) := by
  have hT : ContinuousOn targetDeficit (Set.Icc (0 : ℝ) 1) := by
    unfold targetDeficit
    fun_prop
  have hmaps : Set.MapsTo targetDeficit (Set.Icc (0 : ℝ) 1) (Set.Icc (2.6 : ℝ) 4.1) :=
    fun _ hδ => targetDeficit_mem_Icc hδ
  unfold petkovA4
  exact (continuousOn_const.sub (continuousOn_freeEnergyPlus.comp hT hmaps)).add
    (continuousOn_freeEnergyFour.comp hT hmaps)

/-! ### 4. Mean Map `M_{S_4}`, Optimal 4-Size Gibbs Profile, and Universal `S_+` Upper Bound -/

/-- Mean deficit `M_{S_4}(λ) = (∑_{i ∈ S_4} i w_i(λ)) / Z_{S_4}(λ)`. -/
noncomputable def meanFour (lam : ℝ) : ℝ :=
  (∑ i ∈ ({2, 3, 4, 5} : Finset ℤ), (i : ℝ) * tiltWeight lam (i : ℝ)) / partFuncFour lam

private lemma exp_le_one_add_add_sq {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have hb := Real.exp_bound hx (n := 2) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, pow_one, Nat.factorial_one, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.factorial_two,
    Nat.cast_ofNat] at hb
  have habs_sq : |x| ^ 2 = x ^ 2 := sq_abs x
  rw [habs_sq] at hb
  have h1 := (abs_le.mp hb).2
  nlinarith [sq_nonneg x]

/-- First-order optimality condition: any global minimizer of `μ ↦ log Z_{S_4}(μ) - μ T` satisfies
`meanFour lam = T` (proved directly via quadratic Taylor remainder without calculus imports). -/
theorem meanFour_eq_of_isMin {T lam : ℝ}
    (hall : ∀ μ : ℝ, Real.log (partFuncFour lam) - lam * T ≤
      Real.log (partFuncFour μ) - μ * T) :
    meanFour lam = T := by
  by_contra hne
  set Δ : ℝ := meanFour lam - T
  have hΔ_ne : Δ ≠ 0 := sub_ne_zero.mpr hne
  have hZpos : 0 < partFuncFour lam := partFuncFour_pos lam
  by_cases hpos : 0 < Δ
  · set ε : ℝ := min (1 / 10) (Δ / 50)
    have hε_pos : 0 < ε := lt_min (by norm_num) (by positivity)
    have hε_le10 : ε ≤ 1 / 10 := min_le_left _ _
    have hε_leΔ : ε ≤ Δ / 50 := min_le_right _ _
    have hZbound : partFuncFour (lam - ε) ≤
        partFuncFour lam * (1 - ε * meanFour lam + 25 * ε ^ 2) := by
      have hterm : ∀ i ∈ ({2, 3, 4, 5} : Finset ℤ),
          tiltWeight (lam - ε) (i : ℝ) ≤
            tiltWeight lam (i : ℝ) * (1 - ε * (i : ℝ) + 25 * ε ^ 2) := by
        intro i hi
        have hi_b : (2 : ℝ) ≤ (i : ℝ) ∧ (i : ℝ) ≤ 5 := by
          fin_cases hi <;> norm_num
        have hsplit : tiltWeight (lam - ε) (i : ℝ) =
            tiltWeight lam (i : ℝ) * Real.exp (-(ε * (i : ℝ))) := by
          unfold tiltWeight
          rw [← Real.exp_add]
          congr 1
          ring
        have habs : |-(ε * (i : ℝ))| ≤ 1 := by
          rw [abs_neg, abs_of_pos (mul_pos hε_pos (by linarith [hi_b.1]))]
          nlinarith [hi_b.2]
        have hexp := exp_le_one_add_add_sq habs
        have hi_sq : (i : ℝ) ^ 2 ≤ 25 := by nlinarith [hi_b.1, hi_b.2]
        have hsq25 : (-(ε * (i : ℝ))) ^ 2 ≤ 25 * ε ^ 2 := by
          calc
            (-(ε * (i : ℝ))) ^ 2 = ε ^ 2 * (i : ℝ) ^ 2 := by ring
            _ ≤ ε ^ 2 * 25 := mul_le_mul_of_nonneg_left hi_sq (sq_nonneg ε)
            _ = 25 * ε ^ 2 := by ring
        rw [hsplit]
        exact mul_le_mul_of_nonneg_left (by linarith) (tiltWeight_pos _ _).le
      calc
        partFuncFour (lam - ε)
            ≤ ∑ i ∈ ({2, 3, 4, 5} : Finset ℤ),
                tiltWeight lam (i : ℝ) * (1 - ε * (i : ℝ) + 25 * ε ^ 2) :=
          Finset.sum_le_sum hterm
        _ = partFuncFour lam -
              ε * (∑ i ∈ ({2, 3, 4, 5} : Finset ℤ), (i : ℝ) * tiltWeight lam (i : ℝ)) +
              25 * ε ^ 2 * partFuncFour lam := by
          have hlin : ∀ i : ℤ, tiltWeight lam (i : ℝ) * (1 - ε * (i : ℝ) + 25 * ε ^ 2) =
              tiltWeight lam (i : ℝ) - ε * ((i : ℝ) * tiltWeight lam (i : ℝ)) +
                25 * ε ^ 2 * tiltWeight lam (i : ℝ) := fun _ => by ring
          simp_rw [hlin, sum_add_distrib, sum_sub_distrib, ← mul_sum, partFuncFour_eq_sum]
        _ = partFuncFour lam * (1 - ε * meanFour lam + 25 * ε ^ 2) := by
          unfold meanFour
          field_simp [hZpos.ne']
    have hfactor_pos : 0 < 1 - ε * meanFour lam + 25 * ε ^ 2 :=
      pos_of_mul_pos_right ((partFuncFour_pos (lam - ε)).trans_le hZbound) hZpos.le
    have hlog_le : Real.log (partFuncFour (lam - ε)) ≤
        Real.log (partFuncFour lam) - ε * meanFour lam + 25 * ε ^ 2 := by
      calc
        Real.log (partFuncFour (lam - ε))
            ≤ Real.log (partFuncFour lam * (1 - ε * meanFour lam + 25 * ε ^ 2)) :=
          Real.log_le_log (partFuncFour_pos _) hZbound
        _ = Real.log (partFuncFour lam) + Real.log (1 - ε * meanFour lam + 25 * ε ^ 2) :=
          Real.log_mul hZpos.ne' hfactor_pos.ne'
        _ ≤ Real.log (partFuncFour lam) + (-ε * meanFour lam + 25 * ε ^ 2) := by
          linarith [Real.log_le_sub_one_of_pos hfactor_pos]
        _ = Real.log (partFuncFour lam) - ε * meanFour lam + 25 * ε ^ 2 := by ring
    have hmin_ineq := hall (lam - ε)
    have hcontra : ε * Δ ≤ 25 * ε ^ 2 := by
      dsimp [Δ]
      linarith
    nlinarith
  · have hneg : Δ < 0 := lt_of_le_of_ne (not_lt.mp hpos) hΔ_ne
    set ε : ℝ := min (1 / 10) ((-Δ) / 50)
    have hε_pos : 0 < ε := lt_min (by norm_num) (by linarith)
    have hε_le10 : ε ≤ 1 / 10 := min_le_left _ _
    have hε_leΔ : ε ≤ (-Δ) / 50 := min_le_right _ _
    have hZbound : partFuncFour (lam + ε) ≤
        partFuncFour lam * (1 + ε * meanFour lam + 25 * ε ^ 2) := by
      have hterm : ∀ i ∈ ({2, 3, 4, 5} : Finset ℤ),
          tiltWeight (lam + ε) (i : ℝ) ≤
            tiltWeight lam (i : ℝ) * (1 + ε * (i : ℝ) + 25 * ε ^ 2) := by
        intro i hi
        have hi_b : (2 : ℝ) ≤ (i : ℝ) ∧ (i : ℝ) ≤ 5 := by
          fin_cases hi <;> norm_num
        have hsplit : tiltWeight (lam + ε) (i : ℝ) =
            tiltWeight lam (i : ℝ) * Real.exp (ε * (i : ℝ)) := by
          unfold tiltWeight
          rw [← Real.exp_add]
          congr 1
          ring
        have habs : |ε * (i : ℝ)| ≤ 1 := by
          rw [abs_of_pos (mul_pos hε_pos (by linarith [hi_b.1]))]
          nlinarith [hi_b.2]
        have hexp := exp_le_one_add_add_sq habs
        have hi_sq : (i : ℝ) ^ 2 ≤ 25 := by nlinarith [hi_b.1, hi_b.2]
        have hsq25 : (ε * (i : ℝ)) ^ 2 ≤ 25 * ε ^ 2 := by
          calc
            (ε * (i : ℝ)) ^ 2 = ε ^ 2 * (i : ℝ) ^ 2 := by ring
            _ ≤ ε ^ 2 * 25 := mul_le_mul_of_nonneg_left hi_sq (sq_nonneg ε)
            _ = 25 * ε ^ 2 := by ring
        rw [hsplit]
        exact mul_le_mul_of_nonneg_left (by linarith) (tiltWeight_pos _ _).le
      calc
        partFuncFour (lam + ε)
            ≤ ∑ i ∈ ({2, 3, 4, 5} : Finset ℤ),
                tiltWeight lam (i : ℝ) * (1 + ε * (i : ℝ) + 25 * ε ^ 2) :=
          Finset.sum_le_sum hterm
        _ = partFuncFour lam +
              ε * (∑ i ∈ ({2, 3, 4, 5} : Finset ℤ), (i : ℝ) * tiltWeight lam (i : ℝ)) +
              25 * ε ^ 2 * partFuncFour lam := by
          have hlin : ∀ i : ℤ, tiltWeight lam (i : ℝ) * (1 + ε * (i : ℝ) + 25 * ε ^ 2) =
              tiltWeight lam (i : ℝ) + ε * ((i : ℝ) * tiltWeight lam (i : ℝ)) +
                25 * ε ^ 2 * tiltWeight lam (i : ℝ) := fun _ => by ring
          simp_rw [hlin, sum_add_distrib, ← mul_sum, partFuncFour_eq_sum]
        _ = partFuncFour lam * (1 + ε * meanFour lam + 25 * ε ^ 2) := by
          unfold meanFour
          field_simp [hZpos.ne']
    have hfactor_pos : 0 < 1 + ε * meanFour lam + 25 * ε ^ 2 :=
      pos_of_mul_pos_right ((partFuncFour_pos (lam + ε)).trans_le hZbound) hZpos.le
    have hlog_le : Real.log (partFuncFour (lam + ε)) ≤
        Real.log (partFuncFour lam) + ε * meanFour lam + 25 * ε ^ 2 := by
      calc
        Real.log (partFuncFour (lam + ε))
            ≤ Real.log (partFuncFour lam * (1 + ε * meanFour lam + 25 * ε ^ 2)) :=
          Real.log_le_log (partFuncFour_pos _) hZbound
        _ = Real.log (partFuncFour lam) + Real.log (1 + ε * meanFour lam + 25 * ε ^ 2) :=
          Real.log_mul hZpos.ne' hfactor_pos.ne'
        _ ≤ Real.log (partFuncFour lam) + (ε * meanFour lam + 25 * ε ^ 2) := by
          linarith [Real.log_le_sub_one_of_pos hfactor_pos]
        _ = Real.log (partFuncFour lam) + ε * meanFour lam + 25 * ε ^ 2 := by ring
    have hmin_ineq := hall (lam + ε)
    have hcontra : ε * (-Δ) ≤ 25 * ε ^ 2 := by
      dsimp [Δ]
      linarith
    nlinarith

/-- Strict monotonicity of `meanFour` on `ℝ` (proved directly by pairwise weight comparison). -/
theorem strictMono_meanFour : StrictMono meanFour := by
  intro lam₁ lam₂ hlt
  unfold meanFour
  have hZ₁ : 0 < partFuncFour lam₁ := partFuncFour_pos lam₁
  have hZ₂ : 0 < partFuncFour lam₂ := partFuncFour_pos lam₂
  rw [div_lt_div_iff₀ hZ₁ hZ₂]
  set S : Finset ℤ := {2, 3, 4, 5}
  have hdiff :
      (∑ i ∈ S, (i : ℝ) * tiltWeight lam₂ (i : ℝ)) * partFuncFour lam₁ -
      (∑ i ∈ S, (i : ℝ) * tiltWeight lam₁ (i : ℝ)) * partFuncFour lam₂ =
      (1 / 2 : ℝ) * ∑ i ∈ S, ∑ j ∈ S,
        ((i : ℝ) - (j : ℝ)) *
          (tiltWeight lam₂ (i : ℝ) * tiltWeight lam₁ (j : ℝ) -
           tiltWeight lam₁ (i : ℝ) * tiltWeight lam₂ (j : ℝ)) := by
    have h4 : S = insert 2 (insert 3 (insert 4 {5})) := rfl
    rw [partFuncFour_eq_sum, partFuncFour_eq_sum]
    change (∑ i ∈ S, (i : ℝ) * tiltWeight lam₂ (i : ℝ)) * (∑ j ∈ S, tiltWeight lam₁ (j : ℝ)) -
      (∑ i ∈ S, (i : ℝ) * tiltWeight lam₁ (i : ℝ)) * (∑ j ∈ S, tiltWeight lam₂ (j : ℝ)) = _
    rw [h4]
    simp only [sum_insert (by decide : (2 : ℤ) ∉ insert 3 (insert 4 ({5} : Finset ℤ))),
      sum_insert (by decide : (3 : ℤ) ∉ insert 4 ({5} : Finset ℤ)),
      sum_insert (by decide : (4 : ℤ) ∉ ({5} : Finset ℤ)), sum_singleton]
    ring
  have hterm_nonneg : ∀ i ∈ S, ∀ j ∈ S,
      0 ≤ ((i : ℝ) - (j : ℝ)) *
          (tiltWeight lam₂ (i : ℝ) * tiltWeight lam₁ (j : ℝ) -
           tiltWeight lam₁ (i : ℝ) * tiltWeight lam₂ (j : ℝ)) := by
    intro i _ j _
    have hprod1 : tiltWeight lam₂ (i : ℝ) * tiltWeight lam₁ (j : ℝ) =
        Real.exp ((lam₁ * (i : ℝ) + lam₁ * (j : ℝ) -
          (Real.log 2 / 2) * ((i : ℝ) ^ 2 + (j : ℝ) ^ 2)) + (lam₂ - lam₁) * (i : ℝ)) := by
      unfold tiltWeight
      rw [← Real.exp_add]
      congr 1
      ring
    have hprod2 : tiltWeight lam₁ (i : ℝ) * tiltWeight lam₂ (j : ℝ) =
        Real.exp ((lam₁ * (i : ℝ) + lam₁ * (j : ℝ) -
          (Real.log 2 / 2) * ((i : ℝ) ^ 2 + (j : ℝ) ^ 2)) + (lam₂ - lam₁) * (j : ℝ)) := by
      unfold tiltWeight
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hprod1, hprod2]
    rcases lt_trichotomy (i : ℝ) (j : ℝ) with hij | hij | hij
    · have hexp_lt : Real.exp ((lam₁ * (i : ℝ) + lam₁ * (j : ℝ) -
          (Real.log 2 / 2) * ((i : ℝ) ^ 2 + (j : ℝ) ^ 2)) + (lam₂ - lam₁) * (i : ℝ)) <
          Real.exp ((lam₁ * (i : ℝ) + lam₁ * (j : ℝ) -
          (Real.log 2 / 2) * ((i : ℝ) ^ 2 + (j : ℝ) ^ 2)) + (lam₂ - lam₁) * (j : ℝ)) :=
        Real.exp_lt_exp.mpr (by nlinarith)
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    · rw [hij]
      ring_nf
      exact le_rfl
    · have hexp_gt : Real.exp ((lam₁ * (i : ℝ) + lam₁ * (j : ℝ) -
          (Real.log 2 / 2) * ((i : ℝ) ^ 2 + (j : ℝ) ^ 2)) + (lam₂ - lam₁) * (j : ℝ)) <
          Real.exp ((lam₁ * (i : ℝ) + lam₁ * (j : ℝ) -
          (Real.log 2 / 2) * ((i : ℝ) ^ 2 + (j : ℝ) ^ 2)) + (lam₂ - lam₁) * (i : ℝ)) :=
        Real.exp_lt_exp.mpr (by nlinarith)
      exact mul_nonneg (by linarith) (by linarith)
  have hstrict_pair : 0 < ((3 : ℤ) - (2 : ℤ) : ℝ) *
      (tiltWeight lam₂ (3 : ℤ) * tiltWeight lam₁ (2 : ℤ) -
       tiltWeight lam₁ (3 : ℤ) * tiltWeight lam₂ (2 : ℤ)) := by
    have hprod1 : tiltWeight lam₂ 3 * tiltWeight lam₁ 2 =
        Real.exp ((lam₁ * 3 + lam₁ * 2 - (Real.log 2 / 2) * (3 ^ 2 + 2 ^ 2)) +
          (lam₂ - lam₁) * 3) := by
      unfold tiltWeight; rw [← Real.exp_add]; congr 1; ring
    have hprod2 : tiltWeight lam₁ 3 * tiltWeight lam₂ 2 =
        Real.exp ((lam₁ * 3 + lam₁ * 2 - (Real.log 2 / 2) * (3 ^ 2 + 2 ^ 2)) +
          (lam₂ - lam₁) * 2) := by
      unfold tiltWeight; rw [← Real.exp_add]; congr 1; ring
    norm_num
    rw [hprod1, hprod2]
    linarith [Real.exp_lt_exp.mpr (show (lam₁ * 3 + lam₁ * 2 -
        (Real.log 2 / 2) * (3 ^ 2 + 2 ^ 2)) + (lam₂ - lam₁) * 2 <
        (lam₁ * 3 + lam₁ * 2 - (Real.log 2 / 2) * (3 ^ 2 + 2 ^ 2)) +
        (lam₂ - lam₁) * 3 by linarith)]
  have hsum_pos : 0 < ∑ i ∈ S, ∑ j ∈ S,
      ((i : ℝ) - (j : ℝ)) *
        (tiltWeight lam₂ (i : ℝ) * tiltWeight lam₁ (j : ℝ) -
         tiltWeight lam₁ (i : ℝ) * tiltWeight lam₂ (j : ℝ)) := by
    have h3 : (3 : ℤ) ∈ S := by decide
    have h2 : (2 : ℤ) ∈ S := by decide
    have hinner := Finset.single_le_sum (fun j hj => hterm_nonneg 3 h3 j hj) h2
    have houter := Finset.single_le_sum
      (fun i hi => Finset.sum_nonneg fun j hj => hterm_nonneg i hi j hj) h3
    linarith
  linarith

/-- Optimal 4-size primal Gibbs probability distribution `p_i*(T)` on `S_4 = {2, 3, 4, 5}` for
any `T ∈ [2.6, 4.1]`, with explicit uniform positive lower bound `p_i ≥ 10 ^ (-35)`. -/
theorem exists_optimal_gibbs_four {T : ℝ} (hT : T ∈ Set.Icc (2.6 : ℝ) 4.1) :
    ∃ p : ℤ → ℝ,
      (∀ i ∈ ({2, 3, 4, 5} : Finset ℤ), (1 / 10 ^ 35 : ℝ) ≤ p i) ∧
      (∑ i ∈ ({2, 3, 4, 5} : Finset ℤ), p i = 1) ∧
      (∑ i ∈ ({2, 3, 4, 5} : Finset ℤ), (i : ℝ) * p i = T) ∧
      (∑ i ∈ ({2, 3, 4, 5} : Finset ℤ),
        p i * (-(Real.log 2 / 2) * (i : ℝ) ^ 2 - Real.log (p i)) = freeEnergyFour T) := by
  obtain ⟨lam, hlam_mem, hfeq, hall⟩ := exists_min_dualFour hT
  have hmean : meanFour lam = T := meanFour_eq_of_isMin hall
  have hZpos : 0 < partFuncFour lam := partFuncFour_pos lam
  let p : ℤ → ℝ := fun i => tiltWeight lam (i : ℝ) / partFuncFour lam
  have hp_pos : ∀ i : ℤ, 0 < p i := fun i => div_pos (tiltWeight_pos lam _) hZpos
  have hp_sum : ∑ i ∈ ({2, 3, 4, 5} : Finset ℤ), p i = 1 := by
    dsimp [p]
    rw [← Finset.sum_div, ← partFuncFour_eq_sum, div_self hZpos.ne']
  have hp_mean : ∑ i ∈ ({2, 3, 4, 5} : Finset ℤ), (i : ℝ) * p i = T := by
    dsimp [p]
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    exact hmean
  have hp_ent : ∑ i ∈ ({2, 3, 4, 5} : Finset ℤ),
      p i * (-(Real.log 2 / 2) * (i : ℝ) ^ 2 - Real.log (p i)) = freeEnergyFour T := by
    have hterm : ∀ i ∈ ({2, 3, 4, 5} : Finset ℤ),
        p i * (-(Real.log 2 / 2) * (i : ℝ) ^ 2 - Real.log (p i)) =
          p i * Real.log (partFuncFour lam) - lam * ((i : ℝ) * p i) := by
      intro i _
      have hlogp : Real.log (p i) =
          lam * (i : ℝ) - (Real.log 2 / 2) * (i : ℝ) ^ 2 - Real.log (partFuncFour lam) := by
        dsimp [p, tiltWeight]
        rw [Real.log_div (Real.exp_pos _).ne' hZpos.ne', Real.log_exp]
      rw [hlogp]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      hp_sum, one_mul, hp_mean, hfeq]
  have hp_lb : ∀ i ∈ ({2, 3, 4, 5} : Finset ℤ), (1 / 10 ^ 35 : ℝ) ≤ p i := by
    intro i hi
    have hi_b : (2 : ℝ) ≤ (i : ℝ) ∧ (i : ℝ) ≤ 5 := by
      fin_cases hi <;> norm_num
    have hq_hi := Real.log_two_lt_d9
    have hnum_ge : Real.exp (-24) ≤ tiltWeight lam (i : ℝ) := by
      unfold tiltWeight
      apply Real.exp_le_exp.mpr
      nlinarith [hlam_mem.1, hlam_mem.2, hi_b.1, hi_b.2]
    have hden_le : partFuncFour lam ≤ 4 * Real.exp 50 := by
      unfold partFuncFour
      have hle_each : ∀ j ∈ ({2, 3, 4, 5} : Finset ℤ),
          Real.exp (lam * (j : ℝ) - (Real.log 2 / 2) * (j : ℝ) ^ 2) ≤ Real.exp 50 := by
        intro j hj
        have hj_b : (2 : ℝ) ≤ (j : ℝ) ∧ (j : ℝ) ≤ 5 := by
          fin_cases hj <;> norm_num
        have hq_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hsq : 0 ≤ (Real.log 2 / 2) * (j : ℝ) ^ 2 := by positivity
        exact Real.exp_le_exp.mpr (by nlinarith [hlam_mem.1, hlam_mem.2, hj_b.1, hj_b.2])
      calc
        partFuncFour lam ≤ ∑ _ ∈ ({2, 3, 4, 5} : Finset ℤ), Real.exp 50 :=
          Finset.sum_le_sum hle_each
        _ = 4 * Real.exp 50 := by norm_num
    have hexp74 : 4 * Real.exp 74 ≤ 10 ^ 35 := by
      have he_le : Real.exp 1 ≤ 11 / 4 := by linarith [Real.exp_one_lt_d9]
      have h74 : Real.exp 74 ≤ (11 / 4 : ℝ) ^ 74 := by
        rw [show (74 : ℝ) = ((74 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
        exact pow_le_pow_left₀ (Real.exp_pos 1).le he_le 74
      calc
        4 * Real.exp 74 ≤ 4 * (11 / 4 : ℝ) ^ 74 := by linarith
        _ ≤ 10 ^ 35 := by norm_num
    dsimp [p]
    rw [div_le_div_iff₀ (by positivity) hZpos]
    calc
      1 * partFuncFour lam ≤ 4 * Real.exp 50 := by linarith
      _ = (4 * Real.exp 74) * Real.exp (-24) := by
        rw [mul_assoc, ← Real.exp_add]
        norm_num
      _ ≤ (10 ^ 35 : ℝ) * tiltWeight lam (i : ℝ) :=
        mul_le_mul hexp74 hnum_ge (Real.exp_pos _).le (by positivity)
      _ = tiltWeight lam (i : ℝ) * 10 ^ 35 := mul_comm _ _
  exact ⟨p, hp_lb, hp_sum, hp_mean, hp_ent⟩

/-- **Universal Gibbs upper bound on `S_+`**: for any finite subset `I : Finset ℕ` (`i = k - 1 ≥ -1`)
and probability weights `p : ℕ → ℝ` (`0 ≤ p k`, `∑_{k ∈ I} p k = 1`) with mean
`T = ∑_{k ∈ I} (k - 1) p_k`, the Gaussian-penalized entropy is at most `freeEnergyPlus T`. -/
theorem gibbs_upper_bound_plus (I : Finset ℕ) (p : ℕ → ℝ)
    (hp_nonneg : ∀ k ∈ I, 0 ≤ p k)
    (hp_sum : ∑ k ∈ I, p k = 1) :
    (∑ k ∈ I, if p k = 0 then 0
      else p k * (-(Real.log 2 / 2) * ((k : ℝ) - 1) ^ 2 - Real.log (p k))) ≤
      freeEnergyPlus (∑ k ∈ I, ((k : ℝ) - 1) * p k) := by
  unfold freeEnergyPlus
  refine le_ciInf fun lam => ?_
  have hZpos : 0 < partFuncPlus lam := partFuncPlus_pos lam
  let q : ℕ → ℝ := fun k => tiltWeight lam ((k : ℝ) - 1) / partFuncPlus lam
  have hq_pos : ∀ k : ℕ, 0 < q k := fun k => div_pos (tiltWeight_pos lam _) hZpos
  have hq_sum_le : ∑ k ∈ I, q k ≤ 1 := by
    dsimp [q]
    rw [← Finset.sum_div, div_le_one hZpos]
    exact (summable_tiltWeight_plus lam).sum_le_tsum I (fun k _ => (tiltWeight_pos lam _).le)
  have hterm : ∀ k ∈ I,
      (if p k = 0 then 0
        else p k * (-(Real.log 2 / 2) * ((k : ℝ) - 1) ^ 2 - Real.log (p k))) ≤
      p k * Real.log (partFuncPlus lam) - lam * (((k : ℝ) - 1) * p k) + (q k - p k) := by
    intro k hk
    by_cases hpk0 : p k = 0
    · simp [hpk0, (hq_pos k).le]
    · have hpk_pos : 0 < p k := lt_of_le_of_ne (hp_nonneg k hk) (Ne.symm hpk0)
      simp only [hpk0, ↓reduceIte]
      have hlogq : Real.log (q k) =
          lam * ((k : ℝ) - 1) - (Real.log 2 / 2) * ((k : ℝ) - 1) ^ 2 -
            Real.log (partFuncPlus lam) := by
        dsimp [q, tiltWeight]
        rw [Real.log_div (Real.exp_pos _).ne' hZpos.ne', Real.log_exp]
      have hkl : Real.log (q k / p k) ≤ q k / p k - 1 :=
        Real.log_le_sub_one_of_pos (div_pos (hq_pos k) hpk_pos)
      have hmul := mul_le_mul_of_nonneg_left hkl hpk_pos.le
      rw [Real.log_div (hq_pos k).ne' hpk_pos.ne'] at hmul
      have hrhs : p k * (q k / p k - 1) = q k - p k := by
        field_simp [hpk_pos.ne']
      rw [hrhs, hlogq] at hmul
      linarith
  calc
    (∑ k ∈ I, if p k = 0 then 0
      else p k * (-(Real.log 2 / 2) * ((k : ℝ) - 1) ^ 2 - Real.log (p k)))
        ≤ ∑ k ∈ I, (p k * Real.log (partFuncPlus lam) -
            lam * (((k : ℝ) - 1) * p k) + (q k - p k)) := Finset.sum_le_sum hterm
    _ = (∑ k ∈ I, p k) * Real.log (partFuncPlus lam) -
          lam * (∑ k ∈ I, ((k : ℝ) - 1) * p k) + (∑ k ∈ I, q k - ∑ k ∈ I, p k) := by
      simp_rw [sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum]
    _ ≤ Real.log (partFuncPlus lam) - lam * (∑ k ∈ I, ((k : ℝ) - 1) * p k) := by
      rw [hp_sum, one_mul]
      linarith

/-! ### 5. Lemma 5.1: Uniform `log(200 / 153)` Entropy Certificate -/

/-- Low omitted-ratio `R_low(λ) = lowWeightSum(λ) / partFuncFour(λ)`. -/
noncomputable def ratioLow (lam : ℝ) : ℝ :=
  lowWeightSum lam / partFuncFour lam

/-- High omitted-ratio `R_high(λ) = highWeightSum(λ) / partFuncFour(λ)`. -/
noncomputable def ratioHigh (lam : ℝ) : ℝ :=
  highWeightSum lam / partFuncFour lam

theorem antitone_ratioLow : Antitone ratioLow := by
  intro lam₁ lam₂ hle
  unfold ratioLow
  rw [div_le_div_iff₀ (partFuncFour_pos lam₂) (partFuncFour_pos lam₁)]
  have hlow_le : lowWeightSum lam₂ ≤ lowWeightSum lam₁ * Real.exp (lam₂ - lam₁) := by
    unfold lowWeightSum
    have h1 : ∀ x : ℝ, x ≤ 1 → tiltWeight lam₂ x ≤ tiltWeight lam₁ x * Real.exp (lam₂ - lam₁) := by
      intro x hx
      unfold tiltWeight
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith)
    linarith [h1 (-1) (by norm_num), h1 0 (by norm_num), h1 1 le_rfl]
  have hfour_ge : partFuncFour lam₁ * Real.exp (2 * (lam₂ - lam₁)) ≤ partFuncFour lam₂ := by
    rw [partFuncFour_eq_sum, partFuncFour_eq_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi2 : (2 : ℝ) ≤ (i : ℝ) := by fin_cases hi <;> norm_num
    unfold tiltWeight
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hexp_le : Real.exp (lam₂ - lam₁) ≤ Real.exp (2 * (lam₂ - lam₁)) :=
    Real.exp_le_exp.mpr (by linarith)
  calc
    lowWeightSum lam₂ * partFuncFour lam₁
        ≤ (lowWeightSum lam₁ * Real.exp (lam₂ - lam₁)) * partFuncFour lam₁ :=
      mul_le_mul_of_nonneg_right hlow_le (partFuncFour_pos lam₁).le
    _ = lowWeightSum lam₁ * (partFuncFour lam₁ * Real.exp (lam₂ - lam₁)) := by ring
    _ ≤ lowWeightSum lam₁ * (partFuncFour lam₁ * Real.exp (2 * (lam₂ - lam₁))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hexp_le (partFuncFour_pos lam₁).le) (lowWeightSum_pos lam₁).le
    _ ≤ lowWeightSum lam₁ * partFuncFour lam₂ :=
      mul_le_mul_of_nonneg_left hfour_ge (lowWeightSum_pos lam₁).le

theorem monotone_ratioHigh : Monotone ratioHigh := by
  intro lam₁ lam₂ hle
  unfold ratioHigh
  rw [div_le_div_iff₀ (partFuncFour_pos lam₁) (partFuncFour_pos lam₂)]
  have hfour_le : partFuncFour lam₂ ≤ partFuncFour lam₁ * Real.exp (5 * (lam₂ - lam₁)) := by
    rw [partFuncFour_eq_sum, partFuncFour_eq_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi5 : (i : ℝ) ≤ 5 := by fin_cases hi <;> norm_num
    unfold tiltWeight
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hhigh_ge : highWeightSum lam₁ * Real.exp (6 * (lam₂ - lam₁)) ≤ highWeightSum lam₂ := by
    unfold highWeightSum
    rw [← tsum_mul_right]
    refine ((summable_highWeight lam₁).mul_right _).tsum_le_tsum (fun m => ?_)
      (summable_highWeight lam₂)
    unfold tiltWeight
    rw [← Real.exp_add]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hexp_le : Real.exp (5 * (lam₂ - lam₁)) ≤ Real.exp (6 * (lam₂ - lam₁)) :=
    Real.exp_le_exp.mpr (by linarith)
  calc
    highWeightSum lam₁ * partFuncFour lam₂
        ≤ highWeightSum lam₁ * (partFuncFour lam₁ * Real.exp (5 * (lam₂ - lam₁))) :=
      mul_le_mul_of_nonneg_left hfour_le (highWeightSum_pos lam₁).le
    _ ≤ highWeightSum lam₁ * (partFuncFour lam₁ * Real.exp (6 * (lam₂ - lam₁))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hexp_le (partFuncFour_pos lam₁).le) (highWeightSum_pos lam₁).le
    _ = (highWeightSum lam₁ * Real.exp (6 * (lam₂ - lam₁))) * partFuncFour lam₁ := by ring
    _ ≤ highWeightSum lam₂ * partFuncFour lam₁ :=
      mul_le_mul_of_nonneg_right hhigh_ge (partFuncFour_pos lam₁).le

private lemma inv_sqrt_two_bounds :
    (707 / 1000 : ℝ) < Real.exp (-Real.log 2 / 2) ∧
      Real.exp (-Real.log 2 / 2) < (708 / 1000 : ℝ) := by
  set θ : ℝ := Real.exp (-Real.log 2 / 2)
  have hθ_pos : 0 < θ := Real.exp_pos _
  have hθ_sq : θ ^ 2 = 1 / 2 := by
    dsimp [θ]
    rw [← Real.exp_nat_mul]
    have hexp : ((2 : ℕ) : ℝ) * (-Real.log 2 / 2) = -Real.log 2 := by push_cast; ring
    rw [hexp, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  constructor
  · nlinarith [sq_nonneg (θ - 707 / 1000)]
  · nlinarith [sq_nonneg (708 / 1000 - θ)]

private lemma tiltWeight_two_log_two (i : ℤ) :
    tiltWeight (2 * Real.log 2) (i : ℝ) =
      4 * (Real.exp (-Real.log 2 / 2)) ^ ((i - 2).natAbs ^ 2) := by
  unfold tiltWeight
  have h4 : (4 : ℝ) = Real.exp (2 * Real.log 2) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_num
  rw [h4, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  have hnat : (((i - 2).natAbs ^ 2 : ℕ) : ℝ) = ((i : ℝ) - 2) ^ 2 := by
    simp
  rw [hnat]
  ring

private lemma meanFour_two_log_two_lt :
    meanFour (2 * Real.log 2) < 2.885 := by
  unfold meanFour
  have h4 : ({2, 3, 4, 5} : Finset ℤ) = insert 2 (insert 3 (insert 4 {5})) := rfl
  rw [partFuncFour_eq_sum, h4]
  simp only [sum_insert (by decide : (2 : ℤ) ∉ insert 3 (insert 4 ({5} : Finset ℤ))),
    sum_insert (by decide : (3 : ℤ) ∉ insert 4 ({5} : Finset ℤ)),
    sum_insert (by decide : (4 : ℤ) ∉ ({5} : Finset ℤ)), sum_singleton,
    tiltWeight_two_log_two]
  set θ : ℝ := Real.exp (-Real.log 2 / 2)
  have hθ := inv_sqrt_two_bounds
  have hθ_sq : θ ^ 2 = 1 / 2 := by
    dsimp [θ]
    rw [← Real.exp_nat_mul]
    have hexp : ((2 : ℕ) : ℝ) * (-Real.log 2 / 2) = -Real.log 2 := by push_cast; ring
    rw [hexp, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  have hθ4 : θ ^ 4 = 1 / 4 := by nlinarith [hθ_sq]
  have hθ9 : θ ^ 9 = θ / 16 := by
    rw [show θ ^ 9 = (θ ^ 2) ^ 4 * θ by ring, hθ_sq]
    ring
  norm_num [hθ4, hθ9]
  rw [div_lt_iff₀ (by linarith [hθ.1])]
  linarith [hθ.1, hθ.2]

private lemma ratioLow_two_log_two_lt :
    ratioLow (2 * Real.log 2) < 502 / 1000 := by
  unfold ratioLow lowWeightSum
  have h4 : ({2, 3, 4, 5} : Finset ℤ) = insert 2 (insert 3 (insert 4 {5})) := rfl
  rw [partFuncFour_eq_sum, h4]
  simp only [sum_insert (by decide : (2 : ℤ) ∉ insert 3 (insert 4 ({5} : Finset ℤ))),
    sum_insert (by decide : (3 : ℤ) ∉ insert 4 ({5} : Finset ℤ)),
    sum_insert (by decide : (4 : ℤ) ∉ ({5} : Finset ℤ)), sum_singleton]
  have hm1 : (-1 : ℝ) = ((-1 : ℤ) : ℝ) := by norm_num
  have h0 : (0 : ℝ) = ((0 : ℤ) : ℝ) := by norm_num
  have h1 : (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
  rw [hm1, h0, h1]
  simp only [tiltWeight_two_log_two]
  set θ : ℝ := Real.exp (-Real.log 2 / 2)
  have hθ := inv_sqrt_two_bounds
  have hθ_sq : θ ^ 2 = 1 / 2 := by
    dsimp [θ]
    rw [← Real.exp_nat_mul]
    have hexp : ((2 : ℕ) : ℝ) * (-Real.log 2 / 2) = -Real.log 2 := by push_cast; ring
    rw [hexp, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  have hθ4 : θ ^ 4 = 1 / 4 := by nlinarith [hθ_sq]
  have hθ9 : θ ^ 9 = θ / 16 := by
    rw [show θ ^ 9 = (θ ^ 2) ^ 4 * θ by ring, hθ_sq]
    ring
  norm_num [hθ4, hθ9]
  rw [div_lt_iff₀ (by linarith [hθ.1])]
  linarith [hθ.1, hθ.2]

private lemma tiltWeight_three_log_two (i : ℤ) :
    tiltWeight (3 * Real.log 2) (i : ℝ) =
      Real.exp (9 / 2 * Real.log 2) * (Real.exp (-Real.log 2 / 2)) ^ ((i - 3).natAbs ^ 2) := by
  unfold tiltWeight
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  have hnat : (((i - 3).natAbs ^ 2 : ℕ) : ℝ) = ((i : ℝ) - 3) ^ 2 := by
    simp
  rw [hnat]
  ring

private lemma ratioLow_three_log_two_bounds :
    (111 / 1000 : ℝ) < ratioLow (3 * Real.log 2) ∧
      ratioLow (3 * Real.log 2) < 12 / 100 := by
  unfold ratioLow lowWeightSum
  have h4 : ({2, 3, 4, 5} : Finset ℤ) = insert 2 (insert 3 (insert 4 {5})) := rfl
  rw [partFuncFour_eq_sum, h4]
  simp only [sum_insert (by decide : (2 : ℤ) ∉ insert 3 (insert 4 ({5} : Finset ℤ))),
    sum_insert (by decide : (3 : ℤ) ∉ insert 4 ({5} : Finset ℤ)),
    sum_insert (by decide : (4 : ℤ) ∉ ({5} : Finset ℤ)), sum_singleton]
  have hm1 : (-1 : ℝ) = ((-1 : ℤ) : ℝ) := by norm_num
  have h0 : (0 : ℝ) = ((0 : ℤ) : ℝ) := by norm_num
  have h1 : (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
  rw [hm1, h0, h1]
  simp only [tiltWeight_three_log_two]
  set c : ℝ := Real.exp (9 / 2 * Real.log 2)
  have hc : 0 < c := Real.exp_pos _
  set θ : ℝ := Real.exp (-Real.log 2 / 2)
  have hθ := inv_sqrt_two_bounds
  have hθ_sq : θ ^ 2 = 1 / 2 := by
    dsimp [θ]
    rw [← Real.exp_nat_mul]
    have hexp : ((2 : ℕ) : ℝ) * (-Real.log 2 / 2) = -Real.log 2 := by push_cast; ring
    rw [hexp, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  have hθ4 : θ ^ 4 = 1 / 4 := by nlinarith [hθ_sq]
  have hθ9 : θ ^ 9 = θ / 16 := by
    rw [show θ ^ 9 = (θ ^ 2) ^ 4 * θ by ring, hθ_sq]; ring
  have hθ16 : θ ^ 16 = 1 / 256 := by
    rw [show θ ^ 16 = (θ ^ 4) ^ 4 by ring, hθ4]; norm_num
  norm_num [hθ4, hθ9, hθ16]
  have hcancel : (c * (1 / 256) + c * (θ / 16) + c * (1 / 4)) /
      (c * θ + (c + (c * θ + c * (1 / 4)))) =
      (1 / 256 + θ / 16 + 1 / 4) / (5 / 4 + 2 * θ) := by
    field_simp [hc.ne']
    ring
  rw [hcancel]
  constructor
  · rw [lt_div_iff₀ (by linarith [hθ.1])]
    linarith [hθ.1, hθ.2]
  · rw [div_lt_iff₀ (by linarith [hθ.1])]
    linarith [hθ.1, hθ.2]

private lemma ratioHigh_three_log_two_lt :
    ratioHigh (3 * Real.log 2) < 20 / 1000 := by
  unfold ratioHigh
  let c : ℝ := Real.exp (9 / 2 * Real.log 2)
  have hc : 0 < c := Real.exp_pos _
  let θ : ℝ := Real.exp (-Real.log 2 / 2)
  have hθ := inv_sqrt_two_bounds
  have hθ_pos : 0 < θ := Real.exp_pos _
  have hθ_sq : θ ^ 2 = 1 / 2 := by
    dsimp [θ]
    rw [← Real.exp_nat_mul]
    have hexp : ((2 : ℕ) : ℝ) * (-Real.log 2 / 2) = -Real.log 2 := by push_cast; ring
    rw [hexp, Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hθ4 : θ ^ 4 = 1 / 4 := by nlinarith [hθ_sq]
  have hθ9 : θ ^ 9 = θ / 16 := by
    rw [show θ ^ 9 = (θ ^ 2) ^ 4 * θ by ring, hθ_sq]; ring
  have hθ16 : θ ^ 16 = 1 / 256 := by
    rw [show θ ^ 16 = (θ ^ 4) ^ 4 by ring, hθ4]; norm_num
  have hden : partFuncFour (3 * Real.log 2) = c * (5 / 4 + 2 * θ) := by
    have h4 : ({2, 3, 4, 5} : Finset ℤ) = insert 2 (insert 3 (insert 4 {5})) := rfl
    rw [partFuncFour_eq_sum, h4]
    simp only [sum_insert (by decide : (2 : ℤ) ∉ insert 3 (insert 4 ({5} : Finset ℤ))),
      sum_insert (by decide : (3 : ℤ) ∉ insert 4 ({5} : Finset ℤ)),
      sum_insert (by decide : (4 : ℤ) ∉ ({5} : Finset ℤ)), sum_singleton,
      tiltWeight_three_log_two]
    change c * θ ^ ((2 - 3 : ℤ).natAbs ^ 2) +
      (c * θ ^ ((3 - 3 : ℤ).natAbs ^ 2) +
        (c * θ ^ ((4 - 3 : ℤ).natAbs ^ 2) + c * θ ^ ((5 - 3 : ℤ).natAbs ^ 2))) =
      c * (5 / 4 + 2 * θ)
    norm_num [hθ4]
    ring
  rw [highWeightSum, ← (summable_highWeight (3 * Real.log 2)).sum_add_tsum_nat_add 2]
  have hhead : ∑ m ∈ range 2, tiltWeight (3 * Real.log 2) ((m : ℝ) + 6) =
      c * (θ / 16 + 1 / 256) := by
    simp only [sum_range_succ, sum_range_zero, zero_add, Nat.cast_zero, Nat.cast_one]
    have h6 : (6 : ℝ) = ((6 : ℤ) : ℝ) := by norm_num
    have h7 : (1 : ℝ) + 6 = ((7 : ℤ) : ℝ) := by norm_num
    rw [h7, h6, tiltWeight_three_log_two, tiltWeight_three_log_two]
    change c * θ ^ ((6 - 3 : ℤ).natAbs ^ 2) + c * θ ^ ((7 - 3 : ℤ).natAbs ^ 2) =
      c * (θ / 16 + 1 / 256)
    norm_num [hθ9, hθ16]
    ring
  have htail_term : ∀ j : ℕ, tiltWeight (3 * Real.log 2) (((j + 2 : ℕ) : ℝ) + 6) ≤
      c * (1 / 4096 : ℝ) * (1 / 32 : ℝ) ^ j := by
    intro j
    have hq : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hexp_le : (3 * Real.log 2) * (((j + 2 : ℕ) : ℝ) + 6) -
        (Real.log 2 / 2) * (((j + 2 : ℕ) : ℝ) + 6) ^ 2 ≤
        9 / 2 * Real.log 2 - ((12 + 5 * j : ℕ) : ℝ) * Real.log 2 := by
      have hquad : 0 ≤ (((j : ℝ) ^ 2 + 1) / 2) * Real.log 2 := by positivity
      have hid : (3 * Real.log 2) * (((j + 2 : ℕ) : ℝ) + 6) -
          (Real.log 2 / 2) * (((j + 2 : ℕ) : ℝ) + 6) ^ 2 =
          9 / 2 * Real.log 2 - ((12 + 5 * j : ℕ) : ℝ) * Real.log 2 -
            (((j : ℝ) ^ 2 + 1) / 2) * Real.log 2 := by
        push_cast
        ring
      linarith
    calc
      tiltWeight (3 * Real.log 2) (((j + 2 : ℕ) : ℝ) + 6)
          ≤ Real.exp (9 / 2 * Real.log 2 - ((12 + 5 * j : ℕ) : ℝ) * Real.log 2) :=
        Real.exp_le_exp.mpr hexp_le
      _ = c * Real.exp (-(((12 + 5 * j : ℕ) : ℝ) * Real.log 2)) := by
        rw [sub_eq_add_neg, Real.exp_add]
      _ = c * (2⁻¹ : ℝ) ^ (12 + 5 * j) := by
        congr 1
        rw [show -(((12 + 5 * j : ℕ) : ℝ) * Real.log 2) =
            ((12 + 5 * j : ℕ) : ℝ) * Real.log (2⁻¹) by rw [Real.log_inv]; ring,
          Real.exp_nat_mul, Real.exp_log (by norm_num)]
      _ = c * (1 / 4096 : ℝ) * (1 / 32 : ℝ) ^ j := by
        rw [pow_add, pow_mul]
        norm_num
        ring
  have hgeom : Summable (fun j : ℕ => c * (1 / 4096 : ℝ) * (1 / 32 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have htail_le : (∑' j : ℕ, tiltWeight (3 * Real.log 2) (((j + 2 : ℕ) : ℝ) + 6)) ≤
      c * (1 / 3968 : ℝ) := by
    calc
      (∑' j : ℕ, tiltWeight (3 * Real.log 2) (((j + 2 : ℕ) : ℝ) + 6))
          ≤ ∑' j : ℕ, c * (1 / 4096 : ℝ) * (1 / 32 : ℝ) ^ j :=
        ((summable_highWeight (3 * Real.log 2)).comp_injective (fun _ _ h => by omega)).tsum_le_tsum
          htail_term hgeom
      _ = c * (1 / 4096 : ℝ) * (1 - 1 / 32 : ℝ)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      _ = c * (1 / 3968 : ℝ) := by ring
  rw [hhead, hden, div_lt_iff₀ (mul_pos hc (by linarith [hθ.1]))]
  nlinarith [hc, hθ.1, hθ.2, htail_le]

private lemma tiltWeight_nine_halves_log_two (i : ℤ) :
    tiltWeight ((9 / 2 : ℝ) * Real.log 2) (i : ℝ) =
      Real.exp (81 / 8 * Real.log 2) * (Real.exp (-Real.log 2 / 8)) ^ ((2 * i - 9).natAbs ^ 2) := by
  unfold tiltWeight
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  have hnat : (((2 * i - 9).natAbs ^ 2 : ℕ) : ℝ) = (2 * (i : ℝ) - 9) ^ 2 := by
    simp
  rw [hnat]
  ring

private lemma four_lt_meanFour_nine_halves_log_two :
    4 < meanFour ((9 / 2 : ℝ) * Real.log 2) := by
  unfold meanFour
  have h4 : ({2, 3, 4, 5} : Finset ℤ) = insert 2 (insert 3 (insert 4 {5})) := rfl
  rw [partFuncFour_eq_sum, h4]
  simp only [sum_insert (by decide : (2 : ℤ) ∉ insert 3 (insert 4 ({5} : Finset ℤ))),
    sum_insert (by decide : (3 : ℤ) ∉ insert 4 ({5} : Finset ℤ)),
    sum_insert (by decide : (4 : ℤ) ∉ ({5} : Finset ℤ)), sum_singleton,
    tiltWeight_nine_halves_log_two]
  set c : ℝ := Real.exp (81 / 8 * Real.log 2)
  have hc : 0 < c := Real.exp_pos _
  set t : ℝ := Real.exp (-Real.log 2 / 8)
  have ht : 0 < t := Real.exp_pos _
  have ht8 : t ^ 8 = 1 / 2 := by
    dsimp [t]
    rw [← Real.exp_nat_mul]
    have hexp : ((8 : ℕ) : ℝ) * (-Real.log 2 / 8) = -Real.log 2 := by push_cast; ring
    rw [hexp, Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have ht9 : t ^ 9 = t / 2 := by rw [show t ^ 9 = t ^ 8 * t by ring, ht8]; ring
  have ht25 : t ^ 25 = t / 8 := by rw [show t ^ 25 = (t ^ 8) ^ 3 * t by ring, ht8]; norm_num; ring
  norm_num [ht9, ht25]
  rw [lt_div_iff₀ (by nlinarith [hc, ht])]
  nlinarith [hc, ht]

private lemma ratioHigh_nine_halves_log_two_lt :
    ratioHigh ((9 / 2 : ℝ) * Real.log 2) < 1 / 4 := by
  unfold ratioHigh
  let c : ℝ := Real.exp (81 / 8 * Real.log 2)
  have hc : 0 < c := Real.exp_pos _
  let t : ℝ := Real.exp (-Real.log 2 / 8)
  have ht : 0 < t := Real.exp_pos _
  have ht_lt1 : t < 1 := by
    dsimp [t]
    exact Real.exp_lt_one_iff.mpr (by linarith [Real.log_two_gt_d9])
  have ht8 : t ^ 8 = 1 / 2 := by
    dsimp [t]
    rw [← Real.exp_nat_mul]
    have hexp : ((8 : ℕ) : ℝ) * (-Real.log 2 / 8) = -Real.log 2 := by push_cast; ring
    rw [hexp, Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have ht9 : t ^ 9 = t / 2 := by rw [show t ^ 9 = t ^ 8 * t by ring, ht8]; ring
  have ht25 : t ^ 25 = t / 8 := by rw [show t ^ 25 = (t ^ 8) ^ 3 * t by ring, ht8]; norm_num; ring
  have hden : partFuncFour ((9 / 2 : ℝ) * Real.log 2) = c * t * (21 / 8) := by
    have h4 : ({2, 3, 4, 5} : Finset ℤ) = insert 2 (insert 3 (insert 4 {5})) := rfl
    rw [partFuncFour_eq_sum, h4]
    simp only [sum_insert (by decide : (2 : ℤ) ∉ insert 3 (insert 4 ({5} : Finset ℤ))),
      sum_insert (by decide : (3 : ℤ) ∉ insert 4 ({5} : Finset ℤ)),
      sum_insert (by decide : (4 : ℤ) ∉ ({5} : Finset ℤ)), sum_singleton,
      tiltWeight_nine_halves_log_two]
    change c * t ^ ((2 * 2 - 9 : ℤ).natAbs ^ 2) +
      (c * t ^ ((2 * 3 - 9 : ℤ).natAbs ^ 2) +
        (c * t ^ ((2 * 4 - 9 : ℤ).natAbs ^ 2) + c * t ^ ((2 * 5 - 9 : ℤ).natAbs ^ 2))) =
      c * t * (21 / 8)
    norm_num [ht9, ht25]
    ring
  rw [highWeightSum, ← (summable_highWeight ((9 / 2 : ℝ) * Real.log 2)).sum_add_tsum_nat_add 2]
  have hhead : ∑ m ∈ range 2, tiltWeight ((9 / 2 : ℝ) * Real.log 2) ((m : ℝ) + 6) =
      c * t * (5 / 8) := by
    simp only [sum_range_succ, sum_range_zero, zero_add, Nat.cast_zero, Nat.cast_one]
    have h6 : (6 : ℝ) = ((6 : ℤ) : ℝ) := by norm_num
    have h7 : (1 : ℝ) + 6 = ((7 : ℤ) : ℝ) := by norm_num
    rw [h7, h6, tiltWeight_nine_halves_log_two, tiltWeight_nine_halves_log_two]
    change c * t ^ ((2 * 6 - 9 : ℤ).natAbs ^ 2) + c * t ^ ((2 * 7 - 9 : ℤ).natAbs ^ 2) =
      c * t * (5 / 8)
    norm_num [ht9, ht25]
    ring
  have htail_term : ∀ j : ℕ, tiltWeight ((9 / 2 : ℝ) * Real.log 2) (((j + 2 : ℕ) : ℝ) + 6) ≤
      c * t * (1 / 64 : ℝ) * (1 / 8 : ℝ) ^ j := by
    intro j
    have h8 : (((j + 2 : ℕ) : ℝ) + 6) = (((j + 8 : ℕ) : ℝ)) := by push_cast; ring
    have hcast : (((j + 8 : ℕ) : ℝ)) = (((j + 8 : ℕ) : ℤ) : ℝ) := by norm_cast
    rw [h8, hcast, tiltWeight_nine_halves_log_two]
    have hexp_ge : 49 + 24 * j ≤ ((2 * ((j + 8 : ℕ) : ℤ) - 9).natAbs ^ 2) := by
      have hna : (2 * ((j + 8 : ℕ) : ℤ) - 9).natAbs = 2 * j + 7 := by omega
      rw [hna]
      nlinarith
    have hpow_le : t ^ ((2 * ((j + 8 : ℕ) : ℤ) - 9).natAbs ^ 2) ≤ t ^ (49 + 24 * j) :=
      pow_le_pow_of_le_one ht.le ht_lt1.le hexp_ge
    have ht49 : t ^ (49 + 24 * j) = t * (1 / 64 : ℝ) * (1 / 8 : ℝ) ^ j := by
      rw [show 49 + 24 * j = 1 + 8 * 6 + (8 * 3) * j by omega, pow_add, pow_add, pow_one,
        pow_mul, pow_mul, pow_mul, ht8]
      norm_num
    calc
      c * t ^ ((2 * ((j + 8 : ℕ) : ℤ) - 9).natAbs ^ 2)
          ≤ c * t ^ (49 + 24 * j) := mul_le_mul_of_nonneg_left hpow_le hc.le
      _ = c * t * (1 / 64 : ℝ) * (1 / 8 : ℝ) ^ j := by rw [ht49]; ring
  have hgeom : Summable (fun j : ℕ => c * t * (1 / 64 : ℝ) * (1 / 8 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have htail_le : (∑' j : ℕ, tiltWeight ((9 / 2 : ℝ) * Real.log 2) (((j + 2 : ℕ) : ℝ) + 6)) ≤
      c * t * (1 / 56 : ℝ) := by
    calc
      (∑' j : ℕ, tiltWeight ((9 / 2 : ℝ) * Real.log 2) (((j + 2 : ℕ) : ℝ) + 6))
          ≤ ∑' j : ℕ, c * t * (1 / 64 : ℝ) * (1 / 8 : ℝ) ^ j :=
        ((summable_highWeight ((9 / 2 : ℝ) * Real.log 2)).comp_injective
          (fun _ _ h => by omega)).tsum_le_tsum htail_term hgeom
      _ = c * t * (1 / 64 : ℝ) * (1 - 1 / 8 : ℝ)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      _ = c * t * (1 / 56 : ℝ) := by ring
  rw [hhead, hden, div_lt_iff₀ (by positivity)]
  nlinarith [mul_pos hc ht, htail_le]

/-- Nonnegativity of the 4-size restriction entropy loss `D_4(δ) = 𝓕_{S_+}(T_δ) - 𝓕_{S_4}(T_δ)`. -/
theorem freeEnergyFour_le_freeEnergyPlus {T : ℝ} (hT : T ∈ Set.Icc (2.6 : ℝ) 4.1) :
    freeEnergyFour T ≤ freeEnergyPlus T := by
  obtain ⟨lam, _, hfeq, _⟩ := exists_min_dualPlus hT
  calc
    freeEnergyFour T ≤ Real.log (partFuncFour lam) - lam * T := freeEnergyFour_le_eval hT lam
    _ ≤ Real.log (partFuncPlus lam) - lam * T := by
      linarith [Real.log_le_log (partFuncFour_pos lam) (partFuncFour_le_partFuncPlus lam)]
    _ = freeEnergyPlus T := hfeq.symm

/-- **Lemma 5.1 (`arXiv:2608.30604`) — Constructive Uniform Entropy Certificate**:
For every `δ ∈ [0, 1]`, `D_4(δ) ≤ log(61 / 40) < log(153 / 100)`, and therefore
`petkovA4 δ ≥ log(80 / 61) = log(200 / 153) + log(306 / 305)`. -/
theorem petkovA4_uniform_margin {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    Real.log (200 / 153) + Real.log (306 / 305) ≤ petkovA4 δ := by
  have hT_mem : targetDeficit δ ∈ Set.Icc (2.6 : ℝ) 4.1 := targetDeficit_mem_Icc hδ
  have hT_b := targetDeficit_bounds hδ
  obtain ⟨lam₄, _, hfeq₄, hall₄⟩ := exists_min_dualFour hT_mem
  have hmean₄ : meanFour lam₄ = targetDeficit δ := meanFour_eq_of_isMin hall₄
  have hlam_lo : 2 * Real.log 2 < lam₄ := by
    by_contra hle
    have hm := strictMono_meanFour.monotone (not_lt.mp hle)
    linarith [meanFour_two_log_two_lt]
  have hlam_hi : lam₄ < (9 / 2 : ℝ) * Real.log 2 := by
    by_contra hge
    have hm := strictMono_meanFour.monotone (not_lt.mp hge)
    linarith [four_lt_meanFour_nine_halves_log_two]
  have hsum_ratio : ratioLow lam₄ + ratioHigh lam₄ ≤ 21 / 40 := by
    by_cases hmid : lam₄ ≤ 3 * Real.log 2
    · have hl := antitone_ratioLow hlam_lo.le
      have hh := monotone_ratioHigh hmid
      linarith [ratioLow_two_log_two_lt, ratioHigh_three_log_two_lt]
    · have hl := antitone_ratioLow (not_le.mp hmid).le
      have hh := monotone_ratioHigh hlam_hi.le
      linarith [ratioLow_three_log_two_bounds.2, ratioHigh_nine_halves_log_two_lt]
  have hZratio : partFuncPlus lam₄ / partFuncFour lam₄ = 1 + ratioLow lam₄ + ratioHigh lam₄ := by
    rw [partFuncPlus_decomp]
    unfold ratioLow ratioHigh
    field_simp [(partFuncFour_pos lam₄).ne']
    ring
  have hD4_le : freeEnergyPlus (targetDeficit δ) - freeEnergyFour (targetDeficit δ) ≤
      Real.log (61 / 40) := by
    have hplus_le := freeEnergyPlus_le_eval hT_mem lam₄
    have hdiff_le : freeEnergyPlus (targetDeficit δ) - freeEnergyFour (targetDeficit δ) ≤
        Real.log (partFuncPlus lam₄) - Real.log (partFuncFour lam₄) := by
      linarith [hfeq₄]
    rw [← Real.log_div (partFuncPlus_pos lam₄).ne' (partFuncFour_pos lam₄).ne', hZratio]
      at hdiff_le
    refine hdiff_le.trans (Real.log_le_log ?_ (by linarith))
    rw [← hZratio]
    exact div_pos (partFuncPlus_pos lam₄) (partFuncFour_pos lam₄)
  have hlog_eq : Real.log 2 - Real.log (61 / 40) =
      Real.log (200 / 153) + Real.log (306 / 305) := by
    rw [← Real.log_div (by norm_num) (by norm_num), ← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  unfold petkovA4
  linarith

/-- Strict pointwise entropy certificate `petkovA4 δ > log(200 / 153)` for every `δ ∈ [0, 1]`. -/
theorem petkovA4_gt_log_200_153 {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    Real.log (200 / 153) < petkovA4 δ := by
  have hpos : 0 < Real.log (306 / 305 : ℝ) := Real.log_pos (by norm_num)
  linarith [petkovA4_uniform_margin hδ]

/-! ### 6. Nonconstancy of `petkovA4` on `[0, 1]` -/

/-- `petkovA4` is nonconstant on `[0, 1]`: its value at the dyadic symmetry phase
`δ_* = 2 / log 2 - 5/2 ∈ (0, 1)` strictly exceeds its value at `δ = 1`. -/
theorem petkovA4_nonconstant :
    ∃ δ₁ ∈ Set.Icc (0 : ℝ) 1, ∃ δ₂ ∈ Set.Icc (0 : ℝ) 1, petkovA4 δ₁ ≠ petkovA4 δ₂ := by
  let δstar : ℝ := 2 / Real.log 2 - 5 / 2
  have hq_lo := Real.log_two_gt_d9
  have hq_hi := Real.log_two_lt_d9
  have hdiv_lo : 2.885 < 2 / Real.log 2 := by
    rw [lt_div_iff₀ (by linarith)]; nlinarith
  have hdiv_hi : 2 / Real.log 2 < 2.886 := by
    rw [div_lt_iff₀ (by linarith)]; nlinarith
  have hδstar_mem : δstar ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [δstar]; constructor <;> linarith
  have hTstar : targetDeficit δstar = 7 / 2 := by
    unfold targetDeficit; dsimp [δstar]; ring
  let lam₀ : ℝ := (7 / 2 : ℝ) * Real.log 2
  have hmean_lam₀ : meanFour lam₀ = 7 / 2 := by
    unfold meanFour
    have h4 : ({2, 3, 4, 5} : Finset ℤ) = insert 2 (insert 3 (insert 4 {5})) := rfl
    rw [partFuncFour_seven_halves_log_two, h4]
    simp only [sum_insert (by decide : (2 : ℤ) ∉ insert 3 (insert 4 ({5} : Finset ℤ))),
      sum_insert (by decide : (3 : ℤ) ∉ insert 4 ({5} : Finset ℤ)),
      sum_insert (by decide : (4 : ℤ) ∉ ({5} : Finset ℤ)), sum_singleton,
      Int.cast_ofNat, tiltWeight, lam₀]
    have h2 : (7 / 2 : ℝ) * Real.log 2 * 2 - Real.log 2 / 2 * 2 ^ 2 = (5 : ℕ) * Real.log 2 := by
      push_cast; ring
    have h3 : (7 / 2 : ℝ) * Real.log 2 * 3 - Real.log 2 / 2 * 3 ^ 2 = (6 : ℕ) * Real.log 2 := by
      push_cast; ring
    have h4' : (7 / 2 : ℝ) * Real.log 2 * 4 - Real.log 2 / 2 * 4 ^ 2 = (6 : ℕ) * Real.log 2 := by
      push_cast; ring
    have h5 : (7 / 2 : ℝ) * Real.log 2 * 5 - Real.log 2 / 2 * 5 ^ 2 = (5 : ℕ) * Real.log 2 := by
      push_cast; ring
    rw [h2, h3, h4', h5, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_num
  have hTstar_mem : (7 / 2 : ℝ) ∈ Set.Icc (2.6 : ℝ) 4.1 := by norm_num
  obtain ⟨lam₄, _, hfeq₄, hall₄⟩ := exists_min_dualFour hTstar_mem
  have hlam₄_eq : lam₄ = lam₀ :=
    strictMono_meanFour.injective ((meanFour_eq_of_isMin hall₄).trans hmean_lam₀.symm)
  subst hlam₄_eq
  have hD4_star : freeEnergyPlus (7 / 2) - freeEnergyFour (7 / 2) ≤
      Real.log (1 + 291 / 3072) := by
    have hplus_le := freeEnergyPlus_le_eval hTstar_mem lam₀
    have hdiff_le : freeEnergyPlus (7 / 2) - freeEnergyFour (7 / 2) ≤
        Real.log (partFuncPlus lam₀ / partFuncFour lam₀) := by
      rw [Real.log_div (partFuncPlus_pos lam₀).ne' (partFuncFour_pos lam₀).ne']
      linarith [hfeq₄]
    refine hdiff_le.trans (Real.log_le_log (div_pos (partFuncPlus_pos lam₀) (partFuncFour_pos lam₀)) ?_)
    rw [partFuncFour_seven_halves_log_two]
    linarith [partFuncPlus_seven_halves_log_two_le]
  have h1_mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hT1_mem : targetDeficit 1 ∈ Set.Icc (2.6 : ℝ) 4.1 := targetDeficit_mem_Icc h1_mem
  have hT1_lt3 : targetDeficit 1 < 3 := by
    unfold targetDeficit; linarith
  obtain ⟨lam₁, _, hfeq₁, hall₁⟩ := exists_min_dualPlus hT1_mem
  have hlam₁_le : lam₁ ≤ 3 * Real.log 2 := by
    by_contra hgt
    have hd : 0 < lam₁ - 3 * Real.log 2 := sub_pos.mpr (not_le.mp hgt)
    have hsym_Z : partFuncPlus (3 * Real.log 2) * Real.exp (3 * (lam₁ - 3 * Real.log 2)) ≤
        partFuncPlus lam₁ := by
      rw [partFuncPlus_eq_tsum, partFuncPlus_eq_tsum, ← tsum_mul_right,
        ← ((summable_tiltWeight_plus (3 * Real.log 2)).mul_right _).sum_add_tsum_nat_add 9,
        ← (summable_tiltWeight_plus lam₁).sum_add_tsum_nat_add 9]
      have hterm_ge : ∀ k : ℕ,
          tiltWeight (3 * Real.log 2) ((k : ℝ) - 1) * Real.exp (3 * (lam₁ - 3 * Real.log 2)) *
            (1 + (lam₁ - 3 * Real.log 2) * ((k : ℝ) - 4)) ≤
          tiltWeight lam₁ ((k : ℝ) - 1) := by
        intro k
        have hsplit : tiltWeight lam₁ ((k : ℝ) - 1) =
            tiltWeight (3 * Real.log 2) ((k : ℝ) - 1) *
              Real.exp (3 * (lam₁ - 3 * Real.log 2)) *
              Real.exp ((lam₁ - 3 * Real.log 2) * ((k : ℝ) - 4)) := by
          unfold tiltWeight
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        rw [hsplit]
        exact mul_le_mul_of_nonneg_left
          (by linarith [Real.add_one_le_exp ((lam₁ - 3 * Real.log 2) * ((k : ℝ) - 4))])
          (mul_pos (tiltWeight_pos _ _) (Real.exp_pos _)).le
      have hhead_le : ∑ k ∈ range 9,
          tiltWeight (3 * Real.log 2) ((k : ℝ) - 1) * Real.exp (3 * (lam₁ - 3 * Real.log 2)) ≤
          ∑ k ∈ range 9, tiltWeight lam₁ ((k : ℝ) - 1) := by
        have hzero : ∑ k ∈ range 9,
            tiltWeight (3 * Real.log 2) ((k : ℝ) - 1) * ((k : ℝ) - 4) = 0 := by
          simp only [sum_range_succ, sum_range_zero, zero_add, Nat.cast_zero, Nat.cast_one,
            Nat.cast_ofNat]
          have hpair : ∀ k : ℤ, tiltWeight (3 * Real.log 2) (k : ℝ) =
              tiltWeight (3 * Real.log 2) ((6 - k : ℤ) : ℝ) := by
            intro k
            rw [tiltWeight_three_log_two, tiltWeight_three_log_two]
            congr 2
            have heq : (k - 3).natAbs = (6 - k - 3).natAbs := by omega
            rw [heq]
          have p0 := hpair (-1)
          have p1 := hpair 0
          have p2 := hpair 1
          have p3 := hpair 2
          norm_num at p0 p1 p2 p3 ⊢
          linarith
        have hsum9 := Finset.sum_le_sum fun k (_ : k ∈ range 9) => hterm_ge k
        have hexp9 : ∑ k ∈ range 9,
            tiltWeight (3 * Real.log 2) ((k : ℝ) - 1) * Real.exp (3 * (lam₁ - 3 * Real.log 2)) *
              (1 + (lam₁ - 3 * Real.log 2) * ((k : ℝ) - 4)) =
            (∑ k ∈ range 9,
              tiltWeight (3 * Real.log 2) ((k : ℝ) - 1) * Real.exp (3 * (lam₁ - 3 * Real.log 2))) +
            Real.exp (3 * (lam₁ - 3 * Real.log 2)) * (lam₁ - 3 * Real.log 2) *
              (∑ k ∈ range 9, tiltWeight (3 * Real.log 2) ((k : ℝ) - 1) * ((k : ℝ) - 4)) := by
          have hlin : ∀ k : ℕ,
              tiltWeight (3 * Real.log 2) ((k : ℝ) - 1) * Real.exp (3 * (lam₁ - 3 * Real.log 2)) *
                (1 + (lam₁ - 3 * Real.log 2) * ((k : ℝ) - 4)) =
              tiltWeight (3 * Real.log 2) ((k : ℝ) - 1) * Real.exp (3 * (lam₁ - 3 * Real.log 2)) +
              (Real.exp (3 * (lam₁ - 3 * Real.log 2)) * (lam₁ - 3 * Real.log 2)) *
                (tiltWeight (3 * Real.log 2) ((k : ℝ) - 1) * ((k : ℝ) - 4)) := fun _ => by ring
          simp_rw [hlin, sum_add_distrib, ← mul_sum]
        rw [hzero, mul_zero, add_zero] at hexp9
        linarith
      have htail_le : (∑' m : ℕ,
          tiltWeight (3 * Real.log 2) (((m + 9 : ℕ) : ℝ) - 1) *
            Real.exp (3 * (lam₁ - 3 * Real.log 2))) ≤
          ∑' m : ℕ, tiltWeight lam₁ (((m + 9 : ℕ) : ℝ) - 1) := by
        refine (((summable_tiltWeight_plus (3 * Real.log 2)).mul_right _).comp_injective
          (fun _ _ h => by omega)).tsum_le_tsum (fun m => ?_)
          ((summable_tiltWeight_plus lam₁).comp_injective (fun _ _ h => by omega))
        have hm_ge : (0 : ℝ) ≤ ((m + 9 : ℕ) : ℝ) - 4 := by
          have : (4 : ℝ) ≤ ((m + 9 : ℕ) : ℝ) := by exact_mod_cast (by omega : 4 ≤ m + 9)
          linarith
        have hpos_prod : 0 ≤ (lam₁ - 3 * Real.log 2) * (((m + 9 : ℕ) : ℝ) - 4) :=
          mul_nonneg hd.le hm_ge
        have h1le : 1 ≤ 1 + (lam₁ - 3 * Real.log 2) * (((m + 9 : ℕ) : ℝ) - 4) := by linarith
        calc
          tiltWeight (3 * Real.log 2) (((m + 9 : ℕ) : ℝ) - 1) *
              Real.exp (3 * (lam₁ - 3 * Real.log 2))
              ≤ tiltWeight (3 * Real.log 2) (((m + 9 : ℕ) : ℝ) - 1) *
                  Real.exp (3 * (lam₁ - 3 * Real.log 2)) *
                  (1 + (lam₁ - 3 * Real.log 2) * (((m + 9 : ℕ) : ℝ) - 4)) :=
            le_mul_of_one_le_right (mul_pos (tiltWeight_pos _ _) (Real.exp_pos _)).le h1le
          _ ≤ tiltWeight lam₁ (((m + 9 : ℕ) : ℝ) - 1) := hterm_ge (m + 9)
      linarith
    have hlog_ge : Real.log (partFuncPlus (3 * Real.log 2)) + 3 * (lam₁ - 3 * Real.log 2) ≤
        Real.log (partFuncPlus lam₁) := by
      have h1 := Real.log_le_log
        (mul_pos (partFuncPlus_pos _) (Real.exp_pos _)) hsym_Z
      rwa [Real.log_mul (partFuncPlus_pos _).ne' (Real.exp_pos _).ne', Real.log_exp] at h1
    have hmin := hall₁ (3 * Real.log 2)
    nlinarith
  have hD4_one : Real.log (1 + 111 / 1000) <
      freeEnergyPlus (targetDeficit 1) - freeEnergyFour (targetDeficit 1) := by
    have hfour_le := freeEnergyFour_le_eval hT1_mem lam₁
    have hdiff_ge : Real.log (partFuncPlus lam₁ / partFuncFour lam₁) ≤
        freeEnergyPlus (targetDeficit 1) - freeEnergyFour (targetDeficit 1) := by
      rw [Real.log_div (partFuncPlus_pos lam₁).ne' (partFuncFour_pos lam₁).ne']
      linarith [hfeq₁]
    have hZratio : 1 + ratioLow (3 * Real.log 2) < partFuncPlus lam₁ / partFuncFour lam₁ := by
      have hl : ratioLow (3 * Real.log 2) ≤ ratioLow lam₁ := antitone_ratioLow hlam₁_le
      have hh : 0 < ratioHigh lam₁ := div_pos (highWeightSum_pos lam₁) (partFuncFour_pos lam₁)
      rw [partFuncPlus_decomp]
      unfold ratioLow at hl ⊢
      unfold ratioHigh at hh
      have hsplit : (lowWeightSum lam₁ + partFuncFour lam₁ + highWeightSum lam₁) /
          partFuncFour lam₁ = 1 + lowWeightSum lam₁ / partFuncFour lam₁ +
            highWeightSum lam₁ / partFuncFour lam₁ := by
        field_simp [(partFuncFour_pos lam₁).ne']
        ring
      linarith
    have hlt_log : Real.log (1 + 111 / 1000) <
        Real.log (partFuncPlus lam₁ / partFuncFour lam₁) :=
      Real.log_lt_log (by norm_num) (by linarith [ratioLow_three_log_two_bounds.1])
    linarith
  have hstrict_log : Real.log (1 + 291 / 3072 : ℝ) < Real.log (1 + 111 / 1000 : ℝ) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  refine ⟨δstar, hδstar_mem, 1, h1_mem, ?_⟩
  unfold petkovA4
  rw [hTstar]
  intro heq
  linarith

end JSP000506
