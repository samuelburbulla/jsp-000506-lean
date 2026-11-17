import Mathlib.Analysis.SpecialFunctions.Stirling
import JSP000506.EntropyCert

/-!
# Independence-Number Scale, Stirling Bounds, Falling Factorials, and Independence Cap

This module formalizes Section 2 of Samuil Petkov's *A Full-Sequence Quantitative Gap Between the
Chromatic and Cochromatic Numbers of a Random Graph* (`arXiv:2608.30604`):

1. **Independence-number integer center `alphaNat n`** (`α = ⌊α₀(n)⌋₊`), the exact logarithmic
   identity `log 2 * α = 2 log n - 2 log(log n) + 2 alphaConst - log 2 * δ_n`, and effective
   two-sided growth bounds `(3 / 2) * log n ≤ log 2 * α ≤ 2 log n` eventually.
2. **Effective two-sided Stirling bounds** on `log (m!)` for all `m ≥ 1` derived from Mathlib's
   `Stirling.le_log_factorial_stirling` and `Stirling.log_stirlingSeq'_antitone`, together with the
   exact two-sided identity for `- α * log α` up to `O(log(log n))`.
3. **Falling-factorial + quadratic edge-exponent shift bounds**:
   - Universal upper bound (`falling_shift_upper_all`) for ALL fiber sizes `s = α + 1 - j`
     (`0 ≤ j ≤ α + 1`, i.e. `0 ≤ s ≤ α + 1`), used in Part B (`PartB.lean`).
   - Quantitative `O(1 / α)` lower bound (`falling_shift_lower_bounded`) for bounded deficits
     `i ≤ 5`, used in Part A (`PartA.lean`).
4. **High-probability independence-number cap (`IndepCapEvent n`)**:
   with probability `→ 1` in `G(n, 1/2)`, every independent set of `G` has cardinality at most
   `alphaNat n + 1` (`tendsto_probGnpHalf_indepCapEvent`).
-/

open Filter SimpleGraph Finset
open scoped Topology BigOperators Nat

namespace JSP000506

/-! ### 1. Integer Center `alphaNat`, Logarithmic Decomposition, and Growth -/

/-- Natural-number independence-number center `α_n = (⌊α₀(n)⌋).toNat`. -/
noncomputable def alphaNat (n : ℕ) : ℕ :=
  (alphaFloor n).toNat

/-- Constant `log(log 2) + 1 - (log 2)/2` appearing in `log 2 * α₀(n)`. -/
noncomputable def alphaConst : ℝ :=
  Real.log (Real.log 2) + 1 - Real.log 2 / 2

/-- Global elementary bound `log x ≤ x / 2 + log 2 - 1` for every `x > 0`. -/
theorem log_le_half_add {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ x / 2 + Real.log 2 - 1 := by
  have h1 : Real.log (x / 2) ≤ x / 2 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hx.ne' (by norm_num)] at h1
  linarith

/-- Exact logarithmic identity for `log 2 * alpha0 n` whenever `n ≥ 3`. -/
theorem log_two_mul_alpha0 {n : ℕ} (hn : 3 ≤ n) :
    Real.log 2 * alpha0 n =
      2 * Real.log (n : ℝ) - 2 * Real.log (Real.log (n : ℝ)) + 2 * alphaConst := by
  have hq : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn_gt1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn_gt1
  unfold alpha0 logBase2 alphaConst
  have hlog_div : Real.log (Real.log (n : ℝ) / Real.log 2) =
      Real.log (Real.log (n : ℝ)) - Real.log (Real.log 2) :=
    Real.log_div hL_pos.ne' hq.ne'
  have hlog_e2 : Real.log (Real.exp 1 / 2) = 1 - Real.log 2 := by
    rw [Real.log_div (Real.exp_pos 1).ne' (by norm_num), Real.log_exp]
  rw [hlog_div, hlog_e2]
  field_simp [hq.ne']
  ring

/-- `alpha0 n → +∞` as `n → ∞`. -/
theorem tendsto_alpha0_atTop : Tendsto alpha0 atTop atTop := by
  rw [tendsto_atTop]
  intro B
  have hq : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 3,
    hL.eventually_ge_atTop (Real.log 2 * B + 2 * Real.log 2 - 2 - 2 * alphaConst)] with n hn hLn
  have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hll := log_le_half_add hL_pos
  have hmul : Real.log 2 * B ≤ Real.log 2 * alpha0 n := by
    rw [log_two_mul_alpha0 hn]
    linarith
  exact le_of_mul_le_mul_left hmul hq

/-- Whenever `1 ≤ alpha0 n`, `(alphaNat n : ℝ) = alpha0 n - phaseDelta n`. -/
theorem alphaNat_cast_of_one_le {n : ℕ} (h : 1 ≤ alpha0 n) :
    (alphaNat n : ℝ) = alpha0 n - phaseDelta n := by
  unfold alphaNat alphaFloor phaseDelta
  have hfl_nonneg : 0 ≤ ⌊alpha0 n⌋ := Int.floor_nonneg.mpr (by linarith)
  have htoNat : ((⌊alpha0 n⌋.toNat : ℕ) : ℤ) = ⌊alpha0 n⌋ := Int.toNat_of_nonneg hfl_nonneg
  have hcast : ((⌊alpha0 n⌋.toNat : ℕ) : ℝ) = (⌊alpha0 n⌋ : ℝ) := by exact_mod_cast htoNat
  rw [hcast, Int.fract]
  ring

/-- `alphaNat n → +∞` as `n → ∞`. -/
theorem tendsto_alphaNat_atTop : Tendsto alphaNat atTop atTop := by
  rw [tendsto_atTop]
  intro M
  filter_upwards [tendsto_alpha0_atTop.eventually_ge_atTop ((M : ℝ) + 2)] with n hn
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have h1 : 1 ≤ alpha0 n := by linarith
  have hcast := alphaNat_cast_of_one_le h1
  have hδ := (phaseDelta_mem_Icc n).2
  have hle : (M : ℝ) ≤ (alphaNat n : ℝ) := by linarith
  exact Nat.cast_le.mp hle

/-- Joint asymptotic regime for `alphaNat n`: eventually `n ≥ 16`, `alphaNat n ≥ 20`,
`log 2 * alphaNat n = 2 log n - 2 log(log n) + 2 alphaConst - log 2 * phaseDelta n`, and
`(3 / 2) * log n ≤ log 2 * alphaNat n ≤ 2 * log n`. -/
theorem eventually_alphaNat_regime :
    ∀ᶠ n : ℕ in atTop,
      16 ≤ n ∧
      20 ≤ alphaNat n ∧
      (alphaNat n : ℝ) = alpha0 n - phaseDelta n ∧
      Real.log 2 * (alphaNat n : ℝ) =
        2 * Real.log (n : ℝ) - 2 * Real.log (Real.log (n : ℝ)) +
          2 * alphaConst - Real.log 2 * phaseDelta n ∧
      (3 / 2 : ℝ) * Real.log (n : ℝ) ≤ Real.log 2 * (alphaNat n : ℝ) ∧
      Real.log 2 * (alphaNat n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
  have hL : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  have hratio : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact h0.comp hL
  filter_upwards [eventually_ge_atTop 16,
    tendsto_alphaNat_atTop.eventually_ge_atTop 20,
    tendsto_alpha0_atTop.eventually_ge_atTop 10,
    hL.eventually_ge_atTop (40 + 8 * |alphaConst|),
    hll.eventually_ge_atTop (|alphaConst| + 2),
    hratio.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num))] with
      n hn16 hα20 hα0 hLbig hllbig hrat
  have hn3 : 3 ≤ n := by omega
  have hcast := alphaNat_cast_of_one_le (by linarith : 1 ≤ alpha0 n)
  have hq : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq_lt1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hδ := phaseDelta_mem_Icc n
  have heq : Real.log 2 * (alphaNat n : ℝ) =
      2 * Real.log (n : ℝ) - 2 * Real.log (Real.log (n : ℝ)) +
        2 * alphaConst - Real.log 2 * phaseDelta n := by
    rw [hcast, mul_sub, log_two_mul_alpha0 hn3]
  have habs_c : -|alphaConst| ≤ alphaConst ∧ alphaConst ≤ |alphaConst| := abs_le.mp le_rfl
  have hLpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hll_le : Real.log (Real.log (n : ℝ)) ≤ (1 / 8 : ℝ) * Real.log (n : ℝ) :=
    (div_le_iff₀ hLpos).mp hrat
  have hlo : (3 / 2 : ℝ) * Real.log (n : ℝ) ≤ Real.log 2 * (alphaNat n : ℝ) := by
    rw [heq]
    nlinarith [hδ.1, hδ.2, hq_lt1, habs_c.1, hLbig]
  have hhi : Real.log 2 * (alphaNat n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    rw [heq]
    nlinarith [hδ.1, hq, habs_c.2, hllbig]
  exact ⟨hn16, hα20, hcast, heq, hlo, hhi⟩

/-! ### 2. Effective Two-Sided Stirling Bounds and `- α * log α` Identity -/

/-- Effective two-sided Stirling bounds on `log (m!)` valid for **every** `m ≥ 1`:
`m log m - m + (log m)/2 ≤ log (m!) ≤ m log m - m + (log m)/2 + 1`. -/
theorem log_factorial_bounds {m : ℕ} (hm : 1 ≤ m) :
    (m : ℝ) * Real.log (m : ℝ) - (m : ℝ) + Real.log (m : ℝ) / 2 ≤ Real.log (m ! : ℝ) ∧
    Real.log (m ! : ℝ) ≤ (m : ℝ) * Real.log (m : ℝ) - (m : ℝ) + Real.log (m : ℝ) / 2 + 1 := by
  have hm_ne : m ≠ 0 := by omega
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  constructor
  · have hst := Stirling.le_log_factorial_stirling hm_ne
    have h2pi : 0 ≤ Real.log (2 * Real.pi) / 2 := by
      have hgt : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
      exact div_nonneg (Real.log_nonneg hgt) (by norm_num)
    linarith
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
    have hant : Real.log (Stirling.stirlingSeq (k + 1)) ≤ Real.log (Stirling.stirlingSeq 1) :=
      Stirling.log_stirlingSeq'_antitone (Nat.zero_le k)
    have hs1 : Real.log (Stirling.stirlingSeq 1) = 1 - Real.log 2 / 2 := by
      rw [Stirling.stirlingSeq_one, Real.log_div (Real.exp_pos 1).ne' (by positivity),
        Real.log_exp, Real.log_sqrt (by norm_num)]
    have hform := Stirling.log_stirlingSeq_formula (k + 1)
    have hlog2m : Real.log (2 * ((k + 1 : ℕ) : ℝ)) =
        Real.log 2 + Real.log ((k + 1 : ℕ) : ℝ) :=
      Real.log_mul (by norm_num) hm_pos.ne'
    have hlogme : Real.log (((k + 1 : ℕ) : ℝ) / Real.exp 1) =
        Real.log ((k + 1 : ℕ) : ℝ) - 1 := by
      rw [Real.log_div hm_pos.ne' (Real.exp_pos 1).ne', Real.log_exp]
    rw [hform, hs1, hlog2m, hlogme] at hant
    linarith

/-- Two-sided approximation of `- α * log α` using only `log u ≤ u - 1` applied to
`(2 L / q) / α` and `α / (2 L / q)` (zero asymptotic series required). -/
theorem alpha_mul_log_alpha_bounds {α L : ℝ} (hα : 0 < α) (hL : 0 < L) :
    let q := Real.log 2;
    -(α * (q - Real.log q + Real.log L)) + α * (2 * L - q * α) / (2 * L) ≤ -(α * Real.log α) ∧
    -(α * Real.log α) ≤ -(α * (q - Real.log q + Real.log L)) + (2 * L - q * α) / q := by
  intro q
  have hq : 0 < q := Real.log_pos (by norm_num)
  have h2Lq_pos : 0 < 2 * L / q := by positivity
  have hlog_2Lq : Real.log (2 * L / q) = q - Real.log q + Real.log L := by
    rw [Real.log_div (by positivity) hq.ne', Real.log_mul (by norm_num) hL.ne']
    dsimp [q]
    ring
  constructor
  · have h1 : Real.log (α / (2 * L / q)) ≤ α / (2 * L / q) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hα h2Lq_pos)
    rw [Real.log_div hα.ne' h2Lq_pos.ne', hlog_2Lq] at h1
    have hmul := mul_le_mul_of_nonneg_left h1 hα.le
    have hrhs : α * (α / (2 * L / q) - 1) = -(α * (2 * L - q * α) / (2 * L)) := by
      field_simp [hL.ne', hq.ne']
      ring
    rw [hrhs, mul_sub] at hmul
    linarith
  · have h2 : Real.log ((2 * L / q) / α) ≤ (2 * L / q) / α - 1 :=
      Real.log_le_sub_one_of_pos (div_pos h2Lq_pos hα)
    rw [Real.log_div h2Lq_pos.ne' hα.ne', hlog_2Lq] at h2
    have hmul := mul_le_mul_of_nonneg_left h2 hα.le
    have hrhs : α * ((2 * L / q) / α - 1) = (2 * L - q * α) / q := by
      field_simp [hα.ne', hq.ne']
    rw [hrhs] at hmul
    linarith

/-! ### 3. Falling-Factorial and Binomial Quadratic Shift Inequalities -/

/-- Exact real cast of `m.choose 2` valid for **every** `m : ℕ` (including `m = 0` and `m = 1`). -/
theorem cast_choose_two (m : ℕ) :
    (m.choose 2 : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  rcases m with _ | _ | m
  · norm_num
  · norm_num
  · rw [Nat.choose_two_right]
    have hsub : (m + 1 + 1 - 1 : ℕ) = m + 1 := by omega
    rw [hsub]
    have hdiv : 2 ∣ (m + 1 + 1) * (m + 1) := by
      rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · refine ⟨(k + 1) * (2 * k + 1), ?_⟩; ring
      · refine ⟨(2 * k + 3) * (k + 1), ?_⟩; ring
    rw [Nat.cast_div hdiv (by norm_num)]
    push_cast
    ring

/-- For every `0 ≤ i ≤ α`, `α! ≤ (α - i)! * α ^ i`. -/
theorem factorial_le_factorial_sub_mul_pow {α i : ℕ} (hi : i ≤ α) :
    α ! ≤ (α - i) ! * α ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hi' : i ≤ α := by omega
    have hstep : α - i = (α - (i + 1)) + 1 := by omega
    have hle : α - (i + 1) + 1 ≤ α := by omega
    calc
      α ! ≤ (α - i) ! * α ^ i := ih hi'
      _ = ((α - (i + 1) + 1) * (α - (i + 1)) !) * α ^ i := by
        rw [hstep, Nat.factorial_succ]
      _ ≤ (α * (α - (i + 1)) !) * α ^ i :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hle)
      _ = (α - (i + 1)) ! * α ^ (i + 1) := by
        rw [pow_succ]
        ring

/-- For every `0 ≤ i ≤ α`, `(α - i)! * (α - i) ^ i ≤ α!`. -/
theorem factorial_sub_mul_pow_le_factorial {α i : ℕ} (hi : i ≤ α) :
    (α - i) ! * (α - i) ^ i ≤ α ! := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hi' : i ≤ α := by omega
    have hstep : α - i = (α - (i + 1)) + 1 := by omega
    have hpow : (α - (i + 1)) ^ i ≤ (α - i) ^ i :=
      Nat.pow_le_pow_left (by omega) i
    have h1 : α - (i + 1) ≤ α - (i + 1) + 1 := by omega
    calc
      (α - (i + 1)) ! * (α - (i + 1)) ^ (i + 1)
          = (α - (i + 1)) ! * ((α - (i + 1)) * (α - (i + 1)) ^ i) := by
            rw [pow_succ']
      _ ≤ (α - (i + 1)) ! * ((α - (i + 1) + 1) * (α - i) ^ i) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 hpow)
      _ = ((α - (i + 1) + 1) * (α - (i + 1)) !) * (α - i) ^ i := by ring
      _ = (α - i) ! * (α - i) ^ i := by rw [← Nat.factorial_succ, ← hstep]
      _ ≤ α ! := ih hi'

/-- **Universal `S_+` falling-factorial + edge-exponent upper bound**:
For every `α ≥ 1` and **every** `0 ≤ j ≤ α + 1` (corresponding to fiber size
`s = α + 1 - j ∈ {0, 1, ..., α + 1}` and deficit `i = j - 1 ∈ {-1, 0, ..., α}`),
`- log (s!) - log 2 * s.choose 2 ≤ - log (α!) - log 2 * α.choose 2 +
  (j - 1) * (log 2 * α - log 2 / 2 + log α) - (log 2 / 2) * (j - 1) ^ 2`. -/
theorem falling_shift_upper_all {α j : ℕ} (hα : 1 ≤ α) (hj : j ≤ α + 1) :
    let s := α + 1 - j;
    let q := Real.log 2;
    -Real.log (s ! : ℝ) - q * (s.choose 2 : ℝ) ≤
      -Real.log (α ! : ℝ) - q * (α.choose 2 : ℝ) +
        ((j : ℝ) - 1) * (q * (α : ℝ) - q / 2 + Real.log (α : ℝ)) -
        (q / 2) * ((j : ℝ) - 1) ^ 2 := by
  intro s q
  have hα_pos : (0 : ℝ) < (α : ℝ) := by exact_mod_cast (by omega : 0 < α)
  rcases j with _ | i
  · -- Case `j = 0`, so `s = α + 1` and `j - 1 = -1`
    have hs : s = α + 1 := by omega
    rw [hs, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero α)),
      cast_choose_two (α + 1), cast_choose_two α, Nat.cast_zero]
    have hlog_le : Real.log (α : ℝ) ≤ Real.log ((α + 1 : ℕ) : ℝ) :=
      Real.log_le_log hα_pos (by exact_mod_cast (by omega : α ≤ α + 1))
    push_cast at hlog_le ⊢
    linarith
  · -- Case `j = i + 1`, so `0 ≤ i ≤ α`, `s = α - i`, and `j - 1 = i`
    have hi : i ≤ α := by omega
    have hs : s = α - i := by omega
    have hcast_s : (s : ℝ) = (α : ℝ) - (i : ℝ) := by
      rw [hs, Nat.cast_sub hi]
    have hquad : q * (s.choose 2 : ℝ) =
        q * (α.choose 2 : ℝ) - (i : ℝ) * (q * (α : ℝ) - q / 2) + (q / 2) * (i : ℝ) ^ 2 := by
      rw [cast_choose_two s, cast_choose_two α, hcast_s]
      ring
    have hfac_nat : α ! ≤ s ! * α ^ i := by
      rw [hs]
      exact factorial_le_factorial_sub_mul_pow hi
    have hfac_real : (α ! : ℝ) ≤ (s ! : ℝ) * (α : ℝ) ^ i := by exact_mod_cast hfac_nat
    have hlog_fac : Real.log (α ! : ℝ) ≤ Real.log (s ! : ℝ) + (i : ℝ) * Real.log (α : ℝ) := by
      have h1 := Real.log_le_log (Nat.cast_pos.mpr (Nat.factorial_pos α)) hfac_real
      rwa [Real.log_mul (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s)) (pow_ne_zero i hα_pos.ne'),
        Real.log_pow] at h1
    have hj_sub : ((i + 1 : ℕ) : ℝ) - 1 = (i : ℝ) := by push_cast; ring
    rw [hj_sub, hquad]
    linarith

/-- **Quantitative `O(1 / α)` lower bound** on the falling-factorial + edge-exponent shift for
bounded deficits `i ≤ 5` when `10 ≤ α`: error is at least `-50 / α`. -/
theorem falling_shift_lower_bounded {α i : ℕ} (hα : 10 ≤ α) (hi : i ≤ 5) :
    let s := α - i;
    let q := Real.log 2;
    -Real.log (α ! : ℝ) - q * (α.choose 2 : ℝ) +
        (i : ℝ) * (q * (α : ℝ) - q / 2 + Real.log (α : ℝ)) -
        (q / 2) * (i : ℝ) ^ 2 - 50 / (α : ℝ) ≤
      -Real.log (s ! : ℝ) - q * (s.choose 2 : ℝ) := by
  intro s q
  have hi_le_α : i ≤ α := by omega
  have hα_pos : (0 : ℝ) < (α : ℝ) := by exact_mod_cast (by omega : 0 < α)
  have hs_ge : 5 ≤ s := by dsimp [s]; omega
  have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
  have hcast_s : (s : ℝ) = (α : ℝ) - (i : ℝ) := Nat.cast_sub hi_le_α
  have hquad : q * (s.choose 2 : ℝ) =
      q * (α.choose 2 : ℝ) - (i : ℝ) * (q * (α : ℝ) - q / 2) + (q / 2) * (i : ℝ) ^ 2 := by
    rw [cast_choose_two s, cast_choose_two α, hcast_s]
    ring
  have hfac_nat : s ! * s ^ i ≤ α ! := factorial_sub_mul_pow_le_factorial hi_le_α
  have hfac_real : (s ! : ℝ) * (s : ℝ) ^ i ≤ (α ! : ℝ) := by exact_mod_cast hfac_nat
  have hlog_fac : Real.log (s ! : ℝ) + (i : ℝ) * Real.log (s : ℝ) ≤ Real.log (α ! : ℝ) := by
    have h1 := Real.log_le_log (by positivity) hfac_real
    rwa [Real.log_mul (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s)) (pow_ne_zero i hs_pos.ne'),
      Real.log_pow] at h1
  have hlog_diff : (i : ℝ) * (Real.log (α : ℝ) - Real.log (s : ℝ)) ≤ 50 / (α : ℝ) := by
    have hrat : Real.log (α : ℝ) - Real.log (s : ℝ) ≤ ((α : ℝ) - (s : ℝ)) / (s : ℝ) := by
      rw [← Real.log_div hα_pos.ne' hs_pos.ne']
      have h1 := Real.log_le_sub_one_of_pos (div_pos hα_pos hs_pos)
      have h2 : (α : ℝ) / (s : ℝ) - 1 = ((α : ℝ) - (s : ℝ)) / (s : ℝ) := by
        field_simp [hs_pos.ne']
      linarith
    have hi_le5 : (i : ℝ) ≤ 5 := by exact_mod_cast hi
    have hα_sub_s : (α : ℝ) - (s : ℝ) = (i : ℝ) := by linarith [hcast_s]
    have hs_half : (α : ℝ) / 2 ≤ (s : ℝ) := by
      have : (10 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα
      linarith [hcast_s, hi_le5]
    have hfrac : ((α : ℝ) - (s : ℝ)) / (s : ℝ) ≤ 10 / (α : ℝ) := by
      rw [hα_sub_s, div_le_div_iff₀ hs_pos hα_pos]
      nlinarith [hi_le5, hs_half, hα_pos]
    calc
      (i : ℝ) * (Real.log (α : ℝ) - Real.log (s : ℝ))
          ≤ (i : ℝ) * (10 / (α : ℝ)) :=
        mul_le_mul_of_nonneg_left (hrat.trans hfrac) (Nat.cast_nonneg i)
      _ ≤ 5 * (10 / (α : ℝ)) := mul_le_mul_of_nonneg_right hi_le5 (by positivity)
      _ = 50 / (α : ℝ) := by ring
  rw [hquad]
  linarith

/-! ### 4. High-Probability Independence-Number Cap (`IndepCapEvent`) -/

/-- Elementary binomial upper bound `n.choose m * m! ≤ n ^ m` for all `n, m : ℕ`. -/
theorem choose_mul_factorial_le_pow (n m : ℕ) : n.choose m * m ! ≤ n ^ m := by
  rw [Nat.mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, pow_succ']
    exact Nat.mul_le_mul (Nat.sub_le n k) ih

/-- Event that every independent set of `G` has cardinality at most `alphaNat n + 1`. -/
def IndepCapEvent (n : ℕ) : Set (SimpleGraph (Fin n)) :=
  {G | ∀ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) → S.card ≤ alphaNat n + 1}

/-- The expected number of independent sets of cardinality `alphaNat n + 2` in `G(n, 1/2)`
tends to `0` as `n → ∞`. -/
theorem tendsto_expected_indepSet_alpha_add_two :
    Tendsto
      (fun n : ℕ =>
        (n.choose (alphaNat n + 2) : ℝ) * (2⁻¹ : ℝ) ^ ((alphaNat n + 2).choose 2))
      atTop (𝓝 0) := by
  have hL : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact h0.comp hL
  have hquarter : Tendsto (fun n : ℕ => (1 / 4 : ℝ) * Real.log (n : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 4) hL
  have hexp0 : Tendsto (fun n : ℕ => Real.exp (-((1 / 4 : ℝ) * Real.log (n : ℝ))))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hquarter)
  refine squeeze_zero'
    (f := fun n : ℕ => (n.choose (alphaNat n + 2) : ℝ) * (2⁻¹ : ℝ) ^ ((alphaNat n + 2).choose 2))
    (g := fun n : ℕ => Real.exp (-((1 / 4 : ℝ) * Real.log (n : ℝ)))) ?_ ?_ hexp0
  · filter_upwards with n
    positivity
  · filter_upwards [eventually_alphaNat_regime,
      hL.eventually_ge_atTop (200 + 40 * |alphaConst|),
      hratio.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 40 by norm_num))] with
        n ⟨hn16, hα20, _, hqα, hlo, _⟩ hLbig hrat
    set α : ℕ := alphaNat n
    set L : ℝ := Real.log (n : ℝ)
    set q : ℝ := Real.log 2
    have hq_pos : 0 < q := Real.log_pos (by norm_num)
    have hq_gt : (0.69 : ℝ) < q := by dsimp [q]; linarith [Real.log_two_gt_d9]
    have hq_lt1 : q < 1 := by dsimp [q]; linarith [Real.log_two_lt_d9]
    have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hα_pos : (0 : ℝ) < (α : ℝ) := by exact_mod_cast (by omega : 0 < α)
    have hll_le : Real.log L ≤ (1 / 40 : ℝ) * L := (div_le_iff₀ hL_pos).mp hrat
    -- Step 1: `n.choose (α + 2) ≤ n ^ (α + 2) / α!`
    have hchoose_nat : n.choose (α + 2) * α ! ≤ n ^ (α + 2) := by
      calc
        n.choose (α + 2) * α ! ≤ n.choose (α + 2) * (α + 2) ! :=
          Nat.mul_le_mul_left _ (Nat.factorial_le (by omega))
        _ ≤ n ^ (α + 2) := choose_mul_factorial_le_pow n (α + 2)
    have hfac_pos : (0 : ℝ) < (α ! : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos α)
    have hchoose_real : (n.choose (α + 2) : ℝ) ≤ (n : ℝ) ^ (α + 2) / (α ! : ℝ) := by
      rw [le_div_iff₀ hfac_pos]
      exact_mod_cast hchoose_nat
    have hexp_n : (n : ℝ) ^ (α + 2) = Real.exp (((α + 2 : ℕ) : ℝ) * L) := by
      rw [Real.exp_nat_mul, Real.exp_log hn_pos]
    have hexp_fac : (α ! : ℝ) = Real.exp (Real.log (α ! : ℝ)) := (Real.exp_log hfac_pos).symm
    have hexp_two : (2⁻¹ : ℝ) ^ ((α + 2).choose 2) =
        Real.exp (-q * (((α + 2).choose 2 : ℝ))) := by
      rw [show -q * (((α + 2).choose 2 : ℝ)) =
          (((α + 2).choose 2 : ℕ) : ℝ) * Real.log (2⁻¹) by
            dsimp [q]; rw [Real.log_inv]; ring,
        Real.exp_nat_mul, Real.exp_log (by norm_num)]
    have hprod_le : (n.choose (α + 2) : ℝ) * (2⁻¹ : ℝ) ^ ((α + 2).choose 2) ≤
        Real.exp ((((α + 2 : ℕ) : ℝ) * L - Real.log (α ! : ℝ)) -
          q * (((α + 2).choose 2 : ℝ))) := by
      calc
        (n.choose (α + 2) : ℝ) * (2⁻¹ : ℝ) ^ ((α + 2).choose 2)
            ≤ ((n : ℝ) ^ (α + 2) / (α ! : ℝ)) * (2⁻¹ : ℝ) ^ ((α + 2).choose 2) :=
          mul_le_mul_of_nonneg_right hchoose_real (by positivity)
        _ = Real.exp ((((α + 2 : ℕ) : ℝ) * L - Real.log (α ! : ℝ)) -
              q * (((α + 2).choose 2 : ℝ))) := by
          rw [hexp_n, hexp_fac, hexp_two, Real.log_exp, ← Real.exp_sub, ← Real.exp_add]
          congr 1
          ring
    refine hprod_le.trans (Real.exp_le_exp.mpr ?_)
    -- Step 2: Bound the exponent by `-((1 / 4) * L)`
    have hst := (log_factorial_bounds (by omega : 1 ≤ α)).1
    have hlogα_nonneg : 0 ≤ Real.log (α : ℝ) / 2 :=
      div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ α))) (by norm_num)
    have hαlog := (alpha_mul_log_alpha_bounds hα_pos hL_pos).2
    have hch : (((α + 2).choose 2 : ℝ)) = ((α : ℝ) + 2) * ((α : ℝ) + 1) / 2 := by
      have h1 := cast_choose_two (α + 2)
      push_cast at h1
      linarith
    push_cast
    set Δ : ℝ := 2 * Real.log L - 2 * alphaConst + q * phaseDelta n
    have h2L_sub : 2 * L - q * (α : ℝ) = Δ := by
      dsimp [Δ, α, L, q] at hqα ⊢
      linarith
    have hq_prod : q * (((α : ℝ) + 2) * ((α : ℝ) + 1) / 2) =
        (1 / 2 : ℝ) * ((α : ℝ) + 2) * ((2 * L - Δ) + q) := by
      have hqα' : q * (α : ℝ) = 2 * L - Δ := by linarith only [h2L_sub]
      calc
        q * (((α : ℝ) + 2) * ((α : ℝ) + 1) / 2)
            = (1 / 2 : ℝ) * ((α : ℝ) + 2) * (q * (α : ℝ) + q) := by ring
        _ = (1 / 2 : ℝ) * ((α : ℝ) + 2) * ((2 * L - Δ) + q) := by rw [hqα']
    have hid : ((α : ℝ) + 2) * L +
        (-((α : ℝ) * (q - Real.log q + Real.log L)) + Δ / q + (α : ℝ)) -
        (1 / 2 : ℝ) * ((α : ℝ) + 2) * ((2 * L - Δ) + q) =
        (α : ℝ) * (-q + (q / 2) * phaseDelta n) + Δ / q + Δ - q := by
      dsimp [Δ, alphaConst, q]
      ring
    have hexp_le1 : (((α : ℝ) + 2) * L - Real.log (α ! : ℝ)) -
        q * (((α + 2).choose 2 : ℝ)) ≤
        (α : ℝ) * (-q + (q / 2) * phaseDelta n) + Δ / q + Δ - q := by
      rw [hch, hq_prod]
      have hαlog' : -((α : ℝ) * (q - Real.log q + Real.log L)) + (2 * L - q * (α : ℝ)) / q ≥
          -((α : ℝ) * Real.log (α : ℝ)) := hαlog
      rw [h2L_sub] at hαlog'
      linarith only [hst, hlogα_nonneg, hαlog', hid]
    have hδ := phaseDelta_mem_Icc n
    have habs_c : -|alphaConst| ≤ alphaConst ∧ alphaConst ≤ |alphaConst| := abs_le.mp le_rfl
    have hα_term : (α : ℝ) * (-q + (q / 2) * phaseDelta n) ≤ -(3 / 4 : ℝ) * L := by
      have hqδ_le : q * phaseDelta n ≤ q := mul_le_of_le_one_right hq_pos.le hδ.2
      have hcoeff : -q + (q / 2) * phaseDelta n ≤ -(q / 2) := by linarith only [hqδ_le]
      calc
        (α : ℝ) * (-q + (q / 2) * phaseDelta n)
            ≤ (α : ℝ) * (-(q / 2)) := mul_le_mul_of_nonneg_left hcoeff hα_pos.le
        _ = -(1 / 2 : ℝ) * (q * (α : ℝ)) := by ring
        _ ≤ -(1 / 2 : ℝ) * ((3 / 2 : ℝ) * L) := by linarith only [hlo]
        _ = -(3 / 4 : ℝ) * L := by ring
    have hqδ_le1 : q * phaseDelta n ≤ 1 :=
      (mul_le_of_le_one_right hq_pos.le hδ.2).trans hq_lt1.le
    have hΔ_hi : Δ ≤ (1 / 20 : ℝ) * L + 2 * |alphaConst| + 1 := by
      dsimp [Δ]
      linarith only [hll_le, habs_c.1, hqδ_le1]
    have hΔq_hi : Δ / q ≤ 2 * ((1 / 20 : ℝ) * L + 2 * |alphaConst| + 1) := by
      rw [div_le_iff₀ hq_pos]
      have hpos_rhs : 0 ≤ (1 / 20 : ℝ) * L + 2 * |alphaConst| + 1 := by positivity
      have hgt_half : (1 / 2 : ℝ) ≤ q := by linarith only [hq_gt]
      calc
        Δ ≤ (1 / 20 : ℝ) * L + 2 * |alphaConst| + 1 := hΔ_hi
        _ = (2 * ((1 / 20 : ℝ) * L + 2 * |alphaConst| + 1)) * (1 / 2) := by ring
        _ ≤ (2 * ((1 / 20 : ℝ) * L + 2 * |alphaConst| + 1)) * q :=
          mul_le_mul_of_nonneg_left hgt_half (by positivity)
    have habs_nonneg : 0 ≤ |alphaConst| := abs_nonneg alphaConst
    linarith only [hexp_le1, hα_term, hΔ_hi, hΔq_hi, hLbig, hq_pos, habs_nonneg]

/-- **High-probability independence-number cap (`arXiv:2608.30604`, Section 2)**:
As `n → ∞`, with probability `→ 1` in `G(n, 1/2)`, every independent set of `G` has cardinality
at most `alphaNat n + 1`. -/
theorem tendsto_probGnpHalf_indepCapEvent :
    Tendsto (fun n : ℕ => probGnpHalf n (IndepCapEvent n)) atTop (𝓝 1) := by
  apply tendsto_probGnpHalf_one_of_compl_tendsto_zero
  refine squeeze_zero'
    (f := fun n : ℕ => probGnpHalf n (IndepCapEvent n)ᶜ)
    (g := fun n : ℕ => (n.choose (alphaNat n + 2) : ℝ) * (2⁻¹ : ℝ) ^ ((alphaNat n + 2).choose 2))
    ?_ ?_ tendsto_expected_indepSet_alpha_add_two
  · filter_upwards with n
    exact probGnpHalf_nonneg n _
  · filter_upwards with n
    let m := alphaNat n + 2
    let F : Finset (Finset (Fin n)) := Finset.univ.powersetCard m
    have hsub : (IndepCapEvent n)ᶜ ⊆
        ⋃ T ∈ F, {G : SimpleGraph (Fin n) | G.IsIndepSet (T : Set (Fin n))} := by
      intro G hG
      simp only [IndepCapEvent, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall] at hG
      rcases hG with ⟨S, hS_indep, hS_gt⟩
      have hm_le : m ≤ S.card := by dsimp [m]; omega
      obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hm_le
      refine Set.mem_biUnion (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ T, hTcard⟩) ?_
      exact hS_indep.mono (Finset.coe_subset.mpr hTS)
    calc
      probGnpHalf n (IndepCapEvent n)ᶜ
          ≤ probGnpHalf n (⋃ T ∈ F, {G | G.IsIndepSet (T : Set (Fin n))}) :=
        probGnpHalf_mono hsub
      _ ≤ ∑ T ∈ F, probGnpHalf n {G | G.IsIndepSet (T : Set (Fin n))} :=
        probGnpHalf_biUnion_le n F _
      _ = ∑ T ∈ F, (2⁻¹ : ℝ) ^ m.choose 2 := by
        refine Finset.sum_congr rfl fun T hT => ?_
        rw [probGnpHalf_isIndepSet, (Finset.mem_powersetCard.mp hT).2]
      _ = (n.choose m : ℝ) * (2⁻¹ : ℝ) ^ m.choose 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard, Finset.card_univ,
          Fintype.card_fin]

end JSP000506
