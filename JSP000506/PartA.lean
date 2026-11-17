import Mathlib.Topology.Order.IntermediateValue
import JSP000506.Phase

/-!
# Part A: Continuous Profile Roots, Threshold Separation, and Rounded 4-Size Witness

This module formalizes Sections 3 and 4 (Part A) of Samuil Petkov's *A Full-Sequence Quantitative
Gap Between the Chromatic and Cochromatic Numbers of a Random Graph* (`arXiv:2608.30604`):

1. **Base profile functional `profileBasePhi n s`**:
   captures the common leading log-expectation per color class at average class size `s`, satisfying
   `profileBasePhi n (α_n - T) = (T - targetDeficit δ_n) * log n + O(log(log n))` uniformly on
   `T ∈ [2.6, 4.1]` and exact linear difference
   `profileBasePhi n (α_n - T₁) - profileBasePhi n (α_n - T₂) = (T₁ - T₂) * (log n + O(log(log n)))`.
2. **Continuous threshold roots `TPlus n`, `TFour n`, `sPlus n`, `sFourCo n`**:
   existence via the intermediate value theorem (`intermediate_value_Icc`) and quantitative root
   separation
   `n / sPlus n - n / sFourCo n = ((log 2)^2 / 4 * petkovA4 δ_n + O(log(log n) / log n)) * n / (log n)^3`.
3. **Discrete thresholds `kChiMinus n` and `kCoSeed n`** separated by
   `((log 2)^2 / 4 * petkovA4 δ_n - ε_A n) * n / (log n)^3` with `0 ≤ ε_A n` and `ε_A n → 0`,
   together with subcritical shift bounds for `kChiMinus n` (used in `PartB.lean`).
4. **Exact integer rounding (`witnessCounts n : Fin 4 → ℕ`)** of the optimal 4-size Gibbs profile
   via unimodular `(2, 3)` deficit adjustment, proving exact block count `kCoSeed n`, exact vertex
   sum `n`, linear multiplicities, and supercritical log-first-moment `≥ 100 * n / (log n)^2`.
-/

open Filter SimpleGraph Finset
open scoped Topology BigOperators Nat Classical

namespace JSP000506

/-! ### 1. Base Profile Functional `profileBasePhi` and Asymptotic Identities -/

/-- Common per-class logarithmic base functional `Φ_base(n, s)` at average class size `s`. -/
noncomputable def profileBasePhi (n : ℕ) (s : ℝ) : ℝ :=
  let α := alphaNat n
  let L := Real.log (n : ℝ)
  let q := Real.log 2
  (s * L - s - L + Real.log s + 1) -
    Real.log (α ! : ℝ) - q * (α.choose 2 : ℝ) +
    ((α : ℝ) - s) * (q * (α : ℝ) - q / 2 + Real.log (α : ℝ))

/-- Continuity of `T ↦ profileBasePhi n ((alphaNat n : ℝ) - T)` on `[2.6, 4.1]` once `10 ≤ alphaNat n`. -/
theorem continuousOn_profileBasePhi_sub {n : ℕ} (hα : 10 ≤ alphaNat n) :
    ContinuousOn (fun T : ℝ => profileBasePhi n ((alphaNat n : ℝ) - T)) (Set.Icc (2.6 : ℝ) 4.1) := by
  unfold profileBasePhi
  have hs_ne : ∀ T ∈ Set.Icc (2.6 : ℝ) 4.1, (alphaNat n : ℝ) - T ≠ 0 := by
    intro T hT
    have hα10 : (10 : ℝ) ≤ (alphaNat n : ℝ) := by exact_mod_cast hα
    linarith [hT.2]
  have hsub : ContinuousOn (fun T : ℝ => (alphaNat n : ℝ) - T) (Set.Icc (2.6 : ℝ) 4.1) :=
    continuousOn_const.sub continuousOn_id
  have hlog : ContinuousOn (fun T : ℝ => Real.log ((alphaNat n : ℝ) - T)) (Set.Icc (2.6 : ℝ) 4.1) :=
    hsub.log hs_ne
  refine ((((((hsub.mul continuousOn_const).sub hsub).sub continuousOn_const).add hlog).add
    continuousOn_const).sub continuousOn_const).sub continuousOn_const |>.add ?_
  exact (continuousOn_const.sub hsub).mul continuousOn_const

/-- Elementary two-sided logarithmic Lipschitz bound `|log a - log b| ≤ |a - b|` for `1 ≤ a, 1 ≤ b`. -/
theorem abs_log_sub_log_le {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| := by
  have ha_pos : 0 < a := by positivity
  have hb_pos : 0 < b := by positivity
  rw [abs_le]
  constructor
  · have h1 : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb_pos ha_pos)
    rw [Real.log_div hb_pos.ne' ha_pos.ne'] at h1
    have h2 : b / a - 1 = (b - a) / a := by field_simp [ha_pos.ne']
    have h3 : (b - a) / a ≤ |a - b| := by
      rw [div_le_iff₀ ha_pos]
      have hba : b - a ≤ |a - b| := by rw [abs_sub_comm]; exact le_abs_self (b - a)
      calc
        b - a ≤ |a - b| := hba
        _ = |a - b| * 1 := (mul_one _).symm
        _ ≤ |a - b| * a := mul_le_mul_of_nonneg_left ha (abs_nonneg _)
    linarith
  · have h1 : Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha_pos hb_pos)
    rw [Real.log_div ha_pos.ne' hb_pos.ne'] at h1
    have h2 : a / b - 1 = (a - b) / b := by field_simp [hb_pos.ne']
    have h3 : (a - b) / b ≤ |a - b| := by
      rw [div_le_iff₀ hb_pos]
      calc
        a - b ≤ |a - b| := le_abs_self (a - b)
        _ = |a - b| * 1 := (mul_one _).symm
        _ ≤ |a - b| * b := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    linarith

/-- Uniform `O(log(log n))` approximation of `profileBasePhi n ((alphaNat n : ℝ) - T)` on `[2.6, 4.1]`. -/
theorem abs_profileBasePhi_approx {n : ℕ}
    (hn16 : 16 ≤ n) (hα20 : 20 ≤ alphaNat n)
    (hqα : Real.log 2 * (alphaNat n : ℝ) =
      2 * Real.log (n : ℝ) - 2 * Real.log (Real.log (n : ℝ)) +
        2 * alphaConst - Real.log 2 * phaseDelta n)
    (hhi : Real.log 2 * (alphaNat n : ℝ) ≤ 2 * Real.log (n : ℝ))
    {T : ℝ} (hT : T ∈ Set.Icc (2.6 : ℝ) 4.1) :
    |profileBasePhi n ((alphaNat n : ℝ) - T) -
      (T - targetDeficit (phaseDelta n)) * Real.log (n : ℝ)| ≤
      30 * |Real.log (Real.log (n : ℝ))| + 30 * |alphaConst| + 60 := by
  set α : ℕ := alphaNat n
  set L : ℝ := Real.log (n : ℝ)
  set q : ℝ := Real.log 2
  set δ : ℝ := phaseDelta n
  set s : ℝ := (α : ℝ) - T
  have hq_pos : 0 < q := Real.log_pos (by norm_num)
  have hq_gt : (2 / 3 : ℝ) < q := by dsimp [q]; linarith [Real.log_two_gt_d9]
  have hq_lt1 : q < 1 := by dsimp [q]; linarith [Real.log_two_lt_d9]
  have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hα_ge20 : (20 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα20
  have hα_pos : 0 < (α : ℝ) := by positivity
  have hs_ge : 1 ≤ s := by dsimp [s]; linarith [hT.2]
  have hs_le : s ≤ (α : ℝ) := by dsimp [s]; linarith [hT.1]
  have hδ := phaseDelta_mem_Icc n
  set Δ : ℝ := 2 * Real.log L - 2 * alphaConst + q * δ
  have h2L_sub : 2 * L - q * (α : ℝ) = Δ := by
    dsimp [Δ, α, L, q, δ] at hqα ⊢
    linarith
  have hα_eq : (α : ℝ) = (2 * L - Δ) / q := by
    rw [eq_div_iff hq_pos.ne']
    linarith only [h2L_sub]
  have hch := cast_choose_two α
  let MainTerm : ℝ :=
    (s * L - s - L + 1) + (-((α : ℝ) * (q - Real.log q + Real.log L)) + (α : ℝ)) -
      q * ((α : ℝ) * ((α : ℝ) - 1) / 2) + T * (q * (α : ℝ) - q / 2)
  let RemTerm : ℝ :=
    Real.log s +
      (-Real.log (α ! : ℝ) - (-((α : ℝ) * Real.log (α : ℝ)) + (α : ℝ) - Real.log (α : ℝ) / 2)) +
      (-((α : ℝ) * Real.log (α : ℝ)) - (-((α : ℝ) * (q - Real.log q + Real.log L)))) -
      Real.log (α : ℝ) / 2 + T * Real.log (α : ℝ)
  have hsplit : profileBasePhi n s = MainTerm + RemTerm := by
    unfold profileBasePhi
    dsimp [MainTerm, RemTerm, α, L, q, s]
    rw [hch]
    ring
  have hMain_id : MainTerm - (T - targetDeficit δ) * L =
      T + 1 - T * Δ - (q / 2) * T - (Δ / q) * (-1 + (q / 2) * δ) := by
    dsimp [MainTerm, s]
    unfold targetDeficit
    rw [hα_eq]
    dsimp [Δ, alphaConst, q]
    field_simp [hq_pos.ne']
    ring
  have habs_Δ : |Δ| ≤ 2 * |Real.log L| + 2 * |alphaConst| + 1 := by
    have hqδ : |q * δ| ≤ 1 := by
      rw [abs_of_nonneg (mul_nonneg hq_pos.le hδ.1)]
      exact (mul_le_of_le_one_right hq_pos.le hδ.2).trans hq_lt1.le
    calc
      |Δ| = |(2 * Real.log L - 2 * alphaConst) + q * δ| := rfl
      _ ≤ |2 * Real.log L - 2 * alphaConst| + |q * δ| := abs_add_le _ _
      _ ≤ (|2 * Real.log L| + |2 * alphaConst|) + 1 := by
        linarith [abs_sub (2 * Real.log L) (2 * alphaConst), hqδ]
      _ = 2 * |Real.log L| + 2 * |alphaConst| + 1 := by
        simp [abs_mul]
  have habs_Main : |MainTerm - (T - targetDeficit δ) * L| ≤ 8 * |Δ| + 6 := by
    rw [hMain_id]
    have hT_abs : |T| ≤ 5 := abs_le.mpr ⟨by linarith [hT.1], by linarith [hT.2]⟩
    have hcoeff_δ : |-1 + (q / 2) * δ| ≤ 1 := by
      rw [abs_le]
      have h1 : 0 ≤ (q / 2) * δ := mul_nonneg (by positivity) hδ.1
      have h2 : (q / 2) * δ ≤ 1 / 2 := by
        have hq2 : q / 2 ≤ 1 / 2 := by linarith only [hq_lt1]
        exact (mul_le_of_le_one_right (by positivity) hδ.2).trans hq2
      constructor <;> linarith
    have hΔq_abs : |(Δ / q) * (-1 + (q / 2) * δ)| ≤ 2 * |Δ| := by
      rw [abs_mul, abs_div, abs_of_pos hq_pos]
      have hdiv2 : |Δ| / q ≤ 2 * |Δ| := by
        rw [div_le_iff₀ hq_pos]
        have hgt_half : (1 / 2 : ℝ) ≤ q := by linarith only [hq_gt]
        calc
          |Δ| = (2 * |Δ|) * (1 / 2) := by ring
          _ ≤ (2 * |Δ|) * q := mul_le_mul_of_nonneg_left hgt_half (by positivity)
      calc
        (|Δ| / q) * |-1 + (q / 2) * δ| ≤ (|Δ| / q) * 1 :=
          mul_le_mul_of_nonneg_left hcoeff_δ (by positivity)
        _ ≤ 2 * |Δ| := by linarith
    have hTΔ_abs : |T * Δ| ≤ 5 * |Δ| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hT_abs (abs_nonneg Δ)
    have hlead_abs : |T + 1 - (q / 2) * T| ≤ 6 := by
      rw [abs_le]
      have h1 : 0 ≤ (q / 2) * T := mul_nonneg (by positivity) (by linarith [hT.1])
      have h2 : (q / 2) * T ≤ 3 := by
        have hq2 : q / 2 ≤ 1 / 2 := by linarith only [hq_lt1]
        calc
          (q / 2) * T ≤ (1 / 2 : ℝ) * T := mul_le_mul_of_nonneg_right hq2 (by linarith [hT.1])
          _ ≤ 3 := by linarith [hT.2]
      constructor <;> linarith [hT.1, hT.2]
    have hrew : T + 1 - T * Δ - (q / 2) * T - (Δ / q) * (-1 + (q / 2) * δ) =
        ((T + 1 - (q / 2) * T) - T * Δ) - (Δ / q) * (-1 + (q / 2) * δ) := by ring
    rw [hrew]
    have htri1 := abs_sub ((T + 1 - (q / 2) * T) - T * Δ) ((Δ / q) * (-1 + (q / 2) * δ))
    have htri2 := abs_sub (T + 1 - (q / 2) * T) (T * Δ)
    linarith [abs_nonneg Δ]
  have hlogα_le : Real.log (α : ℝ) ≤ |Real.log L| + 2 := by
    have hα_le_3L : (α : ℝ) ≤ 3 * L := by
      have h1 : (2 / 3 : ℝ) * (α : ℝ) ≤ q * (α : ℝ) :=
        mul_le_mul_of_nonneg_right hq_gt.le hα_pos.le
      linarith [hhi]
    have hlog3 : Real.log 3 ≤ 2 := by
      have he2 : (3 : ℝ) ≤ Real.exp 2 := by
        have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith
      calc
        Real.log 3 ≤ Real.log (Real.exp 2) := Real.log_le_log (by norm_num) he2
        _ = 2 := Real.log_exp 2
    calc
      Real.log (α : ℝ) ≤ Real.log (3 * L) := Real.log_le_log hα_pos hα_le_3L
      _ = Real.log 3 + Real.log L := Real.log_mul (by norm_num) hL_pos.ne'
      _ ≤ 2 + |Real.log L| := add_le_add hlog3 (le_abs_self _)
      _ = |Real.log L| + 2 := add_comm _ _
  have hlogα_nonneg : 0 ≤ Real.log (α : ℝ) := Real.log_nonneg (by linarith)
  have hlogs_nonneg : 0 ≤ Real.log s := Real.log_nonneg hs_ge
  have hlogs_le : Real.log s ≤ Real.log (α : ℝ) := Real.log_le_log (by positivity) hs_le
  have hst := log_factorial_bounds (by omega : 1 ≤ α)
  have hst_abs :
      |-Real.log (α ! : ℝ) - (-((α : ℝ) * Real.log (α : ℝ)) + (α : ℝ) - Real.log (α : ℝ) / 2)| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hst.2], by linarith [hst.1]⟩
  have hαlog := alpha_mul_log_alpha_bounds hα_pos hL_pos
  have hαlog_abs :
      |-((α : ℝ) * Real.log (α : ℝ)) - (-((α : ℝ) * (q - Real.log q + Real.log L)))| ≤ 2 * |Δ| := by
    have hlo_b : -((α : ℝ) * (q - Real.log q + Real.log L)) + (α : ℝ) * Δ / (2 * L) ≤
        -((α : ℝ) * Real.log (α : ℝ)) := by
      have h1 := hαlog.1
      change -((α : ℝ) * (q - Real.log q + Real.log L)) +
        (α : ℝ) * (2 * L - q * (α : ℝ)) / (2 * L) ≤ -((α : ℝ) * Real.log (α : ℝ)) at h1
      rwa [h2L_sub] at h1
    have hhi_b : -((α : ℝ) * Real.log (α : ℝ)) ≤
        -((α : ℝ) * (q - Real.log q + Real.log L)) + Δ / q := by
      have h2 := hαlog.2
      change -((α : ℝ) * Real.log (α : ℝ)) ≤
        -((α : ℝ) * (q - Real.log q + Real.log L)) + (2 * L - q * (α : ℝ)) / q at h2
      rwa [h2L_sub] at h2
    have hα_div_2L : (α : ℝ) / (2 * L) ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : (2 / 3 : ℝ) * (α : ℝ) ≤ q * (α : ℝ) :=
        mul_le_mul_of_nonneg_right hq_gt.le hα_pos.le
      linarith [hhi, hα_pos]
    have hb1 : -2 * |Δ| ≤ (α : ℝ) * Δ / (2 * L) := by
      have habs_t : |(α : ℝ) * Δ / (2 * L)| ≤ 2 * |Δ| := by
        rw [show (α : ℝ) * Δ / (2 * L) = ((α : ℝ) / (2 * L)) * Δ by ring,
          abs_mul, abs_of_pos (by positivity)]
        exact mul_le_mul_of_nonneg_right hα_div_2L (abs_nonneg Δ)
      linarith [(abs_le.mp habs_t).1]
    have hb2 : Δ / q ≤ 2 * |Δ| := by
      rw [div_le_iff₀ hq_pos]
      have hgt_half : (1 / 2 : ℝ) ≤ q := by linarith only [hq_gt]
      calc
        Δ ≤ |Δ| := le_abs_self Δ
        _ = (2 * |Δ|) * (1 / 2) := by ring
        _ ≤ (2 * |Δ|) * q := mul_le_mul_of_nonneg_left hgt_half (by positivity)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have habs_Rem : |RemTerm| ≤ 6 * |Real.log L| + 2 * |Δ| + 15 := by
    have htail_abs : |Real.log s - Real.log (α : ℝ) / 2 + T * Real.log (α : ℝ)| ≤
        6 * Real.log (α : ℝ) := by
      rw [abs_le]
      have h1 : 0 ≤ T * Real.log (α : ℝ) := mul_nonneg (by linarith [hT.1]) hlogα_nonneg
      have h2 : T * Real.log (α : ℝ) ≤ 5 * Real.log (α : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith [hT.2]) hlogα_nonneg
      constructor <;> linarith
    have hrew_R : RemTerm =
        ((Real.log s - Real.log (α : ℝ) / 2 + T * Real.log (α : ℝ)) +
          (-Real.log (α ! : ℝ) - (-((α : ℝ) * Real.log (α : ℝ)) + (α : ℝ) - Real.log (α : ℝ) / 2))) +
          (-((α : ℝ) * Real.log (α : ℝ)) - (-((α : ℝ) * (q - Real.log q + Real.log L)))) := by
      dsimp [RemTerm]
      ring
    rw [hrew_R]
    have ht1 := abs_add_le
      ((Real.log s - Real.log (α : ℝ) / 2 + T * Real.log (α : ℝ)) +
        (-Real.log (α ! : ℝ) - (-((α : ℝ) * Real.log (α : ℝ)) + (α : ℝ) - Real.log (α : ℝ) / 2)))
      (-((α : ℝ) * Real.log (α : ℝ)) - (-((α : ℝ) * (q - Real.log q + Real.log L))))
    have ht2 := abs_add_le
      (Real.log s - Real.log (α : ℝ) / 2 + T * Real.log (α : ℝ))
      (-Real.log (α ! : ℝ) - (-((α : ℝ) * Real.log (α : ℝ)) + (α : ℝ) - Real.log (α : ℝ) / 2))
    linarith [hlogα_le]
  rw [hsplit, show MainTerm + RemTerm - (T - targetDeficit δ) * L =
    (MainTerm - (T - targetDeficit δ) * L) + RemTerm by ring]
  have htri := abs_add_le (MainTerm - (T - targetDeficit δ) * L) RemTerm
  linarith [htri, habs_Main, habs_Rem, habs_Δ, abs_nonneg (Real.log L), abs_nonneg alphaConst]

/-- Exact linear-slope difference bound for `profileBasePhi n ((alphaNat n : ℝ) - T)` on `[2.6, 4.1]`:
`|(profileBasePhi n (α - T₁) - profileBasePhi n (α - T₂)) - (T₁ - T₂) * L|
  ≤ |T₁ - T₂| * (3 |log L| + 2 |alphaConst| + 6)`. -/
theorem abs_profileBasePhi_diff_approx {n : ℕ}
    (hn16 : 16 ≤ n) (hα20 : 20 ≤ alphaNat n)
    (hqα : Real.log 2 * (alphaNat n : ℝ) =
      2 * Real.log (n : ℝ) - 2 * Real.log (Real.log (n : ℝ)) +
        2 * alphaConst - Real.log 2 * phaseDelta n)
    (hhi : Real.log 2 * (alphaNat n : ℝ) ≤ 2 * Real.log (n : ℝ))
    {T₁ T₂ : ℝ} (hT₁ : T₁ ∈ Set.Icc (2.6 : ℝ) 4.1) (hT₂ : T₂ ∈ Set.Icc (2.6 : ℝ) 4.1) :
    |(profileBasePhi n ((alphaNat n : ℝ) - T₁) - profileBasePhi n ((alphaNat n : ℝ) - T₂)) -
      (T₁ - T₂) * Real.log (n : ℝ)| ≤
      |T₁ - T₂| * (3 * |Real.log (Real.log (n : ℝ))| + 2 * |alphaConst| + 6) := by
  set α : ℕ := alphaNat n
  set L : ℝ := Real.log (n : ℝ)
  set q : ℝ := Real.log 2
  have hq_pos : 0 < q := Real.log_pos (by norm_num)
  have hq_gt : (2 / 3 : ℝ) < q := by dsimp [q]; linarith [Real.log_two_gt_d9]
  have hq_lt1 : q < 1 := by dsimp [q]; linarith [Real.log_two_lt_d9]
  have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hα_ge20 : (20 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα20
  have hα_pos : 0 < (α : ℝ) := by positivity
  have hs₁_ge : 1 ≤ (α : ℝ) - T₁ := by linarith [hT₁.2]
  have hs₂_ge : 1 ≤ (α : ℝ) - T₂ := by linarith [hT₂.2]
  have hdiff_id :
      (profileBasePhi n ((α : ℝ) - T₁) - profileBasePhi n ((α : ℝ) - T₂)) - (T₁ - T₂) * L =
        (T₁ - T₂) * ((q * (α : ℝ) - 2 * L) + 1 - q / 2 + Real.log (α : ℝ)) +
          (Real.log ((α : ℝ) - T₁) - Real.log ((α : ℝ) - T₂)) := by
    unfold profileBasePhi
    dsimp [α, L, q]
    ring
  rw [hdiff_id]
  have hlog_lip : |Real.log ((α : ℝ) - T₁) - Real.log ((α : ℝ) - T₂)| ≤ |T₁ - T₂| := by
    have h1 := abs_log_sub_log_le hs₁_ge hs₂_ge
    have heq : |((α : ℝ) - T₁) - ((α : ℝ) - T₂)| = |T₁ - T₂| := by
      rw [show ((α : ℝ) - T₁) - ((α : ℝ) - T₂) = -(T₁ - T₂) by ring, abs_neg]
    rwa [heq] at h1
  have hlogα_le : Real.log (α : ℝ) ≤ |Real.log L| + 2 := by
    have hα_le_3L : (α : ℝ) ≤ 3 * L := by
      have h1 : (2 / 3 : ℝ) * (α : ℝ) ≤ q * (α : ℝ) :=
        mul_le_mul_of_nonneg_right hq_gt.le hα_pos.le
      linarith [hhi]
    have hlog3 : Real.log 3 ≤ 2 := by
      have he2 : (3 : ℝ) ≤ Real.exp 2 := by
        have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith
      calc
        Real.log 3 ≤ Real.log (Real.exp 2) := Real.log_le_log (by norm_num) he2
        _ = 2 := Real.log_exp 2
    calc
      Real.log (α : ℝ) ≤ Real.log (3 * L) := Real.log_le_log hα_pos hα_le_3L
      _ = Real.log 3 + Real.log L := Real.log_mul (by norm_num) hL_pos.ne'
      _ ≤ 2 + |Real.log L| := add_le_add hlog3 (le_abs_self _)
      _ = |Real.log L| + 2 := add_comm _ _
  have hlogα_nonneg : 0 ≤ Real.log (α : ℝ) := Real.log_nonneg (by linarith)
  have hδ := phaseDelta_mem_Icc n
  have hcoeff_abs : |(q * (α : ℝ) - 2 * L) + 1 - q / 2 + Real.log (α : ℝ)| ≤
      3 * |Real.log L| + 2 * |alphaConst| + 5 := by
    have hqa_sub : q * (α : ℝ) - 2 * L = -2 * Real.log L + 2 * alphaConst - q * phaseDelta n := by
      dsimp [α, L, q] at hqα ⊢
      linarith
    rw [hqa_sub]
    have habs_ll : -|Real.log L| ≤ Real.log L ∧ Real.log L ≤ |Real.log L| := abs_le.mp le_rfl
    have habs_c : -|alphaConst| ≤ alphaConst ∧ alphaConst ≤ |alphaConst| := abs_le.mp le_rfl
    have hqδ_nonneg : 0 ≤ q * phaseDelta n := mul_nonneg hq_pos.le hδ.1
    have hqδ_le1 : q * phaseDelta n ≤ 1 :=
      (mul_le_of_le_one_right hq_pos.le hδ.2).trans hq_lt1.le
    rw [abs_le]
    constructor <;> linarith
  calc
    |(T₁ - T₂) * ((q * (α : ℝ) - 2 * L) + 1 - q / 2 + Real.log (α : ℝ)) +
        (Real.log ((α : ℝ) - T₁) - Real.log ((α : ℝ) - T₂))|
        ≤ |(T₁ - T₂) * ((q * (α : ℝ) - 2 * L) + 1 - q / 2 + Real.log (α : ℝ))| +
            |Real.log ((α : ℝ) - T₁) - Real.log ((α : ℝ) - T₂)| := abs_add_le _ _
    _ = |T₁ - T₂| * |(q * (α : ℝ) - 2 * L) + 1 - q / 2 + Real.log (α : ℝ)| +
          |Real.log ((α : ℝ) - T₁) - Real.log ((α : ℝ) - T₂)| := by rw [abs_mul]
    _ ≤ |T₁ - T₂| * (3 * |Real.log L| + 2 * |alphaConst| + 5) + |T₁ - T₂| :=
      add_le_add (mul_le_mul_of_nonneg_left hcoeff_abs (abs_nonneg _)) hlog_lip
    _ = |T₁ - T₂| * (3 * |Real.log L| + 2 * |alphaConst| + 6) := by ring

/-! ### 2. Continuous Threshold Roots `TPlus`, `TFour` and Quantitative Root Separation -/

/-- Continuous `S_+` deficit root `TPlus n ∈ [2.6, 4.1]`. -/
noncomputable def TPlus (n : ℕ) : ℝ :=
  if h : ∃ T ∈ Set.Icc (2.6 : ℝ) 4.1,
      profileBasePhi n ((alphaNat n : ℝ) - T) + freeEnergyPlus T = 0
  then Classical.choose h
  else 3.5

/-- Continuous `S_4` cocoloring deficit root `TFour n ∈ [2.6, 4.1]`. -/
noncomputable def TFour (n : ℕ) : ℝ :=
  if h : ∃ T ∈ Set.Icc (2.6 : ℝ) 4.1,
      profileBasePhi n ((alphaNat n : ℝ) - T) + Real.log 2 + freeEnergyFour T = 0
  then Classical.choose h
  else 3.5

/-- Continuous `S_+` average class size `sPlus n = alphaNat n - TPlus n`. -/
noncomputable def sPlus (n : ℕ) : ℝ :=
  (alphaNat n : ℝ) - TPlus n

/-- Continuous `S_4` cocoloring average class size `sFourCo n = alphaNat n - TFour n`. -/
noncomputable def sFourCo (n : ℕ) : ℝ :=
  (alphaNat n : ℝ) - TFour n

theorem TPlus_mem_Icc (n : ℕ) : TPlus n ∈ Set.Icc (2.6 : ℝ) 4.1 := by
  unfold TPlus
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · constructor <;> norm_num

theorem TFour_mem_Icc (n : ℕ) : TFour n ∈ Set.Icc (2.6 : ℝ) 4.1 := by
  unfold TFour
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · constructor <;> norm_num

/-- Explicit uniform constant bounding `|freeEnergyPlus T|` and `|Real.log 2 + freeEnergyFour T|`
on `[2.6, 4.1]`. -/
private noncomputable def feBoundConst : ℝ :=
  |freeEnergyPlus 3.5| + |freeEnergyFour 3.5| + 15

private lemma feBoundConst_nonneg : 0 ≤ feBoundConst := by
  unfold feBoundConst
  positivity

private lemma abs_freeEnergyPlus_le_const {T : ℝ} (hT : T ∈ Set.Icc (2.6 : ℝ) 4.1) :
    |freeEnergyPlus T| ≤ feBoundConst := by
  have h35 : (3.5 : ℝ) ∈ Set.Icc (2.6 : ℝ) 4.1 := by norm_num
  have hlip := abs_freeEnergyPlus_sub_le hT h35
  have hd : |T - 3.5| ≤ 1 := abs_le.mpr ⟨by linarith [hT.1], by linarith [hT.2]⟩
  have htri : |freeEnergyPlus T| ≤ |freeEnergyPlus T - freeEnergyPlus 3.5| + |freeEnergyPlus 3.5| := by
    simpa using abs_add_le (freeEnergyPlus T - freeEnergyPlus 3.5) (freeEnergyPlus 3.5)
  unfold feBoundConst
  linarith [abs_nonneg (freeEnergyFour 3.5)]

private lemma abs_log2_add_freeEnergyFour_le_const {T : ℝ} (hT : T ∈ Set.Icc (2.6 : ℝ) 4.1) :
    |Real.log 2 + freeEnergyFour T| ≤ feBoundConst := by
  have h35 : (3.5 : ℝ) ∈ Set.Icc (2.6 : ℝ) 4.1 := by norm_num
  have hlip := abs_freeEnergyFour_sub_le hT h35
  have hd : |T - 3.5| ≤ 1 := abs_le.mpr ⟨by linarith [hT.1], by linarith [hT.2]⟩
  have hq : |Real.log 2| ≤ 1 :=
    abs_le.mpr ⟨by linarith [Real.log_two_gt_d9], by linarith [Real.log_two_lt_d9]⟩
  have htri1 := abs_add_le (Real.log 2) (freeEnergyFour T)
  have htri2 : |freeEnergyFour T| ≤ |freeEnergyFour T - freeEnergyFour 3.5| + |freeEnergyFour 3.5| := by
    simpa using abs_add_le (freeEnergyFour T - freeEnergyFour 3.5) (freeEnergyFour 3.5)
  unfold feBoundConst
  linarith [abs_nonneg (freeEnergyPlus 3.5)]

private lemma targetDeficit_bounds_tight (n : ℕ) :
    2.885 ≤ targetDeficit (phaseDelta n) ∧ targetDeficit (phaseDelta n) ≤ 3.886 := by
  unfold targetDeficit
  have hq_lo := Real.log_two_gt_d9
  have hq_hi := Real.log_two_lt_d9
  have hδ := phaseDelta_mem_Icc n
  have hd1 : 2.885 ≤ 2 / Real.log 2 := by
    rw [le_div_iff₀ (by linarith only [hq_lo])]
    linarith only [hq_hi]
  have hd2 : 2 / Real.log 2 ≤ 2.886 := by
    rw [div_le_iff₀ (by linarith only [hq_lo])]
    linarith only [hq_lo]
  exact ⟨by linarith only [hd1, hδ.2], by linarith only [hd2, hδ.1]⟩

private lemma exists_rootErrConst :
    ∃ M₀ : ℝ, 1 ≤ M₀ ∧ feBoundConst ≤ M₀ ∧
      30 + 30 * |alphaConst| + 60 + feBoundConst = M₀ := by
  refine ⟨30 + 30 * |alphaConst| + 60 + feBoundConst, ?_, ?_, rfl⟩
  · linarith [abs_nonneg alphaConst, feBoundConst_nonneg]
  · linarith [abs_nonneg alphaConst]

/-- **Part A continuous root existence, localization, and quantitative separation**:
Eventually for large `n`, `TPlus n` and `TFour n` solve their exact profile equations, lie within
`O(log(log n) / log n)` of `targetDeficit (phaseDelta n)`, and satisfy
`((Real.log 2)^2 / 4 * petkovA4 (phaseDelta n) - C_sep * log(log n) / log n) * n / (log n)^3 ≤
  n / sPlus n - n / sFourCo n`. -/
theorem eventually_continuous_roots_separation :
    ∃ C_sep : ℝ, 0 < C_sep ∧
      ∀ᶠ n : ℕ in atTop,
        let L := Real.log (n : ℝ);
        profileBasePhi n (sPlus n) + freeEnergyPlus (TPlus n) = 0 ∧
        profileBasePhi n (sFourCo n) + Real.log 2 + freeEnergyFour (TFour n) = 0 ∧
        |TPlus n - targetDeficit (phaseDelta n)| ≤ C_sep * (Real.log L / L) ∧
        |TFour n - targetDeficit (phaseDelta n)| ≤ C_sep * (Real.log L / L) ∧
        2 * L ≤ sPlus n ∧ sPlus n ≤ 3 * L ∧
        2 * L ≤ sFourCo n ∧ sFourCo n ≤ 3 * L ∧
        ((Real.log 2) ^ 2 / 4 * petkovA4 (phaseDelta n) - C_sep * (Real.log L / L)) *
            (n : ℝ) / L ^ 3 ≤
          (n : ℝ) / sPlus n - (n : ℝ) / sFourCo n := by
  obtain ⟨M₀, hM₀_ge1, hfe_le_M₀, hM₀_def⟩ := exists_rootErrConst
  have hM₀_pos : 0 < M₀ := by linarith only [hM₀_ge1]
  refine ⟨100 * M₀ ^ 2, by positivity, ?_⟩
  have hL : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  have hratio : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact h0.comp hL
  have hlogRat_pos : 0 < Real.log (200 / 153 : ℝ) := Real.log_pos (by norm_num)
  have hthresh : 0 < min (1 / (200 * M₀ ^ 2)) (Real.log (200 / 153 : ℝ) / (100 * M₀ ^ 2)) :=
    lt_min (by positivity) (by positivity)
  filter_upwards [eventually_alphaNat_regime,
    hL.eventually_ge_atTop (1000 + 20 * M₀),
    hll.eventually_ge_atTop 2,
    hratio.eventually (ge_mem_nhds hthresh)] with
      n ⟨hn16, hα20, _, hqα, _, hhi⟩ hLbig hll_ge2 hrat_both
  intro L
  have hrat : Real.log L / L ≤ 1 / (200 * M₀ ^ 2) := (le_min_iff.mp hrat_both).1
  have hrat_A4 : Real.log L / L ≤ Real.log (200 / 153 : ℝ) / (100 * M₀ ^ 2) :=
    (le_min_iff.mp hrat_both).2
  have hL_ge1000 : 1000 + 20 * M₀ ≤ L := hLbig
  have hll_ge2' : 2 ≤ Real.log L := hll_ge2
  have hL_pos : 0 < L := by linarith only [hL_ge1000, hM₀_pos]
  have hll_pos : 0 < Real.log L := by linarith only [hll_ge2']
  have habs_ll : |Real.log L| = Real.log L := abs_of_pos hll_pos
  have hM₀_le_sq : M₀ ≤ M₀ ^ 2 := by
    simpa [sq] using mul_le_mul_of_nonneg_left hM₀_ge1 hM₀_pos.le
  have hrat_M : Real.log L / L ≤ 1 / (100 * M₀) := by
    refine hrat.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq_pos : 0 ≤ M₀ ^ 2 := sq_nonneg M₀
    linarith only [hM₀_le_sq, hsq_pos]
  have hll_le_rat : Real.log L ≤ L / (100 * M₀) := by
    calc
      Real.log L ≤ 1 / (100 * M₀) * L := (div_le_iff₀ hL_pos).mp hrat_M
      _ = L / (100 * M₀) := by ring
  have herr_phi : ∀ {T : ℝ}, T ∈ Set.Icc (2.6 : ℝ) 4.1 →
      |profileBasePhi n ((alphaNat n : ℝ) - T) -
        (T - targetDeficit (phaseDelta n)) * L| ≤ M₀ * Real.log L := by
    intro T hT
    have hb := abs_profileBasePhi_approx hn16 hα20 hqα hhi hT
    change |profileBasePhi n ((alphaNat n : ℝ) - T) -
      (T - targetDeficit (phaseDelta n)) * L| ≤
      30 * |Real.log L| + 30 * |alphaConst| + 60 at hb
    rw [habs_ll] at hb
    have h1 : 30 * Real.log L + 30 * |alphaConst| + 60 ≤ M₀ * Real.log L := by
      have hll1 : 1 ≤ Real.log L := by linarith only [hll_ge2']
      have hc0 : 0 ≤ 30 * |alphaConst| + 60 + feBoundConst :=
        add_nonneg (by positivity) feBoundConst_nonneg
      have hmul1 := le_mul_of_one_le_right hc0 hll1
      have hexp : M₀ * Real.log L =
          30 * Real.log L + (30 * |alphaConst| + 60 + feBoundConst) * Real.log L := by
        rw [← hM₀_def]; ring
      linarith only [hmul1, hexp, feBoundConst_nonneg]
    exact hb.trans h1
  have hTδ_bounds := targetDeficit_bounds_tight n
  have h26 : (2.6 : ℝ) ∈ Set.Icc (2.6 : ℝ) 4.1 := by norm_num
  have h41 : (4.1 : ℝ) ∈ Set.Icc (2.6 : ℝ) 4.1 := by norm_num
  have hMll_small : M₀ * Real.log L + feBoundConst ≤ (1 / 10 : ℝ) * L := by
    have h1 : M₀ * Real.log L ≤ (1 / 100 : ℝ) * L := by
      have h2 := mul_le_mul_of_nonneg_left hll_le_rat hM₀_pos.le
      have h3 : M₀ * (L / (100 * M₀)) = (1 / 100 : ℝ) * L := by field_simp [hM₀_pos.ne']
      linarith only [h2, h3]
    linarith only [h1, hfe_le_M₀, hL_ge1000, hM₀_pos]
  have hex_plus : ∃ T ∈ Set.Icc (2.6 : ℝ) 4.1,
      profileBasePhi n ((alphaNat n : ℝ) - T) + freeEnergyPlus T = 0 := by
    let f := fun T : ℝ => profileBasePhi n ((alphaNat n : ℝ) - T) + freeEnergyPlus T
    have hcont : ContinuousOn f (Set.Icc (2.6 : ℝ) 4.1) :=
      (continuousOn_profileBasePhi_sub (by omega)).add continuousOn_freeEnergyPlus
    have hf26 : f 2.6 ≤ 0 := by
      have he := (abs_le.mp (herr_phi h26)).2
      have hfe := (abs_le.mp (abs_freeEnergyPlus_le_const h26)).2
      dsimp [f]
      have hlin : (2.6 - targetDeficit (phaseDelta n)) * L ≤ -(1 / 5 : ℝ) * L :=
        mul_le_mul_of_nonneg_right (by linarith only [hTδ_bounds.1]) hL_pos.le
      linarith only [he, hfe, hlin, hMll_small, hL_pos]
    have hf41 : 0 ≤ f 4.1 := by
      have he := (abs_le.mp (herr_phi h41)).1
      have hfe := (abs_le.mp (abs_freeEnergyPlus_le_const h41)).1
      dsimp [f]
      have hlin : (1 / 5 : ℝ) * L ≤ (4.1 - targetDeficit (phaseDelta n)) * L :=
        mul_le_mul_of_nonneg_right (by linarith only [hTδ_bounds.2]) hL_pos.le
      linarith only [he, hfe, hlin, hMll_small, hL_pos]
    exact intermediate_value_Icc (by norm_num) hcont ⟨hf26, hf41⟩
  have hex_four : ∃ T ∈ Set.Icc (2.6 : ℝ) 4.1,
      profileBasePhi n ((alphaNat n : ℝ) - T) + Real.log 2 + freeEnergyFour T = 0 := by
    let f := fun T : ℝ => profileBasePhi n ((alphaNat n : ℝ) - T) + Real.log 2 + freeEnergyFour T
    have hcont : ContinuousOn f (Set.Icc (2.6 : ℝ) 4.1) :=
      ((continuousOn_profileBasePhi_sub (by omega)).add continuousOn_const).add
        continuousOn_freeEnergyFour
    have hf26 : f 2.6 ≤ 0 := by
      have he := (abs_le.mp (herr_phi h26)).2
      have hfe := (abs_le.mp (abs_log2_add_freeEnergyFour_le_const h26)).2
      dsimp [f]
      have hlin : (2.6 - targetDeficit (phaseDelta n)) * L ≤ -(1 / 5 : ℝ) * L :=
        mul_le_mul_of_nonneg_right (by linarith only [hTδ_bounds.1]) hL_pos.le
      linarith only [he, hfe, hlin, hMll_small, hL_pos]
    have hf41 : 0 ≤ f 4.1 := by
      have he := (abs_le.mp (herr_phi h41)).1
      have hfe := (abs_le.mp (abs_log2_add_freeEnergyFour_le_const h41)).1
      dsimp [f]
      have hlin : (1 / 5 : ℝ) * L ≤ (4.1 - targetDeficit (phaseDelta n)) * L :=
        mul_le_mul_of_nonneg_right (by linarith only [hTδ_bounds.2]) hL_pos.le
      linarith only [he, hfe, hlin, hMll_small, hL_pos]
    exact intermediate_value_Icc (by norm_num) hcont ⟨hf26, hf41⟩
  have hroot_plus : profileBasePhi n (sPlus n) + freeEnergyPlus (TPlus n) = 0 := by
    have hTP_eq : TPlus n = Classical.choose hex_plus := by
      unfold TPlus
      exact dite_eq_left_of_eq_true (eq_true hex_plus)
    unfold sPlus
    rw [hTP_eq]
    exact (Classical.choose_spec hex_plus).2
  have hroot_four : profileBasePhi n (sFourCo n) + Real.log 2 + freeEnergyFour (TFour n) = 0 := by
    have hTF_eq : TFour n = Classical.choose hex_four := by
      unfold TFour
      exact dite_eq_left_of_eq_true (eq_true hex_four)
    unfold sFourCo
    rw [hTF_eq]
    exact (Classical.choose_spec hex_four).2
  have hTP_mem := TPlus_mem_Icc n
  have hTF_mem := TFour_mem_Icc n
  have hfe_ll : feBoundConst ≤ M₀ * Real.log L := by
    calc
      feBoundConst ≤ M₀ := hfe_le_M₀
      _ = M₀ * 1 := (mul_one _).symm
      _ ≤ M₀ * Real.log L := mul_le_mul_of_nonneg_left (by linarith only [hll_ge2']) hM₀_pos.le
  have hTP_loc : |TPlus n - targetDeficit (phaseDelta n)| ≤ 2 * M₀ * (Real.log L / L) := by
    rw [← mul_div_assoc, le_div_iff₀ hL_pos]
    have habsL : |TPlus n - targetDeficit (phaseDelta n)| * L =
        |(TPlus n - targetDeficit (phaseDelta n)) * L| := by
      rw [abs_mul, abs_of_pos hL_pos]
    rw [habsL]
    have he := herr_phi hTP_mem
    have hfe := abs_freeEnergyPlus_le_const hTP_mem
    have heq : (TPlus n - targetDeficit (phaseDelta n)) * L =
        -(profileBasePhi n ((alphaNat n : ℝ) - TPlus n) -
          (TPlus n - targetDeficit (phaseDelta n)) * L) -
          freeEnergyPlus (TPlus n) := by
      unfold sPlus at hroot_plus
      linarith only [hroot_plus]
    rw [heq]
    have htri := abs_sub
      (-(profileBasePhi n ((alphaNat n : ℝ) - TPlus n) - (TPlus n - targetDeficit (phaseDelta n)) * L))
      (freeEnergyPlus (TPlus n))
    rw [abs_neg] at htri
    linarith only [htri, he, hfe, hfe_ll]
  have hTF_loc : |TFour n - targetDeficit (phaseDelta n)| ≤ 2 * M₀ * (Real.log L / L) := by
    rw [← mul_div_assoc, le_div_iff₀ hL_pos]
    have habsL : |TFour n - targetDeficit (phaseDelta n)| * L =
        |(TFour n - targetDeficit (phaseDelta n)) * L| := by
      rw [abs_mul, abs_of_pos hL_pos]
    rw [habsL]
    have he := herr_phi hTF_mem
    have hfe := abs_log2_add_freeEnergyFour_le_const hTF_mem
    have heq : (TFour n - targetDeficit (phaseDelta n)) * L =
        -(profileBasePhi n ((alphaNat n : ℝ) - TFour n) -
          (TFour n - targetDeficit (phaseDelta n)) * L) -
          (Real.log 2 + freeEnergyFour (TFour n)) := by
      unfold sFourCo at hroot_four
      linarith only [hroot_four]
    rw [heq]
    have htri := abs_sub
      (-(profileBasePhi n ((alphaNat n : ℝ) - TFour n) - (TFour n - targetDeficit (phaseDelta n)) * L))
      (Real.log 2 + freeEnergyFour (TFour n))
    rw [abs_neg] at htri
    linarith only [htri, he, hfe, hfe_ll]
  have hTδ_mem : targetDeficit (phaseDelta n) ∈ Set.Icc (2.6 : ℝ) 4.1 :=
    targetDeficit_mem_Icc (phaseDelta_mem_Icc n)
  have hA4_approx :
      |(profileBasePhi n (sPlus n) - profileBasePhi n (sFourCo n)) - petkovA4 (phaseDelta n)| ≤
        40 * M₀ * (Real.log L / L) := by
    have hsub_roots : profileBasePhi n (sPlus n) - profileBasePhi n (sFourCo n) =
        Real.log 2 - freeEnergyPlus (TPlus n) + freeEnergyFour (TFour n) := by
      linarith only [hroot_plus, hroot_four]
    rw [hsub_roots]
    unfold petkovA4
    have hrew : (Real.log 2 - freeEnergyPlus (TPlus n) + freeEnergyFour (TFour n)) -
        (Real.log 2 - freeEnergyPlus (targetDeficit (phaseDelta n)) +
          freeEnergyFour (targetDeficit (phaseDelta n))) =
        (freeEnergyPlus (targetDeficit (phaseDelta n)) - freeEnergyPlus (TPlus n)) +
          (freeEnergyFour (TFour n) - freeEnergyFour (targetDeficit (phaseDelta n))) := by ring
    rw [hrew]
    have hlip1 := abs_freeEnergyPlus_sub_le hTδ_mem hTP_mem
    rw [abs_sub_comm (targetDeficit (phaseDelta n)) (TPlus n)] at hlip1
    have hlip2 := abs_freeEnergyFour_sub_le hTF_mem hTδ_mem
    have htri := abs_add_le
      (freeEnergyPlus (targetDeficit (phaseDelta n)) - freeEnergyPlus (TPlus n))
      (freeEnergyFour (TFour n) - freeEnergyFour (targetDeficit (phaseDelta n)))
    linarith only [htri, hlip1, hlip2, hTP_loc, hTF_loc]
  have hdiff_phi := abs_profileBasePhi_diff_approx hn16 hα20 hqα hhi hTP_mem hTF_mem
  change |(profileBasePhi n (sPlus n) - profileBasePhi n (sFourCo n)) - (TPlus n - TFour n) * L| ≤
    |TPlus n - TFour n| * (3 * |Real.log L| + 2 * |alphaConst| + 6) at hdiff_phi
  rw [habs_ll] at hdiff_phi
  have hslope_err : 3 * Real.log L + 2 * |alphaConst| + 6 ≤ M₀ * Real.log L := by
    have hll1 : 1 ≤ Real.log L := by linarith only [hll_ge2']
    have hc0 : 0 ≤ 2 * |alphaConst| + 6 := by positivity
    have hm1 := le_mul_of_one_le_right hc0 hll1
    have hexp : M₀ * Real.log L =
        3 * Real.log L + (2 * |alphaConst| + 6) * Real.log L +
          (27 + 28 * |alphaConst| + 54 + feBoundConst) * Real.log L := by
      rw [← hM₀_def]; ring
    have hextra : 0 ≤ (27 + 28 * |alphaConst| + 54 + feBoundConst) * Real.log L :=
      mul_nonneg (add_nonneg (by positivity) feBoundConst_nonneg) hll_pos.le
    linarith only [hm1, hexp, hextra]
  have hdiff_phi' :
      |(profileBasePhi n (sPlus n) - profileBasePhi n (sFourCo n)) - (TPlus n - TFour n) * L| ≤
        |TPlus n - TFour n| * (M₀ * Real.log L) :=
    hdiff_phi.trans (mul_le_mul_of_nonneg_left hslope_err (abs_nonneg _))
  have hA4_upper : |petkovA4 (phaseDelta n)| ≤ 2 * M₀ := by
    unfold petkovA4
    have h1 := abs_freeEnergyPlus_le_const hTδ_mem
    have h2 := abs_log2_add_freeEnergyFour_le_const hTδ_mem
    have hrew : Real.log 2 - freeEnergyPlus (targetDeficit (phaseDelta n)) +
        freeEnergyFour (targetDeficit (phaseDelta n)) =
        (Real.log 2 + freeEnergyFour (targetDeficit (phaseDelta n))) -
          freeEnergyPlus (targetDeficit (phaseDelta n)) := by ring
    rw [hrew]
    have htri := abs_sub (Real.log 2 + freeEnergyFour (targetDeficit (phaseDelta n)))
      (freeEnergyPlus (targetDeficit (phaseDelta n)))
    linarith only [htri, h1, h2, hfe_le_M₀]
  have hTdiff_crude : |TPlus n - TFour n| ≤ 6 * M₀ / L := by
    rw [le_div_iff₀ hL_pos]
    have h1 : |TPlus n - TFour n| * L - |TPlus n - TFour n| * (M₀ * Real.log L) ≤
        |petkovA4 (phaseDelta n)| + 40 * M₀ * (Real.log L / L) := by
      have ha : |(TPlus n - TFour n) * L| = |TPlus n - TFour n| * L := by
        rw [abs_mul, abs_of_pos hL_pos]
      have ht1 := abs_sub_le ((TPlus n - TFour n) * L)
        (profileBasePhi n (sPlus n) - profileBasePhi n (sFourCo n)) (petkovA4 (phaseDelta n))
      have ht2 := abs_add_le
        ((TPlus n - TFour n) * L - petkovA4 (phaseDelta n)) (petkovA4 (phaseDelta n))
      rw [sub_add_cancel] at ht2
      have hcomm1 : |(TPlus n - TFour n) * L -
          (profileBasePhi n (sPlus n) - profileBasePhi n (sFourCo n))| =
          |(profileBasePhi n (sPlus n) - profileBasePhi n (sFourCo n)) -
            (TPlus n - TFour n) * L| := abs_sub_comm _ _
      rw [hcomm1] at ht1
      linarith only [ha, ht1, ht2, hdiff_phi', hA4_approx]
    have hMll_half : M₀ * Real.log L ≤ (1 / 2 : ℝ) * L := by
      linarith only [hMll_small, feBoundConst_nonneg, hL_pos]
    have hlhs : (1 / 2 : ℝ) * (|TPlus n - TFour n| * L) ≤
        |TPlus n - TFour n| * L - |TPlus n - TFour n| * (M₀ * Real.log L) := by
      have hm := mul_le_mul_of_nonneg_left hMll_half (abs_nonneg (TPlus n - TFour n))
      have heq : |TPlus n - TFour n| * ((1 / 2 : ℝ) * L) =
          (1 / 2 : ℝ) * (|TPlus n - TFour n| * L) := by ring
      linarith only [hm, heq]
    have h40 : 40 * M₀ * (Real.log L / L) ≤ M₀ := by
      have hm := mul_le_mul_of_nonneg_left hrat_M (by positivity : 0 ≤ 40 * M₀)
      have hs : 40 * M₀ * (1 / (100 * M₀)) = 2 / 5 := by field_simp [hM₀_pos.ne']; ring
      linarith only [hm, hs, hM₀_ge1]
    linarith only [hlhs, h1, hA4_upper, h40]
  have hTdiff_lb :
      (petkovA4 (phaseDelta n) - 50 * M₀ ^ 2 * (Real.log L / L)) / L ≤ TPlus n - TFour n := by
    rw [div_le_iff₀ hL_pos]
    have h1 := (abs_le.mp hA4_approx).1
    have h2 := (abs_le.mp hdiff_phi').2
    have hprod_err : |TPlus n - TFour n| * (M₀ * Real.log L) ≤
        6 * M₀ ^ 2 * (Real.log L / L) := by
      calc
        |TPlus n - TFour n| * (M₀ * Real.log L)
            ≤ (6 * M₀ / L) * (M₀ * Real.log L) :=
          mul_le_mul_of_nonneg_right hTdiff_crude (by positivity)
        _ = 6 * M₀ ^ 2 * (Real.log L / L) := by ring
    have h40_sq : 40 * M₀ * (Real.log L / L) ≤ 40 * M₀ ^ 2 * (Real.log L / L) :=
      mul_le_mul_of_nonneg_right (by linarith only [hM₀_le_sq]) (by positivity)
    have hpos_sq : 0 ≤ M₀ ^ 2 * (Real.log L / L) := by positivity
    have h50_split : 50 * M₀ ^ 2 * (Real.log L / L) =
        40 * M₀ ^ 2 * (Real.log L / L) + 6 * M₀ ^ 2 * (Real.log L / L) +
          4 * (M₀ ^ 2 * (Real.log L / L)) := by ring
    linarith only [h1, h2, hprod_err, h40_sq, hpos_sq, h50_split]
  have hq : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq_lo := Real.log_two_gt_d9
  have hq_hi := Real.log_two_lt_d9
  have hs_bounds : ∀ {T : ℝ}, T ∈ Set.Icc (2.6 : ℝ) 4.1 →
      2 * L ≤ (alphaNat n : ℝ) - T ∧ (alphaNat n : ℝ) - T ≤ 3 * L ∧
      |(alphaNat n : ℝ) - T - (2 / Real.log 2) * L| ≤ M₀ * Real.log L := by
    intro T hT
    have hqa_diff : |(alphaNat n : ℝ) - (2 / Real.log 2) * L| ≤
        (2 * Real.log L + 2 * |alphaConst| + 1) / Real.log 2 := by
      have hid : Real.log 2 * ((alphaNat n : ℝ) - (2 / Real.log 2) * L) =
          -2 * Real.log L + 2 * alphaConst - Real.log 2 * phaseDelta n := by
        have hqα' : Real.log 2 * (alphaNat n : ℝ) =
            2 * L - 2 * Real.log L + 2 * alphaConst - Real.log 2 * phaseDelta n := hqα
        have hcancel : Real.log 2 * ((2 / Real.log 2) * L) = 2 * L := by
          field_simp [hq.ne']
        linarith only [hqα', hcancel]
      rw [le_div_iff₀ hq]
      have habsq : |(alphaNat n : ℝ) - (2 / Real.log 2) * L| * Real.log 2 =
          |Real.log 2 * ((alphaNat n : ℝ) - (2 / Real.log 2) * L)| := by
        rw [abs_mul, abs_of_pos hq, mul_comm]
      rw [habsq, hid]
      have habs_c : -|alphaConst| ≤ alphaConst ∧ alphaConst ≤ |alphaConst| := abs_le.mp le_rfl
      have hδ := phaseDelta_mem_Icc n
      have hqδ0 : 0 ≤ Real.log 2 * phaseDelta n := mul_nonneg hq.le hδ.1
      have hqδ1 : Real.log 2 * phaseDelta n ≤ 1 :=
        (mul_le_of_le_one_right hq.le hδ.2).trans (by linarith only [hq_hi])
      rw [abs_le]
      exact ⟨by linarith only [hll_pos, habs_c.1, hqδ1],
        by linarith only [hll_pos, habs_c.2, hqδ0]⟩
    have hs_approx : |(alphaNat n : ℝ) - T - (2 / Real.log 2) * L| ≤ M₀ * Real.log L := by
      have htri : |(alphaNat n : ℝ) - T - (2 / Real.log 2) * L| ≤
          |(alphaNat n : ℝ) - (2 / Real.log 2) * L| + |T| := by
        simpa [sub_right_comm] using abs_sub ((alphaNat n : ℝ) - (2 / Real.log 2) * L) T
      have hdiv2 : (2 * Real.log L + 2 * |alphaConst| + 1) / Real.log 2 ≤
          2 * (2 * Real.log L + 2 * |alphaConst| + 1) := by
        rw [div_le_iff₀ hq]
        have hgt_half : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [hq_lo]
        calc
          2 * Real.log L + 2 * |alphaConst| + 1
              = (2 * (2 * Real.log L + 2 * |alphaConst| + 1)) * (1 / 2) := by ring
          _ ≤ (2 * (2 * Real.log L + 2 * |alphaConst| + 1)) * Real.log 2 :=
            mul_le_mul_of_nonneg_left hgt_half (by positivity)
      have hTabs : |T| ≤ 5 := abs_le.mpr ⟨by linarith only [hT.1], by linarith only [hT.2]⟩
      have h1 : 4 * Real.log L + 4 * |alphaConst| + 7 ≤ M₀ * Real.log L := by
        have hll1 : 1 ≤ Real.log L := by linarith only [hll_ge2']
        have hc0 : 0 ≤ 4 * |alphaConst| + 7 := by positivity
        have hm1 := le_mul_of_one_le_right hc0 hll1
        have hexp : M₀ * Real.log L =
            4 * Real.log L + (4 * |alphaConst| + 7) * Real.log L +
              (26 + 26 * |alphaConst| + 53 + feBoundConst) * Real.log L := by
          rw [← hM₀_def]; ring
        have hextra : 0 ≤ (26 + 26 * |alphaConst| + 53 + feBoundConst) * Real.log L :=
          mul_nonneg (add_nonneg (by positivity) feBoundConst_nonneg) hll_pos.le
        linarith only [hm1, hexp, hextra]
      linarith only [htri, hqa_diff, hdiv2, hTabs, h1]
    have h2q_lo : 2.88 ≤ 2 / Real.log 2 := by rw [le_div_iff₀ hq]; linarith only [hq_hi]
    have h2q_hi : 2 / Real.log 2 ≤ 2.89 := by rw [div_le_iff₀ hq]; linarith only [hq_lo]
    have hMll_01 : M₀ * Real.log L ≤ (1 / 10 : ℝ) * L := by
      linarith only [hMll_small, feBoundConst_nonneg]
    have habs_u := abs_le.mp hs_approx
    have h2qL_lo : 2.88 * L ≤ (2 / Real.log 2) * L := mul_le_mul_of_nonneg_right h2q_lo hL_pos.le
    have h2qL_hi : (2 / Real.log 2) * L ≤ 2.89 * L := mul_le_mul_of_nonneg_right h2q_hi hL_pos.le
    refine ⟨by linarith only [habs_u.1, h2qL_lo, hMll_01, hL_pos],
      by linarith only [habs_u.2, h2qL_hi, hMll_01, hL_pos], hs_approx⟩
  obtain ⟨hsP_lo, hsP_hi, hsP_app⟩ := hs_bounds hTP_mem
  obtain ⟨hsF_lo, hsF_hi, hsF_app⟩ := hs_bounds hTF_mem
  have hsP_pos : 0 < sPlus n := by unfold sPlus; linarith only [hsP_lo, hL_pos]
  have hsF_pos : 0 < sFourCo n := by unfold sFourCo; linarith only [hsF_lo, hL_pos]
  set θ : ℝ := 2 * M₀ * (Real.log L / L)
  have hθ_nonneg : 0 ≤ θ := by positivity
  have hθ_lt1 : θ ≤ 1 / 2 := by
    dsimp [θ]
    have hm := mul_le_mul_of_nonneg_left hrat_M (by positivity : 0 ≤ 2 * M₀)
    have hs : 2 * M₀ * (1 / (100 * M₀)) = 1 / 50 := by field_simp [hM₀_pos.ne']; ring
    linarith only [hm, hs]
  have hprod_upper : sPlus n * sFourCo n ≤
      (4 / (Real.log 2) ^ 2) * L ^ 2 * (1 + θ) := by
    have h2q_gt2 : 2 ≤ 2 / Real.log 2 := by rw [le_div_iff₀ hq]; linarith only [hq_hi]
    have huP : sPlus n ≤ (2 / Real.log 2) * L * (1 + (1 / 4 : ℝ) * θ) := by
      have h1 := (abs_le.mp hsP_app).2
      change sPlus n - (2 / Real.log 2) * L ≤ M₀ * Real.log L at h1
      have h2 : M₀ * Real.log L ≤ (2 / Real.log 2) * L * ((1 / 4 : ℝ) * θ) := by
        dsimp [θ]
        have heq : L * ((1 / 4 : ℝ) * (2 * M₀ * (Real.log L / L))) =
            (1 / 2 : ℝ) * (M₀ * Real.log L) := by
          field_simp [hL_pos.ne']; ring
        rw [mul_assoc, heq]
        have hm := mul_le_mul_of_nonneg_right h2q_gt2
          (by positivity : 0 ≤ (1 / 2 : ℝ) * (M₀ * Real.log L))
        have htwo : 2 * ((1 / 2 : ℝ) * (M₀ * Real.log L)) = M₀ * Real.log L := by ring
        linarith only [hm, htwo]
      have hexp : (2 / Real.log 2) * L * (1 + (1 / 4 : ℝ) * θ) =
          (2 / Real.log 2) * L + (2 / Real.log 2) * L * ((1 / 4 : ℝ) * θ) := by ring
      linarith only [h1, h2, hexp]
    have huF : sFourCo n ≤ (2 / Real.log 2) * L * (1 + (1 / 4 : ℝ) * θ) := by
      have h1 := (abs_le.mp hsF_app).2
      change sFourCo n - (2 / Real.log 2) * L ≤ M₀ * Real.log L at h1
      have h2 : M₀ * Real.log L ≤ (2 / Real.log 2) * L * ((1 / 4 : ℝ) * θ) := by
        dsimp [θ]
        have heq : L * ((1 / 4 : ℝ) * (2 * M₀ * (Real.log L / L))) =
            (1 / 2 : ℝ) * (M₀ * Real.log L) := by
          field_simp [hL_pos.ne']; ring
        rw [mul_assoc, heq]
        have hm := mul_le_mul_of_nonneg_right h2q_gt2
          (by positivity : 0 ≤ (1 / 2 : ℝ) * (M₀ * Real.log L))
        have htwo : 2 * ((1 / 2 : ℝ) * (M₀ * Real.log L)) = M₀ * Real.log L := by ring
        linarith only [hm, htwo]
      have hexp : (2 / Real.log 2) * L * (1 + (1 / 4 : ℝ) * θ) =
          (2 / Real.log 2) * L + (2 / Real.log 2) * L * ((1 / 4 : ℝ) * θ) := by ring
      linarith only [h1, h2, hexp]
    calc
      sPlus n * sFourCo n
          ≤ ((2 / Real.log 2) * L * (1 + (1 / 4 : ℝ) * θ)) *
              ((2 / Real.log 2) * L * (1 + (1 / 4 : ℝ) * θ)) :=
        mul_le_mul huP huF hsF_pos.le (by positivity)
      _ = (4 / (Real.log 2) ^ 2) * L ^ 2 * (1 + (1 / 2 : ℝ) * θ + (1 / 16 : ℝ) * θ ^ 2) := by ring
      _ ≤ (4 / (Real.log 2) ^ 2) * L ^ 2 * (1 + θ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hsq : θ ^ 2 ≤ θ := by
          calc
            θ ^ 2 = θ * θ := sq θ
            _ ≤ θ * 1 := mul_le_mul_of_nonneg_left (by linarith only [hθ_lt1]) hθ_nonneg
            _ = θ := mul_one θ
        linarith only [hθ_nonneg, hsq]
  have hsep_main :
      ((Real.log 2) ^ 2 / 4 * petkovA4 (phaseDelta n) - (100 * M₀ ^ 2) * (Real.log L / L)) *
          (n : ℝ) / L ^ 3 ≤
        (n : ℝ) / sPlus n - (n : ℝ) / sFourCo n := by
    have hfrac_id : (n : ℝ) / sPlus n - (n : ℝ) / sFourCo n =
        (n : ℝ) * (TPlus n - TFour n) / (sPlus n * sFourCo n) := by
      have hsdiff : TPlus n - TFour n = sFourCo n - sPlus n := by
        unfold sPlus sFourCo; ring
      rw [hsdiff, eq_div_iff (mul_ne_zero hsP_pos.ne' hsF_pos.ne')]
      have h1 : (n : ℝ) / sPlus n * sPlus n = (n : ℝ) := div_mul_cancel₀ _ hsP_pos.ne'
      have h2 : (n : ℝ) / sFourCo n * sFourCo n = (n : ℝ) := div_mul_cancel₀ _ hsF_pos.ne'
      calc
        ((n : ℝ) / sPlus n - (n : ℝ) / sFourCo n) * (sPlus n * sFourCo n)
            = ((n : ℝ) / sPlus n * sPlus n) * sFourCo n -
              ((n : ℝ) / sFourCo n * sFourCo n) * sPlus n := by ring
        _ = (n : ℝ) * sFourCo n - (n : ℝ) * sPlus n := by rw [h1, h2]
        _ = (n : ℝ) * (sFourCo n - sPlus n) := by ring
    rw [hfrac_id]
    set num : ℝ := petkovA4 (phaseDelta n) - 50 * M₀ ^ 2 * (Real.log L / L)
    have hnum_pos : 0 < num := by
      dsimp [num]
      have hA4_ge := petkovA4_gt_log_200_153 (phaseDelta_mem_Icc n)
      have hm := mul_le_mul_of_nonneg_left hrat_A4 (by positivity : 0 ≤ 50 * M₀ ^ 2)
      have hs : 50 * M₀ ^ 2 * (Real.log (200 / 153 : ℝ) / (100 * M₀ ^ 2)) =
          (1 / 2 : ℝ) * Real.log (200 / 153 : ℝ) := by field_simp [hM₀_pos.ne']; ring
      linarith only [hA4_ge, hm, hs, hlogRat_pos]
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hstep1 :
        ((Real.log 2) ^ 2 / 4 * num / (1 + θ)) * (n : ℝ) / L ^ 3 ≤
          (n : ℝ) * (TPlus n - TFour n) / (sPlus n * sFourCo n) := by
      have h1θ_pos : 0 < 1 + θ := by linarith only [hθ_nonneg]
      calc
        ((Real.log 2) ^ 2 / 4 * num / (1 + θ)) * (n : ℝ) / L ^ 3
            = (n : ℝ) * (num / L) / ((4 / (Real.log 2) ^ 2) * L ^ 2 * (1 + θ)) := by
              field_simp [hq.ne', hL_pos.ne', h1θ_pos.ne']
        _ ≤ (n : ℝ) * (num / L) / (sPlus n * sFourCo n) :=
          div_le_div_of_nonneg_left (by positivity) (mul_pos hsP_pos hsF_pos) hprod_upper
        _ ≤ (n : ℝ) * (TPlus n - TFour n) / (sPlus n * sFourCo n) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hTdiff_lb hn_pos.le) (mul_pos hsP_pos hsF_pos).le
    refine le_trans ?_ hstep1
    refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hn_pos.le) (by positivity)
    have h1_sub_θ : num * (1 - θ) ≤ num / (1 + θ) := by
      rw [le_div_iff₀ (by linarith only [hθ_nonneg])]
      have hsq : 0 ≤ num * θ ^ 2 := by positivity
      have hid : num * (1 - θ) * (1 + θ) = num - num * θ ^ 2 := by ring
      linarith only [hsq, hid]
    have hq4_le1 : (Real.log 2) ^ 2 / 4 ≤ 1 := by
      have hq1 : Real.log 2 ≤ 1 := by linarith only [hq_hi]
      have hqsq : (Real.log 2) ^ 2 ≤ 1 := by
        calc
          (Real.log 2) ^ 2 = Real.log 2 * Real.log 2 := sq _
          _ ≤ 1 * 1 := mul_le_mul hq1 hq1 hq.le zero_le_one
          _ = 1 := mul_one 1
      linarith only [hqsq]
    have hnum_le : num ≤ 2 * M₀ := by
      dsimp [num]
      have h1 : petkovA4 (phaseDelta n) ≤ 2 * M₀ := (abs_le.mp hA4_upper).2
      have h2 : 0 ≤ 50 * M₀ ^ 2 * (Real.log L / L) := by positivity
      linarith only [h1, h2]
    have hprod_le : (Real.log 2) ^ 2 / 4 * (num * θ) ≤ 4 * M₀ ^ 2 * (Real.log L / L) := by
      calc
        (Real.log 2) ^ 2 / 4 * (num * θ)
            ≤ 1 * ((2 * M₀) * θ) :=
          mul_le_mul hq4_le1 (mul_le_mul_of_nonneg_right hnum_le hθ_nonneg)
            (by positivity) zero_le_one
        _ = 4 * M₀ ^ 2 * (Real.log L / L) := by dsimp [θ]; ring
    have h50_le : (Real.log 2) ^ 2 / 4 * (50 * M₀ ^ 2 * (Real.log L / L)) ≤
        50 * M₀ ^ 2 * (Real.log L / L) :=
      mul_le_of_le_one_left (by positivity) hq4_le1
    have hstep_q : (Real.log 2) ^ 2 / 4 * (num * (1 - θ)) ≤
        (Real.log 2) ^ 2 / 4 * num / (1 + θ) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left h1_sub_θ (by positivity)
    have hexp_num : (Real.log 2) ^ 2 / 4 * (num * (1 - θ)) =
        (Real.log 2) ^ 2 / 4 * petkovA4 (phaseDelta n) -
          (Real.log 2) ^ 2 / 4 * (50 * M₀ ^ 2 * (Real.log L / L)) -
          (Real.log 2) ^ 2 / 4 * (num * θ) := by
      dsimp [num]; ring
    have hextra46 : 0 ≤ 46 * (M₀ ^ 2 * (Real.log L / L)) := by positivity
    have h100_split : (100 * M₀ ^ 2) * (Real.log L / L) =
        50 * M₀ ^ 2 * (Real.log L / L) + 4 * M₀ ^ 2 * (Real.log L / L) +
          46 * (M₀ ^ 2 * (Real.log L / L)) := by ring
    linarith only [hstep_q, hexp_num, h50_le, hprod_le, hextra46, h100_split]
  have h2M_le : 2 * M₀ ≤ 100 * M₀ ^ 2 := by linarith only [hM₀_le_sq, hM₀_pos]
  have hTP_loc' : |TPlus n - targetDeficit (phaseDelta n)| ≤ 100 * M₀ ^ 2 * (Real.log L / L) :=
    hTP_loc.trans (mul_le_mul_of_nonneg_right h2M_le (by positivity))
  have hTF_loc' : |TFour n - targetDeficit (phaseDelta n)| ≤ 100 * M₀ ^ 2 * (Real.log L / L) :=
    hTF_loc.trans (mul_le_mul_of_nonneg_right h2M_le (by positivity))
  exact ⟨hroot_plus, hroot_four, hTP_loc', hTF_loc',
    hsP_lo, hsP_hi, hsF_lo, hsF_hi, hsep_main⟩

/-! ### 3. Discrete Thresholds `kChiMinus`, `kCoSeed`, Gap Bound, and `PartB` Subcriticality -/

/-- Lower chromatic threshold `k_χ^-(n) = ⌊n / sPlus n⌋₊ - ⌈100 * n / (log n)^4⌉₊`. -/
noncomputable def kChiMinus (n : ℕ) : ℕ :=
  ⌊(n : ℝ) / sPlus n⌋₊ - ⌈100 * (n : ℝ) / (Real.log (n : ℝ)) ^ 4⌉₊

/-- Seed cochromatic block count `K_n = ⌈n / sFourCo n⌉₊ + ⌈1000 * n / (log n)^4⌉₊`. -/
noncomputable def kCoSeed (n : ℕ) : ℕ :=
  ⌈(n : ℝ) / sFourCo n⌉₊ + ⌈1000 * (n : ℝ) / (Real.log (n : ℝ)) ^ 4⌉₊

/-- Helper bound `c * (x / L ^ 4) ≤ x / L` whenever `0 ≤ x`, `0 < L`, and `c ≤ L ^ 3`. -/
private lemma mul_div_pow_four_le_div {c x L : ℝ}
    (hx : 0 ≤ x) (hL : 0 < L) (hc : c ≤ L ^ 3) :
    c * (x / L ^ 4) ≤ x / L := by
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) hL]
  calc
    c * x * L ≤ L ^ 3 * x * L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hx) hL.le
    _ = x * L ^ 4 := by ring

/-- **Discrete threshold gap between `kChiMinus` and `kCoSeed`**:
There exists a nonnegative sequence `ε_A n → 0` such that eventually
`((log 2)^2 / 4 * petkovA4 (phaseDelta n) - ε_A n) * n / (log n)^3 ≤ kChiMinus n - kCoSeed n`. -/
theorem exists_kChiMinus_sub_kCoSeed_gap :
    ∃ ε_A : ℕ → ℝ, (∀ n, 0 ≤ ε_A n) ∧ Tendsto ε_A atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ((Real.log 2) ^ 2 / 4 * petkovA4 (phaseDelta n) - ε_A n) *
          (n : ℝ) / (Real.log (n : ℝ)) ^ 3 ≤
            (kChiMinus n : ℝ) - (kCoSeed n : ℝ) := by
  obtain ⟨C_sep, hC_pos, hev_sep⟩ := eventually_continuous_roots_separation
  let ε_A : ℕ → ℝ := fun n =>
    |(C_sep + 1200) * (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))|
  have hε_nonneg : ∀ n, 0 ≤ ε_A n := fun n => abs_nonneg _
  have hL : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  have hratio : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact h0.comp hL
  have hε_zero : Tendsto ε_A atTop (𝓝 0) := by
    have hmul0 : Tendsto
        (fun n : ℕ => (C_sep + 1200) * (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)))
        atTop (𝓝 0) := by
      simpa using hratio.const_mul (C_sep + 1200)
    simpa [ε_A] using hmul0.abs
  refine ⟨ε_A, hε_nonneg, hε_zero, ?_⟩
  filter_upwards [hev_sep, eventually_ge_atTop 16,
    hL.eventually_ge_atTop 1000,
    hll.eventually_ge_atTop 1,
    (tendsto_nat_div_log_pow_atTop 4).eventually_ge_atTop 1] with
      n ⟨_, _, _, _, hsP_lo, hsP_hi, hsF_lo, _, hsep⟩ hn16 hL1000 hll1 hnL4
  set L : ℝ := Real.log (n : ℝ)
  have hL1000' : (1000 : ℝ) ≤ L := hL1000
  have hll1' : (1 : ℝ) ≤ Real.log L := hll1
  have hnL4' : (1 : ℝ) ≤ (n : ℝ) / L ^ 4 := hnL4
  have hL_pos : 0 < L := by linarith only [hL1000']
  have hsP_pos : 0 < sPlus n := by linarith only [hsP_lo, hL_pos]
  have hsF_pos : 0 < sFourCo n := by linarith only [hsF_lo, hL_pos]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  -- Show `⌈100 * n / L^4⌉₊ ≤ ⌊n / sPlus n⌋₊`
  have hsub_ok : ⌈100 * (n : ℝ) / L ^ 4⌉₊ ≤ ⌊(n : ℝ) / sPlus n⌋₊ := by
    have h1 : (⌈100 * (n : ℝ) / L ^ 4⌉₊ : ℝ) ≤ 100 * (n : ℝ) / L ^ 4 + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    have h2 : (n : ℝ) / (3 * L) ≤ (n : ℝ) / sPlus n :=
      div_le_div_of_nonneg_left hn_pos.le hsP_pos hsP_hi
    have h3 : 100 * (n : ℝ) / L ^ 4 + 2 ≤ (n : ℝ) / (3 * L) := by
      have hL3 : (306 : ℝ) ≤ L ^ 3 := by
        calc
          (306 : ℝ) ≤ 1000 ^ 3 := by norm_num
          _ ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL1000' 3
      have hmul := mul_div_pow_four_le_div hn_pos.le hL_pos hL3
      have hdiv3 : (n : ℝ) / L = 3 * ((n : ℝ) / (3 * L)) := by ring
      have h100_eq : 100 * (n : ℝ) / L ^ 4 = 100 * ((n : ℝ) / L ^ 4) := by ring
      linarith only [hmul, hdiv3, h100_eq, hnL4']
    have hfloor : (n : ℝ) / sPlus n - 1 ≤ (⌊(n : ℝ) / sPlus n⌋₊ : ℝ) :=
      (Nat.sub_one_lt_floor _).le
    have hlt : (⌈100 * (n : ℝ) / L ^ 4⌉₊ : ℝ) < (⌊(n : ℝ) / sPlus n⌋₊ : ℝ) + 1 := by
      linarith only [h1, h2, h3, hfloor]
    exact Nat.lt_succ_iff.mp (Nat.cast_lt.mp (by push_cast; exact hlt))
  have hkChi_lb : (n : ℝ) / sPlus n - 100 * (n : ℝ) / L ^ 4 - 2 ≤ (kChiMinus n : ℝ) := by
    unfold kChiMinus
    rw [Nat.cast_sub hsub_ok]
    have h1 : (n : ℝ) / sPlus n - 1 ≤ (⌊(n : ℝ) / sPlus n⌋₊ : ℝ) := (Nat.sub_one_lt_floor _).le
    have h2 : (⌈100 * (n : ℝ) / L ^ 4⌉₊ : ℝ) ≤ 100 * (n : ℝ) / L ^ 4 + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    change (n : ℝ) / sPlus n - 100 * (n : ℝ) / L ^ 4 - 2 ≤
      (⌊(n : ℝ) / sPlus n⌋₊ : ℝ) - (⌈100 * (n : ℝ) / L ^ 4⌉₊ : ℝ)
    linarith only [h1, h2]
  have hkCo_ub : (kCoSeed n : ℝ) ≤ (n : ℝ) / sFourCo n + 1000 * (n : ℝ) / L ^ 4 + 2 := by
    unfold kCoSeed
    push_cast
    have h1 : (⌈(n : ℝ) / sFourCo n⌉₊ : ℝ) ≤ (n : ℝ) / sFourCo n + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    have h2 : (⌈1000 * (n : ℝ) / L ^ 4⌉₊ : ℝ) ≤ 1000 * (n : ℝ) / L ^ 4 + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    change (⌈(n : ℝ) / sFourCo n⌉₊ : ℝ) + (⌈1000 * (n : ℝ) / L ^ 4⌉₊ : ℝ) ≤
      (n : ℝ) / sFourCo n + 1000 * (n : ℝ) / L ^ 4 + 2
    linarith only [h1, h2]
  have hshift_le : 1100 * (n : ℝ) / L ^ 4 + 4 ≤
      (1200 * (Real.log L / L)) * (n : ℝ) / L ^ 3 := by
    have h1100_eq : 1100 * (n : ℝ) / L ^ 4 = 1100 * ((n : ℝ) / L ^ 4) := by ring
    have h1200 : 1100 * (n : ℝ) / L ^ 4 + 4 ≤ (1200 / L) * (n : ℝ) / L ^ 3 := by
      have heq : (1200 / L) * (n : ℝ) / L ^ 3 = 1200 * ((n : ℝ) / L ^ 4) := by ring
      rw [heq]
      linarith only [h1100_eq, hnL4']
    refine h1200.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hn_pos.le)
      (by positivity))
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hL_pos]
    linarith only [hll1']
  have hε_eq : ε_A n = (C_sep + 1200) * (Real.log L / L) := by
    dsimp [ε_A]
    change |(C_sep + 1200) * (Real.log L / L)| = (C_sep + 1200) * (Real.log L / L)
    exact abs_of_nonneg (mul_nonneg (by positivity) (div_nonneg (by linarith only [hll1']) hL_pos.le))
  rw [hε_eq]
  have hsep' :
      ((Real.log 2) ^ 2 / 4 * petkovA4 (phaseDelta n) - C_sep * (Real.log L / L)) *
        (n : ℝ) / L ^ 3 ≤ (n : ℝ) / sPlus n - (n : ℝ) / sFourCo n := hsep
  have hsplit_lhs :
      ((Real.log 2) ^ 2 / 4 * petkovA4 (phaseDelta n) - (C_sep + 1200) * (Real.log L / L)) *
        (n : ℝ) / L ^ 3 =
      (((Real.log 2) ^ 2 / 4 * petkovA4 (phaseDelta n) - C_sep * (Real.log L / L)) *
        (n : ℝ) / L ^ 3) -
      ((1200 * (Real.log L / L)) * (n : ℝ) / L ^ 3) := by ring
  change ((Real.log 2) ^ 2 / 4 * petkovA4 (phaseDelta n) - (C_sep + 1200) * (Real.log L / L)) *
      (n : ℝ) / L ^ 3 ≤ (kChiMinus n : ℝ) - (kCoSeed n : ℝ)
  rw [hsplit_lhs]
  have h100_1000 : 100 * (n : ℝ) / L ^ 4 + 1000 * (n : ℝ) / L ^ 4 = 1100 * (n : ℝ) / L ^ 4 := by
    ring
  linarith only [hsep', hkChi_lb, hkCo_ub, hshift_le, h100_1000]

/-- **Subcriticality of `kChiMinus n` for Part B (`PartB.lean`)**:
Eventually `1 ≤ kChiMinus n ≤ n`, the average class size `s_k = n / kChiMinus n` satisfies
`alphaNat n - s_k ∈ [2.6, 4.1]`, and
`(kChiMinus n : ℝ) * (profileBasePhi n s_k + freeEnergyPlus (alphaNat n - s_k)) ≤
  -50 * (n : ℝ) / (Real.log (n : ℝ)) ^ 2`. -/
theorem eventually_kChiMinus_subcritical :
    ∀ᶠ n : ℕ in atTop,
      let k := kChiMinus n;
      let s_k := (n : ℝ) / (k : ℝ);
      let T_k := (alphaNat n : ℝ) - s_k;
      1 ≤ k ∧ k ≤ n ∧
      T_k ∈ Set.Icc (2.6 : ℝ) 4.1 ∧
      (k : ℝ) * (profileBasePhi n s_k + freeEnergyPlus T_k) ≤
        -50 * (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
  obtain ⟨C_sep, hC_pos, hev_sep⟩ := eventually_continuous_roots_separation
  have hL : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact h0.comp hL
  filter_upwards [eventually_alphaNat_regime, hev_sep,
    hL.eventually_ge_atTop (10000 + 20 * |alphaConst|),
    hratio.eventually (ge_mem_nhds (show (0 : ℝ) < min (1 / 20) (1 / (20 * C_sep)) by positivity)),
    (tendsto_nat_div_log_pow_atTop 4).eventually_ge_atTop 10] with
      n ⟨hn16, hα20, _, hqα, _, hhi⟩ ⟨hroot_plus, _, hTP_loc, _, hsP_lo, hsP_hi, _, _, _⟩
      hLbig hrat_both hnL4
  intro k s_k T_k
  set L : ℝ := Real.log (n : ℝ)
  have hLbig' : 10000 + 20 * |alphaConst| ≤ L := hLbig
  have hL10000 : (10000 : ℝ) ≤ L := by linarith only [hLbig', abs_nonneg alphaConst]
  have hnL4' : (10 : ℝ) ≤ (n : ℝ) / L ^ 4 := hnL4
  have hL_pos : 0 < L := by linarith only [hL10000]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hsP_pos : 0 < sPlus n := by linarith only [hsP_lo, hL_pos]
  have hrat20 : Real.log L / L ≤ 1 / 20 := (le_min_iff.mp hrat_both).1
  have hratC : Real.log L / L ≤ 1 / (20 * C_sep) := (le_min_iff.mp hrat_both).2
  -- Bounds `(n : ℝ) / (4 * L) ≤ k ≤ (n : ℝ) / (2 * L)`
  have hL3_2000 : (2000 : ℝ) ≤ L ^ 3 := by
    calc
      (2000 : ℝ) ≤ 10000 ^ 3 := by norm_num
      _ ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL10000 3
  have hmul_2000 := mul_div_pow_four_le_div hn_pos.le hL_pos hL3_2000
  have h100_eq : 100 * (n : ℝ) / L ^ 4 = 100 * ((n : ℝ) / L ^ 4) := by ring
  have hsub_ok : ⌈100 * (n : ℝ) / L ^ 4⌉₊ ≤ ⌊(n : ℝ) / sPlus n⌋₊ := by
    have h1 : (⌈100 * (n : ℝ) / L ^ 4⌉₊ : ℝ) ≤ 100 * (n : ℝ) / L ^ 4 + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    have h2 : (n : ℝ) / (3 * L) ≤ (n : ℝ) / sPlus n :=
      div_le_div_of_nonneg_left hn_pos.le hsP_pos hsP_hi
    have hdiv3 : (n : ℝ) / L = 3 * ((n : ℝ) / (3 * L)) := by ring
    have hfloor : (n : ℝ) / sPlus n - 1 ≤ (⌊(n : ℝ) / sPlus n⌋₊ : ℝ) :=
      (Nat.sub_one_lt_floor _).le
    have hlt : (⌈100 * (n : ℝ) / L ^ 4⌉₊ : ℝ) < (⌊(n : ℝ) / sPlus n⌋₊ : ℝ) + 1 := by
      linarith only [h1, h2, hmul_2000, hdiv3, h100_eq, hfloor, hnL4']
    exact Nat.lt_succ_iff.mp (Nat.cast_lt.mp (by push_cast; exact hlt))
  have hk_cast : (k : ℝ) = (⌊(n : ℝ) / sPlus n⌋₊ : ℝ) - (⌈100 * (n : ℝ) / L ^ 4⌉₊ : ℝ) := by
    dsimp [k, kChiMinus, L]
    exact Nat.cast_sub hsub_ok
  have hk_lo_real : (n : ℝ) / (4 * L) ≤ (k : ℝ) := by
    rw [hk_cast]
    have h1 : (n : ℝ) / (3 * L) - 1 ≤ (⌊(n : ℝ) / sPlus n⌋₊ : ℝ) := by
      have hf := (Nat.sub_one_lt_floor ((n : ℝ) / sPlus n)).le
      have hd := div_le_div_of_nonneg_left hn_pos.le hsP_pos hsP_hi
      linarith only [hf, hd]
    have h2 : (⌈100 * (n : ℝ) / L ^ 4⌉₊ : ℝ) ≤ 100 * (n : ℝ) / L ^ 4 + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    have hdiv3 : (n : ℝ) / (3 * L) = (1 / 3 : ℝ) * ((n : ℝ) / L) := by ring
    have hdiv4 : (n : ℝ) / (4 * L) = (1 / 4 : ℝ) * ((n : ℝ) / L) := by ring
    linarith only [h1, h2, hmul_2000, h100_eq, hdiv3, hdiv4, hnL4']
  have hk_hi_real : (k : ℝ) ≤ (n : ℝ) / (2 * L) := by
    rw [hk_cast]
    have h1 : (⌊(n : ℝ) / sPlus n⌋₊ : ℝ) ≤ (n : ℝ) / sPlus n := Nat.floor_le (by positivity)
    have h2 : (n : ℝ) / sPlus n ≤ (n : ℝ) / (2 * L) :=
      div_le_div_of_nonneg_left hn_pos.le (by positivity) hsP_lo
    have h3 : 0 ≤ (⌈100 * (n : ℝ) / L ^ 4⌉₊ : ℝ) := Nat.cast_nonneg _
    linarith only [h1, h2, h3]
  have hk_ge1 : 1 ≤ k := by
    have hgt : (1 : ℝ) ≤ (n : ℝ) / (4 * L) := by
      have hdiv4 : (n : ℝ) / (4 * L) = (1 / 4 : ℝ) * ((n : ℝ) / L) := by ring
      linarith only [hmul_2000, hnL4', hdiv4]
    exact_mod_cast (hgt.trans hk_lo_real)
  have hk_le_n : k ≤ n := by
    have hle : (n : ℝ) / (2 * L) ≤ (n : ℝ) :=
      div_le_self hn_pos.le (by linarith only [hL10000])
    exact_mod_cast (hk_hi_real.trans hle)
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_ge1
  -- Bounds on `TPlus n - T_k = s_k - sPlus n`
  have hTP_sub_Tk_eq : TPlus n - T_k = ((n : ℝ) - (k : ℝ) * sPlus n) / (k : ℝ) := by
    dsimp [T_k, s_k]
    unfold sPlus
    rw [eq_div_iff hk_pos.ne']
    field_simp [hk_pos.ne']
    ring
  have hTP_sub_Tk_lo : 400 / L ^ 2 ≤ TPlus n - T_k := by
    rw [hTP_sub_Tk_eq, le_div_iff₀ hk_pos]
    have hk_le_sub : (k : ℝ) ≤ (n : ℝ) / sPlus n - 100 * (n : ℝ) / L ^ 4 := by
      rw [hk_cast]
      have h1 : (⌊(n : ℝ) / sPlus n⌋₊ : ℝ) ≤ (n : ℝ) / sPlus n := Nat.floor_le (by positivity)
      have h2 : 100 * (n : ℝ) / L ^ 4 ≤ (⌈100 * (n : ℝ) / L ^ 4⌉₊ : ℝ) := Nat.le_ceil _
      linarith only [h1, h2]
    have hnum_lo : 100 * (n : ℝ) / L ^ 4 * (2 * L) ≤ (n : ℝ) - (k : ℝ) * sPlus n := by
      have hm := mul_le_mul_of_nonneg_right hk_le_sub hsP_pos.le
      have hns : ((n : ℝ) / sPlus n - 100 * (n : ℝ) / L ^ 4) * sPlus n =
          (n : ℝ) - (100 * (n : ℝ) / L ^ 4) * sPlus n := by
        field_simp [hsP_pos.ne']
      rw [hns] at hm
      have hs2 : (100 * (n : ℝ) / L ^ 4) * (2 * L) ≤ (100 * (n : ℝ) / L ^ 4) * sPlus n :=
        mul_le_mul_of_nonneg_left hsP_lo (by positivity)
      linarith only [hm, hs2]
    calc
      400 / L ^ 2 * (k : ℝ)
          ≤ 400 / L ^ 2 * ((n : ℝ) / (2 * L)) :=
        mul_le_mul_of_nonneg_left hk_hi_real (by positivity)
      _ = 100 * (n : ℝ) / L ^ 4 * (2 * L) := by field_simp [hL_pos.ne']; ring
      _ ≤ (n : ℝ) - (k : ℝ) * sPlus n := hnum_lo
  have hTP_sub_Tk_hi : TPlus n - T_k ≤ 2000 / L ^ 2 := by
    rw [hTP_sub_Tk_eq, div_le_iff₀ hk_pos]
    have hk_ge_sub : (n : ℝ) / sPlus n - 100 * (n : ℝ) / L ^ 4 - 2 ≤ (k : ℝ) := by
      rw [hk_cast]
      have h1 := (Nat.sub_one_lt_floor ((n : ℝ) / sPlus n)).le
      have h2 := (Nat.ceil_lt_add_one (show 0 ≤ 100 * (n : ℝ) / L ^ 4 by positivity)).le
      linarith only [h1, h2]
    have hnum_hi : (n : ℝ) - (k : ℝ) * sPlus n ≤ (102 * (n : ℝ) / L ^ 4) * (3 * L) := by
      have hm := mul_le_mul_of_nonneg_right hk_ge_sub hsP_pos.le
      have hns : ((n : ℝ) / sPlus n - 100 * (n : ℝ) / L ^ 4 - 2) * sPlus n =
          (n : ℝ) - (100 * (n : ℝ) / L ^ 4 + 2) * sPlus n := by
        field_simp [hsP_pos.ne']; ring
      rw [hns] at hm
      have h102_eq : 102 * (n : ℝ) / L ^ 4 = 102 * ((n : ℝ) / L ^ 4) := by ring
      have h102_ge : 100 * (n : ℝ) / L ^ 4 + 2 ≤ 102 * (n : ℝ) / L ^ 4 := by
        linarith only [h100_eq, h102_eq, hnL4']
      have hs3 : (100 * (n : ℝ) / L ^ 4 + 2) * sPlus n ≤ (102 * (n : ℝ) / L ^ 4) * (3 * L) :=
        mul_le_mul h102_ge hsP_hi hsP_pos.le (by positivity)
      linarith only [hm, hs3]
    calc
      (n : ℝ) - (k : ℝ) * sPlus n
          ≤ (102 * (n : ℝ) / L ^ 4) * (3 * L) := hnum_hi
      _ = 306 * ((n : ℝ) / L ^ 3) := by field_simp [hL_pos.ne']; ring
      _ ≤ 500 * ((n : ℝ) / L ^ 3) := by
        have hpos3 : 0 ≤ (n : ℝ) / L ^ 3 := by positivity
        linarith only [hpos3]
      _ = 2000 / L ^ 2 * ((n : ℝ) / (4 * L)) := by field_simp [hL_pos.ne']; ring
      _ ≤ 2000 / L ^ 2 * (k : ℝ) :=
        mul_le_mul_of_nonneg_left hk_lo_real (by positivity)
  -- Show `T_k ∈ [2.6, 4.1]`
  have hTk_mem : T_k ∈ Set.Icc (2.6 : ℝ) 4.1 := by
    have hTδ_bounds := targetDeficit_bounds_tight n
    have hTP_close : |TPlus n - targetDeficit (phaseDelta n)| ≤ 1 / 20 := by
      have hm := mul_le_mul_of_nonneg_left hratC hC_pos.le
      have hs : C_sep * (1 / (20 * C_sep)) = 1 / 20 := by field_simp [hC_pos.ne']
      have hloc' : |TPlus n - targetDeficit (phaseDelta n)| ≤ C_sep * (Real.log L / L) := hTP_loc
      linarith only [hloc', hm, hs]
    have h2000_small : 2000 / L ^ 2 ≤ 1 / 20 := by
      rw [div_le_iff₀ (by positivity)]
      have hsq : (10000 : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hL10000 2
      linarith only [hsq]
    have habs_TP := abs_le.mp hTP_close
    have h400_nonneg : 0 ≤ 400 / L ^ 2 := by positivity
    exact ⟨by linarith only [hTδ_bounds.1, habs_TP.1, hTP_sub_Tk_hi, h2000_small],
      by linarith only [hTδ_bounds.2, habs_TP.2, hTP_sub_Tk_lo, h400_nonneg]⟩
  -- Evaluate `profileBasePhi n s_k + freeEnergyPlus T_k` by subtracting root equation at `TPlus n`
  have hTP_mem := TPlus_mem_Icc n
  have hdiff_phi := abs_profileBasePhi_diff_approx hn16 hα20 hqα hhi hTk_mem hTP_mem
  have hs_k_eq : (alphaNat n : ℝ) - T_k = s_k := by dsimp [T_k]; ring
  have hlip_fe := abs_freeEnergyPlus_sub_le hTk_mem hTP_mem
  have hTP_gt_Tk : 0 < TPlus n - T_k := by
    have hpos400 : 0 < 400 / L ^ 2 := by positivity
    linarith only [hTP_sub_Tk_lo, hpos400]
  have habs_diff : |T_k - TPlus n| = TPlus n - T_k := by
    rw [abs_sub_comm, abs_of_pos hTP_gt_Tk]
  have hll_pos : 0 ≤ Real.log L := Real.log_nonneg (by linarith only [hL10000])
  have hslope_small : 3 * |Real.log L| + 2 * |alphaConst| + 16 ≤ (1 / 2 : ℝ) * L := by
    rw [abs_of_nonneg hll_pos]
    have hll_le : Real.log L ≤ (1 / 20 : ℝ) * L := by
      have h1 := (div_le_iff₀ hL_pos).mp hrat20
      linarith only [h1]
    linarith only [hll_le, hLbig', abs_nonneg alphaConst]
  have hsum_neg : profileBasePhi n s_k + freeEnergyPlus T_k ≤ -(200 / L) := by
    have hsub : profileBasePhi n s_k + freeEnergyPlus T_k =
        (profileBasePhi n ((alphaNat n : ℝ) - T_k) - profileBasePhi n ((alphaNat n : ℝ) - TPlus n)) +
        (freeEnergyPlus T_k - freeEnergyPlus (TPlus n)) := by
      rw [hs_k_eq]
      unfold sPlus at hroot_plus
      linarith only [hroot_plus]
    rw [hsub]
    have hp1 := (abs_le.mp hdiff_phi).2
    change (profileBasePhi n ((alphaNat n : ℝ) - T_k) -
        profileBasePhi n ((alphaNat n : ℝ) - TPlus n)) - (T_k - TPlus n) * L ≤
      |T_k - TPlus n| * (3 * |Real.log L| + 2 * |alphaConst| + 6) at hp1
    have hp2 := (abs_le.mp hlip_fe).2
    rw [habs_diff] at hp1 hp2
    have hexp_c : -(TPlus n - T_k) * (L - (3 * |Real.log L| + 2 * |alphaConst| + 16)) =
        (T_k - TPlus n) * L + (TPlus n - T_k) * (3 * |Real.log L| + 2 * |alphaConst| + 6) +
          10 * (TPlus n - T_k) := by ring
    have hcomb : (profileBasePhi n ((alphaNat n : ℝ) - T_k) -
        profileBasePhi n ((alphaNat n : ℝ) - TPlus n)) +
        (freeEnergyPlus T_k - freeEnergyPlus (TPlus n)) ≤
        -(TPlus n - T_k) * (L - (3 * |Real.log L| + 2 * |alphaConst| + 16)) := by
      linarith only [hp1, hp2, hexp_c]
    have hhalf : -(TPlus n - T_k) * (L - (3 * |Real.log L| + 2 * |alphaConst| + 16)) ≤
        -(TPlus n - T_k) * ((1 / 2 : ℝ) * L) := by
      have hm := mul_le_mul_of_nonneg_left
        (show (1 / 2 : ℝ) * L ≤ L - (3 * |Real.log L| + 2 * |alphaConst| + 16) by
          linarith only [hslope_small])
        hTP_gt_Tk.le
      linarith only [hm]
    have h200 : 200 / L ≤ (TPlus n - T_k) * ((1 / 2 : ℝ) * L) := by
      calc
        200 / L = (400 / L ^ 2) * ((1 / 2 : ℝ) * L) := by field_simp [hL_pos.ne']; ring
        _ ≤ (TPlus n - T_k) * ((1 / 2 : ℝ) * L) :=
          mul_le_mul_of_nonneg_right hTP_sub_Tk_lo (by positivity)
    have hneg_eq : -(TPlus n - T_k) * ((1 / 2 : ℝ) * L) =
        -((TPlus n - T_k) * ((1 / 2 : ℝ) * L)) := by ring
    linarith only [hcomb, hhalf, h200, hneg_eq]
  refine ⟨hk_ge1, hk_le_n, hTk_mem, ?_⟩
  calc
    (k : ℝ) * (profileBasePhi n s_k + freeEnergyPlus T_k)
        ≤ (k : ℝ) * (-(200 / L)) := mul_le_mul_of_nonneg_left hsum_neg hk_pos.le
    _ ≤ ((n : ℝ) / (4 * L)) * (-(200 / L)) := by
      have hm := mul_le_mul_of_nonneg_right hk_lo_real (by positivity : 0 ≤ 200 / L)
      have he1 : (k : ℝ) * (-(200 / L)) = -((k : ℝ) * (200 / L)) := by ring
      have he2 : ((n : ℝ) / (4 * L)) * (-(200 / L)) = -(((n : ℝ) / (4 * L)) * (200 / L)) := by ring
      linarith only [hm, he1, he2]
    _ = -50 * (n : ℝ) / L ^ 2 := by field_simp [hL_pos.ne']; ring

/-! ### 4. Rounded Integer 4-Size Witness Multiplicities (`witnessCounts`) -/

/-- The four block sizes `α_n - 2, α_n - 3, α_n - 4, α_n - 5` indexed by `j : Fin 4`. -/
noncomputable def witnessSize (n : ℕ) (j : Fin 4) : ℕ :=
  alphaNat n - (j.val + 2)

/-- Effective average deficit `T_seed(n) = α_n - n / kCoSeed(n)` at the seed block count. -/
noncomputable def seedDeficit (n : ℕ) : ℝ :=
  (alphaNat n : ℝ) - (n : ℝ) / (kCoSeed n : ℝ)

/-- Optimal 4-size Gibbs probability vector at `seedDeficit n` (defaulting to `1 / 4` outside `[2.6, 4.1]`). -/
noncomputable def gibbsSeedProb (n : ℕ) : ℤ → ℝ :=
  if h : seedDeficit n ∈ Set.Icc (2.6 : ℝ) 4.1
  then Classical.choose (exists_optimal_gibbs_four h)
  else fun _ => 1 / 4

/-- Rounded integer 4-size block multiplicities `witnessCounts n : Fin 4 → ℕ` via Petkov's
unimodular `(2, 3)` deficit adjustment (`κ_4 = ⌊K p_4⌋₊`, `κ_5 = ⌊K p_5⌋₊`, and `(κ_2, κ_3)`
solving `κ_2 + κ_3 = K - κ_4 - κ_5` and `2 κ_2 + 3 κ_3 = (K α_n - n) - 4 κ_4 - 5 κ_5`). -/
noncomputable def witnessCounts (n : ℕ) : Fin 4 → ℕ :=
  let K : ℕ := kCoSeed n
  let α : ℕ := alphaNat n
  let D : ℤ := (K : ℤ) * (α : ℤ) - (n : ℤ)
  let κ₄ : ℕ := ⌊(K : ℝ) * gibbsSeedProb n 4⌋₊
  let κ₅ : ℕ := ⌊(K : ℝ) * gibbsSeedProb n 5⌋₊
  let R_count : ℤ := (K : ℤ) - (κ₄ : ℤ) - (κ₅ : ℤ)
  let R_def : ℤ := D - 4 * (κ₄ : ℤ) - 5 * (κ₅ : ℤ)
  fun j =>
    match j.val with
    | 0 => (3 * R_count - R_def).toNat
    | 1 => (R_def - 2 * R_count).toNat
    | 2 => κ₄
    | _ => κ₅

private lemma ten_pow_35_spec :
    ∃ c35 : ℝ, 1 ≤ c35 ∧ c35 ≤ Real.exp 100 ∧ (10 : ℝ) ^ 35 = c35 := by
  refine ⟨(10 : ℝ) ^ 35, by norm_num, ?_, rfl⟩
  have h10_le : (10 : ℝ) ≤ Real.exp 2.5 := by
    have he1 : (2.71 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have he2 : (2.71 : ℝ) ^ 5 ≤ Real.exp 5 := by
      rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num) he1 5
    have hsq : Real.exp 5 = Real.exp 2.5 * Real.exp 2.5 := by
      rw [← Real.exp_add]; norm_num
    have h100 : (10 : ℝ) ^ 2 ≤ (2.71 : ℝ) ^ 5 := by norm_num
    nlinarith only [he2, hsq, h100, Real.exp_pos 2.5]
  calc
    (10 : ℝ) ^ 35 ≤ (Real.exp 2.5) ^ 35 := pow_le_pow_left₀ (by norm_num) h10_le 35
    _ = Real.exp 87.5 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ Real.exp 100 := Real.exp_le_exp.mpr (by norm_num)

/-- **Master specification of the rounded 4-size witness profile (`arXiv:2608.30604`, Section 4)**:
Eventually for large `n`:
1. `∑ j, witnessCounts n j = kCoSeed n`,
2. `∑ j, witnessSize n j * witnessCounts n j = n`,
3. Every size `witnessSize n j ≥ 10` and every multiplicity satisfies `1 ≤ witnessCounts n j` and
   `(kCoSeed n : ℝ) / (2 * 10^35) ≤ witnessCounts n j`,
4. The exact log-first-moment of unordered signed 4-size partitions with profile `witnessCounts n`
   is at least `+100 * n / (log n)^2`. -/
theorem eventually_witnessCounts_spec :
    ∀ᶠ n : ℕ in atTop,
      (∑ j : Fin 4, witnessCounts n j = kCoSeed n) ∧
      (∑ j : Fin 4, witnessSize n j * witnessCounts n j = n) ∧
      (∀ j : Fin 4, 10 ≤ witnessSize n j) ∧
      (∀ j : Fin 4, 1 ≤ witnessCounts n j ∧
        (kCoSeed n : ℝ) / (2 * (10 : ℝ) ^ 35) ≤ (witnessCounts n j : ℝ)) ∧
      100 * (n : ℝ) / (Real.log (n : ℝ)) ^ 2 ≤
        Real.log (n ! : ℝ) + (kCoSeed n : ℝ) * Real.log 2 -
          ∑ j : Fin 4, Real.log ((witnessCounts n j) ! : ℝ) -
          ∑ j : Fin 4, (witnessCounts n j : ℝ) *
            (Real.log ((witnessSize n j) ! : ℝ) +
              Real.log 2 * ((witnessSize n j).choose 2 : ℝ)) := by
  obtain ⟨c35, hc35_ge1, hc35_exp, hc35_def⟩ := ten_pow_35_spec
  have hc35_pos : 0 < c35 := by linarith only [hc35_ge1]
  obtain ⟨C_sep, hC_pos, hev_sep⟩ := eventually_continuous_roots_separation
  have hL : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact h0.comp hL
  filter_upwards [eventually_alphaNat_regime, hev_sep,
    hL.eventually_ge_atTop (100000 + 20 * |alphaConst|),
    hratio.eventually (ge_mem_nhds (show (0 : ℝ) < min (1 / 20) (1 / (20 * C_sep)) by positivity)),
    (tendsto_nat_div_log_pow_atTop 4).eventually_ge_atTop (40 * c35)] with
      n ⟨hn16, hα20, _, hqα, hlo, hhi⟩ ⟨_, hroot_four, _, hTF_loc, _, _, hsF_lo, hsF_hi, _⟩
      hLbig hrat_both hnL4
  rw [hc35_def]
  set α : ℕ := alphaNat n
  set K : ℕ := kCoSeed n
  set L : ℝ := Real.log (n : ℝ)
  set q : ℝ := Real.log 2
  have hLbig' : 100000 + 20 * |alphaConst| ≤ L := hLbig
  have hL100000 : (100000 : ℝ) ≤ L := by linarith only [hLbig', abs_nonneg alphaConst]
  have hnL4' : 40 * c35 ≤ (n : ℝ) / L ^ 4 := hnL4
  have hnL4_ge40 : (40 : ℝ) ≤ (n : ℝ) / L ^ 4 := by
    have h40c : (40 : ℝ) ≤ 40 * c35 := by linarith only [hc35_ge1]
    linarith only [h40c, hnL4']
  have hL_pos : 0 < L := by linarith only [hL100000]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hsF_pos : 0 < sFourCo n := by linarith only [hsF_lo, hL_pos]
  have hrat20 : Real.log L / L ≤ 1 / 20 := (le_min_iff.mp hrat_both).1
  have hratC : Real.log L / L ≤ 1 / (20 * C_sep) := (le_min_iff.mp hrat_both).2
  -- Bounds `(n : ℝ) / (3 * L) ≤ K ≤ (n : ℝ) / L` and `20 * c35 ≤ K`
  have hL3_4000 : (4000 : ℝ) ≤ L ^ 3 := by
    calc
      (4000 : ℝ) ≤ 100000 ^ 3 := by norm_num
      _ ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL100000 3
  have hmul_4000 := mul_div_pow_four_le_div hn_pos.le hL_pos hL3_4000
  have h1000_eq : 1000 * (n : ℝ) / L ^ 4 = 1000 * ((n : ℝ) / L ^ 4) := by ring
  have hK_lo_real : (n : ℝ) / (3 * L) ≤ (K : ℝ) := by
    dsimp [K, kCoSeed]
    push_cast
    have h1 : (n : ℝ) / (3 * L) ≤ (n : ℝ) / sFourCo n :=
      div_le_div_of_nonneg_left hn_pos.le hsF_pos hsF_hi
    have h2 : (n : ℝ) / sFourCo n ≤ (⌈(n : ℝ) / sFourCo n⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : 0 ≤ (⌈1000 * (n : ℝ) / (Real.log (n : ℝ)) ^ 4⌉₊ : ℝ) := Nat.cast_nonneg _
    linarith only [h1, h2, h3]
  have hK_hi_real : (K : ℝ) ≤ (n : ℝ) / L := by
    dsimp [K, kCoSeed]
    push_cast
    have h1 : (⌈(n : ℝ) / sFourCo n⌉₊ : ℝ) ≤ (n : ℝ) / (2 * L) + 1 := by
      have hc := (Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) / sFourCo n by positivity)).le
      have hd := div_le_div_of_nonneg_left hn_pos.le (by positivity) hsF_lo
      linarith only [hc, hd]
    have h2 : (⌈1000 * (n : ℝ) / L ^ 4⌉₊ : ℝ) ≤ 1000 * (n : ℝ) / L ^ 4 + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    have hdiv2 : (n : ℝ) / (2 * L) = (1 / 2 : ℝ) * ((n : ℝ) / L) := by ring
    change (⌈(n : ℝ) / sFourCo n⌉₊ : ℝ) + (⌈1000 * (n : ℝ) / L ^ 4⌉₊ : ℝ) ≤ (n : ℝ) / L
    linarith only [h1, h2, hmul_4000, h1000_eq, hdiv2, hnL4_ge40]
  have hK_huge : 20 * c35 ≤ (K : ℝ) := by
    have hdiv3 : (n : ℝ) / (3 * L) = (1 / 3 : ℝ) * ((n : ℝ) / L) := by ring
    linarith only [hmul_4000, hnL4', hdiv3, hK_lo_real, hc35_pos]
  have hK_pos : 0 < (K : ℝ) := by linarith only [hK_huge, hc35_pos]
  -- Bounds on `seedDeficit n - TFour n`
  set T_K : ℝ := seedDeficit n
  have hKne : (kCoSeed n : ℝ) ≠ 0 := hK_pos.ne'
  have hTK_sub_TF_eq : T_K - TFour n = ((K : ℝ) * sFourCo n - (n : ℝ)) / (K : ℝ) := by
    dsimp [T_K, seedDeficit, K]
    unfold sFourCo
    rw [eq_div_iff hKne]
    field_simp [hKne]
    ring
  have hTK_sub_TF_lo : 2000 / L ^ 2 ≤ T_K - TFour n := by
    rw [hTK_sub_TF_eq, le_div_iff₀ hK_pos]
    have hK_ge_add : (n : ℝ) / sFourCo n + 1000 * (n : ℝ) / L ^ 4 ≤ (K : ℝ) := by
      dsimp [K, kCoSeed]
      push_cast
      have hc1 := Nat.le_ceil ((n : ℝ) / sFourCo n)
      have hc2 := Nat.le_ceil (1000 * (n : ℝ) / L ^ 4)
      change (n : ℝ) / sFourCo n + 1000 * (n : ℝ) / L ^ 4 ≤
        (⌈(n : ℝ) / sFourCo n⌉₊ : ℝ) + (⌈1000 * (n : ℝ) / L ^ 4⌉₊ : ℝ)
      linarith only [hc1, hc2]
    have hnum_lo : (1000 * (n : ℝ) / L ^ 4) * (2 * L) ≤ (K : ℝ) * sFourCo n - (n : ℝ) := by
      have hm := mul_le_mul_of_nonneg_right hK_ge_add hsF_pos.le
      have hns : ((n : ℝ) / sFourCo n + 1000 * (n : ℝ) / L ^ 4) * sFourCo n =
          (n : ℝ) + (1000 * (n : ℝ) / L ^ 4) * sFourCo n := by
        field_simp [hsF_pos.ne']
      rw [hns] at hm
      have hs2 := mul_le_mul_of_nonneg_left hsF_lo (show 0 ≤ 1000 * (n : ℝ) / L ^ 4 by positivity)
      linarith only [hm, hs2]
    calc
      2000 / L ^ 2 * (K : ℝ)
          ≤ 2000 / L ^ 2 * ((n : ℝ) / L) :=
        mul_le_mul_of_nonneg_left hK_hi_real (by positivity)
      _ = (1000 * (n : ℝ) / L ^ 4) * (2 * L) := by field_simp [hL_pos.ne']; ring
      _ ≤ (K : ℝ) * sFourCo n - (n : ℝ) := hnum_lo
  have hTK_sub_TF_hi : T_K - TFour n ≤ 10000 / L ^ 2 := by
    rw [hTK_sub_TF_eq, div_le_iff₀ hK_pos]
    have hK_le_add : (K : ℝ) ≤ (n : ℝ) / sFourCo n + 1000 * (n : ℝ) / L ^ 4 + 2 := by
      dsimp [K, kCoSeed]
      push_cast
      have hc1 := (Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) / sFourCo n by positivity)).le
      have hc2 := (Nat.ceil_lt_add_one (show 0 ≤ 1000 * (n : ℝ) / L ^ 4 by positivity)).le
      change (⌈(n : ℝ) / sFourCo n⌉₊ : ℝ) + (⌈1000 * (n : ℝ) / L ^ 4⌉₊ : ℝ) ≤
        (n : ℝ) / sFourCo n + 1000 * (n : ℝ) / L ^ 4 + 2
      linarith only [hc1, hc2]
    have hnum_hi : (K : ℝ) * sFourCo n - (n : ℝ) ≤ (1002 * (n : ℝ) / L ^ 4) * (3 * L) := by
      have hm := mul_le_mul_of_nonneg_right hK_le_add hsF_pos.le
      have hns : ((n : ℝ) / sFourCo n + 1000 * (n : ℝ) / L ^ 4 + 2) * sFourCo n =
          (n : ℝ) + (1000 * (n : ℝ) / L ^ 4 + 2) * sFourCo n := by
        field_simp [hsF_pos.ne']; ring
      rw [hns] at hm
      have h1002_eq : 1002 * (n : ℝ) / L ^ 4 = 1002 * ((n : ℝ) / L ^ 4) := by ring
      have h1002_ge : 1000 * (n : ℝ) / L ^ 4 + 2 ≤ 1002 * (n : ℝ) / L ^ 4 := by
        linarith only [h1000_eq, h1002_eq, hnL4_ge40]
      have hs3 := mul_le_mul h1002_ge hsF_hi hsF_pos.le (by positivity)
      linarith only [hm, hs3]
    calc
      (K : ℝ) * sFourCo n - (n : ℝ)
          ≤ (1002 * (n : ℝ) / L ^ 4) * (3 * L) := hnum_hi
      _ = 3006 * ((n : ℝ) / L ^ 3) := by field_simp [hL_pos.ne']; ring
      _ ≤ (10000 / 3) * ((n : ℝ) / L ^ 3) := by
        have hpos3 : 0 ≤ (n : ℝ) / L ^ 3 := by positivity
        linarith only [hpos3]
      _ = 10000 / L ^ 2 * ((n : ℝ) / (3 * L)) := by field_simp [hL_pos.ne']
      _ ≤ 10000 / L ^ 2 * (K : ℝ) :=
        mul_le_mul_of_nonneg_left hK_lo_real (by positivity)
  have hTK_mem : T_K ∈ Set.Icc (2.6 : ℝ) 4.1 := by
    have hTδ_bounds := targetDeficit_bounds_tight n
    have hTF_close : |TFour n - targetDeficit (phaseDelta n)| ≤ 1 / 20 := by
      have hm := mul_le_mul_of_nonneg_left hratC hC_pos.le
      have hs : C_sep * (1 / (20 * C_sep)) = 1 / 20 := by field_simp [hC_pos.ne']
      have hloc' : |TFour n - targetDeficit (phaseDelta n)| ≤ C_sep * (Real.log L / L) := hTF_loc
      linarith only [hloc', hm, hs]
    have h10000_small : 10000 / L ^ 2 ≤ 1 / 20 := by
      rw [div_le_iff₀ (by positivity)]
      have hsq : (100000 : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hL100000 2
      linarith only [hsq]
    have habs_TF := abs_le.mp hTF_close
    have h2000_nonneg : 0 ≤ 2000 / L ^ 2 := by positivity
    exact ⟨by linarith only [hTδ_bounds.1, habs_TF.1, hTK_sub_TF_lo, h2000_nonneg],
      by linarith only [hTδ_bounds.2, habs_TF.2, hTK_sub_TF_hi, h10000_small]⟩
  -- Extract optimal Gibbs probabilities `p = gibbsSeedProb n` at `T_K`
  have hp_spec_raw :
      (∀ i ∈ ({2, 3, 4, 5} : Finset ℤ), (1 / (10 : ℝ) ^ 35) ≤ gibbsSeedProb n i) ∧
      (∑ i ∈ ({2, 3, 4, 5} : Finset ℤ), gibbsSeedProb n i = 1) ∧
      (∑ i ∈ ({2, 3, 4, 5} : Finset ℤ), (i : ℝ) * gibbsSeedProb n i = T_K) ∧
      (∑ i ∈ ({2, 3, 4, 5} : Finset ℤ),
        gibbsSeedProb n i * (-(q / 2) * (i : ℝ) ^ 2 - Real.log (gibbsSeedProb n i)) =
          freeEnergyFour T_K) := by
    unfold gibbsSeedProb
    split_ifs with h
    · exact Classical.choose_spec (exists_optimal_gibbs_four h)
    · exact False.elim (h hTK_mem)
  rw [hc35_def] at hp_spec_raw
  rcases hp_spec_raw with ⟨hp_lb, hp_sum, hp_mean, hp_ent⟩
  set p : ℤ → ℝ := gibbsSeedProb n
  have h4set : ({2, 3, 4, 5} : Finset ℤ) = insert 2 (insert 3 (insert 4 {5})) := rfl
  have hp_sum4 : p 2 + p 3 + p 4 + p 5 = 1 := by
    rw [h4set] at hp_sum
    simp only [sum_insert (by decide : (2 : ℤ) ∉ insert 3 (insert 4 ({5} : Finset ℤ))),
      sum_insert (by decide : (3 : ℤ) ∉ insert 4 ({5} : Finset ℤ)),
      sum_insert (by decide : (4 : ℤ) ∉ ({5} : Finset ℤ)), sum_singleton] at hp_sum
    linarith only [hp_sum]
  have hp_mean4 : 2 * p 2 + 3 * p 3 + 4 * p 4 + 5 * p 5 = T_K := by
    rw [h4set] at hp_mean
    simp only [sum_insert (by decide : (2 : ℤ) ∉ insert 3 (insert 4 ({5} : Finset ℤ))),
      sum_insert (by decide : (3 : ℤ) ∉ insert 4 ({5} : Finset ℤ)),
      sum_insert (by decide : (4 : ℤ) ∉ ({5} : Finset ℤ)), sum_singleton] at hp_mean
    norm_num at hp_mean
    linarith only [hp_mean]
  have hp2_lb : 1 / c35 ≤ p 2 := hp_lb 2 (by decide)
  have hp3_lb : 1 / c35 ≤ p 3 := hp_lb 3 (by decide)
  have hp4_lb : 1 / c35 ≤ p 4 := hp_lb 4 (by decide)
  have hp5_lb : 1 / c35 ≤ p 5 := hp_lb 5 (by decide)
  -- Rounding errors for `witnessCounts n`
  set D : ℤ := (K : ℤ) * (α : ℤ) - (n : ℤ)
  set κ₄ : ℕ := ⌊(K : ℝ) * p 4⌋₊
  set κ₅ : ℕ := ⌊(K : ℝ) * p 5⌋₊
  set R_count : ℤ := (K : ℤ) - (κ₄ : ℤ) - (κ₅ : ℤ)
  set R_def : ℤ := D - 4 * (κ₄ : ℤ) - 5 * (κ₅ : ℤ)
  set κ₂_z : ℤ := 3 * R_count - R_def
  set κ₃_z : ℤ := R_def - 2 * R_count
  have hD_real : (D : ℝ) = (K : ℝ) * T_K := by
    dsimp [D, T_K, seedDeficit, K, α]
    push_cast
    field_simp [hKne]
  set f₄ : ℝ := (K : ℝ) * p 4 - (κ₄ : ℝ)
  set f₅ : ℝ := (K : ℝ) * p 5 - (κ₅ : ℝ)
  have hp4_nonneg : 0 ≤ p 4 := le_trans (by positivity) hp4_lb
  have hp5_nonneg : 0 ≤ p 5 := le_trans (by positivity) hp5_lb
  have hf₄_bounds : 0 ≤ f₄ ∧ f₄ ≤ 1 := by
    dsimp [f₄, κ₄]
    exact ⟨sub_nonneg.mpr (Nat.floor_le (by positivity)),
      by linarith only [(Nat.lt_floor_add_one ((K : ℝ) * p 4)).le]⟩
  have hf₅_bounds : 0 ≤ f₅ ∧ f₅ ≤ 1 := by
    dsimp [f₅, κ₅]
    exact ⟨sub_nonneg.mpr (Nat.floor_le (by positivity)),
      by linarith only [(Nat.lt_floor_add_one ((K : ℝ) * p 5)).le]⟩
  have hKs_lin : (K : ℝ) = (K : ℝ) * p 2 + (K : ℝ) * p 3 + (K : ℝ) * p 4 + (K : ℝ) * p 5 := by
    have h1 : (K : ℝ) = (K : ℝ) * (p 2 + p 3 + p 4 + p 5) := by rw [hp_sum4, mul_one]
    linarith [show (K : ℝ) * (p 2 + p 3 + p 4 + p 5) =
      (K : ℝ) * p 2 + (K : ℝ) * p 3 + (K : ℝ) * p 4 + (K : ℝ) * p 5 by ring]
  have hKm_lin : (K : ℝ) * T_K =
      2 * ((K : ℝ) * p 2) + 3 * ((K : ℝ) * p 3) + 4 * ((K : ℝ) * p 4) + 5 * ((K : ℝ) * p 5) := by
    rw [← hp_mean4]
    ring
  have hf4_eq : (κ₄ : ℝ) = (K : ℝ) * p 4 - f₄ := by dsimp [f₄]; ring
  have hf5_eq : (κ₅ : ℝ) = (K : ℝ) * p 5 - f₅ := by dsimp [f₅]; ring
  have hκ₂_real : (κ₂_z : ℝ) = (K : ℝ) * p 2 - f₄ - 2 * f₅ := by
    have hexp : (κ₂_z : ℝ) =
        3 * ((K : ℝ) - (κ₄ : ℝ) - (κ₅ : ℝ)) - ((D : ℝ) - 4 * (κ₄ : ℝ) - 5 * (κ₅ : ℝ)) := by
      dsimp [κ₂_z, R_count, R_def]; push_cast; ring
    linarith only [hexp, hD_real, hKs_lin, hKm_lin, hf4_eq, hf5_eq]
  have hκ₃_real : (κ₃_z : ℝ) = (K : ℝ) * p 3 + 2 * f₄ + 3 * f₅ := by
    have hexp : (κ₃_z : ℝ) =
        ((D : ℝ) - 4 * (κ₄ : ℝ) - 5 * (κ₅ : ℝ)) - 2 * ((K : ℝ) - (κ₄ : ℝ) - (κ₅ : ℝ)) := by
      dsimp [κ₃_z, R_count, R_def]; push_cast; ring
    linarith only [hexp, hD_real, hKs_lin, hKm_lin, hf4_eq, hf5_eq]
  have hKp_ge20 : ∀ {x : ℝ}, 1 / c35 ≤ x → 20 ≤ (K : ℝ) * x ∧
      (K : ℝ) / (2 * c35) + 5 ≤ (K : ℝ) * x := by
    intro x hx
    have h1 : (K : ℝ) / c35 ≤ (K : ℝ) * x := by
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hx hK_pos.le
    have h20 : (20 : ℝ) ≤ (K : ℝ) / c35 := (le_div_iff₀ hc35_pos).mpr hK_huge
    have hhalf : (K : ℝ) / (2 * c35) = (1 / 2 : ℝ) * ((K : ℝ) / c35) := by ring
    exact ⟨by linarith only [h1, h20], by linarith only [h1, h20, hhalf]⟩
  have hκ₂_pos : 0 ≤ κ₂_z := by
    have h1 := (hKp_ge20 hp2_lb).1
    have h2 : (0 : ℝ) ≤ (κ₂_z : ℝ) := by
      linarith only [h1, hκ₂_real, hf₄_bounds.2, hf₅_bounds.2]
    exact_mod_cast h2
  have hκ₃_pos : 0 ≤ κ₃_z := by
    have h1 := (hKp_ge20 hp3_lb).1
    have h2 : (0 : ℝ) ≤ (κ₃_z : ℝ) := by
      linarith only [h1, hκ₃_real, hf₄_bounds.1, hf₅_bounds.1]
    exact_mod_cast h2
  have hw0 : witnessCounts n 0 = κ₂_z.toNat := rfl
  have hw1 : witnessCounts n 1 = κ₃_z.toNat := rfl
  have hw2 : witnessCounts n 2 = κ₄ := rfl
  have hw3 : witnessCounts n 3 = κ₅ := rfl
  -- Part 1: `∑ j, witnessCounts n j = K`
  have hsum_counts : ∑ j : Fin 4, witnessCounts n j = K := by
    rw [Fin.sum_univ_four, hw0, hw1, hw2, hw3]
    apply Int.ofNat_inj.mp
    push_cast
    rw [Int.toNat_of_nonneg hκ₂_pos, Int.toNat_of_nonneg hκ₃_pos]
    dsimp [κ₂_z, κ₃_z, R_count]
    ring
  -- Part 2: `∑ j, witnessSize n j * witnessCounts n j = n`
  have hsum_verts : ∑ j : Fin 4, witnessSize n j * witnessCounts n j = n := by
    rw [Fin.sum_univ_four, hw0, hw1, hw2, hw3]
    apply Int.ofNat_inj.mp
    push_cast
    rw [Int.toNat_of_nonneg hκ₂_pos, Int.toNat_of_nonneg hκ₃_pos]
    have hs0 : ((witnessSize n 0 : ℕ) : ℤ) = (α : ℤ) - 2 := by
      unfold witnessSize; change ((α - 2 : ℕ) : ℤ) = (α : ℤ) - 2; omega
    have hs1 : ((witnessSize n 1 : ℕ) : ℤ) = (α : ℤ) - 3 := by
      unfold witnessSize; change ((α - 3 : ℕ) : ℤ) = (α : ℤ) - 3; omega
    have hs2 : ((witnessSize n 2 : ℕ) : ℤ) = (α : ℤ) - 4 := by
      unfold witnessSize; change ((α - 4 : ℕ) : ℤ) = (α : ℤ) - 4; omega
    have hs3 : ((witnessSize n 3 : ℕ) : ℤ) = (α : ℤ) - 5 := by
      unfold witnessSize; change ((α - 5 : ℕ) : ℤ) = (α : ℤ) - 5; omega
    rw [hs0, hs1, hs2, hs3]
    dsimp [κ₂_z, κ₃_z, R_count, R_def, D]
    ring
  -- Part 3: Size ≥ 10 and linear counts
  have hsize_ge10 : ∀ j : Fin 4, 10 ≤ witnessSize n j := by
    intro j
    unfold witnessSize
    have hj := j.isLt
    omega
  let pFin : Fin 4 → ℝ := fun j => p ((j.val : ℤ) + 2)
  have hcount_err : ∀ j : Fin 4, |(witnessCounts n j : ℝ) - (K : ℝ) * pFin j| ≤ 5 := by
    intro j
    fin_cases j
    · change |(witnessCounts n 0 : ℝ) - (K : ℝ) * p 2| ≤ 5
      rw [hw0]
      have hcast : ((κ₂_z.toNat : ℕ) : ℝ) = (κ₂_z : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hκ₂_pos
      rw [hcast, hκ₂_real, abs_le]
      exact ⟨by linarith only [hf₄_bounds.2, hf₅_bounds.2],
        by linarith only [hf₄_bounds.1, hf₅_bounds.1]⟩
    · change |(witnessCounts n 1 : ℝ) - (K : ℝ) * p 3| ≤ 5
      rw [hw1]
      have hcast : ((κ₃_z.toNat : ℕ) : ℝ) = (κ₃_z : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hκ₃_pos
      rw [hcast, hκ₃_real, abs_le]
      exact ⟨by linarith only [hf₄_bounds.1, hf₅_bounds.1],
        by linarith only [hf₄_bounds.2, hf₅_bounds.2]⟩
    · change |(witnessCounts n 2 : ℝ) - (K : ℝ) * p 4| ≤ 5
      rw [hw2, abs_le]
      have hf4' : (K : ℝ) * p 4 - (κ₄ : ℝ) = f₄ := rfl
      exact ⟨by linarith only [hf4', hf₄_bounds.2], by linarith only [hf4', hf₄_bounds.1]⟩
    · change |(witnessCounts n 3 : ℝ) - (K : ℝ) * p 5| ≤ 5
      rw [hw3, abs_le]
      have hf5' : (K : ℝ) * p 5 - (κ₅ : ℝ) = f₅ := rfl
      exact ⟨by linarith only [hf5', hf₅_bounds.2], by linarith only [hf5', hf₅_bounds.1]⟩
  have hpFin_lb : ∀ j : Fin 4, 1 / c35 ≤ pFin j := by
    intro j
    fin_cases j
    · exact hp2_lb
    · exact hp3_lb
    · exact hp4_lb
    · exact hp5_lb
  have hpFin_le1 : ∀ j : Fin 4, pFin j ≤ 1 := by
    intro j
    have h2 : 0 ≤ p 2 := le_trans (by positivity) hp2_lb
    have h3 : 0 ≤ p 3 := le_trans (by positivity) hp3_lb
    fin_cases j
    · change p 2 ≤ 1; linarith only [hp_sum4, h2, h3, hp4_nonneg, hp5_nonneg]
    · change p 3 ≤ 1; linarith only [hp_sum4, h2, h3, hp4_nonneg, hp5_nonneg]
    · change p 4 ≤ 1; linarith only [hp_sum4, h2, h3, hp4_nonneg, hp5_nonneg]
    · change p 5 ≤ 1; linarith only [hp_sum4, h2, h3, hp4_nonneg, hp5_nonneg]
  have hcounts_linear : ∀ j : Fin 4,
      1 ≤ witnessCounts n j ∧ (K : ℝ) / (2 * c35) ≤ (witnessCounts n j : ℝ) := by
    intro j
    have herr := (abs_le.mp (hcount_err j)).1
    have hkp := hKp_ge20 (hpFin_lb j)
    have hge_real : (K : ℝ) / (2 * c35) ≤ (witnessCounts n j : ℝ) := by
      linarith only [herr, hkp.2]
    have hge_1 : (1 : ℝ) ≤ (witnessCounts n j : ℝ) := by
      linarith only [herr, hkp.1]
    exact ⟨by exact_mod_cast hge_1, hge_real⟩
  -- Part 4: Supercritical log-first-moment `≥ 100 * n / L^2`
  refine ⟨hsum_counts, hsum_verts, hsize_ge10, hcounts_linear, ?_⟩
  set s_K : ℝ := (n : ℝ) / (K : ℝ)
  have hs_K_pos : 0 < s_K := by positivity
  -- 4a: Lower bound on `log(n!) - ∑_j log(κ_j!)` using Stirling
  have hlog_nfac : (n : ℝ) * L - (n : ℝ) ≤ Real.log (n ! : ℝ) := by
    have hst := (log_factorial_bounds (by omega : 1 ≤ n)).1
    have hln0 : 0 ≤ L / 2 := by positivity
    change (n : ℝ) * L - (n : ℝ) + L / 2 ≤ Real.log (n ! : ℝ) at hst
    linarith only [hst, hln0]
  have hlog_κfac : ∀ j : Fin 4,
      Real.log ((witnessCounts n j) ! : ℝ) ≤
        (witnessCounts n j : ℝ) * Real.log (K : ℝ) +
          (witnessCounts n j : ℝ) * Real.log (pFin j) -
          (witnessCounts n j : ℝ) + L + 20 := by
    intro j
    set κ_j : ℕ := witnessCounts n j
    have hκ1 : 1 ≤ κ_j := (hcounts_linear j).1
    have hκ_pos : 0 < (κ_j : ℝ) := by exact_mod_cast hκ1
    have hst := (log_factorial_bounds hκ1).2
    have hκ_le_K : (κ_j : ℝ) ≤ (K : ℝ) := by
      have : κ_j ≤ K := by
        rw [← hsum_counts]
        exact Finset.single_le_sum (f := witnessCounts n) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j)
      exact_mod_cast this
    have hlogκ_le_L : Real.log (κ_j : ℝ) / 2 ≤ L := by
      have hK_le_n : (K : ℝ) ≤ (n : ℝ) :=
        hK_hi_real.trans (div_le_self hn_pos.le (by linarith only [hL100000]))
      have h1 : Real.log (κ_j : ℝ) ≤ L := Real.log_le_log hκ_pos (hκ_le_K.trans hK_le_n)
      have h0 : 0 ≤ Real.log (κ_j : ℝ) := Real.log_nonneg (by exact_mod_cast hκ1)
      linarith only [h1, h0]
    -- Bound `(κ_j : ℝ) * Real.log ((κ_j : ℝ) / ((K : ℝ) * pFin j)) ≤ 10`
    have hpj_pos : 0 < pFin j := lt_of_lt_of_le (by positivity) (hpFin_lb j)
    have hKpj_pos : 0 < (K : ℝ) * pFin j := mul_pos hK_pos hpj_pos
    have hkl : (κ_j : ℝ) * Real.log (κ_j : ℝ) ≤
        (κ_j : ℝ) * Real.log (K : ℝ) + (κ_j : ℝ) * Real.log (pFin j) + 10 := by
      have hlog_rat : Real.log ((κ_j : ℝ) / ((K : ℝ) * pFin j)) ≤
          ((κ_j : ℝ) - (K : ℝ) * pFin j) / ((K : ℝ) * pFin j) := by
        have h1 := Real.log_le_sub_one_of_pos (div_pos hκ_pos hKpj_pos)
        have h2 : (κ_j : ℝ) / ((K : ℝ) * pFin j) - 1 =
            ((κ_j : ℝ) - (K : ℝ) * pFin j) / ((K : ℝ) * pFin j) := by
          field_simp [hKpj_pos.ne']
        linarith only [h1, h2]
      have hmul_rat := mul_le_mul_of_nonneg_left hlog_rat hκ_pos.le
      rw [Real.log_div hκ_pos.ne' hKpj_pos.ne', Real.log_mul hK_pos.ne' hpj_pos.ne'] at hmul_rat
      have hdist : (κ_j : ℝ) * (Real.log (κ_j : ℝ) - (Real.log (K : ℝ) + Real.log (pFin j))) =
          (κ_j : ℝ) * Real.log (κ_j : ℝ) - (κ_j : ℝ) * Real.log (K : ℝ) -
            (κ_j : ℝ) * Real.log (pFin j) := by ring
      have herr_j := (abs_le.mp (hcount_err j)).2
      have hκ_le_2Kp : (κ_j : ℝ) ≤ 2 * ((K : ℝ) * pFin j) := by
        have h20 := (hKp_ge20 (hpFin_lb j)).1
        linarith only [herr_j, h20]
      have hprod_le10 : (κ_j : ℝ) * (((κ_j : ℝ) - (K : ℝ) * pFin j) / ((K : ℝ) * pFin j)) ≤ 10 := by
        by_cases hsign : 0 ≤ (κ_j : ℝ) - (K : ℝ) * pFin j
        · calc
            (κ_j : ℝ) * (((κ_j : ℝ) - (K : ℝ) * pFin j) / ((K : ℝ) * pFin j))
                ≤ (2 * ((K : ℝ) * pFin j)) * (5 / ((K : ℝ) * pFin j)) :=
              mul_le_mul hκ_le_2Kp (div_le_div_of_nonneg_right herr_j hKpj_pos.le)
                (div_nonneg hsign hKpj_pos.le) (by positivity)
            _ = 10 := by field_simp [hKpj_pos.ne']; ring
        · push Not at hsign
          have hneg : (κ_j : ℝ) * (((κ_j : ℝ) - (K : ℝ) * pFin j) / ((K : ℝ) * pFin j)) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hκ_pos.le (div_nonpos_of_nonpos_of_nonneg hsign.le hKpj_pos.le)
          linarith only [hneg]
      linarith only [hmul_rat, hdist, hprod_le10]
    linarith only [hst, hlogκ_le_L, hkl]
  have hsum_κ_real : ∑ j : Fin 4, (witnessCounts n j : ℝ) = (K : ℝ) := by
    exact_mod_cast hsum_counts
  have hlog_K_eq : Real.log (K : ℝ) = L - Real.log s_K := by
    have heq : (K : ℝ) = (n : ℝ) / s_K := by
      dsimp [s_K]
      field_simp [hK_pos.ne']
    rw [heq, Real.log_div hn_pos.ne' hs_K_pos.ne']
  -- 4b: Falling-factorial shift summed over `j : Fin 4`
  have hfall_each : ∀ j : Fin 4,
      -Real.log (α ! : ℝ) - q * (α.choose 2 : ℝ) +
        ((j.val + 2 : ℕ) : ℝ) * (q * (α : ℝ) - q / 2 + Real.log (α : ℝ)) -
        (q / 2) * ((j.val + 2 : ℕ) : ℝ) ^ 2 - 50 / (α : ℝ) ≤
      -(Real.log ((witnessSize n j) ! : ℝ) + q * ((witnessSize n j).choose 2 : ℝ)) := by
    intro j
    have hj5 : j.val + 2 ≤ 5 := by have := j.isLt; omega
    have hf := falling_shift_lower_bounded (by omega : 10 ≤ α) hj5
    change -Real.log (α ! : ℝ) - q * (α.choose 2 : ℝ) +
        ((j.val + 2 : ℕ) : ℝ) * (q * (α : ℝ) - q / 2 + Real.log (α : ℝ)) -
        (q / 2) * ((j.val + 2 : ℕ) : ℝ) ^ 2 - 50 / (α : ℝ) ≤
      -Real.log ((witnessSize n j) ! : ℝ) - q * ((witnessSize n j).choose 2 : ℝ) at hf
    linarith only [hf]
  have hsum_deficits :
      ∑ j : Fin 4, (witnessCounts n j : ℝ) * ((j.val + 2 : ℕ) : ℝ) = (K : ℝ) * ((α : ℝ) - s_K) := by
    have hverts_real : ∑ j : Fin 4, ((witnessSize n j : ℝ) * (witnessCounts n j : ℝ)) = (n : ℝ) := by
      exact_mod_cast hsum_verts
    have hsize_cast : ∀ j : Fin 4, (witnessSize n j : ℝ) = (α : ℝ) - ((j.val + 2 : ℕ) : ℝ) := by
      intro j
      unfold witnessSize
      exact Nat.cast_sub (by have := j.isLt; omega)
    have hid : ∑ j : Fin 4, (witnessCounts n j : ℝ) * ((j.val + 2 : ℕ) : ℝ) =
        (α : ℝ) * (∑ j : Fin 4, (witnessCounts n j : ℝ)) -
          ∑ j : Fin 4, ((witnessSize n j : ℝ) * (witnessCounts n j : ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hsize_cast j]
      ring
    rw [hid, hsum_κ_real, hverts_real]
    dsimp [s_K]
    field_simp [hK_pos.ne']
  -- 4c: Compare `- ∑ κ_j * (log p_j + (q/2) i_j^2)` with `(K : ℝ) * freeEnergyFour T_K`
  have hent_fin4 :
      ∑ j : Fin 4, (K : ℝ) * pFin j * (-(q / 2) * ((j.val + 2 : ℕ) : ℝ) ^ 2 - Real.log (pFin j)) =
        (K : ℝ) * freeEnergyFour T_K := by
    rw [← hp_ent, Finset.mul_sum, h4set, Fin.sum_univ_four]
    simp only [sum_insert (by decide : (2 : ℤ) ∉ insert 3 (insert 4 ({5} : Finset ℤ))),
      sum_insert (by decide : (3 : ℤ) ∉ insert 4 ({5} : Finset ℤ)),
      sum_insert (by decide : (4 : ℤ) ∉ ({5} : Finset ℤ)), sum_singleton]
    change (K : ℝ) * p 2 * (-(q / 2) * ((2 : ℕ) : ℝ) ^ 2 - Real.log (p 2)) +
      (K : ℝ) * p 3 * (-(q / 2) * ((3 : ℕ) : ℝ) ^ 2 - Real.log (p 3)) +
      (K : ℝ) * p 4 * (-(q / 2) * ((4 : ℕ) : ℝ) ^ 2 - Real.log (p 4)) +
      (K : ℝ) * p 5 * (-(q / 2) * ((5 : ℕ) : ℝ) ^ 2 - Real.log (p 5)) =
      (K : ℝ) * (p 2 * (-(q / 2) * ((2 : ℤ) : ℝ) ^ 2 - Real.log (p 2))) +
      ((K : ℝ) * (p 3 * (-(q / 2) * ((3 : ℤ) : ℝ) ^ 2 - Real.log (p 3))) +
      ((K : ℝ) * (p 4 * (-(q / 2) * ((4 : ℤ) : ℝ) ^ 2 - Real.log (p 4))) +
      (K : ℝ) * (p 5 * (-(q / 2) * ((5 : ℤ) : ℝ) ^ 2 - Real.log (p 5)))))
    norm_num
    ring
  have hent_round : ∀ j : Fin 4,
      (K : ℝ) * pFin j * (-(q / 2) * ((j.val + 2 : ℕ) : ℝ) ^ 2 - Real.log (pFin j)) - 600 ≤
        (witnessCounts n j : ℝ) * (-(q / 2) * ((j.val + 2 : ℕ) : ℝ) ^ 2 - Real.log (pFin j)) := by
    intro j
    have hlogp_abs : |Real.log (pFin j)| ≤ 100 := by
      have hpj_pos : 0 < pFin j := lt_of_lt_of_le (by positivity) (hpFin_lb j)
      have hnonpos : Real.log (pFin j) ≤ 0 := Real.log_nonpos hpj_pos.le (hpFin_le1 j)
      rw [abs_of_nonpos hnonpos]
      have hinv : Real.exp (-100) ≤ pFin j := by
        refine le_trans ?_ (hpFin_lb j)
        rw [Real.exp_neg, one_div]
        exact inv_anti₀ hc35_pos hc35_exp
      have hlog_ge := Real.log_le_log (Real.exp_pos _) hinv
      rw [Real.log_exp] at hlog_ge
      linarith only [hlog_ge]
    have hterm_abs : |-(q / 2) * ((j.val + 2 : ℕ) : ℝ) ^ 2 - Real.log (pFin j)| ≤ 120 := by
      have hq_lt1 : q < 1 := by dsimp [q]; linarith [Real.log_two_lt_d9]
      have hq_pos : 0 < q := Real.log_pos (by norm_num)
      have hj5 : ((j.val + 2 : ℕ) : ℝ) ≤ 5 := by
        exact_mod_cast (show j.val + 2 ≤ 5 by have := j.isLt; omega)
      have hsq25 : ((j.val + 2 : ℕ) : ℝ) ^ 2 ≤ 25 := by
        calc
          ((j.val + 2 : ℕ) : ℝ) ^ 2 ≤ 5 ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hj5 2
          _ = 25 := by norm_num
      have hqsq : |-(q / 2) * ((j.val + 2 : ℕ) : ℝ) ^ 2| ≤ 20 := by
        rw [abs_mul, abs_neg, abs_of_pos (by positivity), abs_of_nonneg (sq_nonneg _)]
        have h1 : (q / 2) * ((j.val + 2 : ℕ) : ℝ) ^ 2 ≤ (1 / 2 : ℝ) * 25 :=
          mul_le_mul (by linarith only [hq_lt1]) hsq25 (sq_nonneg _) (by positivity)
        linarith only [h1]
      have htri := abs_sub (-(q / 2) * ((j.val + 2 : ℕ) : ℝ) ^ 2) (Real.log (pFin j))
      linarith only [htri, hqsq, hlogp_abs]
    have hprod_err :
        |((witnessCounts n j : ℝ) - (K : ℝ) * pFin j) *
          (-(q / 2) * ((j.val + 2 : ℕ) : ℝ) ^ 2 - Real.log (pFin j))| ≤ 600 := by
      rw [abs_mul]
      calc
        |(witnessCounts n j : ℝ) - (K : ℝ) * pFin j| *
            |-(q / 2) * ((j.val + 2 : ℕ) : ℝ) ^ 2 - Real.log (pFin j)|
            ≤ 5 * 120 := mul_le_mul (hcount_err j) hterm_abs (abs_nonneg _) (by norm_num)
        _ = 600 := by norm_num
    have hl := (abs_le.mp hprod_err).1
    rw [sub_mul] at hl
    linarith only [hl]
  -- 4d: Assemble full log-first-moment lower bound in terms of `profileBasePhi` + `freeEnergyFour`
  have hlog_total_lb :
      (K : ℝ) * (profileBasePhi n s_K + q + freeEnergyFour T_K) -
        (K : ℝ) * (50 / (α : ℝ)) - 4 * L - 2500 ≤
      Real.log (n ! : ℝ) + (K : ℝ) * q -
        ∑ j : Fin 4, Real.log ((witnessCounts n j) ! : ℝ) -
        ∑ j : Fin 4, (witnessCounts n j : ℝ) *
          (Real.log ((witnessSize n j) ! : ℝ) + q * ((witnessSize n j).choose 2 : ℝ)) := by
    have hsum_κfac := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hlog_κfac j
    have hsum_fall :
        ∑ j : Fin 4, (witnessCounts n j : ℝ) *
          (-Real.log (α ! : ℝ) - q * (α.choose 2 : ℝ) +
            ((j.val + 2 : ℕ) : ℝ) * (q * (α : ℝ) - q / 2 + Real.log (α : ℝ)) -
            (q / 2) * ((j.val + 2 : ℕ) : ℝ) ^ 2 - 50 / (α : ℝ)) ≤
        -∑ j : Fin 4, (witnessCounts n j : ℝ) *
          (Real.log ((witnessSize n j) ! : ℝ) + q * ((witnessSize n j).choose 2 : ℝ)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      have hm := mul_le_mul_of_nonneg_left (hfall_each j) (Nat.cast_nonneg (witnessCounts n j))
      have hneg_r : (witnessCounts n j : ℝ) *
          (-(Real.log ((witnessSize n j) ! : ℝ) + q * ((witnessSize n j).choose 2 : ℝ))) =
        -((witnessCounts n j : ℝ) *
          (Real.log ((witnessSize n j) ! : ℝ) + q * ((witnessSize n j).choose 2 : ℝ))) := by ring
      linarith only [hm, hneg_r]
    have hsum_ent_round := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hent_round j
    -- Expand the sums using `hsum_κ_real`, `hsum_deficits`, `hlog_K_eq`, and `hent_fin4`
    have hexp_κfac :
        ∑ j : Fin 4, ((witnessCounts n j : ℝ) * Real.log (K : ℝ) +
          (witnessCounts n j : ℝ) * Real.log (pFin j) -
          (witnessCounts n j : ℝ) + L + 20) =
        (K : ℝ) * (L - Real.log s_K - 1) +
          (∑ j : Fin 4, (witnessCounts n j : ℝ) * Real.log (pFin j)) + 4 * L + 80 := by
      simp_rw [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hsum_κ_real, hlog_K_eq]
      ring
    have hexp_fall :
        ∑ j : Fin 4, (witnessCounts n j : ℝ) *
          (-Real.log (α ! : ℝ) - q * (α.choose 2 : ℝ) +
            ((j.val + 2 : ℕ) : ℝ) * (q * (α : ℝ) - q / 2 + Real.log (α : ℝ)) -
            (q / 2) * ((j.val + 2 : ℕ) : ℝ) ^ 2 - 50 / (α : ℝ)) =
        (K : ℝ) * (-Real.log (α ! : ℝ) - q * (α.choose 2 : ℝ)) +
          ((K : ℝ) * ((α : ℝ) - s_K)) * (q * (α : ℝ) - q / 2 + Real.log (α : ℝ)) -
          (∑ j : Fin 4, (witnessCounts n j : ℝ) * ((q / 2) * ((j.val + 2 : ℕ) : ℝ) ^ 2)) -
          (K : ℝ) * (50 / (α : ℝ)) := by
      have hlin : ∀ j : Fin 4,
          (witnessCounts n j : ℝ) *
            (-Real.log (α ! : ℝ) - q * (α.choose 2 : ℝ) +
              ((j.val + 2 : ℕ) : ℝ) * (q * (α : ℝ) - q / 2 + Real.log (α : ℝ)) -
              (q / 2) * ((j.val + 2 : ℕ) : ℝ) ^ 2 - 50 / (α : ℝ)) =
          (witnessCounts n j : ℝ) * (-Real.log (α ! : ℝ) - q * (α.choose 2 : ℝ)) +
          ((witnessCounts n j : ℝ) * ((j.val + 2 : ℕ) : ℝ)) *
            (q * (α : ℝ) - q / 2 + Real.log (α : ℝ)) -
          (witnessCounts n j : ℝ) * ((q / 2) * ((j.val + 2 : ℕ) : ℝ) ^ 2) -
          (witnessCounts n j : ℝ) * (50 / (α : ℝ)) := fun _ => by ring
      simp_rw [hlin, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
      rw [hsum_κ_real, hsum_deficits]
    have hexp_ent :
        ∑ j : Fin 4, ((K : ℝ) * pFin j * (-(q / 2) * ((j.val + 2 : ℕ) : ℝ) ^ 2 - Real.log (pFin j)) - 600) =
        (K : ℝ) * freeEnergyFour T_K - 2400 := by
      rw [Finset.sum_sub_distrib, hent_fin4, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      norm_num
    have hexp_ent_rhs :
        ∑ j : Fin 4, (witnessCounts n j : ℝ) * (-(q / 2) * ((j.val + 2 : ℕ) : ℝ) ^ 2 - Real.log (pFin j)) =
        -(∑ j : Fin 4, (witnessCounts n j : ℝ) * ((q / 2) * ((j.val + 2 : ℕ) : ℝ) ^ 2)) -
          (∑ j : Fin 4, (witnessCounts n j : ℝ) * Real.log (pFin j)) := by
      have hlin : ∀ j : Fin 4,
          (witnessCounts n j : ℝ) * (-(q / 2) * ((j.val + 2 : ℕ) : ℝ) ^ 2 - Real.log (pFin j)) =
          -((witnessCounts n j : ℝ) * ((q / 2) * ((j.val + 2 : ℕ) : ℝ) ^ 2)) -
            (witnessCounts n j : ℝ) * Real.log (pFin j) := fun _ => by ring
      simp_rw [hlin, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    have hn_eq_Ks : (n : ℝ) = (K : ℝ) * s_K := by
      dsimp [s_K]; field_simp [hK_pos.ne']
    have hphi_expand :
        (K : ℝ) * (profileBasePhi n s_K + q + freeEnergyFour T_K) =
        ((n : ℝ) * L - (n : ℝ)) + (K : ℝ) * q - (K : ℝ) * (L - Real.log s_K - 1) +
          (K : ℝ) * (-Real.log (α ! : ℝ) - q * (α.choose 2 : ℝ)) +
          ((K : ℝ) * ((α : ℝ) - s_K)) * (q * (α : ℝ) - q / 2 + Real.log (α : ℝ)) +
          (K : ℝ) * freeEnergyFour T_K := by
      have hbase : profileBasePhi n s_K =
          (s_K * L - s_K - L + Real.log s_K + 1) -
            Real.log (α ! : ℝ) - q * (α.choose 2 : ℝ) +
            ((α : ℝ) - s_K) * (q * (α : ℝ) - q / 2 + Real.log (α : ℝ)) := rfl
      rw [hbase, hn_eq_Ks]
      ring
    rw [hexp_κfac] at hsum_κfac
    rw [hexp_fall] at hsum_fall
    rw [hexp_ent, hexp_ent_rhs] at hsum_ent_round
    linarith only [hlog_nfac, hsum_κfac, hsum_fall, hsum_ent_round, hphi_expand]
  -- 4e: Lower bound `(K : ℝ) * (profileBasePhi n s_K + q + freeEnergyFour T_K) ≥ 300 * n / L^2`
  have hTF_mem := TFour_mem_Icc n
  have hdiff_phi := abs_profileBasePhi_diff_approx hn16 hα20 hqα hhi hTK_mem hTF_mem
  have hs_K_eq : (α : ℝ) - T_K = s_K := by dsimp [T_K, seedDeficit, s_K, α, K]; ring
  have hlip_fe := abs_freeEnergyFour_sub_le hTK_mem hTF_mem
  have hTK_gt_TF : 0 < T_K - TFour n := by
    have hpos2000 : 0 < 2000 / L ^ 2 := by positivity
    linarith only [hTK_sub_TF_lo, hpos2000]
  have habs_diff : |T_K - TFour n| = T_K - TFour n := abs_of_pos hTK_gt_TF
  have hll_pos : 0 ≤ Real.log L := Real.log_nonneg (by linarith only [hL100000])
  have hslope_small : 3 * |Real.log L| + 2 * |alphaConst| + 16 ≤ (1 / 2 : ℝ) * L := by
    rw [abs_of_nonneg hll_pos]
    have hll_le : Real.log L ≤ (1 / 20 : ℝ) * L := by
      have h1 := (div_le_iff₀ hL_pos).mp hrat20
      linarith only [h1]
    linarith only [hll_le, hLbig', abs_nonneg alphaConst]
  have hsum_pos_gain : 1000 / L ≤ profileBasePhi n s_K + q + freeEnergyFour T_K := by
    have hsub : profileBasePhi n s_K + q + freeEnergyFour T_K =
        (profileBasePhi n ((α : ℝ) - T_K) - profileBasePhi n ((α : ℝ) - TFour n)) +
        (freeEnergyFour T_K - freeEnergyFour (TFour n)) := by
      rw [hs_K_eq]
      have hrf : profileBasePhi n ((α : ℝ) - TFour n) + q + freeEnergyFour (TFour n) = 0 :=
        hroot_four
      linarith only [hrf]
    rw [hsub]
    have hp1 := (abs_le.mp hdiff_phi).1
    change -(|T_K - TFour n| * (3 * |Real.log L| + 2 * |alphaConst| + 6)) ≤
      (profileBasePhi n ((α : ℝ) - T_K) - profileBasePhi n ((α : ℝ) - TFour n)) -
        (T_K - TFour n) * L at hp1
    have hp2 := (abs_le.mp hlip_fe).1
    rw [habs_diff] at hp1 hp2
    have hexp_c : (T_K - TFour n) * (L - (3 * |Real.log L| + 2 * |alphaConst| + 16)) =
        (T_K - TFour n) * L - (T_K - TFour n) * (3 * |Real.log L| + 2 * |alphaConst| + 6) -
          10 * (T_K - TFour n) := by ring
    have hcomb : (T_K - TFour n) * (L - (3 * |Real.log L| + 2 * |alphaConst| + 16)) ≤
        (profileBasePhi n ((α : ℝ) - T_K) - profileBasePhi n ((α : ℝ) - TFour n)) +
          (freeEnergyFour T_K - freeEnergyFour (TFour n)) := by
      linarith only [hp1, hp2, hexp_c]
    have hhalf : (T_K - TFour n) * ((1 / 2 : ℝ) * L) ≤
        (T_K - TFour n) * (L - (3 * |Real.log L| + 2 * |alphaConst| + 16)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hslope_small]) hTK_gt_TF.le
    have h1000 : 1000 / L ≤ (T_K - TFour n) * ((1 / 2 : ℝ) * L) := by
      calc
        1000 / L = (2000 / L ^ 2) * ((1 / 2 : ℝ) * L) := by field_simp [hL_pos.ne']; ring
        _ ≤ (T_K - TFour n) * ((1 / 2 : ℝ) * L) :=
          mul_le_mul_of_nonneg_right hTK_sub_TF_lo (by positivity)
    linarith only [hcomb, hhalf, h1000]
  have hgain_main : 300 * (n : ℝ) / L ^ 2 ≤
      (K : ℝ) * (profileBasePhi n s_K + q + freeEnergyFour T_K) := by
    calc
      300 * (n : ℝ) / L ^ 2 = 300 * ((n : ℝ) / L ^ 2) := by ring
      _ ≤ (1000 / 3 : ℝ) * ((n : ℝ) / L ^ 2) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = ((n : ℝ) / (3 * L)) * (1000 / L) := by field_simp [hL_pos.ne']
      _ ≤ (K : ℝ) * (profileBasePhi n s_K + q + freeEnergyFour T_K) :=
        mul_le_mul hK_lo_real hsum_pos_gain (by positivity) hK_pos.le
  -- 4f: Bound the losses `(K : ℝ) * (50 / α) ≤ 25 * n / L^2` and `4 * L + 2500 ≤ n / L^2`
  have hloss_fall : (K : ℝ) * (50 / (α : ℝ)) ≤ 25 * (n : ℝ) / L ^ 2 := by
    have hα_ge_2L : 2 * L ≤ (α : ℝ) := by
      have hq_lt : q ≤ 3 / 4 := by dsimp [q]; linarith [Real.log_two_lt_d9]
      have hα_pos : 0 < (α : ℝ) := by exact_mod_cast (by omega : 0 < α)
      have hm := mul_le_mul_of_nonneg_right hq_lt hα_pos.le
      have hlo' : (3 / 2 : ℝ) * L ≤ q * (α : ℝ) := hlo
      linarith only [hm, hlo']
    have hα_pos : 0 < (α : ℝ) := by linarith only [hα_ge_2L, hL_pos]
    have h50 : 50 / (α : ℝ) ≤ 25 / L := by
      rw [div_le_div_iff₀ hα_pos hL_pos]
      linarith only [hα_ge_2L]
    calc
      (K : ℝ) * (50 / (α : ℝ)) ≤ ((n : ℝ) / L) * (25 / L) :=
        mul_le_mul hK_hi_real h50 (by positivity) (by positivity)
      _ = 25 * (n : ℝ) / L ^ 2 := by field_simp [hL_pos.ne']
  have hloss_L : 4 * L + 2500 ≤ (n : ℝ) / L ^ 2 := by
    have hn_ge : 40 * L ^ 4 ≤ (n : ℝ) := (le_div_iff₀ (by positivity)).mp hnL4_ge40
    rw [le_div_iff₀ (by positivity)]
    have hL2 : 100000 * L ≤ L ^ 2 := by
      calc
        100000 * L ≤ L * L := mul_le_mul_of_nonneg_right hL100000 hL_pos.le
        _ = L ^ 2 := (sq L).symm
    have h1 : 4 * L + 2500 ≤ 40 * L ^ 2 := by linarith only [hL100000, hL2]
    have h2 : (4 * L + 2500) * L ^ 2 ≤ 40 * L ^ 4 := by
      calc
        (4 * L + 2500) * L ^ 2 ≤ (40 * L ^ 2) * L ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg L)
        _ = 40 * L ^ 4 := by ring
    linarith only [h2, hn_ge]
  have h300 : 300 * (n : ℝ) / L ^ 2 = 300 * ((n : ℝ) / L ^ 2) := by ring
  have h25 : 25 * (n : ℝ) / L ^ 2 = 25 * ((n : ℝ) / L ^ 2) := by ring
  have h100 : 100 * (n : ℝ) / L ^ 2 = 100 * ((n : ℝ) / L ^ 2) := by ring
  have hnL2_nonneg : 0 ≤ (n : ℝ) / L ^ 2 := by positivity
  change 100 * (n : ℝ) / L ^ 2 ≤
    Real.log (n ! : ℝ) + (K : ℝ) * q -
      ∑ j : Fin 4, Real.log ((witnessCounts n j) ! : ℝ) -
      ∑ j : Fin 4, (witnessCounts n j : ℝ) *
        (Real.log ((witnessSize n j) ! : ℝ) + q * ((witnessSize n j).choose 2 : ℝ))
  linarith only [hlog_total_lb, hgain_main, hloss_fall, hloss_L, h300, h25, h100, hnL2_nonneg]

end JSP000506
