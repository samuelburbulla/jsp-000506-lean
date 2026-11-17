import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import JSP000506.Overlap

/-!
# Section 7: Partial-Diagonal Weights `D_n(v)` and Uniform Subexponential Bound

This module formalizes Section 7 of Samuil Petkov's *A Full-Sequence Quantitative Gap Between the
Chromatic and Cochromatic Numbers of a Random Graph* (`arXiv:2608.30604`), establishing the
phase-uniform subcritical bound on the partial-diagonal weight sum
`∑_{v ∈ 𝒱_n} D_n(v) ≤ exp(η_pd(n) * n / (log n)^4)` with `η_pd(n) → 0`:

1. **Exact Local Cell Reward (`localCellReward`) and Partial-Diagonal Weight (`diagWeight`)**:
   Defines `localCellReward r = 2 ^ (r.choose 2 - 1)` (matching `g(r)` of `(6.5)` for all `r : ℕ`)
   and `diagWeight n v` on the 4-coordinate profile box `diagBox n` (`0 ≤ v_i ≤ witnessCounts n i`).
2. **Small-Support Range (`diagMass n v ≤ n / (log n)^6`)**:
   Direct closed-form upper bound `diagWeight n v ≤ (n : ℝ) ^ (3 * diagMass n v) ≤ exp(3 n / (log n)^5)`.
3. **Full-Corner Range (`1024 * (n - diagMass n v) ≤ n`)**:
   Exact complementary identity `diagWeight n v * 𝔼[unordSignedWitness n] = B_n(h)` (`(7.5)`),
   coupled with `B_n(h) ≤ 1` and supercriticality `𝔼[unordSignedWitness n] ≥ 1`.
4. **Central Range (`n / (log n)^6 < diagMass n v` and `n < 1024 * (n - diagMass n v)`)**:
   Uniform Stirling extraction `(7.14)`, elementary boundary-safe entropy inequality `(7.15a)`,
   4-size affine energy decomposition `(7.16)–(7.18)`, and uniform rate negativity
   `Φ_T(z) ≤ -Y / 30000` (`(7.23)`), yielding `diagWeight n v ≤ exp(44 * log n)`.
5. **Master Partial-Diagonal Sum Bound (`eventually_sum_diagWeight_le`)**:
   Combines all three ranges over `|diagBox n| ≤ (n + 1)^4`.
-/

open Filter SimpleGraph Finset
open scoped Topology BigOperators Nat

namespace JSP000506

/-! ### 1. Reusable Finite-Product Helpers, Local Cell Reward, and `diagWeight` -/

theorem prod_le_prod_nat {ι : Type*} (s : Finset ι) {f g : ι → ℕ}
    (h : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact Nat.mul_le_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem prod_le_prod_real {ι : Type*} (s : Finset ι) {f g : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have ha_mem := Finset.mem_insert_self a s
    refine mul_le_mul (h a ha_mem)
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => h i (Finset.mem_insert_of_mem hi)))
      (Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi))
      ((hf a ha_mem).trans (h a ha_mem))

theorem prod_le_one_real {ι : Type*} (s : Finset ι) {f : ι → ℝ}
    (hf0 : ∀ i ∈ s, 0 ≤ f i) (hf1 : ∀ i ∈ s, f i ≤ 1) :
    ∏ i ∈ s, f i ≤ 1 := by
  calc
    ∏ i ∈ s, f i ≤ ∏ _i ∈ s, (1 : ℝ) := prod_le_prod_real s hf0 hf1
    _ = 1 := Finset.prod_const_one

theorem prod_pow_eq_pow_sum_real {ι : Type*} (s : Finset ι) (a : ℝ) (f : ι → ℕ) :
    (∏ i ∈ s, a ^ f i) = a ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx, pow_add, ih]

/-- Local cell reward `g(r) = 2^{C(r, 2) - 1}` (`(6.5)` of `arXiv:2608.30604`).
In `ℕ`, `0.choose 2 - 1 = 1.choose 2 - 1 = 2.choose 2 - 1 = 0`, so `localCellReward r = 1` for
`r ≤ 2` and `2^{C(r, 2) - 1}` for `r ≥ 3`. -/
noncomputable def localCellReward (r : ℕ) : ℝ :=
  (2 : ℝ) ^ (r.choose 2 - 1)

theorem localCellReward_pos (r : ℕ) : 0 < localCellReward r := by
  unfold localCellReward
  positivity

theorem localCellReward_ge_one (r : ℕ) : 1 ≤ localCellReward r := by
  unfold localCellReward
  exact one_le_pow₀ (by norm_num)

theorem localCellReward_eq_one_of_le_two {r : ℕ} (hr : r ≤ 2) : localCellReward r = 1 := by
  unfold localCellReward
  have h0 : r.choose 2 - 1 = 0 := by
    rcases r with _ | _ | _ | r <;> simp at hr ⊢
  rw [h0, pow_zero]

theorem localCellReward_eq_div_two_of_two_le {r : ℕ} (hr : 2 ≤ r) :
    localCellReward r = (2 : ℝ) ^ (r.choose 2) / 2 := by
  unfold localCellReward
  have h1 : 1 ≤ r.choose 2 := by simpa using Nat.choose_le_choose 2 hr
  have hsub : r.choose 2 = (r.choose 2 - 1) + 1 := (Nat.sub_add_cancel h1).symm
  conv_rhs => rw [hsub, pow_succ]
  ring

theorem localCellReward_le_two_pow_choose (r : ℕ) :
    localCellReward r ≤ (2 : ℝ) ^ (r.choose 2) := by
  unfold localCellReward
  exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)

/-- Coordinate box `𝒱_n = {v : Fin 4 → ℕ | ∀ i, v i ≤ witnessCounts n i}`. -/
noncomputable def diagBox (n : ℕ) : Finset (Fin 4 → ℕ) :=
  Fintype.piFinset (fun i : Fin 4 => Finset.range (witnessCounts n i + 1))

theorem mem_diagBox_iff {n : ℕ} {v : Fin 4 → ℕ} :
    v ∈ diagBox n ↔ ∀ i : Fin 4, v i ≤ witnessCounts n i := by
  simp [diagBox]

/-- Total vertex support `m(v) = ∑_{i=0}^3 witnessSize n i * v i` of a partial-diagonal profile. -/
noncomputable def diagMass (n : ℕ) (v : Fin 4 → ℕ) : ℕ :=
  ∑ i : Fin 4, witnessSize n i * v i

theorem diagMass_le_of_mem_diagBox {n : ℕ}
    (hn : ∑ i : Fin 4, witnessSize n i * witnessCounts n i = n)
    {v : Fin 4 → ℕ} (hv : v ∈ diagBox n) :
    diagMass n v ≤ n := by
  calc
    diagMass n v = ∑ i : Fin 4, witnessSize n i * v i := rfl
    _ ≤ ∑ i : Fin 4, witnessSize n i * witnessCounts n i :=
      Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ ((mem_diagBox_iff.mp hv) i)
    _ = n := hn

theorem card_diagBox_le (n : ℕ)
    (hn : ∑ i : Fin 4, witnessSize n i * witnessCounts n i = n)
    (hsize : ∀ i : Fin 4, 10 ≤ witnessSize n i) :
    (diagBox n).card ≤ (n + 1) ^ 4 := by
  unfold diagBox
  rw [Fintype.card_piFinset]
  simp_rw [Finset.card_range]
  have hκ_le_n : ∀ i : Fin 4, witnessCounts n i ≤ n := by
    intro i
    have h1 : witnessCounts n i ≤ witnessSize n i * witnessCounts n i :=
      Nat.le_mul_of_pos_left _ (by have := hsize i; omega)
    have h2 : witnessSize n i * witnessCounts n i ≤ n := by
      calc
        witnessSize n i * witnessCounts n i
            ≤ ∑ j : Fin 4, witnessSize n j * witnessCounts n j :=
          Finset.single_le_sum (f := fun j => witnessSize n j * witnessCounts n j)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        _ = n := hn
    omega
  calc
    ∏ i : Fin 4, (witnessCounts n i + 1) ≤ ∏ _i : Fin 4, (n + 1) :=
      prod_le_prod_nat Finset.univ fun i _ => Nat.add_le_add_right (hκ_le_n i) 1
    _ = (n + 1) ^ 4 := by simp

/-- Partial-diagonal common-subprofile weight `D_n(v)` (`(7.3)` / `(8.15)` of `arXiv:2608.30604`). -/
noncomputable def diagWeight (n : ℕ) (v : Fin 4 → ℕ) : ℝ :=
  ((∏ i : Fin 4, ((witnessCounts n i).descFactorial (v i) : ℝ) ^ 2) /
      (∏ i : Fin 4, ((v i) ! : ℝ))) *
    ((∏ i : Fin 4, (((witnessSize n i) ! : ℝ) * localCellReward (witnessSize n i)) ^ (v i)) /
      (n.descFactorial (diagMass n v) : ℝ))

theorem diagWeight_nonneg (n : ℕ) (v : Fin 4 → ℕ) : 0 ≤ diagWeight n v := by
  unfold diagWeight
  refine mul_nonneg (div_nonneg ?_ ?_) (div_nonneg ?_ (Nat.cast_nonneg _))
  · exact Finset.prod_nonneg fun _ _ => sq_nonneg _
  · exact Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
  · exact Finset.prod_nonneg fun _ _ => pow_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (localCellReward_pos _).le) _

/-! ### 2. Elementary Factorial and Falling-Factorial Helpers -/

theorem descFactorial_mul_factorial_sub {a b : ℕ} (hb : b ≤ a) :
    a.descFactorial b * (a - b) ! = a ! := by
  have h := Nat.choose_mul_factorial_mul_factorial hb
  have hd := Nat.descFactorial_eq_factorial_mul_choose a b
  nlinarith

theorem descFactorial_pos_of_le {a b : ℕ} (hb : b ≤ a) : 0 < a.descFactorial b :=
  Nat.descFactorial_pos.mpr hb

theorem descFactorial_le_pow (a b : ℕ) : a.descFactorial b ≤ a ^ b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.descFactorial_succ, pow_succ']
    exact Nat.mul_le_mul (Nat.sub_le a b) ih

theorem nat_factorial_le_pow (m : ℕ) : m ! ≤ m ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.factorial_succ, pow_succ']
    refine Nat.mul_le_mul_left (m + 1) (ih.trans ?_)
    exact Nat.pow_le_pow_left (Nat.le_succ m) m

theorem diagWeight_pos_of_mem_diagBox {n : ℕ}
    (hn : ∑ i : Fin 4, witnessSize n i * witnessCounts n i = n)
    {v : Fin 4 → ℕ} (hv : v ∈ diagBox n) :
    0 < diagWeight n v := by
  unfold diagWeight
  have hv_le := mem_diagBox_iff.mp hv
  have hm_le := diagMass_le_of_mem_diagBox hn hv
  refine mul_pos (div_pos ?_ ?_) (div_pos ?_ ?_)
  · refine Finset.prod_pos fun i _ => sq_pos_of_pos ?_
    exact Nat.cast_pos.mpr (descFactorial_pos_of_le (hv_le i))
  · exact Finset.prod_pos fun i _ => Nat.cast_pos.mpr (Nat.factorial_pos _)
  · refine Finset.prod_pos fun i _ => pow_pos ?_ _
    exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (localCellReward_pos _)
  · exact Nat.cast_pos.mpr (descFactorial_pos_of_le hm_le)

/-! ### 3. Range 1: Small-Support Bound (`diagMass n v ≤ n / (log n)^6`) -/

/-- Closed-form bound `diagWeight n v ≤ (n : ℝ) ^ (3 * diagMass n v)` valid for all `v ∈ diagBox n`
whenever `log 2 * alphaNat n ≤ 2 * log n` and `witnessSize n i ≥ 10`. -/
theorem diagWeight_le_pow_three_diagMass {n : ℕ}
    (hn1 : 1 ≤ n)
    (hn : ∑ i : Fin 4, witnessSize n i * witnessCounts n i = n)
    (hsize : ∀ i : Fin 4, 10 ≤ witnessSize n i)
    (hκ_pos : ∀ i : Fin 4, 1 ≤ witnessCounts n i)
    (hα_hi : Real.log 2 * (alphaNat n : ℝ) ≤ 2 * Real.log (n : ℝ))
    {v : Fin 4 → ℕ} (hv : v ∈ diagBox n) :
    diagWeight n v ≤ (n : ℝ) ^ (3 * diagMass n v) := by
  unfold diagWeight
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hm_le : diagMass n v ≤ n := diagMass_le_of_mem_diagBox hn hv
  have hden1 : (1 : ℝ) ≤ ∏ i : Fin 4, ((v i) ! : ℝ) := by
    have hnat : 1 ≤ ∏ i : Fin 4, (v i) ! :=
      Finset.one_le_prod fun i _ => Nat.factorial_pos (v i)
    exact_mod_cast hnat
  have hden2 : (1 : ℝ) ≤ (n.descFactorial (diagMass n v) : ℝ) := by
    have hnat : 1 ≤ n.descFactorial (diagMass n v) := descFactorial_pos_of_le hm_le
    exact_mod_cast hnat
  have hκ_le_n : ∀ i : Fin 4, witnessCounts n i ≤ n := by
    intro i
    have h1 : witnessCounts n i ≤ witnessSize n i * witnessCounts n i :=
      Nat.le_mul_of_pos_left _ (by have := hsize i; omega)
    have h2 : witnessSize n i * witnessCounts n i ≤ n := by
      calc
        witnessSize n i * witnessCounts n i
            ≤ ∑ j : Fin 4, witnessSize n j * witnessCounts n j :=
          Finset.single_le_sum (f := fun j => witnessSize n j * witnessCounts n j)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        _ = n := hn
    omega
  have hu_le_n : ∀ i : Fin 4, witnessSize n i ≤ n := by
    intro i
    have h1 : witnessSize n i ≤ witnessSize n i * witnessCounts n i :=
      Nat.le_mul_of_pos_right _ (hκ_pos i)
    have h2 : witnessSize n i * witnessCounts n i ≤ n := by
      calc
        witnessSize n i * witnessCounts n i
            ≤ ∑ j : Fin 4, witnessSize n j * witnessCounts n j :=
          Finset.single_le_sum (f := fun j => witnessSize n j * witnessCounts n j)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        _ = n := hn
    omega
  have hnum1 : ∏ i : Fin 4, ((witnessCounts n i).descFactorial (v i) : ℝ) ^ 2 ≤
      (n : ℝ) ^ (diagMass n v) := by
    calc
      ∏ i : Fin 4, ((witnessCounts n i).descFactorial (v i) : ℝ) ^ 2
          ≤ ∏ i : Fin 4, ((n : ℝ) ^ (v i)) ^ 2 := by
            refine prod_le_prod_real Finset.univ (fun _ _ => sq_nonneg _) fun i _ => ?_
            have hd : ((witnessCounts n i).descFactorial (v i) : ℝ) ≤ (n : ℝ) ^ (v i) := by
              calc
                ((witnessCounts n i).descFactorial (v i) : ℝ)
                    ≤ ((witnessCounts n i : ℝ)) ^ (v i) := by
                      exact_mod_cast descFactorial_le_pow _ _
                _ ≤ (n : ℝ) ^ (v i) :=
                  pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hκ_le_n i) _
            exact pow_le_pow_left₀ (Nat.cast_nonneg _) hd 2
      _ = ∏ i : Fin 4, (n : ℝ) ^ (2 * v i) := by
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [← pow_mul, mul_comm]
      _ ≤ ∏ i : Fin 4, (n : ℝ) ^ (witnessSize n i * v i) := by
            refine prod_le_prod_real Finset.univ (fun _ _ => by positivity) fun i _ => ?_
            refine pow_le_pow_right₀ hn_ge1 (Nat.mul_le_mul_right (v i) ?_)
            have := hsize i; omega
      _ = (n : ℝ) ^ (diagMass n v) := prod_pow_eq_pow_sum_real Finset.univ (n : ℝ) _
  have hnum2 :
      ∏ i : Fin 4, (((witnessSize n i) ! : ℝ) * localCellReward (witnessSize n i)) ^ (v i) ≤
        (n : ℝ) ^ (2 * diagMass n v) := by
    have hcell : ∀ i : Fin 4,
        ((witnessSize n i) ! : ℝ) * localCellReward (witnessSize n i) ≤
          (n : ℝ) ^ (2 * witnessSize n i) := by
      intro i
      set u := witnessSize n i
      have hu_fac : (u ! : ℝ) ≤ (n : ℝ) ^ u := by
        calc
          (u ! : ℝ) ≤ (u : ℝ) ^ u := by exact_mod_cast nat_factorial_le_pow u
          _ ≤ (n : ℝ) ^ u :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hu_le_n i) u
      have hu_rew : localCellReward u ≤ (n : ℝ) ^ u := by
        have hu_le_α : u ≤ alphaNat n := Nat.sub_le _ _
        have hch : Real.log 2 * (u.choose 2 : ℝ) ≤ (u : ℝ) * Real.log (n : ℝ) := by
          rw [cast_choose_two u]
          have h1 : (u : ℝ) - 1 ≤ (alphaNat n : ℝ) := by
            have : (u : ℝ) ≤ (alphaNat n : ℝ) := by exact_mod_cast hu_le_α
            linarith
          have h2 : Real.log 2 * ((u : ℝ) - 1) / 2 ≤ Real.log (n : ℝ) := by
            have hq : 0 < Real.log 2 := Real.log_pos (by norm_num)
            have hm := mul_le_mul_of_nonneg_left h1 hq.le
            linarith [hm, hα_hi]
          calc
            Real.log 2 * ((u : ℝ) * ((u : ℝ) - 1) / 2)
                = (u : ℝ) * (Real.log 2 * ((u : ℝ) - 1) / 2) := by ring
            _ ≤ (u : ℝ) * Real.log (n : ℝ) :=
              mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg u)
        calc
          localCellReward u ≤ (2 : ℝ) ^ (u.choose 2) := localCellReward_le_two_pow_choose u
          _ = Real.exp ((u.choose 2 : ℝ) * Real.log 2) := by
            rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
          _ ≤ Real.exp ((u : ℝ) * Real.log (n : ℝ)) := by
            apply Real.exp_le_exp.mpr
            linarith [hch]
          _ = (n : ℝ) ^ u := by rw [Real.exp_nat_mul, Real.exp_log hn_pos]
      calc
        (u ! : ℝ) * localCellReward u ≤ (n : ℝ) ^ u * (n : ℝ) ^ u :=
          mul_le_mul hu_fac hu_rew (localCellReward_pos u).le (by positivity)
        _ = (n : ℝ) ^ (2 * u) := by rw [← pow_add, two_mul]
    calc
      ∏ i : Fin 4, (((witnessSize n i) ! : ℝ) * localCellReward (witnessSize n i)) ^ (v i)
          ≤ ∏ i : Fin 4, ((n : ℝ) ^ (2 * witnessSize n i)) ^ (v i) := by
            refine prod_le_prod_real Finset.univ
              (fun _ _ => pow_nonneg
                (mul_nonneg (Nat.cast_nonneg _) (localCellReward_pos _).le) _) fun i _ => ?_
            exact pow_le_pow_left₀
              (mul_nonneg (Nat.cast_nonneg _) (localCellReward_pos _).le) (hcell i) _
      _ = ∏ i : Fin 4, (n : ℝ) ^ (2 * (witnessSize n i * v i)) := by
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [← pow_mul, mul_assoc]
      _ = (n : ℝ) ^ (2 * diagMass n v) := by
            rw [prod_pow_eq_pow_sum_real, ← Finset.mul_sum]; rfl
  have h1 :
      (∏ i : Fin 4, ((witnessCounts n i).descFactorial (v i) : ℝ) ^ 2) /
          (∏ i : Fin 4, ((v i) ! : ℝ)) ≤ (n : ℝ) ^ (diagMass n v) := by
    calc
      (∏ i : Fin 4, ((witnessCounts n i).descFactorial (v i) : ℝ) ^ 2) /
          (∏ i : Fin 4, ((v i) ! : ℝ))
          ≤ ∏ i : Fin 4, ((witnessCounts n i).descFactorial (v i) : ℝ) ^ 2 :=
            div_le_self (Finset.prod_nonneg fun _ _ => sq_nonneg _) hden1
      _ ≤ (n : ℝ) ^ (diagMass n v) := hnum1
  have h2_nonneg :
      0 ≤ (∏ i : Fin 4, (((witnessSize n i) ! : ℝ) * localCellReward (witnessSize n i)) ^ (v i)) /
          (n.descFactorial (diagMass n v) : ℝ) :=
    div_nonneg
      (Finset.prod_nonneg fun _ _ => pow_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (localCellReward_pos _).le) _)
      (Nat.cast_nonneg _)
  have h2 :
      (∏ i : Fin 4, (((witnessSize n i) ! : ℝ) * localCellReward (witnessSize n i)) ^ (v i)) /
          (n.descFactorial (diagMass n v) : ℝ) ≤ (n : ℝ) ^ (2 * diagMass n v) := by
    calc
      (∏ i : Fin 4, (((witnessSize n i) ! : ℝ) * localCellReward (witnessSize n i)) ^ (v i)) /
          (n.descFactorial (diagMass n v) : ℝ)
          ≤ ∏ i : Fin 4, (((witnessSize n i) ! : ℝ) * localCellReward (witnessSize n i)) ^ (v i) :=
            div_le_self
              (Finset.prod_nonneg fun _ _ => pow_nonneg
                (mul_nonneg (Nat.cast_nonneg _) (localCellReward_pos _).le) _) hden2
      _ ≤ (n : ℝ) ^ (2 * diagMass n v) := hnum2
  calc
    ((∏ i : Fin 4, ((witnessCounts n i).descFactorial (v i) : ℝ) ^ 2) /
        (∏ i : Fin 4, ((v i) ! : ℝ))) *
      ((∏ i : Fin 4, (((witnessSize n i) ! : ℝ) * localCellReward (witnessSize n i)) ^ (v i)) /
        (n.descFactorial (diagMass n v) : ℝ))
        ≤ (n : ℝ) ^ (diagMass n v) * (n : ℝ) ^ (2 * diagMass n v) :=
      mul_le_mul h1 h2 h2_nonneg (by positivity)
    _ = (n : ℝ) ^ (3 * diagMass n v) := by
      rw [← pow_add]
      congr 1
      omega

/-! ### 4. Range 3: Full-Corner Bound (`1024 * (n - diagMass n v) ≤ n`) -/

/-- Exact complementary identity `(7.5)`:
`diagWeight n v * expectGnpHalf n (unordSignedWitness n)` equals the residual weight `B_n(κ - v)`. -/
theorem diagWeight_mul_expect_unord_eq {n : ℕ}
    (hK : ∑ i : Fin 4, witnessCounts n i = kCoSeed n)
    (hn : ∑ i : Fin 4, witnessSize n i * witnessCounts n i = n)
    (hsize : ∀ i : Fin 4, 10 ≤ witnessSize n i)
    {v : Fin 4 → ℕ} (hv : v ∈ diagBox n) :
    let h : Fin 4 → ℕ := fun i => witnessCounts n i - v i
    let w : ℕ := n - diagMass n v
    diagWeight n v * expectGnpHalf n (unordSignedWitness n) =
      (w ! : ℝ) *
        ∏ i : Fin 4,
          ((((witnessCounts n i).choose (h i) : ℝ) / ((h i) ! : ℝ)) *
            ((2 : ℝ) / (((witnessSize n i) ! : ℝ) * (2 : ℝ) ^ ((witnessSize n i).choose 2))) ^ (h i)) := by
  intro h w
  have hv_le := mem_diagBox_iff.mp hv
  have hm_le := diagMass_le_of_mem_diagBox hn hv
  unfold unordSignedWitness
  have hdiv : expectGnpHalf n (fun G => permSignedWitness n G / witnessSymmetryFactor n) =
      expectGnpHalf n (permSignedWitness n) / witnessSymmetryFactor n := by
    simp_rw [div_eq_mul_inv, mul_comm _ (witnessSymmetryFactor n)⁻¹]
    rw [expectGnpHalf_mul_const, mul_comm]
  rw [hdiv, expectGnpHalf_permSignedWitness]
  have huniv : (Finset.univ : Finset (Fin (kCoSeed n))) =
      Finset.univ.biUnion (fun j : Fin 4 =>
        Finset.univ.filter (fun r : Fin (kCoSeed n) => seedBlockType n r = j)) := by
    ext r; simp
  have hdisj : ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint
      (fun j : Fin 4 => Finset.univ.filter (fun r : Fin (kCoSeed n) => seedBlockType n r = j)) := by
    intro j₁ _ j₂ _ hne
    exact Finset.disjoint_left.mpr fun r hr₁ hr₂ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr₁ hr₂
      exact hne (hr₁.symm.trans hr₂)
  have hprod_cards : ∏ r : Fin (kCoSeed n), ((canonicalBlocks n r).card ! : ℝ) =
      ∏ i : Fin 4, (((witnessSize n i) ! : ℝ) ^ (witnessCounts n i)) := by
    simp_rw [card_canonicalBlocks_eq hK hn]
    unfold seedBlockSize
    conv_lhs => rw [huniv]
    rw [Finset.prod_biUnion hdisj]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hconst : ∀ r ∈ Finset.univ.filter (fun r : Fin (kCoSeed n) => seedBlockType n r = i),
        ((witnessSize n (seedBlockType n r)) ! : ℝ) = ((witnessSize n i) ! : ℝ) :=
      fun _ hr => by rw [(Finset.mem_filter.mp hr).2]
    rw [Finset.prod_congr rfl hconst, Finset.prod_const, card_seedBlockType_eq hK i]
  have hsum_choose : ∑ r : Fin (kCoSeed n), (canonicalBlocks n r).card.choose 2 =
      ∑ i : Fin 4, witnessCounts n i * (witnessSize n i).choose 2 := by
    simp_rw [card_canonicalBlocks_eq hK hn]
    unfold seedBlockSize
    conv_lhs => rw [huniv]
    rw [Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hconst : ∀ r ∈ Finset.univ.filter (fun r : Fin (kCoSeed n) => seedBlockType n r = i),
        (witnessSize n (seedBlockType n r)).choose 2 = (witnessSize n i).choose 2 :=
      fun _ hr => by rw [(Finset.mem_filter.mp hr).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, card_seedBlockType_eq hK i]
  unfold witnessSymmetryFactor diagWeight
  rw [hprod_cards, hsum_choose, ← hK]
  have hn_split : (n ! : ℝ) / (n.descFactorial (diagMass n v) : ℝ) = (w ! : ℝ) := by
    have hid : w ! * n.descFactorial (diagMass n v) = n ! := by
      rw [mul_comm]; exact descFactorial_mul_factorial_sub hm_le
    have hne : (n.descFactorial (diagMass n v) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (descFactorial_pos_of_le hm_le).ne'
    rw [div_eq_iff hne]
    exact_mod_cast hid.symm
  have h2K : (2 : ℝ) ^ (∑ i : Fin 4, witnessCounts n i) =
      ∏ i : Fin 4, (2 : ℝ) ^ (witnessCounts n i) :=
    (prod_pow_eq_pow_sum_real Finset.univ 2 _).symm
  have h2inv : (2⁻¹ : ℝ) ^ (∑ i : Fin 4, witnessCounts n i * (witnessSize n i).choose 2) =
      ∏ i : Fin 4, (1 / (2 : ℝ) ^ ((witnessSize n i).choose 2)) ^ (witnessCounts n i) := by
    rw [← prod_pow_eq_pow_sum_real]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_comm (witnessCounts n i), pow_mul, one_div, inv_pow]
  rw [h2K, h2inv]
  have hreassoc :
      ((∏ i : Fin 4, ((witnessCounts n i).descFactorial (v i) : ℝ) ^ 2) /
          (∏ i : Fin 4, ((v i) ! : ℝ))) *
        ((∏ i : Fin 4, (((witnessSize n i) ! : ℝ) * localCellReward (witnessSize n i)) ^ (v i)) /
          (n.descFactorial (diagMass n v) : ℝ)) *
        ((n ! : ℝ) * (∏ i : Fin 4, (2 : ℝ) ^ (witnessCounts n i)) *
          (∏ i : Fin 4, (1 / (2 : ℝ) ^ ((witnessSize n i).choose 2)) ^ (witnessCounts n i)) /
          ((∏ i : Fin 4, ((witnessCounts n i) ! : ℝ)) *
            (∏ i : Fin 4, (((witnessSize n i) ! : ℝ) ^ (witnessCounts n i))))) =
      ((n ! : ℝ) / (n.descFactorial (diagMass n v) : ℝ)) *
        ((∏ i : Fin 4, ((witnessCounts n i).descFactorial (v i) : ℝ) ^ 2) *
          (∏ i : Fin 4, (((witnessSize n i) ! : ℝ) * localCellReward (witnessSize n i)) ^ (v i)) *
          (∏ i : Fin 4, (2 : ℝ) ^ (witnessCounts n i)) *
          (∏ i : Fin 4, (1 / (2 : ℝ) ^ ((witnessSize n i).choose 2)) ^ (witnessCounts n i)) /
          ((∏ i : Fin 4, ((v i) ! : ℝ)) *
            (∏ i : Fin 4, ((witnessCounts n i) ! : ℝ)) *
            (∏ i : Fin 4, (((witnessSize n i) ! : ℝ) ^ (witnessCounts n i))))) := by
    ring
  rw [hreassoc, hn_split]
  congr 1
  simp_rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hvi : v i ≤ witnessCounts n i := hv_le i
  have hvh : v i + h i = witnessCounts n i := Nat.add_sub_of_le hvi
  have hdesc_id : ((witnessCounts n i).descFactorial (v i) : ℝ) * ((h i) ! : ℝ) =
      ((witnessCounts n i) ! : ℝ) := by
    exact_mod_cast descFactorial_mul_factorial_sub hvi
  have hchoose_id : ((witnessCounts n i).choose (h i) : ℝ) * ((v i) ! : ℝ) * ((h i) ! : ℝ) =
      ((witnessCounts n i) ! : ℝ) := by
    have hc := Nat.choose_mul_factorial_mul_factorial (Nat.sub_le (witnessCounts n i) (v i))
    have hsub2 : witnessCounts n i - h i = v i := by omega
    rw [hsub2] at hc
    have hc' : (witnessCounts n i).choose (h i) * (v i) ! * (h i) ! = (witnessCounts n i) ! := by
      linarith [hc]
    exact_mod_cast hc'
  have hrew : localCellReward (witnessSize n i) =
      (2 : ℝ) ^ ((witnessSize n i).choose 2) / 2 :=
    localCellReward_eq_div_two_of_two_le (by have := hsize i; omega)
  have hp1 : (2 : ℝ) ^ (witnessCounts n i) = (2 : ℝ) ^ (v i) * (2 : ℝ) ^ (h i) := by
    rw [← hvh, pow_add]
  have hp2 : (1 / (2 : ℝ) ^ ((witnessSize n i).choose 2)) ^ (witnessCounts n i) =
      (1 / (2 : ℝ) ^ ((witnessSize n i).choose 2)) ^ (v i) *
        (1 / (2 : ℝ) ^ ((witnessSize n i).choose 2)) ^ (h i) := by
    rw [← hvh, pow_add]
  have hp3 : (((witnessSize n i) ! : ℝ)) ^ (witnessCounts n i) =
      (((witnessSize n i) ! : ℝ)) ^ (v i) * (((witnessSize n i) ! : ℝ)) ^ (h i) := by
    rw [← hvh, pow_add]
  have hvfac_ne : ((v i) ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hhfac_ne : ((h i) ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hκfac_ne : ((witnessCounts n i) ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hufac_ne : (((witnessSize n i) ! : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2c_ne : ((2 : ℝ) ^ ((witnessSize n i).choose 2)) ≠ 0 := by positivity
  have hdesc_eq : ((witnessCounts n i).descFactorial (v i) : ℝ) =
      ((witnessCounts n i) ! : ℝ) / ((h i) ! : ℝ) :=
    (eq_div_iff hhfac_ne).mpr hdesc_id
  have hchoose_eq : ((witnessCounts n i).choose (h i) : ℝ) =
      ((witnessCounts n i) ! : ℝ) / (((v i) ! : ℝ) * ((h i) ! : ℝ)) := by
    rw [eq_div_iff (mul_ne_zero hvfac_ne hhfac_ne)]
    linarith [hchoose_id]
  rw [hdesc_eq, hchoose_eq, hrew, hp1, hp2, hp3]
  simp only [div_pow, mul_pow, one_pow]
  field_simp [hvfac_ne, hhfac_ne, hκfac_ne, hufac_ne, h2c_ne]

/-- Eventually on `diagBox n`, whenever `1024 * (n - diagMass n v) ≤ n`, `diagWeight n v ≤ 1`. -/
theorem eventually_diagWeight_le_one_of_full_corner :
    ∀ᶠ n : ℕ in atTop,
      ∀ v ∈ diagBox n, 1024 * (n - diagMass n v) ≤ n → diagWeight n v ≤ 1 := by
  have hL : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_alphaNat_regime, eventually_witnessCounts_spec,
    eventually_expectGnpHalf_unordSignedWitness_supercritical,
    hL.eventually_ge_atTop (100 + 4 * |alphaConst|)] with
      n ⟨_, _, _, hqα, hlo, _⟩ ⟨hK, hn, hsize, _, _⟩ hexp_unord hLbig
      v hv hcorner
  have hv_le := mem_diagBox_iff.mp hv
  have hexp_ge1 : 1 ≤ expectGnpHalf n (unordSignedWitness n) :=
    (Real.one_le_exp (by positivity)).trans hexp_unord
  suffices hB_le1 : diagWeight n v * expectGnpHalf n (unordSignedWitness n) ≤ 1 by
    nlinarith [diagWeight_nonneg n v, hexp_ge1, hB_le1]
  rw [diagWeight_mul_expect_unord_eq hK hn hsize hv]
  set w : ℕ := n - diagMass n v
  set h : Fin 4 → ℕ := fun i => witnessCounts n i - v i
  have hw_eq : w = ∑ i : Fin 4, witnessSize n i * h i := by
    have hadd : diagMass n v + ∑ i : Fin 4, witnessSize n i * h i = n := by
      unfold diagMass
      rw [← Finset.sum_add_distrib]
      calc
        ∑ i : Fin 4, (witnessSize n i * v i + witnessSize n i * h i)
            = ∑ i : Fin 4, witnessSize n i * witnessCounts n i := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [← Nat.mul_add, Nat.add_sub_of_le (hv_le i)]
        _ = n := hn
    omega
  rcases Nat.eq_zero_or_pos w with hw0 | hw_pos
  · have hh0 : ∀ i : Fin 4, h i = 0 := by
      intro i
      have hterm0 : witnessSize n i * h i = 0 := by
        have hle : witnessSize n i * h i ≤ w := by
          rw [hw_eq]
          exact Finset.single_le_sum (f := fun j => witnessSize n j * h j)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      rcases Nat.mul_eq_zero.mp hterm0 with hu0 | hi0
      · have := hsize i; omega
      · exact hi0
    have hprod1 :
        (∏ i : Fin 4,
          ((((witnessCounts n i).choose (h i) : ℝ) / ((h i) ! : ℝ)) *
            ((2 : ℝ) / (((witnessSize n i) ! : ℝ) * (2 : ℝ) ^ ((witnessSize n i).choose 2))) ^ (h i))) = 1 := by
      refine Finset.prod_eq_one fun i _ => ?_
      rw [hh0 i]
      simp
    rw [hw0, hprod1]
    norm_num
  · have hw_pow : (w ! : ℝ) ≤ ∏ i : Fin 4, ((w : ℝ) ^ (witnessSize n i)) ^ (h i) := by
      calc
        (w ! : ℝ) ≤ (w : ℝ) ^ w := by exact_mod_cast nat_factorial_le_pow w
        _ = (w : ℝ) ^ (∑ i : Fin 4, witnessSize n i * h i) := by rw [hw_eq]
        _ = ∏ i : Fin 4, (w : ℝ) ^ (witnessSize n i * h i) :=
          (prod_pow_eq_pow_sum_real Finset.univ (w : ℝ) _).symm
        _ = ∏ i : Fin 4, ((w : ℝ) ^ (witnessSize n i)) ^ (h i) :=
          Finset.prod_congr rfl fun i _ => pow_mul (w : ℝ) _ _
    have hprod_nonneg :
        0 ≤ ∏ i : Fin 4,
          ((((witnessCounts n i).choose (h i) : ℝ) / ((h i) ! : ℝ)) *
            ((2 : ℝ) / (((witnessSize n i) ! : ℝ) * (2 : ℝ) ^ ((witnessSize n i).choose 2))) ^ (h i)) :=
      Finset.prod_nonneg fun _ _ => mul_nonneg (by positivity) (by positivity)
    refine (mul_le_mul_of_nonneg_right hw_pow hprod_nonneg).trans ?_
    rw [← Finset.prod_mul_distrib]
    refine prod_le_one_real Finset.univ (fun _ _ => by positivity) fun i _ => ?_
    set u : ℕ := witnessSize n i
    have hκ_le_n : witnessCounts n i ≤ n := by
      have h1 : witnessCounts n i ≤ u * witnessCounts n i :=
        Nat.le_mul_of_pos_left _ (by have := hsize i; omega)
      have h2 : u * witnessCounts n i ≤ n := by
        calc
          u * witnessCounts n i ≤ ∑ j : Fin 4, witnessSize n j * witnessCounts n j :=
            Finset.single_le_sum (f := fun j => witnessSize n j * witnessCounts n j)
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          _ = n := hn
      omega
    have hch_le : (((witnessCounts n i).choose (h i) : ℝ) / ((h i) ! : ℝ)) ≤ (n : ℝ) ^ (h i) := by
      have h1 : ((witnessCounts n i).choose (h i) : ℝ) ≤ (witnessCounts n i : ℝ) ^ (h i) := by
        have hnat : (witnessCounts n i).choose (h i) ≤ (witnessCounts n i) ^ (h i) := by
          calc
            (witnessCounts n i).choose (h i)
                ≤ (witnessCounts n i).choose (h i) * (h i) ! :=
              Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)
            _ = (witnessCounts n i).descFactorial (h i) := by
              rw [Nat.descFactorial_eq_factorial_mul_choose, mul_comm]
            _ ≤ (witnessCounts n i) ^ (h i) := descFactorial_le_pow _ _
        exact_mod_cast hnat
      have h2 : (1 : ℝ) ≤ ((h i) ! : ℝ) := by exact_mod_cast Nat.factorial_pos (h i)
      calc
        (((witnessCounts n i).choose (h i) : ℝ) / ((h i) ! : ℝ))
            ≤ ((witnessCounts n i).choose (h i) : ℝ) := div_le_self (Nat.cast_nonneg _) h2
        _ ≤ (witnessCounts n i : ℝ) ^ (h i) := h1
        _ ≤ (n : ℝ) ^ (h i) :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hκ_le_n) _
    have hstep_base :
        (2 : ℝ) * (n : ℝ) * (w : ℝ) ^ u ≤
          ((u ! : ℝ) * (2 : ℝ) ^ (u.choose 2)) := by
      set L : ℝ := Real.log (n : ℝ)
      set q : ℝ := Real.log 2
      have hL_ge : 100 + 4 * |alphaConst| ≤ L := hLbig
      have hL100 : (100 : ℝ) ≤ L := by linarith [abs_nonneg alphaConst]
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hw_pos_r : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw_pos
      have hw_le_div : (w : ℝ) ≤ (n : ℝ) / 1024 := by
        rw [le_div_iff₀ (by norm_num)]
        have hc : (1024 : ℝ) * (w : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcorner
        linarith
      have hq_bounds : (0.69 : ℝ) ≤ q ∧ q ≤ 0.70 := by
        dsimp [q]
        constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
      have hα_ge_2L : 2 * L ≤ (alphaNat n : ℝ) := by
        have hm : q * (alphaNat n : ℝ) ≤ (0.70 : ℝ) * (alphaNat n : ℝ) :=
          mul_le_mul_of_nonneg_right hq_bounds.2 (Nat.cast_nonneg _)
        linarith [hlo, hm]
      have hu_ge_L : L ≤ (u : ℝ) := by
        have hu_sub : (u : ℝ) = (alphaNat n : ℝ) - ((i.val + 2 : ℕ) : ℝ) := by
          dsimp [u, witnessSize]
          exact Nat.cast_sub (by have := i.isLt; omega)
        have hi5 : ((i.val + 2 : ℕ) : ℝ) ≤ 5 := by
          exact_mod_cast (show i.val + 2 ≤ 5 by have := i.isLt; omega)
        linarith
      have hu_pos : (0 : ℝ) < (u : ℝ) := by linarith
      have hlog_lhs :
          Real.log ((2 : ℝ) * (n : ℝ) * (w : ℝ) ^ u) ≤
            q + L + (u : ℝ) * (L - 10 * q) := by
        have h1024 : Real.log (1024 : ℝ) = 10 * q := by
          have : (1024 : ℝ) = (2 : ℝ) ^ (10 : ℕ) := by norm_num
          rw [this, Real.log_pow]
          dsimp [q]
        have hlogw : Real.log (w : ℝ) ≤ L - 10 * q := by
          calc
            Real.log (w : ℝ) ≤ Real.log ((n : ℝ) / 1024) :=
              Real.log_le_log hw_pos_r hw_le_div
            _ = L - 10 * q := by rw [Real.log_div hn_pos.ne' (by norm_num), h1024]
        rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by norm_num) hn_pos.ne', Real.log_pow]
        have hm := mul_le_mul_of_nonneg_left hlogw hu_pos.le
        dsimp [q, L] at hm ⊢
        linarith
      have hlog_rhs :
          (u : ℝ) * (L - |alphaConst| - 5) ≤
            Real.log ((u ! : ℝ) * (2 : ℝ) ^ (u.choose 2)) := by
        rw [Real.log_mul (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero u)) (by positivity)]
        have hlog_2c : Real.log ((2 : ℝ) ^ (u.choose 2)) = (u : ℝ) * (q * ((u : ℝ) - 1) / 2) := by
          rw [Real.log_pow, cast_choose_two u]; dsimp [q]; ring
        rw [hlog_2c]
        have hst := (log_factorial_bounds (by have := hsize i; omega : 1 ≤ u)).1
        have hlogu_ge : Real.log L ≤ Real.log (u : ℝ) :=
          Real.log_le_log (by linarith) hu_ge_L
        have hlog_pos : 0 ≤ Real.log (u : ℝ) / 2 :=
          div_nonneg (Real.log_nonneg (by linarith)) (by norm_num)
        have hfac_lb : (u : ℝ) * (Real.log L - 1) ≤ Real.log (u ! : ℝ) := by
          have hm : (u : ℝ) * Real.log L ≤ (u : ℝ) * Real.log (u : ℝ) :=
            mul_le_mul_of_nonneg_left hlogu_ge hu_pos.le
          linarith
        have hq_lb : L - Real.log L - |alphaConst| - 4 ≤ q * ((u : ℝ) - 1) / 2 := by
          have hu_sub : (u : ℝ) = (alphaNat n : ℝ) - ((i.val + 2 : ℕ) : ℝ) := by
            dsimp [u, witnessSize]
            exact Nat.cast_sub (by have := i.isLt; omega)
          have hi5 : ((i.val + 2 : ℕ) : ℝ) ≤ 5 := by
            exact_mod_cast (show i.val + 2 ≤ 5 by have := i.isLt; omega)
          have hδ := phaseDelta_mem_Icc n
          have hc_abs := neg_abs_le alphaConst
          have hq6 : q * (((i.val + 2 : ℕ) : ℝ) + 1 + phaseDelta n) ≤ 5 := by
            nlinarith [hq_bounds.2, hi5, hδ.2, hq_bounds.1]
          rw [hu_sub]
          have hid : q * ((alphaNat n : ℝ) - ((i.val + 2 : ℕ) : ℝ) - 1) =
              q * (alphaNat n : ℝ) - q * (((i.val + 2 : ℕ) : ℝ) + 1) := by ring
          linarith [hqα, hid, hc_abs, hq6]
        have hmul_q := mul_le_mul_of_nonneg_left hq_lb hu_pos.le
        linarith
      have hac_lt : |alphaConst| ≤ 0.7 := by
        unfold alphaConst
        have hq_gt : Real.exp (-0.4) ≤ q := by
          rw [Real.exp_neg]
          have he01 : (1.1 : ℝ) ≤ Real.exp 0.1 := by
            linarith [Real.add_one_le_exp (0.1 : ℝ)]
          have he04'' : (1.1 : ℝ) ^ 4 ≤ Real.exp 0.4 := by
            calc
              (1.1 : ℝ) ^ 4 ≤ (Real.exp 0.1) ^ 4 := pow_le_pow_left₀ (by norm_num) he01 4
              _ = Real.exp 0.4 := by rw [← Real.exp_nat_mul]; norm_num
          have hinv'' : (Real.exp 0.4)⁻¹ ≤ ((1.1 : ℝ) ^ 4)⁻¹ :=
            inv_anti₀ (by positivity) he04''
          linarith [hq_bounds.1, hinv'']
        have hlogq_lo : -0.4 ≤ Real.log q := by
          have := Real.log_le_log (Real.exp_pos _) hq_gt
          rwa [Real.log_exp] at this
        have hlogq_hi : Real.log q ≤ 0 :=
          Real.log_nonpos (by linarith [hq_bounds.1]) (by linarith [hq_bounds.2])
        rw [abs_le]
        constructor <;> dsimp [q] at hlogq_lo hlogq_hi hq_bounds ⊢ <;> linarith
      have hle_logs :
          Real.log ((2 : ℝ) * (n : ℝ) * (w : ℝ) ^ u) ≤
            Real.log ((u ! : ℝ) * (2 : ℝ) ^ (u.choose 2)) := by
        have hcoef : (1.2 : ℝ) ≤ 10 * q - |alphaConst| - 5 := by
          linarith [hq_bounds.1, hac_lt]
        have hm : (u : ℝ) * 1.2 ≤ (u : ℝ) * (10 * q - |alphaConst| - 5) :=
          mul_le_mul_of_nonneg_left hcoef hu_pos.le
        linarith [hlog_lhs, hlog_rhs, hu_ge_L, hL100, hq_bounds.2, hm]
      exact (Real.log_le_log_iff (by positivity) (by positivity)).mp hle_logs
    have hfactor :
        ((w : ℝ) ^ u) ^ (h i) *
          ((((witnessCounts n i).choose (h i) : ℝ) / ((h i) ! : ℝ)) *
            ((2 : ℝ) / (((u ! : ℝ) * (2 : ℝ) ^ (u.choose 2)))) ^ (h i)) ≤
          (((2 : ℝ) * (n : ℝ) * (w : ℝ) ^ u) / ((u ! : ℝ) * (2 : ℝ) ^ (u.choose 2))) ^ (h i) := by
      calc
        ((w : ℝ) ^ u) ^ (h i) *
            ((((witnessCounts n i).choose (h i) : ℝ) / ((h i) ! : ℝ)) *
              ((2 : ℝ) / (((u ! : ℝ) * (2 : ℝ) ^ (u.choose 2)))) ^ (h i))
            ≤ ((w : ℝ) ^ u) ^ (h i) *
                ((n : ℝ) ^ (h i) *
                  ((2 : ℝ) / (((u ! : ℝ) * (2 : ℝ) ^ (u.choose 2)))) ^ (h i)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact mul_le_mul_of_nonneg_right hch_le (by positivity)
        _ = (((2 : ℝ) * (n : ℝ) * (w : ℝ) ^ u) / ((u ! : ℝ) * (2 : ℝ) ^ (u.choose 2))) ^ (h i) := by
              rw [← mul_assoc, ← mul_pow, ← mul_pow]
              congr 1
              ring
    refine hfactor.trans (pow_le_one₀ (by positivity) ?_)
    exact (div_le_one (by positivity)).mpr hstep_base

/-! ### 5. Range 2: Central-Range Analytic Helpers and Uniform Rate Negativity -/

/-- Uniform Stirling bound `|t log t - t - log(t!)| ≤ 2 log n` valid for ALL `0 ≤ t ≤ n`
(including `t = 0`, since `Real.log 0 = 0`) whenever `3 ≤ n`. -/
theorem abs_mul_log_sub_sub_log_factorial_le {n t : ℕ} (hn3 : 3 ≤ n) (ht : t ≤ n) :
    |(t : ℝ) * Real.log (t : ℝ) - (t : ℝ) - Real.log (t ! : ℝ)| ≤ 2 * Real.log (n : ℝ) := by
  have hL_ge1 : (1 : ℝ) ≤ Real.log (n : ℝ) := by
    have he3 : Real.exp 1 ≤ (n : ℝ) := by
      have he : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      exact he.trans (by exact_mod_cast hn3)
    have hlog := Real.log_le_log (Real.exp_pos 1) he3
    rwa [Real.log_exp] at hlog
  rcases Nat.eq_zero_or_pos t with rfl | ht_pos
  · simp
    linarith
  · have hst := log_factorial_bounds ht_pos
    have ht_pos_r : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos
    have hlog_le : Real.log (t : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log ht_pos_r (by exact_mod_cast ht)
    have hlog_nonneg : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg (by exact_mod_cast ht_pos)
    rw [abs_le]
    constructor <;> linarith

/-- Unconditional scaling identity `(K * x) * log(K * x) = K * (x * log x + x * log K)`
valid for all `0 < K` and `0 ≤ x` (including `x = 0`). -/
theorem mul_log_mul_eq {K x : ℝ} (hK : 0 < K) (hx : 0 ≤ x) :
    (K * x) * Real.log (K * x) = K * (x * Real.log x + x * Real.log K) := by
  rcases eq_or_lt_of_le hx with rfl | hx_pos
  · simp
  · rw [Real.log_mul hK.ne' hx_pos.ne']
    ring

/-- Boundary-safe profile entropy inequality `(7.15a)` with `C_H = 1`:
for all `0 ≤ y ≤ p ≤ 1`, `2 p log p - 2 (p - y) log(p - y) - y log y - y ≤ y (1 - log y)`. -/
theorem profile_entropy_term_le {p y : ℝ} (hy0 : 0 ≤ y) (hyp : y ≤ p) (hp1 : p ≤ 1) :
    2 * (p * Real.log p) - 2 * ((p - y) * Real.log (p - y)) - y * Real.log y - y ≤
      y * (1 - Real.log y) := by
  suffices hstep : p * Real.log p - (p - y) * Real.log (p - y) ≤ y by linarith
  rcases eq_or_lt_of_le hy0 with rfl | hy_pos
  · simp
  · have hp_pos : 0 < p := lt_of_lt_of_le hy_pos hyp
    have hlogp_nonpos : Real.log p ≤ 0 := Real.log_nonpos hp_pos.le hp1
    rcases eq_or_lt_of_le (sub_nonneg.mpr hyp) with hpy0 | hpy_pos
    · have hpy_eq : p - y = 0 := hpy0.symm
      rw [hpy_eq]
      simp only [Real.log_zero, mul_zero, sub_zero]
      have hnp : p * Real.log p ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp_pos.le hlogp_nonpos
      linarith
    · have hsplit : p * Real.log p - (p - y) * Real.log (p - y) =
          y * Real.log p + (p - y) * Real.log (p / (p - y)) := by
        rw [Real.log_div hp_pos.ne' hpy_pos.ne']
        ring
      rw [hsplit]
      have h1 : y * Real.log p ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hy_pos.le hlogp_nonpos
      have h2 : (p - y) * Real.log (p / (p - y)) ≤ y := by
        have hlog := Real.log_le_sub_one_of_pos (div_pos hp_pos hpy_pos)
        have hm := mul_le_mul_of_nonneg_left hlog hpy_pos.le
        have hsimp : (p - y) * (p / (p - y) - 1) = y := by
          field_simp [hpy_pos.ne']
          ring
        linarith
      linarith

/-- Four-coordinate concave entropy bound `∑_{i : Fin 4} (-y_i log y_i) ≤ Y (log 4 - log Y)`. -/
theorem sum_fin4_neg_mul_log_le {y : Fin 4 → ℝ} (hy : ∀ i, 0 ≤ y i)
    (hY : 0 < ∑ i : Fin 4, y i) :
    let Y := ∑ i : Fin 4, y i
    ∑ i : Fin 4, (-y i * Real.log (y i)) ≤ Y * (Real.log 4 - Real.log Y) := by
  intro Y
  have hterm : ∀ i : Fin 4,
      -y i * Real.log (y i) ≤ Y / 4 - y i + y i * (Real.log 4 - Real.log Y) := by
    intro i
    rcases eq_or_lt_of_le (hy i) with hi0 | hi_pos
    · rw [← hi0]
      simp only [neg_zero, zero_mul, sub_zero, add_zero]
      positivity
    · have hY4 : 0 < Y / 4 := div_pos hY (by norm_num)
      have hlog := Real.log_le_sub_one_of_pos (div_pos hY4 hi_pos)
      have hm := mul_le_mul_of_nonneg_left hlog hi_pos.le
      rw [Real.log_div hY4.ne' hi_pos.ne', Real.log_div hY.ne' (by norm_num)] at hm
      have hrhs : y i * (Y / 4 / y i - 1) = Y / 4 - y i := by
        field_simp [hi_pos.ne']
      linarith
  calc
    ∑ i : Fin 4, (-y i * Real.log (y i))
        ≤ ∑ i : Fin 4, (Y / 4 - y i + y i * (Real.log 4 - Real.log Y)) :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ _i : Fin 4, Y / 4) - (∑ i : Fin 4, y i) +
          (∑ i : Fin 4, y i) * (Real.log 4 - Real.log Y) := by
      simp_rw [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul]
    _ = Y * (Real.log 4 - Real.log Y) := by
      simp [Finset.sum_const, Y]
      ring

/-- Elementary comparison `ρ log ρ - R log R ≤ 2060 |ρ - R|` whenever `0 < ρ`,
`1 / 2048 ≤ R ≤ 1`, and `|ρ - R| ≤ 1`. -/
theorem mul_log_sub_mul_log_le {ρ R : ℝ}
    (hρ : 0 < ρ) (hR_lo : 1 / 2048 ≤ R) (hR_hi : R ≤ 1) (hdiff : |ρ - R| ≤ 1) :
    ρ * Real.log ρ - R * Real.log R ≤ 2060 * |ρ - R| := by
  have hR_pos : 0 < R := by linarith
  have hsplit : ρ * Real.log ρ - R * Real.log R =
      (ρ - R) * Real.log R + ρ * Real.log (ρ / R) := by
    rw [Real.log_div hρ.ne' hR_pos.ne']
    ring
  have h1 : ρ * Real.log (ρ / R) ≤ (ρ - R) + (ρ - R) ^ 2 / R := by
    have hlog := Real.log_le_sub_one_of_pos (div_pos hρ hR_pos)
    have hm := mul_le_mul_of_nonneg_left hlog hρ.le
    have hid : ρ * (ρ / R - 1) = (ρ - R) + (ρ - R) ^ 2 / R := by
      field_simp [hR_pos.ne']
      ring
    linarith
  have hlogR_lo : -8 ≤ Real.log R := by
    have he8 : Real.exp (-8) ≤ R := by
      refine le_trans ?_ hR_lo
      rw [Real.exp_neg]
      have h27 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have hp8 : (2048 : ℝ) ≤ Real.exp 8 := by
        calc
          (2048 : ℝ) ≤ (2.7 : ℝ) ^ 8 := by norm_num
          _ ≤ (Real.exp 1) ^ 8 := pow_le_pow_left₀ (by norm_num) h27 8
          _ = Real.exp 8 := by rw [← Real.exp_nat_mul]; norm_num
      simpa [one_div] using inv_anti₀ (by norm_num) hp8
    have hl := Real.log_le_log (Real.exp_pos _) he8
    rwa [Real.log_exp] at hl
  have hlogR_hi : Real.log R ≤ 0 := Real.log_nonpos hR_pos.le hR_hi
  have habs_1logR : |1 + Real.log R| ≤ 9 := by
    rw [abs_le]; constructor <;> linarith
  have hterm1 : (ρ - R) * (1 + Real.log R) ≤ 9 * |ρ - R| := by
    calc
      (ρ - R) * (1 + Real.log R) ≤ |(ρ - R) * (1 + Real.log R)| := le_abs_self _
      _ = |ρ - R| * |1 + Real.log R| := abs_mul _ _
      _ ≤ |ρ - R| * 9 := mul_le_mul_of_nonneg_left habs_1logR (abs_nonneg _)
      _ = 9 * |ρ - R| := by ring
  have hsq_le : (ρ - R) ^ 2 ≤ |ρ - R| := by
    calc
      (ρ - R) ^ 2 = |ρ - R| * |ρ - R| := by rw [← sq_abs, sq]
      _ ≤ |ρ - R| * 1 := mul_le_mul_of_nonneg_left hdiff (abs_nonneg _)
      _ = |ρ - R| := mul_one _
  have hterm2 : (ρ - R) ^ 2 / R ≤ 2048 * |ρ - R| := by
    rw [div_le_iff₀ hR_pos]
    calc
      (ρ - R) ^ 2 ≤ |ρ - R| := hsq_le
      _ = 2048 * |ρ - R| * (1 / 2048) := by ring
      _ ≤ 2048 * |ρ - R| * R :=
        mul_le_mul_of_nonneg_left hR_lo (by positivity)
  linarith [hsplit, h1, hterm1, hterm2, abs_nonneg (ρ - R)]

/-- Padé logarithm bound `log R ≤ 2 * (R - 1) / (R + 1)` for `0 < R ≤ 1`. -/
theorem log_le_two_mul_sub_one_div_add_one {R : ℝ} (hR0 : 0 < R) (hR1 : R ≤ 1) :
    Real.log R ≤ 2 * (R - 1) / (R + 1) := by
  let f : ℝ → ℝ := fun x => Real.log x - 2 * (x - 1) / (x + 1)
  let f' : ℝ → ℝ := fun x => x⁻¹ - 4 / (x + 1) ^ 2
  have hderiv : ∀ x ∈ Set.Icc R 1, HasDerivAt f (f' x) x := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le hR0 hx.1
    have hx1_pos : 0 < x + 1 := by linarith
    have hd1 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx_pos.ne'
    have hd_num : HasDerivAt (fun t : ℝ => 2 * (t - 1)) 2 x := by
      simpa using ((hasDerivAt_id x).sub_const 1).const_mul 2
    have hd_den : HasDerivAt (fun t : ℝ => t + 1) 1 x := by
      simpa using (hasDerivAt_id x).add_const 1
    have hd2 := hd_num.div hd_den hx1_pos.ne'
    have hd2' : HasDerivAt (fun t : ℝ => 2 * (t - 1) / (t + 1)) (4 / (x + 1) ^ 2) x := by
      convert hd2 using 1
      ring
    exact hd1.sub hd2'
  have hcont : ContinuousOn f (Set.Icc R 1) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (interior (Set.Icc R 1)) :=
    fun x hx => (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
  have hf'_nonneg : ∀ x ∈ interior (Set.Icc R 1), 0 ≤ deriv f x := by
    intro x hx
    have hx_mem := interior_subset hx
    have hx_pos : 0 < x := lt_of_lt_of_le hR0 hx_mem.1
    have hx1_pos : 0 < x + 1 := by linarith
    rw [(hderiv x hx_mem).deriv]
    dsimp [f']
    have heq : x⁻¹ - 4 / (x + 1) ^ 2 = (x - 1) ^ 2 / (x * (x + 1) ^ 2) := by
      field_simp [hx_pos.ne', hx1_pos.ne']
      ring
    rw [heq]
    positivity
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc R 1) hcont hdiff hf'_nonneg
  have hle : f R ≤ f 1 := hmono ⟨le_rfl, hR1⟩ ⟨hR1, le_rfl⟩ hR1
  have hf1 : f 1 = 0 := by simp [f]
  rw [hf1] at hle
  dsimp [f] at hle
  linarith

/-- Uniform rate negativity `(7.23)`: whenever `1 / 2048 ≤ R ≤ 1` and `T ≤ 3.95`,
`R log R + (log 2 / 2) * (I_r - T * R) ≤ -Y / 30000`. -/
theorem rate_phi_le_neg_div {y z : Fin 4 → ℝ}
    (hy : ∀ i, 0 ≤ y i) (hz : ∀ i, 0 ≤ z i)
    (hsum1 : (∑ i : Fin 4, z i) + (∑ i : Fin 4, y i) = 1)
    (hR_lo : 1 / 2048 ≤ ∑ i : Fin 4, z i)
    (hT_hi : ∑ i : Fin 4, ((i.val + 2 : ℕ) : ℝ) * (z i + y i) ≤ 3.95) :
    let R := ∑ i : Fin 4, z i
    let Y := ∑ i : Fin 4, y i
    let T := ∑ i : Fin 4, ((i.val + 2 : ℕ) : ℝ) * (z i + y i)
    let I_r := ∑ i : Fin 4, ((i.val + 2 : ℕ) : ℝ) * z i
    R * Real.log R + (Real.log 2 / 2) * (I_r - T * R) ≤ -Y / 30000 := by
  intro R Y T I_r
  have hY_nonneg : 0 ≤ Y := Finset.sum_nonneg fun i _ => hy i
  have hR_pos : 0 < R := by linarith
  have hR1 : R ≤ 1 := by linarith
  have hq_hi : Real.log 2 ≤ 0.70 := by linarith [Real.log_two_lt_d9]
  have hq_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hIr_le_5R : I_r ≤ 5 * R := by
    calc
      I_r = ∑ i : Fin 4, ((i.val + 2 : ℕ) : ℝ) * z i := rfl
      _ ≤ ∑ i : Fin 4, 5 * z i := by
        refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (hz i)
        exact_mod_cast (show i.val + 2 ≤ 5 by have := i.isLt; omega)
      _ = 5 * R := (Finset.mul_sum _ _ _).symm
  have hIy_ge_2Y : 2 * Y ≤ ∑ i : Fin 4, ((i.val + 2 : ℕ) : ℝ) * y i := by
    calc
      2 * Y = ∑ i : Fin 4, 2 * y i := Finset.mul_sum _ _ _
      _ ≤ ∑ i : Fin 4, ((i.val + 2 : ℕ) : ℝ) * y i := by
        refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (hy i)
        exact_mod_cast (show 2 ≤ i.val + 2 by omega)
  have hT_split : T = I_r + ∑ i : Fin 4, ((i.val + 2 : ℕ) : ℝ) * y i := by
    dsimp [T, I_r]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => mul_add _ _ _
  have hbound1 : I_r - T * R ≤ (5 - T) * R := by linarith
  have hbound2 : I_r - T * R ≤ (T - 2) * Y := by
    have hTR : T - T * R = T * Y := by nlinarith [hsum1]
    linarith [hT_split, hIy_ge_2Y, hTR]
  by_cases hR34 : R ≤ 3 / 4
  · have hcomb : I_r - T * R ≤ 3 * R * Y := by
      have hm1 := mul_le_mul_of_nonneg_right hbound1 hY_nonneg
      have hm2 := mul_le_mul_of_nonneg_right hbound2 hR_pos.le
      nlinarith [hsum1, hm1, hm2]
    have hq_term : (Real.log 2 / 2) * (I_r - T * R) ≤ (21 / 20 : ℝ) * R * Y := by
      by_cases hpos : 0 ≤ I_r - T * R
      · calc
          (Real.log 2 / 2) * (I_r - T * R)
              ≤ (0.70 / 2 : ℝ) * (3 * R * Y) :=
            mul_le_mul (by linarith) hcomb hpos (by norm_num)
          _ = (21 / 20 : ℝ) * R * Y := by ring
      · push Not at hpos
        have hneg : (Real.log 2 / 2) * (I_r - T * R) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hpos.le
        have hrhs0 : 0 ≤ (21 / 20 : ℝ) * R * Y := by positivity
        linarith
    have hpade := mul_le_mul_of_nonneg_left (log_le_two_mul_sub_one_div_add_one hR_pos hR1) hR_pos.le
    have hpade_eq : R * (2 * (R - 1) / (R + 1)) = -(2 / (R + 1)) * (R * Y) := by
      have hsub : R - 1 = -Y := by linarith [hsum1]
      rw [hsub]
      ring
    rw [hpade_eq] at hpade
    have h87 : (8 / 7 : ℝ) ≤ 2 / (R + 1) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    have hpade' : R * Real.log R ≤ -(8 / 7 : ℝ) * R * Y := by
      have hm := mul_le_mul_of_nonneg_right h87 (mul_nonneg hR_pos.le hY_nonneg)
      linarith
    have hsum_mid : R * Real.log R + (Real.log 2 / 2) * (I_r - T * R) ≤
        -(13 / 140 : ℝ) * R * Y := by linarith
    have hRY_ge : (1 / 2048 : ℝ) * Y ≤ R * Y :=
      mul_le_mul_of_nonneg_right hR_lo hY_nonneg
    have h13 : (1 / 30000 : ℝ) * Y ≤ (13 / 140 : ℝ) * ((1 / 2048 : ℝ) * Y) := by
      have : (1 / 30000 : ℝ) ≤ (13 / 140 : ℝ) * (1 / 2048 : ℝ) := by norm_num
      linarith [mul_le_mul_of_nonneg_right this hY_nonneg]
    have hm_ry := mul_le_mul_of_nonneg_left hRY_ge (show (0 : ℝ) ≤ 13 / 140 by norm_num)
    linarith [hsum_mid, h13, hm_ry]
  · push Not at hR34
    have hIr_2Y : I_r - T * R ≤ 1.95 * Y := by nlinarith [hbound2, hT_hi, hY_nonneg]
    have hq_term : (Real.log 2 / 2) * (I_r - T * R) ≤ 0.70 * Y := by
      by_cases hpos : 0 ≤ I_r - T * R
      · calc
          (Real.log 2 / 2) * (I_r - T * R)
              ≤ (0.70 / 2 : ℝ) * (1.95 * Y) :=
            mul_le_mul (by linarith) hIr_2Y hpos (by norm_num)
          _ ≤ 0.70 * Y := by nlinarith [hY_nonneg]
      · push Not at hpos
        have hneg : (Real.log 2 / 2) * (I_r - T * R) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hpos.le
        linarith [hY_nonneg]
    have hlog_negY : Real.log R ≤ -Y := by
      have h1 := Real.log_le_sub_one_of_pos hR_pos
      linarith [hsum1, h1]
    have hRlog : R * Real.log R ≤ -0.75 * Y := by
      calc
        R * Real.log R ≤ R * (-Y) := mul_le_mul_of_nonneg_left hlog_negY hR_pos.le
        _ ≤ (3 / 4 : ℝ) * (-Y) := by nlinarith [hR34, hY_nonneg]
        _ = -0.75 * Y := by ring
    linarith [hY_nonneg]

/-! ### 6. Range 2: Central-Range Bound and Master Section 7 Sum Theorem -/

/-- Per-class logarithmic discrepancy `E_i` in the central-range expansion of `log D_n(v)`. -/
private noncomputable def centralClassErr (n : ℕ) (i : Fin 4) : ℝ :=
  Real.log (kCoSeed n : ℝ) + Real.log (((witnessSize n i) ! : ℝ)) + (witnessSize n i : ℝ) -
    (witnessSize n i : ℝ) * Real.log (n : ℝ) +
    Real.log 2 * ((witnessSize n i).choose 2 : ℝ) - Real.log 2

/-- Uniform Stirling upper bound `(7.14)` on `Real.log (diagWeight n v)` in the central range. -/
private lemma central_log_diagWeight_stirling {n : ℕ} {v : Fin 4 → ℕ}
    (hn3 : 3 ≤ n)
    (hK_pos : 0 < (kCoSeed n : ℝ))
    (hn : ∑ i : Fin 4, witnessSize n i * witnessCounts n i = n)
    (hsize : ∀ i : Fin 4, 10 ≤ witnessSize n i)
    (hv : v ∈ diagBox n)
    (hw_pos : 0 < n - diagMass n v) :
    let K : ℝ := (kCoSeed n : ℝ)
    let p : Fin 4 → ℝ := fun i => (witnessCounts n i : ℝ) / K
    let y : Fin 4 → ℝ := fun i => (v i : ℝ) / K
    let z : Fin 4 → ℝ := fun i => p i - y i
    let ρ : ℝ := ((n - diagMass n v : ℕ) : ℝ) / (n : ℝ)
    Real.log (diagWeight n v) ≤
      (n : ℝ) * ρ * Real.log ρ +
        K * (∑ i : Fin 4,
          (2 * (p i * Real.log (p i)) - 2 * (z i * Real.log (z i)) -
            y i * Real.log (y i) - y i + y i * centralClassErr n i)) +
        44 * Real.log (n : ℝ) := by
  intro K p y z ρ
  have hKne : K ≠ 0 := hK_pos.ne'
  set L : ℝ := Real.log (n : ℝ)
  set q : ℝ := Real.log 2
  set m : ℕ := diagMass n v
  set w : ℕ := n - m
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hw_pos_r : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw_pos
  have hρ_pos : 0 < ρ := div_pos hw_pos_r hn_pos
  have hv_le := mem_diagBox_iff.mp hv
  have hm_le : m ≤ n := diagMass_le_of_mem_diagBox hn hv
  have hy_nonneg : ∀ i, 0 ≤ y i := fun i => div_nonneg (Nat.cast_nonneg _) hK_pos.le
  have hy_le_p : ∀ i, y i ≤ p i := fun i =>
    div_le_div_of_nonneg_right (by exact_mod_cast hv_le i) hK_pos.le
  have hz_nonneg : ∀ i, 0 ≤ z i := fun i => sub_nonneg.mpr (hy_le_p i)
  have hz_eq_div : ∀ i, z i = ((witnessCounts n i - v i : ℕ) : ℝ) / K := by
    intro i
    dsimp [z, p, y]
    rw [Nat.cast_sub (hv_le i), sub_div]
  have hlogD_exact :
      Real.log (diagWeight n v) =
        (∑ i : Fin 4, (2 * Real.log ((witnessCounts n i) ! : ℝ) -
          2 * Real.log (((witnessCounts n i - v i) ! : ℝ)) - Real.log ((v i) ! : ℝ))) -
        Real.log (n ! : ℝ) + Real.log (w ! : ℝ) +
        ∑ i : Fin 4, (v i : ℝ) *
          (Real.log (((witnessSize n i) ! : ℝ)) + q * ((witnessSize n i).choose 2 : ℝ) - q) := by
    unfold diagWeight
    have hP1 : 0 < ∏ i : Fin 4, ((witnessCounts n i).descFactorial (v i) : ℝ) ^ 2 :=
      Finset.prod_pos fun i _ => sq_pos_of_pos (Nat.cast_pos.mpr (descFactorial_pos_of_le (hv_le i)))
    have hP2 : 0 < ∏ i : Fin 4, ((v i) ! : ℝ) :=
      Finset.prod_pos fun i _ => Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hP3 : 0 < (n.descFactorial (diagMass n v) : ℝ) :=
      Nat.cast_pos.mpr (descFactorial_pos_of_le hm_le)
    have hP4 : 0 < ∏ i : Fin 4, (((witnessSize n i) ! : ℝ) * localCellReward (witnessSize n i)) ^ (v i) :=
      Finset.prod_pos fun i _ =>
        pow_pos (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (localCellReward_pos _)) _
    rw [Real.log_mul (div_pos hP1 hP2).ne' (div_pos hP4 hP3).ne',
      Real.log_div hP1.ne' hP2.ne',
      Real.log_div hP4.ne' hP3.ne',
      Real.log_prod (fun i _ =>
        (sq_pos_of_pos (Nat.cast_pos.mpr (descFactorial_pos_of_le (hv_le i)))).ne'),
      Real.log_prod (fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (v i))),
      Real.log_prod (fun i _ =>
        (pow_pos (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _))
          (localCellReward_pos _)) _).ne')]
    have hn_desc : Real.log (n.descFactorial m : ℝ) = Real.log (n ! : ℝ) - Real.log (w ! : ℝ) := by
      have hid : (n.descFactorial m : ℝ) * (w ! : ℝ) = (n ! : ℝ) := by
        exact_mod_cast descFactorial_mul_factorial_sub hm_le
      rw [← hid, Real.log_mul (Nat.cast_ne_zero.mpr (descFactorial_pos_of_le hm_le).ne')
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero w))]
      ring
    have hκ_desc : ∀ i : Fin 4,
        Real.log (((witnessCounts n i).descFactorial (v i) : ℝ) ^ 2) =
          2 * Real.log ((witnessCounts n i) ! : ℝ) -
            2 * Real.log (((witnessCounts n i - v i) ! : ℝ)) := by
      intro i
      rw [Real.log_pow]
      have hid : ((witnessCounts n i).descFactorial (v i) : ℝ) *
          (((witnessCounts n i - v i) ! : ℝ)) = ((witnessCounts n i) ! : ℝ) := by
        exact_mod_cast descFactorial_mul_factorial_sub (hv_le i)
      have h1 : Real.log ((witnessCounts n i) ! : ℝ) =
          Real.log ((witnessCounts n i).descFactorial (v i) : ℝ) +
            Real.log (((witnessCounts n i - v i) ! : ℝ)) := by
        rw [← hid, Real.log_mul (Nat.cast_ne_zero.mpr (descFactorial_pos_of_le (hv_le i)).ne')
          (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]
      push_cast; linarith
    have hu_term : ∀ i : Fin 4,
        Real.log ((((witnessSize n i) ! : ℝ) * localCellReward (witnessSize n i)) ^ (v i)) =
          (v i : ℝ) *
            (Real.log (((witnessSize n i) ! : ℝ)) + q * ((witnessSize n i).choose 2 : ℝ) - q) := by
      intro i
      rw [Real.log_pow, localCellReward_eq_div_two_of_two_le (by have := hsize i; omega),
        Real.log_mul (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) (by positivity),
        Real.log_div (by positivity) (by norm_num), Real.log_pow]
      dsimp [q]; ring
    rw [hn_desc]
    simp_rw [hκ_desc, hu_term, Finset.sum_sub_distrib]
    ring
  rw [hlogD_exact]
  have hκ_le_n : ∀ i : Fin 4, witnessCounts n i ≤ n := by
    intro i
    have h1 : witnessCounts n i ≤ witnessSize n i * witnessCounts n i :=
      Nat.le_mul_of_pos_left _ (by have := hsize i; omega)
    have h2 : witnessSize n i * witnessCounts n i ≤ n := by
      calc
        witnessSize n i * witnessCounts n i
            ≤ ∑ j : Fin 4, witnessSize n j * witnessCounts n j :=
          Finset.single_le_sum (f := fun j => witnessSize n j * witnessCounts n j)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        _ = n := hn
    omega
  have hst_n := (abs_le.mp (abs_mul_log_sub_sub_log_factorial_le hn3 le_rfl)).2
  have hst_w := (abs_le.mp (abs_mul_log_sub_sub_log_factorial_le hn3 (Nat.sub_le n m))).1
  have hprof_each : ∀ i : Fin 4,
      2 * Real.log ((witnessCounts n i) ! : ℝ) -
        2 * Real.log (((witnessCounts n i - v i) ! : ℝ)) - Real.log ((v i) ! : ℝ) ≤
      K * (2 * (p i * Real.log (p i)) - 2 * (z i * Real.log (z i)) -
        y i * Real.log (y i) - y i + y i * Real.log K) + 10 * L := by
    intro i
    have hs1 := (abs_le.mp (abs_mul_log_sub_sub_log_factorial_le hn3 (hκ_le_n i))).1
    have hs2 := (abs_le.mp (abs_mul_log_sub_sub_log_factorial_le hn3
      ((Nat.sub_le (witnessCounts n i) (v i)).trans (hκ_le_n i)))).2
    have hs3 := (abs_le.mp (abs_mul_log_sub_sub_log_factorial_le hn3
      ((hv_le i).trans (hκ_le_n i)))).2
    have hκ_eq : (witnessCounts n i : ℝ) = K * p i := by
      dsimp [p]; field_simp [hKne]
    have hv_eq : (v i : ℝ) = K * y i := by
      dsimp [y]; field_simp [hKne]
    have hz_eq : ((witnessCounts n i - v i : ℕ) : ℝ) = K * z i := by
      rw [hz_eq_div i]; field_simp [hKne]
    have hm1 := mul_log_mul_eq hK_pos ((hy_nonneg i).trans (hy_le_p i))
    have hm2 := mul_log_mul_eq hK_pos (hz_nonneg i)
    have hm3 := mul_log_mul_eq hK_pos (hy_nonneg i)
    rw [← hκ_eq] at hm1
    rw [← hz_eq] at hm2
    rw [← hv_eq] at hm3
    have hlin_id :
        2 * ((witnessCounts n i : ℝ) * Real.log (witnessCounts n i : ℝ) - (witnessCounts n i : ℝ)) -
          2 * (((witnessCounts n i - v i : ℕ) : ℝ) *
            Real.log ((witnessCounts n i - v i : ℕ) : ℝ) -
            ((witnessCounts n i - v i : ℕ) : ℝ)) -
          ((v i : ℝ) * Real.log (v i : ℝ) - (v i : ℝ)) =
        K * (2 * (p i * Real.log (p i)) - 2 * (z i * Real.log (z i)) -
          y i * Real.log (y i) - y i + y i * Real.log K) := by
      rw [hm1, hm2, hm3, hκ_eq, hz_eq, hv_eq]
      dsimp [z]
      ring
    change _ ≤ _ + 10 * Real.log (n : ℝ)
    linarith only [hs1, hs2, hs3, hlin_id]
  have hsum_prof := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hprof_each i
  have hsum_10L : ∑ i : Fin 4, (K * (2 * (p i * Real.log (p i)) - 2 * (z i * Real.log (z i)) -
      y i * Real.log (y i) - y i + y i * Real.log K) + 10 * L) =
    K * (∑ i : Fin 4, (2 * (p i * Real.log (p i)) - 2 * (z i * Real.log (z i)) -
      y i * Real.log (y i) - y i + y i * Real.log K)) + 40 * L := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [Finset.sum_const]
    ring
  rw [hsum_10L] at hsum_prof
  have hamb_id :
      -((n : ℝ) * L - (n : ℝ)) + ((w : ℝ) * Real.log (w : ℝ) - (w : ℝ)) =
        (n : ℝ) * ρ * Real.log ρ +
          K * ∑ i : Fin 4, y i * ((witnessSize n i : ℝ) - (witnessSize n i : ℝ) * L) := by
    have hw_nρ : (w : ℝ) = (n : ℝ) * ρ := by dsimp [ρ, w, m]; field_simp [hn_pos.ne']
    have hm_w : (n : ℝ) - (w : ℝ) = (m : ℝ) := by
      dsimp [w]; rw [Nat.cast_sub hm_le]; ring
    have hlog_w := mul_log_mul_eq hn_pos hρ_pos.le
    rw [← hw_nρ] at hlog_w
    have hm_sum : (m : ℝ) = K * ∑ i : Fin 4, y i * (witnessSize n i : ℝ) := by
      dsimp [m, diagMass, y]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hv_eq : (v i : ℝ) = K * ((v i : ℝ) / K) := by field_simp [hKne]
      linarith [show (witnessSize n i : ℝ) * (v i : ℝ) =
        K * ((v i : ℝ) / K * (witnessSize n i : ℝ)) by
        calc
          (witnessSize n i : ℝ) * (v i : ℝ) = (witnessSize n i : ℝ) * (K * ((v i : ℝ) / K)) := by
            rw [← hv_eq]
          _ = K * ((v i : ℝ) / K * (witnessSize n i : ℝ)) := by ring]
    have hsum_uL :
        K * ∑ i : Fin 4, y i * ((witnessSize n i : ℝ) - (witnessSize n i : ℝ) * L) =
          (m : ℝ) * (1 - L) := by
      rw [hm_sum, mul_assoc]
      congr 1
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hlog_w, hsum_uL, ← hm_w, hw_nρ]
    dsimp [L]
    ring
  have hclass_id :
      ∑ i : Fin 4, (v i : ℝ) *
        (Real.log (((witnessSize n i) ! : ℝ)) + q * ((witnessSize n i).choose 2 : ℝ) - q) =
      K * ∑ i : Fin 4, y i *
        (Real.log (((witnessSize n i) ! : ℝ)) + q * ((witnessSize n i).choose 2 : ℝ) - q) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hv_eq : (v i : ℝ) = K * y i := by dsimp [y]; field_simp [hKne]
    rw [hv_eq]; ring
  have hcombine_E :
      K * (∑ i : Fin 4, (2 * (p i * Real.log (p i)) - 2 * (z i * Real.log (z i)) -
          y i * Real.log (y i) - y i + y i * Real.log K)) +
        K * (∑ i : Fin 4, y i * ((witnessSize n i : ℝ) - (witnessSize n i : ℝ) * L)) +
        K * (∑ i : Fin 4, y i *
          (Real.log (((witnessSize n i) ! : ℝ)) + q * ((witnessSize n i).choose 2 : ℝ) - q)) =
      K * (∑ i : Fin 4,
        (2 * (p i * Real.log (p i)) - 2 * (z i * Real.log (z i)) -
          y i * Real.log (y i) - y i + y i * centralClassErr n i)) := by
    rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp [centralClassErr, K, L, q]; ring
  dsimp [L] at hst_n hst_w ⊢
  linarith only [hsum_prof, hst_n, hst_w, hamb_id, hclass_id, hcombine_E]

/-- Bound `(7.18)–(7.19)` on `∑ y_i E_i` via `∑ p_i E_i ≤ 4` and `|F_i - F_0| ≤ 3 |alphaConst| + 24`. -/
private lemma central_sum_yE_le {n : ℕ} {y : Fin 4 → ℝ}
    (hn16 : 16 ≤ n)
    (hqα : Real.log 2 * (alphaNat n : ℝ) =
      2 * Real.log (n : ℝ) - 2 * Real.log (Real.log (n : ℝ)) +
        2 * alphaConst - Real.log 2 * phaseDelta n)
    (hlo : (3 / 2 : ℝ) * Real.log (n : ℝ) ≤ Real.log 2 * (alphaNat n : ℝ))
    (hhi : Real.log 2 * (alphaNat n : ℝ) ≤ 2 * Real.log (n : ℝ))
    (hK : ∑ i : Fin 4, witnessCounts n i = kCoSeed n)
    (hn : ∑ i : Fin 4, witnessSize n i * witnessCounts n i = n)
    (hsize : ∀ i : Fin 4, 10 ≤ witnessSize n i)
    (hlog_fm : 100 * (n : ℝ) / (Real.log (n : ℝ)) ^ 2 ≤
      Real.log (n ! : ℝ) + (kCoSeed n : ℝ) * Real.log 2 -
        ∑ j : Fin 4, Real.log ((witnessCounts n j) ! : ℝ) -
        ∑ j : Fin 4, (witnessCounts n j : ℝ) *
          (Real.log ((witnessSize n j) ! : ℝ) + Real.log 2 * ((witnessSize n j).choose 2 : ℝ)))
    (hL10000 : (10000 : ℝ) ≤ Real.log (n : ℝ))
    (hnL4 : (40 : ℝ) ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 4)
    (hK_pos : 0 < (kCoSeed n : ℝ))
    (hK_lo_real : (n : ℝ) / (3 * Real.log (n : ℝ)) ≤ (kCoSeed n : ℝ))
    (hy_nonneg : ∀ i, 0 ≤ y i) :
    let q : ℝ := Real.log 2
    let α : ℝ := (alphaNat n : ℝ)
    let T : ℝ := seedDeficit n
    let Y : ℝ := ∑ i : Fin 4, y i
    let I_y : ℝ := ∑ i : Fin 4, ((i.val + 2 : ℕ) : ℝ) * y i
    ∑ i : Fin 4, y i * centralClassErr n i ≤
      (q * α / 2) * (T * Y - I_y) + (6 * |alphaConst| + 52) * Y := by
  intro q α T Y I_y
  set L : ℝ := Real.log (n : ℝ)
  set K : ℝ := (kCoSeed n : ℝ)
  have hKne : K ≠ 0 := hK_pos.ne'
  set p : Fin 4 → ℝ := fun i => (witnessCounts n i : ℝ) / K
  have hL_pos : 0 < L := by linarith only [hL10000]
  have hn3 : 3 ≤ n := by omega
  have hp_nonneg : ∀ i : Fin 4, 0 ≤ p i := fun i => div_nonneg (Nat.cast_nonneg _) hK_pos.le
  have hp_sum1 : ∑ i : Fin 4, p i = 1 := by
    dsimp [p]
    rw [← Finset.sum_div]
    have hsum_cast : ∑ i : Fin 4, (witnessCounts n i : ℝ) = K := by dsimp [K]; exact_mod_cast hK
    rw [hsum_cast, div_self hKne]
  have hT_mean : ∑ i : Fin 4, ((i.val + 2 : ℕ) : ℝ) * p i = T := by
    have hn_cast : ∑ i : Fin 4, (witnessSize n i : ℝ) * (witnessCounts n i : ℝ) = (n : ℝ) := by
      exact_mod_cast hn
    have hu_cast : ∀ i : Fin 4, (witnessSize n i : ℝ) = α - ((i.val + 2 : ℕ) : ℝ) := by
      intro i
      have hs0 := hsize 0
      unfold witnessSize at hs0 ⊢
      exact Nat.cast_sub (by have := i.isLt; omega)
    have h1 : ∑ i : Fin 4, ((i.val + 2 : ℕ) : ℝ) * (witnessCounts n i : ℝ) = α * K - (n : ℝ) := by
      have hid : ∑ i : Fin 4, ((i.val + 2 : ℕ) : ℝ) * (witnessCounts n i : ℝ) =
          α * (∑ i : Fin 4, (witnessCounts n i : ℝ)) -
            ∑ i : Fin 4, (witnessSize n i : ℝ) * (witnessCounts n i : ℝ) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hu_cast i]; ring
      have hK_cast : ∑ i : Fin 4, (witnessCounts n i : ℝ) = K := by dsimp [K]; exact_mod_cast hK
      rw [hid, hK_cast, hn_cast]
    dsimp [p, T, seedDeficit, K, α] at h1 ⊢
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div, h1]
    have hKne' : (kCoSeed n : ℝ) ≠ 0 := hKne
    field_simp [hKne']
  have hκ_le_n : ∀ i : Fin 4, witnessCounts n i ≤ n := by
    intro i
    have h1 : witnessCounts n i ≤ witnessSize n i * witnessCounts n i :=
      Nat.le_mul_of_pos_left _ (by have := hsize i; omega)
    have h2 : witnessSize n i * witnessCounts n i ≤ n := by
      calc
        witnessSize n i * witnessCounts n i
            ≤ ∑ j : Fin 4, witnessSize n j * witnessCounts n j :=
          Finset.single_le_sum (f := fun j => witnessSize n j * witnessCounts n j)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        _ = n := hn
    omega
  have hbarE : ∑ i : Fin 4, p i * centralClassErr n i ≤ 4 := by
    have hKbarE :
        K * (∑ i : Fin 4, p i * centralClassErr n i) =
          K * Real.log K +
            (∑ i : Fin 4, (witnessCounts n i : ℝ) *
              (Real.log (((witnessSize n i) ! : ℝ)) + q * ((witnessSize n i).choose 2 : ℝ))) +
            (n : ℝ) - (n : ℝ) * L - K * q := by
      rw [Finset.mul_sum]
      have hκ_eq : ∀ i : Fin 4,
          K * (p i * centralClassErr n i) = (witnessCounts n i : ℝ) * centralClassErr n i := by
        intro i; dsimp [p]; field_simp [hKne]
      simp_rw [hκ_eq]
      dsimp [centralClassErr, K, L, q]
      have hlin : ∀ i : Fin 4,
          (witnessCounts n i : ℝ) *
            (Real.log (kCoSeed n : ℝ) + Real.log (((witnessSize n i) ! : ℝ)) +
              (witnessSize n i : ℝ) - (witnessSize n i : ℝ) * Real.log (n : ℝ) +
              Real.log 2 * ((witnessSize n i).choose 2 : ℝ) - Real.log 2) =
          (witnessCounts n i : ℝ) * Real.log (kCoSeed n : ℝ) +
            (witnessCounts n i : ℝ) *
              (Real.log (((witnessSize n i) ! : ℝ)) +
                Real.log 2 * ((witnessSize n i).choose 2 : ℝ)) +
            (witnessSize n i : ℝ) * (witnessCounts n i : ℝ) -
            ((witnessSize n i : ℝ) * (witnessCounts n i : ℝ)) * Real.log (n : ℝ) -
            (witnessCounts n i : ℝ) * Real.log 2 := fun _ => by ring
      simp_rw [hlin, sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib,
        ← Finset.sum_mul]
      have hK_cast : ∑ i : Fin 4, (witnessCounts n i : ℝ) = (kCoSeed n : ℝ) := by exact_mod_cast hK
      have hn_cast : ∑ i : Fin 4, (witnessSize n i : ℝ) * (witnessCounts n i : ℝ) = (n : ℝ) := by
        exact_mod_cast hn
      rw [hK_cast, hn_cast]
    have hfm0 : 0 ≤ 100 * (n : ℝ) / L ^ 2 := by positivity
    have hst_n := (abs_le.mp (abs_mul_log_sub_sub_log_factorial_le hn3 le_rfl)).1
    have hst_κ : ∀ i : Fin 4,
        -Real.log ((witnessCounts n i) ! : ℝ) ≤
          -K * (p i * Real.log (p i) + p i * Real.log K) +
            (witnessCounts n i : ℝ) + 2 * L := by
      intro i
      have hs := (abs_le.mp (abs_mul_log_sub_sub_log_factorial_le hn3 (hκ_le_n i))).2
      have hκ_eq : (witnessCounts n i : ℝ) = K * p i := by
        dsimp [p]; field_simp [hKne]
      have hm := mul_log_mul_eq hK_pos (hp_nonneg i)
      rw [← hκ_eq] at hm
      dsimp [L]
      linarith only [hs, hm]
    have hsum_stκ := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hst_κ i
    have hsum_stκ_rhs :
        ∑ i : Fin 4, (-K * (p i * Real.log (p i) + p i * Real.log K) +
            (witnessCounts n i : ℝ) + 2 * L) =
          -K * (∑ i : Fin 4, p i * Real.log (p i)) - K * Real.log K + K + 8 * L := by
      simp_rw [neg_mul, add_assoc, Finset.sum_add_distrib, Finset.sum_neg_distrib,
        ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul]
      have hK_cast : ∑ i : Fin 4, (witnessCounts n i : ℝ) = K := by dsimp [K]; exact_mod_cast hK
      rw [hp_sum1, hK_cast]
      simp [Finset.sum_const]
      ring
    rw [hsum_stκ_rhs, Finset.sum_neg_distrib] at hsum_stκ
    have hent_p : -(∑ i : Fin 4, p i * Real.log (p i)) ≤ 2 := by
      have h4 : ∑ i : Fin 4, (-p i * Real.log (p i)) ≤
          (∑ i : Fin 4, p i) * (Real.log 4 - Real.log (∑ i : Fin 4, p i)) :=
        sum_fin4_neg_mul_log_le hp_nonneg (by rw [hp_sum1]; norm_num)
      simp only [hp_sum1, Real.log_one, sub_zero, one_mul, neg_mul, Finset.sum_neg_distrib] at h4
      have hlog4 : Real.log 4 ≤ 2 := by
        have : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
        rw [this, Real.log_pow]
        push_cast
        linarith [Real.log_two_lt_d9]
      linarith only [h4, hlog4]
    have hKent : -K * (∑ i : Fin 4, p i * Real.log (p i)) ≤ 2 * K := by
      have hm := mul_le_mul_of_nonneg_left hent_p hK_pos.le
      linarith only [hm]
    have h10L_le_K : 10 * L ≤ K := by
      have hL2 : 30 * L ^ 2 ≤ 40 * L ^ 4 := by
        have h1 : 1 ≤ L ^ 2 := by
          calc
            (1 : ℝ) ≤ 10000 ^ 2 := by norm_num
            _ ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hL10000 2
        calc
          30 * L ^ 2 ≤ 40 * L ^ 2 := mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg L)
          _ = 40 * L ^ 2 * 1 := by ring
          _ ≤ 40 * L ^ 2 * L ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = 40 * L ^ 4 := by ring
      have hn_ge : 40 * L ^ 4 ≤ (n : ℝ) := (le_div_iff₀ (by positivity)).mp hnL4
      have h30 : 10 * L ≤ (n : ℝ) / (3 * L) := by
        rw [le_div_iff₀ (by positivity)]
        have hmul : 10 * L * (3 * L) = 30 * L ^ 2 := by ring
        linarith only [hmul, hL2, hn_ge]
      linarith only [h30, hK_lo_real]
    have hK4 : K * (∑ i : Fin 4, p i * centralClassErr n i) ≤ 4 * K := by
      have hlog_fm' : 100 * (n : ℝ) / L ^ 2 ≤
          Real.log (n ! : ℝ) + K * q -
            ∑ j : Fin 4, Real.log ((witnessCounts n j) ! : ℝ) -
            ∑ j : Fin 4, (witnessCounts n j : ℝ) *
              (Real.log ((witnessSize n j) ! : ℝ) + q * ((witnessSize n j).choose 2 : ℝ)) := hlog_fm
      have hst_n' : -(2 * L) ≤ (n : ℝ) * L - (n : ℝ) - Real.log (n ! : ℝ) := hst_n
      linarith only [hKbarE, hlog_fm', hfm0, hst_n', hsum_stκ, hKent, h10L_le_K]
    have hK4' : K * (∑ i : Fin 4, p i * centralClassErr n i) ≤ K * 4 := by linarith only [hK4]
    exact le_of_mul_le_mul_left hK4' hK_pos
  set F : Fin 4 → ℝ := fun i => centralClassErr n i + (q * α / 2) * ((i.val + 2 : ℕ) : ℝ)
  have hF_diff0 : ∀ i : Fin 4, |F i - F 0| ≤ 3 * |alphaConst| + 24 := by
    intro i
    set u₀ : ℕ := witnessSize n 0
    have hs0_ge10 : 10 ≤ u₀ := hsize 0
    have hu_eq : witnessSize n i = u₀ - i.val := by
      dsimp [witnessSize, u₀]; omega
    have hi_le_u₀ : i.val ≤ u₀ := by
      have := i.isLt; omega
    have hfac_ratio :
        Real.log ((u₀ ! : ℝ)) - Real.log (((witnessSize n i) ! : ℝ)) =
          Real.log ((u₀.descFactorial i.val : ℝ)) := by
      rw [hu_eq]
      have hid : ((u₀.descFactorial i.val : ℝ)) * (((u₀ - i.val) ! : ℝ)) = (u₀ ! : ℝ) := by
        exact_mod_cast descFactorial_mul_factorial_sub hi_le_u₀
      rw [← hid, Real.log_mul (Nat.cast_ne_zero.mpr (descFactorial_pos_of_le hi_le_u₀).ne')
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]
      ring
    have hq_bounds : (0.69 : ℝ) ≤ q ∧ q ≤ 0.70 := by
      dsimp [q]; constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
    have hu₀_lo : L ≤ ((u₀ - 3 : ℕ) : ℝ) := by
      have hα_2L : 2 * L ≤ α := by
        have hm : q * α ≤ 0.70 * α :=
          mul_le_mul_of_nonneg_right hq_bounds.2 (Nat.cast_nonneg _)
        change (3 / 2 : ℝ) * L ≤ q * α at hlo
        linarith only [hlo, hm, hL_pos]
      have hsub : ((u₀ - 3 : ℕ) : ℝ) = α - 5 := by
        have hs0 := hsize 0
        unfold witnessSize at hs0
        dsimp [u₀, witnessSize, α]
        rw [Nat.sub_sub]
        exact Nat.cast_sub (by omega)
      linarith only [hα_2L, hsub, hL10000]
    have hu₀_hi : (u₀ : ℝ) ≤ 3 * L := by
      have hα_3L : α ≤ 3 * L := by
        have hm : 0.69 * α ≤ q * α :=
          mul_le_mul_of_nonneg_right hq_bounds.1 (Nat.cast_nonneg _)
        change q * α ≤ 2 * L at hhi
        linarith only [hhi, hm, hL_pos]
      have hle : (u₀ : ℝ) ≤ α := by
        dsimp [u₀, witnessSize, α]
        exact_mod_cast Nat.sub_le (alphaNat n) 2
      linarith only [hα_3L, hle]
    have hdesc_bounds :
        (i.val : ℝ) * Real.log L ≤ Real.log ((u₀.descFactorial i.val : ℝ)) ∧
        Real.log ((u₀.descFactorial i.val : ℝ)) ≤ (i.val : ℝ) * (Real.log L + 2) := by
      have hlo_nat : (u₀ - 3) ^ i.val ≤ u₀.descFactorial i.val := by
        have hi3 : i.val ≤ 3 := by have := i.isLt; omega
        have h1 := factorial_sub_mul_pow_le_factorial hi_le_u₀
        have h2 := descFactorial_mul_factorial_sub hi_le_u₀
        have h3 : (u₀ - i.val) ^ i.val ≤ u₀.descFactorial i.val := by
          have hfac_pos : 0 < (u₀ - i.val) ! := Nat.factorial_pos _
          have hmul : (u₀ - i.val) ! * (u₀ - i.val) ^ i.val ≤
              (u₀ - i.val) ! * u₀.descFactorial i.val := by
            calc
              (u₀ - i.val) ! * (u₀ - i.val) ^ i.val ≤ u₀ ! := h1
              _ = u₀.descFactorial i.val * (u₀ - i.val) ! := h2.symm
              _ = (u₀ - i.val) ! * u₀.descFactorial i.val := Nat.mul_comm _ _
          exact Nat.le_of_mul_le_mul_left hmul hfac_pos
        exact le_trans (Nat.pow_le_pow_left (by omega) _) h3
      have hhi_nat : u₀.descFactorial i.val ≤ u₀ ^ i.val := descFactorial_le_pow _ _
      constructor
      · have hu3_pos : (0 : ℝ) < ((u₀ - 3 : ℕ) : ℝ) := lt_of_lt_of_le hL_pos hu₀_lo
        calc
          (i.val : ℝ) * Real.log L
              ≤ (i.val : ℝ) * Real.log (((u₀ - 3 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left (Real.log_le_log hL_pos hu₀_lo) (Nat.cast_nonneg _)
          _ = Real.log ((((u₀ - 3 : ℕ) : ℝ)) ^ i.val) := (Real.log_pow _ _).symm
          _ ≤ Real.log ((u₀.descFactorial i.val : ℝ)) := by
            refine Real.log_le_log (pow_pos hu3_pos _) ?_
            exact_mod_cast hlo_nat
      · have hlog3 : Real.log (3 * L) ≤ Real.log L + 2 := by
          rw [Real.log_mul (by norm_num) hL_pos.ne']
          have h3e : (3 : ℝ) ≤ Real.exp 2 := by
            have h1 := Real.add_one_le_exp (1 : ℝ)
            have hsq : (2 : ℝ) * 2 ≤ Real.exp 2 := by
              have hm := mul_le_mul h1 h1 (by norm_num) (Real.exp_pos 1).le
              rw [← Real.exp_add] at hm; norm_num at hm ⊢; exact hm
            linarith only [hsq]
          have hl3 := Real.log_le_log (by norm_num) h3e
          rw [Real.log_exp] at hl3
          linarith only [hl3]
        calc
          Real.log ((u₀.descFactorial i.val : ℝ))
              ≤ Real.log ((u₀ : ℝ) ^ i.val) := by
            refine Real.log_le_log (Nat.cast_pos.mpr (descFactorial_pos_of_le hi_le_u₀)) ?_
            exact_mod_cast hhi_nat
          _ = (i.val : ℝ) * Real.log (u₀ : ℝ) := Real.log_pow _ _
          _ ≤ (i.val : ℝ) * Real.log (3 * L) :=
            mul_le_mul_of_nonneg_left
              (Real.log_le_log (by exact_mod_cast (show 0 < u₀ by omega)) hu₀_hi)
              (Nat.cast_nonneg _)
          _ ≤ (i.val : ℝ) * (Real.log L + 2) :=
            mul_le_mul_of_nonneg_left hlog3 (Nat.cast_nonneg _)
    have hchoose_diff :
        ((witnessSize n i).choose 2 : ℝ) - (u₀.choose 2 : ℝ) =
          -(i.val : ℝ) * α + (i.val : ℝ) * ((i.val : ℝ) + 5) / 2 := by
      rw [cast_choose_two, cast_choose_two, hu_eq, Nat.cast_sub hi_le_u₀]
      have hu₀_cast : (u₀ : ℝ) = α - 2 := by
        have hs0 := hsize 0
        unfold witnessSize at hs0
        dsimp [u₀, witnessSize, α]
        exact Nat.cast_sub (by omega)
      rw [hu₀_cast]; ring
    have hF_sub_eq :
        F i - F 0 =
          (i.val : ℝ) * (L - q * α / 2 - Real.log L) -
            (Real.log ((u₀.descFactorial i.val : ℝ)) - (i.val : ℝ) * Real.log L) -
            (i.val : ℝ) + q * ((i.val : ℝ) * ((i.val : ℝ) + 5) / 2) := by
      dsimp [F, centralClassErr, L, q]
      have hu_sub : (witnessSize n i : ℝ) - (u₀ : ℝ) = -(i.val : ℝ) := by
        rw [hu_eq, Nat.cast_sub hi_le_u₀]; ring
      have hi2_sub : ((i.val + 2 : ℕ) : ℝ) - ((0 + 2 : ℕ) : ℝ) = (i.val : ℝ) := by
        push_cast; ring
      linear_combination
        -hfac_ratio + Real.log 2 * hchoose_diff + (1 - Real.log (n : ℝ)) * hu_sub +
          (Real.log 2 * α / 2) * hi2_sub
    rw [hF_sub_eq]
    have hL_qα : |L - q * α / 2 - Real.log L| ≤ |alphaConst| + 1 := by
      have hid : L - q * α / 2 - Real.log L = -alphaConst + q * phaseDelta n / 2 := by
        change q * α = 2 * L - 2 * Real.log L + 2 * alphaConst - q * phaseDelta n at hqα
        linarith only [hqα]
      rw [hid, abs_le]
      have hc := abs_le.mp (le_refl |alphaConst|)
      have hδ := phaseDelta_mem_Icc n
      have hqδ_nonneg : 0 ≤ q * phaseDelta n :=
        mul_nonneg (by linarith only [hq_bounds.1]) hδ.1
      have hqδ_le : q * phaseDelta n ≤ 1 := by
        calc
          q * phaseDelta n ≤ 0.70 * 1 :=
            mul_le_mul hq_bounds.2 hδ.2 hδ.1 (by norm_num)
          _ ≤ 1 := by norm_num
      exact ⟨by linarith only [hc.2, hqδ_nonneg], by linarith only [hc.1, hqδ_le]⟩
    have hi3_r : (i.val : ℝ) ≤ 3 := by exact_mod_cast (show i.val ≤ 3 by have := i.isLt; omega)
    have hi0_r : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
    have habs1 : |(i.val : ℝ) * (L - q * α / 2 - Real.log L)| ≤ 3 * |alphaConst| + 3 := by
      rw [abs_mul, abs_of_nonneg hi0_r]
      calc
        (i.val : ℝ) * |L - q * α / 2 - Real.log L|
            ≤ 3 * (|alphaConst| + 1) :=
          mul_le_mul hi3_r hL_qα (abs_nonneg _) (by norm_num)
        _ = 3 * |alphaConst| + 3 := by ring
    have hrem_lo : 0 ≤ Real.log ((u₀.descFactorial i.val : ℝ)) - (i.val : ℝ) * Real.log L := by
      linarith only [hdesc_bounds.1]
    have hrem_hi : Real.log ((u₀.descFactorial i.val : ℝ)) - (i.val : ℝ) * Real.log L ≤ 6 := by
      have h2i : (i.val : ℝ) * 2 ≤ 6 := by linarith only [hi3_r]
      linarith only [hdesc_bounds.2, h2i]
    have hquad_lo : 0 ≤ q * ((i.val : ℝ) * ((i.val : ℝ) + 5) / 2) := by positivity
    have hquad_hi : q * ((i.val : ℝ) * ((i.val : ℝ) + 5) / 2) ≤ 12 := by
      have hprod_hi : (i.val : ℝ) * ((i.val : ℝ) + 5) / 2 ≤ 12 := by
        have hm : (i.val : ℝ) * ((i.val : ℝ) + 5) ≤ 3 * 8 :=
          mul_le_mul hi3_r (by linarith only [hi3_r]) (by positivity) (by norm_num)
        linarith only [hm]
      calc
        q * ((i.val : ℝ) * ((i.val : ℝ) + 5) / 2) ≤ 0.70 * 12 :=
          mul_le_mul hq_bounds.2 hprod_hi (by positivity) (by norm_num)
        _ ≤ 12 := by norm_num
    rw [abs_le]
    have ha1 := abs_le.mp habs1
    have hac0 := abs_nonneg alphaConst
    exact ⟨by linarith only [ha1.1, hrem_hi, hi3_r, hquad_lo, hac0],
      by linarith only [ha1.2, hrem_lo, hi0_r, hquad_hi, hac0]⟩
  have hpF_bar : ∑ j : Fin 4, p j * F j =
      (∑ j : Fin 4, p j * centralClassErr n j) + (q * α / 2) * T := by
    dsimp [F]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← hT_mean, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have hE_upper : ∀ i : Fin 4,
      centralClassErr n i ≤ (q * α / 2) * (T - ((i.val + 2 : ℕ) : ℝ)) + (6 * |alphaConst| + 52) := by
    intro i
    have hFi : F i - ∑ j : Fin 4, p j * F j ≤ 6 * |alphaConst| + 48 := by
      have hsum_id : F i - ∑ j : Fin 4, p j * F j = ∑ j : Fin 4, p j * (F i - F j) := by
        simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp_sum1, one_mul]
      rw [hsum_id]
      calc
        ∑ j : Fin 4, p j * (F i - F j)
            ≤ ∑ j : Fin 4, p j * (6 * |alphaConst| + 48) := by
          refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hp_nonneg j)
          have h1 := (abs_le.mp (hF_diff0 i)).2
          have h2 := (abs_le.mp (hF_diff0 j)).1
          linarith only [h1, h2]
        _ = 6 * |alphaConst| + 48 := by rw [← Finset.sum_mul, hp_sum1, one_mul]
    have hEi_eq : centralClassErr n i = F i - (q * α / 2) * ((i.val + 2 : ℕ) : ℝ) := by
      dsimp [F]; ring
    linarith only [hFi, hpF_bar, hbarE, hEi_eq]
  calc
    ∑ i : Fin 4, y i * centralClassErr n i
        ≤ ∑ i : Fin 4, y i * ((q * α / 2) * (T - ((i.val + 2 : ℕ) : ℝ)) + (6 * |alphaConst| + 52)) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hE_upper i) (hy_nonneg i)
    _ = (q * α / 2) * (T * Y - I_y) + (6 * |alphaConst| + 52) * Y := by
      dsimp [Y, I_y]
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring

/-- Eventually on `diagBox n`, whenever `n / (log n)^6 < diagMass n v` and
`n < 1024 * (n - diagMass n v)`, we have `diagWeight n v ≤ Real.exp (44 * Real.log (n : ℝ))`. -/
theorem eventually_diagWeight_le_of_central_range :
    ∀ᶠ n : ℕ in atTop,
      ∀ v ∈ diagBox n,
        (n : ℝ) / (Real.log (n : ℝ)) ^ 6 < (diagMass n v : ℝ) →
        n < 1024 * (n - diagMass n v) →
        diagWeight n v ≤ Real.exp (44 * Real.log (n : ℝ)) := by
  obtain ⟨C_sep, hC_pos, hev_sep⟩ := eventually_continuous_roots_separation
  set C_diag : ℝ := 6300 + 6 * |alphaConst|
  have hC_diag_pos : 0 < C_diag := by dsimp [C_diag]; linarith [abs_nonneg alphaConst]
  have hL : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  have hratio : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact h0.comp hL
  have hthresh : 0 < min (1 / (40 * C_sep)) (1 / (120000 * C_diag)) :=
    lt_min (by positivity) (by positivity)
  filter_upwards [eventually_alphaNat_regime, eventually_witnessCounts_spec, hev_sep,
    tendsto_alphaNat_atTop.eventually_ge_atTop 7000,
    hL.eventually_ge_atTop 10000,
    hll.eventually_ge_atTop 2,
    hratio.eventually (ge_mem_nhds hthresh),
    (tendsto_nat_div_log_pow_atTop 4).eventually_ge_atTop 40] with
      n ⟨hn16, _, _, hqα, hlo, hhi⟩ ⟨hK, hn, hsize, hcounts_lb, hlog_fm⟩
      ⟨_, _, _, hTF_loc, _, _, hsF_lo, hsF_hi, _⟩
      hα7000 hL10000 hll2 hrat_both hnL4
      v hv hm_gt hrem_gt
  set L : ℝ := Real.log (n : ℝ)
  set q : ℝ := Real.log 2
  set α : ℕ := alphaNat n
  set K : ℕ := kCoSeed n
  set m : ℕ := diagMass n v
  set w : ℕ := n - m
  have hL10000' : (10000 : ℝ) ≤ L := hL10000
  have hll2' : (2 : ℝ) ≤ Real.log L := hll2
  have hnL4' : (40 : ℝ) ≤ (n : ℝ) / L ^ 4 := hnL4
  have hL_pos : 0 < L := by linarith only [hL10000']
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hrat_sep : Real.log L / L ≤ 1 / (40 * C_sep) := (le_min_iff.mp hrat_both).1
  have hrat_diag : Real.log L / L ≤ 1 / (120000 * C_diag) := (le_min_iff.mp hrat_both).2
  have hv_le := mem_diagBox_iff.mp hv
  have hm_le : m ≤ n := diagMass_le_of_mem_diagBox hn hv
  have hw_pos : 0 < w := by omega
  have hw_pos_r : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw_pos
  have hK_pos_nat : 0 < K := by
    have h1 := (hcounts_lb 0).1
    have hle : witnessCounts n 0 ≤ K := by
      rw [← hK]
      exact Finset.single_le_sum (f := witnessCounts n) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ 0)
    omega
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK_pos_nat
  -- Step 1: Bounds on `K` and `seedDeficit n ≤ 3.95`
  have hsF_pos : 0 < sFourCo n := by linarith only [hsF_lo, hL_pos]
  have hK_lo_real : (n : ℝ) / (3 * L) ≤ (K : ℝ) := by
    dsimp [K, kCoSeed]
    push_cast
    have h1 : (n : ℝ) / (3 * L) ≤ (n : ℝ) / sFourCo n :=
      div_le_div_of_nonneg_left hn_pos.le hsF_pos hsF_hi
    have h2 : (n : ℝ) / sFourCo n ≤ (⌈(n : ℝ) / sFourCo n⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : 0 ≤ (⌈1000 * (n : ℝ) / (Real.log (n : ℝ)) ^ 4⌉₊ : ℝ) := Nat.cast_nonneg _
    linarith only [h1, h2, h3]
  set T : ℝ := seedDeficit n
  have hT_hi : T ≤ 3.95 := by
    have hKne : (K : ℝ) ≠ 0 := hK_pos.ne'
    have hT_sub_TF : T - TFour n = ((K : ℝ) * sFourCo n - (n : ℝ)) / (K : ℝ) := by
      dsimp [T, seedDeficit, K]
      unfold sFourCo
      have hKne' : (kCoSeed n : ℝ) ≠ 0 := hKne
      field_simp [hKne']
      ring
    have hT_sub_hi : T - TFour n ≤ 10000 / L ^ 2 := by
      rw [hT_sub_TF, div_le_iff₀ hK_pos]
      have hK_le_add : (K : ℝ) ≤ (n : ℝ) / sFourCo n + 1000 * (n : ℝ) / L ^ 4 + 2 := by
        dsimp [K, kCoSeed]
        push_cast
        have hc1 := (Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) / sFourCo n by positivity)).le
        have hc2 := (Nat.ceil_lt_add_one (show 0 ≤ 1000 * (n : ℝ) / L ^ 4 by positivity)).le
        change (⌈(n : ℝ) / sFourCo n⌉₊ : ℝ) + (⌈1000 * (n : ℝ) / L ^ 4⌉₊ : ℝ) ≤
          (n : ℝ) / sFourCo n + 1000 * (n : ℝ) / L ^ 4 + 2
        linarith only [hc1, hc2]
      have hm := mul_le_mul_of_nonneg_right hK_le_add hsF_pos.le
      have hns : ((n : ℝ) / sFourCo n + 1000 * (n : ℝ) / L ^ 4 + 2) * sFourCo n =
          (n : ℝ) + (1000 * (n : ℝ) / L ^ 4 + 2) * sFourCo n := by
        field_simp [hsF_pos.ne']; ring
      rw [hns] at hm
      have h1002 : 1000 * (n : ℝ) / L ^ 4 + 2 ≤ 1002 * ((n : ℝ) / L ^ 4) := by
        have hrew : 1000 * (n : ℝ) / L ^ 4 = 1000 * ((n : ℝ) / L ^ 4) := by ring
        linarith only [hrew, hnL4']
      have hs3 := mul_le_mul h1002 hsF_hi hsF_pos.le (by positivity)
      calc
        (K : ℝ) * sFourCo n - (n : ℝ) ≤ 1002 * ((n : ℝ) / L ^ 4) * (3 * L) := by
          linarith only [hm, hs3]
        _ = 3006 * ((n : ℝ) / L ^ 3) := by field_simp [hL_pos.ne']; ring
        _ ≤ (10000 / 3 : ℝ) * ((n : ℝ) / L ^ 3) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ = 10000 / L ^ 2 * ((n : ℝ) / (3 * L)) := by field_simp [hL_pos.ne']
        _ ≤ 10000 / L ^ 2 * (K : ℝ) := mul_le_mul_of_nonneg_left hK_lo_real (by positivity)
    have hTδ_hi : targetDeficit (phaseDelta n) ≤ 3.886 := by
      unfold targetDeficit
      have h2q : 2 / Real.log 2 ≤ 2.886 := by
        rw [div_le_iff₀ (Real.log_pos (by norm_num))]
        linarith [Real.log_two_gt_d9]
      linarith only [(phaseDelta_mem_Icc n).1, h2q]
    have hTF_close : TFour n - targetDeficit (phaseDelta n) ≤ 1 / 40 := by
      have hm := mul_le_mul_of_nonneg_left hrat_sep hC_pos.le
      have hs : C_sep * (1 / (40 * C_sep)) = 1 / 40 := by field_simp [hC_pos.ne']
      linarith only [(abs_le.mp hTF_loc).2, hm, hs]
    have h10000_small : 10000 / L ^ 2 ≤ 1 / 10000 := by
      rw [div_le_iff₀ (by positivity)]
      have hsq : (10000 : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hL10000' 2
      linarith only [hsq]
    linarith only [hT_sub_hi, hTδ_hi, hTF_close, h10000_small]
  -- Step 2: Normalized variables `p_i`, `y_i`, `z_i`, `Y`, `R`, `ρ`
  set p : Fin 4 → ℝ := fun i => (witnessCounts n i : ℝ) / (K : ℝ)
  set y : Fin 4 → ℝ := fun i => (v i : ℝ) / (K : ℝ)
  set z : Fin 4 → ℝ := fun i => p i - y i
  have hy_nonneg : ∀ i, 0 ≤ y i := fun i => div_nonneg (Nat.cast_nonneg _) hK_pos.le
  have hy_le_p : ∀ i, y i ≤ p i := fun i =>
    div_le_div_of_nonneg_right (by exact_mod_cast hv_le i) hK_pos.le
  have hz_nonneg : ∀ i, 0 ≤ z i := fun i => sub_nonneg.mpr (hy_le_p i)
  have hp_sum1 : ∑ i : Fin 4, p i = 1 := by
    dsimp [p]
    rw [← Finset.sum_div]
    have hsum_cast : ∑ i : Fin 4, (witnessCounts n i : ℝ) = (K : ℝ) := by exact_mod_cast hK
    rw [hsum_cast, div_self hK_pos.ne']
  have hp_le1 : ∀ i, p i ≤ 1 := by
    intro i
    rw [← hp_sum1]
    exact Finset.single_le_sum (fun j _ => (hy_nonneg j).trans (hy_le_p j)) (Finset.mem_univ i)
  set Y : ℝ := ∑ i : Fin 4, y i
  set R : ℝ := ∑ i : Fin 4, z i
  have hRY_sum : R + Y = 1 := by
    dsimp [R, Y, z]
    rw [Finset.sum_sub_distrib, hp_sum1]
    ring
  have hT_mean : ∑ i : Fin 4, ((i.val + 2 : ℕ) : ℝ) * p i = T := by
    have hn_cast : ∑ i : Fin 4, (witnessSize n i : ℝ) * (witnessCounts n i : ℝ) = (n : ℝ) := by
      exact_mod_cast hn
    have hu_cast : ∀ i : Fin 4, (witnessSize n i : ℝ) = (α : ℝ) - ((i.val + 2 : ℕ) : ℝ) := by
      intro i
      have hs0 := hsize 0
      unfold witnessSize at hs0 ⊢
      exact Nat.cast_sub (by have := i.isLt; omega)
    have h1 : ∑ i : Fin 4, ((i.val + 2 : ℕ) : ℝ) * (witnessCounts n i : ℝ) =
        (α : ℝ) * (K : ℝ) - (n : ℝ) := by
      have hid : ∑ i : Fin 4, ((i.val + 2 : ℕ) : ℝ) * (witnessCounts n i : ℝ) =
          (α : ℝ) * (∑ i : Fin 4, (witnessCounts n i : ℝ)) -
            ∑ i : Fin 4, (witnessSize n i : ℝ) * (witnessCounts n i : ℝ) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hu_cast i]; ring
      have hK_cast : ∑ i : Fin 4, (witnessCounts n i : ℝ) = (K : ℝ) := by exact_mod_cast hK
      rw [hid, hK_cast, hn_cast]
    dsimp [p, T, seedDeficit, K, α] at h1 ⊢
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div, h1]
    have hKne' : (kCoSeed n : ℝ) ≠ 0 := hK_pos.ne'
    field_simp [hKne']
  have hn_eq_KT : (n : ℝ) = (K : ℝ) * ((α : ℝ) - T) := by
    dsimp [T, seedDeficit, K, α]
    have hKne' : (kCoSeed n : ℝ) ≠ 0 := hK_pos.ne'
    field_simp [hKne']
    ring
  set I_y : ℝ := ∑ i : Fin 4, ((i.val + 2 : ℕ) : ℝ) * y i
  set I_r : ℝ := ∑ i : Fin 4, ((i.val + 2 : ℕ) : ℝ) * z i
  have hm_eq_KY : (m : ℝ) = (K : ℝ) * ((α : ℝ) * Y - I_y) := by
    have hm_cast : (m : ℝ) = ∑ i : Fin 4, (witnessSize n i : ℝ) * (v i : ℝ) := by
      dsimp [m, diagMass]; push_cast; rfl
    have hv_Ky : ∀ i : Fin 4, (v i : ℝ) = (K : ℝ) * y i := by
      intro i; dsimp [y]; have hKne : (K : ℝ) ≠ 0 := hK_pos.ne'; field_simp [hKne]
    have hu_cast : ∀ i : Fin 4, (witnessSize n i : ℝ) = (α : ℝ) - ((i.val + 2 : ℕ) : ℝ) := by
      intro i
      have hs0 := hsize 0
      unfold witnessSize at hs0 ⊢
      exact Nat.cast_sub (by have := i.isLt; omega)
    have hrhs :
        (K : ℝ) * ((α : ℝ) * (∑ i : Fin 4, y i) - ∑ i : Fin 4, ((i.val + 2 : ℕ) : ℝ) * y i) =
          ∑ i : Fin 4, ((K : ℝ) * (α : ℝ) * y i - (K : ℝ) * (((i.val + 2 : ℕ) : ℝ) * y i)) := by
      rw [mul_sub, ← mul_assoc, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [hm_cast]
    simp_rw [hu_cast, hv_Ky]
    dsimp [Y, I_y]
    rw [hrhs]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hIy_nonneg : 0 ≤ I_y :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hy_nonneg i)
  have hα_ge7000 : (7000 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα7000
  have hY_gt : 1 / (2 * L ^ 6) < Y := by
    have hm_le_KαY : (m : ℝ) ≤ (K : ℝ) * ((α : ℝ) * Y) := by
      rw [hm_eq_KY]
      have h1 : 0 ≤ (K : ℝ) * I_y := mul_nonneg hK_pos.le hIy_nonneg
      have hexp : (K : ℝ) * ((α : ℝ) * Y - I_y) = (K : ℝ) * ((α : ℝ) * Y) - (K : ℝ) * I_y :=
        mul_sub _ _ _
      linarith only [h1, hexp]
    have hKα_le_2n : (K : ℝ) * (α : ℝ) ≤ 2 * (n : ℝ) := by
      have h1 : (α : ℝ) ≤ 2 * ((α : ℝ) - T) := by linarith only [hT_hi, hα_ge7000]
      have h2 := mul_le_mul_of_nonneg_left h1 hK_pos.le
      have hexp : (K : ℝ) * (2 * ((α : ℝ) - T)) = 2 * ((K : ℝ) * ((α : ℝ) - T)) := by ring
      linarith only [hn_eq_KT, h2, hexp]
    have hm_le_2nY : (m : ℝ) ≤ 2 * (n : ℝ) * Y := by
      have hY0 : 0 ≤ Y := Finset.sum_nonneg fun i _ => hy_nonneg i
      calc
        (m : ℝ) ≤ (K : ℝ) * ((α : ℝ) * Y) := hm_le_KαY
        _ = ((K : ℝ) * (α : ℝ)) * Y := (mul_assoc _ _ _).symm
        _ ≤ (2 * (n : ℝ)) * Y := mul_le_mul_of_nonneg_right hKα_le_2n hY0
        _ = 2 * (n : ℝ) * Y := by ring
    have hgt : (n : ℝ) / L ^ 6 < 2 * (n : ℝ) * Y := lt_of_lt_of_le hm_gt hm_le_2nY
    rw [div_lt_iff₀ (by positivity)] at hgt ⊢
    have hgt' : (n : ℝ) * 1 < (n : ℝ) * (Y * (2 * L ^ 6)) := by
      have hrew : 2 * (n : ℝ) * Y * L ^ 6 = (n : ℝ) * (Y * (2 * L ^ 6)) := by ring
      linarith only [hgt, hrew]
    exact lt_of_mul_lt_mul_left hgt' hn_pos.le
  have hY_pos : 0 < Y := lt_trans (by positivity) hY_gt
  have hY_le1 : Y ≤ 1 := by
    have hR0 : 0 ≤ R := Finset.sum_nonneg fun i _ => hz_nonneg i
    linarith only [hRY_sum, hR0]
  set ρ : ℝ := (w : ℝ) / (n : ℝ)
  have hρ_pos : 0 < ρ := div_pos hw_pos_r hn_pos
  have hρ_gt : 1 / 1024 < ρ := by
    dsimp [ρ]
    rw [div_lt_div_iff₀ (by norm_num) hn_pos]
    have hc : (n : ℝ) < 1024 * (w : ℝ) := by exact_mod_cast hrem_gt
    linarith only [hc]
  have hρ_sub_R : |ρ - R| ≤ 3 * Y / ((α : ℝ) - T) := by
    have hw_cast : (w : ℝ) = (n : ℝ) - (m : ℝ) := Nat.cast_sub hm_le
    have hαT_pos : 0 < (α : ℝ) - T := by linarith only [hα_ge7000, hT_hi]
    have hdiff_eq : ρ - R = (I_y - T * Y) / ((α : ℝ) - T) := by
      have hR_eq : R = 1 - Y := by linarith only [hRY_sum]
      have hKne : (K : ℝ) ≠ 0 := hK_pos.ne'
      dsimp [ρ]
      rw [hw_cast, hm_eq_KY, hn_eq_KT, hR_eq]
      field_simp [hKne, hαT_pos.ne']
      ring
    rw [hdiff_eq, abs_div, abs_of_pos hαT_pos]
    refine div_le_div_of_nonneg_right ?_ hαT_pos.le
    have hT_ge2 : 2 ≤ T := by
      calc
        (2 : ℝ) = 2 * 1 := (mul_one 2).symm
        _ = 2 * ∑ i : Fin 4, p i := by rw [hp_sum1]
        _ = ∑ i : Fin 4, 2 * p i := Finset.mul_sum _ _ _
        _ ≤ ∑ i : Fin 4, ((i.val + 2 : ℕ) : ℝ) * p i := by
          refine Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right ?_ ((hy_nonneg i).trans (hy_le_p i))
          exact_mod_cast (show 2 ≤ i.val + 2 by omega)
        _ = T := hT_mean
    have hsum_diff : I_y - T * Y = ∑ i : Fin 4, (((i.val + 2 : ℕ) : ℝ) - T) * y i := by
      dsimp [I_y, Y]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum_diff]
    calc
      |∑ i : Fin 4, (((i.val + 2 : ℕ) : ℝ) - T) * y i|
          ≤ ∑ i : Fin 4, |(((i.val + 2 : ℕ) : ℝ) - T) * y i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 4, 3 * y i := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (hy_nonneg i)]
        refine mul_le_mul_of_nonneg_right (abs_le.mpr ⟨?_, ?_⟩) (hy_nonneg i)
        · have hi2 : (2 : ℝ) ≤ ((i.val + 2 : ℕ) : ℝ) := by
            exact_mod_cast (by omega : 2 ≤ i.val + 2)
          linarith only [hi2, hT_hi]
        · have hi5 : ((i.val + 2 : ℕ) : ℝ) ≤ 5 := by
            exact_mod_cast (show i.val + 2 ≤ 5 by have := i.isLt; omega)
          linarith only [hi5, hT_ge2]
      _ = 3 * Y := (Finset.mul_sum _ _ _).symm
  have hR_lo : 1 / 2048 ≤ R := by
    have hdiff_small : |ρ - R| ≤ 1 / 2048 := by
      refine hρ_sub_R.trans ?_
      rw [div_le_div_iff₀ (by linarith only [hα_ge7000, hT_hi]) (by norm_num)]
      linarith only [hY_le1, hα_ge7000, hT_hi]
    linarith only [(abs_le.mp hdiff_small).2, hρ_gt]
  -- Step 3 & Step 4: Invoke modular Stirling and `∑ y_i E_i` lemmas
  have hpos_D := diagWeight_pos_of_mem_diagBox hn hv
  rw [← Real.exp_log hpos_D]
  apply Real.exp_le_exp.mpr
  have hlogD_stirling :
      Real.log (diagWeight n v) ≤
        (n : ℝ) * ρ * Real.log ρ +
          (K : ℝ) * (∑ i : Fin 4,
            (2 * (p i * Real.log (p i)) - 2 * (z i * Real.log (z i)) -
              y i * Real.log (y i) - y i + y i * centralClassErr n i)) + 44 * L :=
    central_log_diagWeight_stirling (by omega) hK_pos hn hsize hv hw_pos
  have hsum_yE :
      ∑ i : Fin 4, y i * centralClassErr n i ≤
        (q * (α : ℝ) / 2) * (T * Y - I_y) + (6 * |alphaConst| + 52) * Y :=
    central_sum_yE_le hn16 hqα hlo hhi hK hn hsize hlog_fm hL10000' hnL4'
      hK_pos hK_lo_real hy_nonneg
  -- Step 5: Assemble `(7.20)` + `(7.23)` and conclude `Real.log (diagWeight n v) ≤ 44 * L`
  have hent_sum :
      ∑ i : Fin 4,
        (2 * (p i * Real.log (p i)) - 2 * (z i * Real.log (z i)) - y i * Real.log (y i) - y i) ≤
      Y * (3 - Real.log Y) := by
    have h1 : ∑ i : Fin 4,
        (2 * (p i * Real.log (p i)) - 2 * (z i * Real.log (z i)) - y i * Real.log (y i) - y i) ≤
        ∑ i : Fin 4, y i * (1 - Real.log (y i)) :=
      Finset.sum_le_sum fun i _ => profile_entropy_term_le (hy_nonneg i) (hy_le_p i) (hp_le1 i)
    have hsplit : ∑ i : Fin 4, y i * (1 - Real.log (y i)) =
        Y + ∑ i : Fin 4, (-y i * Real.log (y i)) := by
      dsimp [Y]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h2 : ∑ i : Fin 4, (-y i * Real.log (y i)) ≤ Y * (Real.log 4 - Real.log Y) :=
      sum_fin4_neg_mul_log_le hy_nonneg hY_pos
    have hlog4 : Real.log 4 ≤ 2 := by
      have : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
      rw [this, Real.log_pow]
      push_cast
      linarith [Real.log_two_lt_d9]
    have hm4 := mul_le_mul_of_nonneg_left
      (show Real.log 4 - Real.log Y ≤ 2 - Real.log Y by linarith only [hlog4]) hY_pos.le
    have hrew : Y + Y * (2 - Real.log Y) = Y * (3 - Real.log Y) := by ring
    linarith only [h1, hsplit, h2, hm4, hrew]
  have hρR_bound :
      (n : ℝ) * ρ * Real.log ρ ≤ (K : ℝ) * (α : ℝ) * R * Real.log R + 6185 * (K : ℝ) * Y := by
    have hdiff_le1 : |ρ - R| ≤ 1 := by
      refine hρ_sub_R.trans ?_
      rw [div_le_one (by linarith only [hα_ge7000, hT_hi])]
      linarith only [hY_le1, hα_ge7000, hT_hi]
    have hm := mul_log_sub_mul_log_le hρ_pos hR_lo (by linarith only [hRY_sum, hY_pos]) hdiff_le1
    have hn_mul : (n : ℝ) * (ρ * Real.log ρ - R * Real.log R) ≤ 6180 * (K : ℝ) * Y := by
      calc
        (n : ℝ) * (ρ * Real.log ρ - R * Real.log R)
            ≤ (n : ℝ) * (2060 * |ρ - R|) := mul_le_mul_of_nonneg_left hm hn_pos.le
        _ ≤ ((K : ℝ) * ((α : ℝ) - T)) * (2060 * (3 * Y / ((α : ℝ) - T))) := by
          rw [hn_eq_KT]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hρ_sub_R (by norm_num))
            (mul_nonneg hK_pos.le (by linarith only [hα_ge7000, hT_hi]))
        _ = 6180 * (K : ℝ) * Y := by
          have hαT_ne : (α : ℝ) - T ≠ 0 := by linarith only [hα_ge7000, hT_hi]
          field_simp [hαT_ne]
          ring
    have hR_pos : 0 < R := lt_of_lt_of_le (by norm_num) hR_lo
    have hRlogR_neg : -R * Real.log R ≤ Y := by
      have h1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hR_pos)
      rw [Real.log_inv] at h1
      have hm1 := mul_le_mul_of_nonneg_left h1 hR_pos.le
      have hrhs : R * (R⁻¹ - 1) = 1 - R := by
        rw [mul_sub, mul_inv_cancel₀ hR_pos.ne', mul_one]
      have hrew : R * (-Real.log R) = -R * Real.log R := by ring
      linarith only [hRY_sum, hm1, hrhs, hrew]
    have hKT_term : -(K : ℝ) * T * (R * Real.log R) ≤ 5 * (K : ℝ) * Y := by
      have hT5 : T ≤ 5 := by linarith only [hT_hi]
      have hlogR_le0 : Real.log R ≤ 0 := Real.log_nonpos hR_pos.le (by linarith only [hRY_sum, hY_pos])
      have hneg_nonneg : 0 ≤ -R * Real.log R := by
        rw [neg_mul, neg_nonneg]
        exact mul_nonpos_of_nonneg_of_nonpos hR_pos.le hlogR_le0
      calc
        -(K : ℝ) * T * (R * Real.log R)
            = ((K : ℝ) * T) * (-R * Real.log R) := by ring
        _ ≤ ((K : ℝ) * 5) * Y :=
          mul_le_mul (mul_le_mul_of_nonneg_left hT5 hK_pos.le) hRlogR_neg
            hneg_nonneg (by positivity)
        _ = 5 * (K : ℝ) * Y := by ring
    have hsplit_n :
        (n : ℝ) * ρ * Real.log ρ - (K : ℝ) * (α : ℝ) * R * Real.log R =
          (n : ℝ) * (ρ * Real.log ρ - R * Real.log R) - (K : ℝ) * T * (R * Real.log R) := by
      rw [hn_eq_KT]; ring
    linarith only [hn_mul, hKT_term, hsplit_n]
  have hTY_Ir : T * Y - I_y = I_r - T * R := by
    have hI_sum : I_r + I_y = T := by
      dsimp [I_r, I_y, z]
      rw [← Finset.sum_add_distrib, ← hT_mean]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hY1R : Y = 1 - R := by linarith only [hRY_sum]
    have hIy_eq : I_y = T - I_r := by linarith only [hI_sum]
    rw [hY1R, hIy_eq]; ring
  have hzp_eq : ∀ i : Fin 4, z i + y i = p i := fun i => sub_add_cancel _ _
  have hsum_zy : ∑ i : Fin 4, ((i.val + 2 : ℕ) : ℝ) * (z i + y i) = T := by
    simp_rw [hzp_eq]
    exact hT_mean
  have hrate' :
      R * Real.log R + (q / 2) * (I_r - T * R) ≤ -Y / 30000 := by
    have hrate :
        R * Real.log R +
          (q / 2) * (I_r - (∑ i : Fin 4, ((i.val + 2 : ℕ) : ℝ) * (z i + y i)) * R) ≤
        -Y / 30000 :=
      rate_phi_le_neg_div hy_nonneg hz_nonneg hRY_sum hR_lo (by rw [hsum_zy]; exact hT_hi)
    rwa [hsum_zy] at hrate
  have hneg_logY : -Real.log Y ≤ 7 * Real.log L := by
    have hlog_gt := Real.log_le_log (by positivity) hY_gt.le
    rw [Real.log_div (by norm_num) (by positivity), Real.log_one, zero_sub,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog_gt
    push_cast at hlog_gt
    have hq1 : Real.log 2 ≤ 2 := by linarith [Real.log_two_lt_d9]
    linarith only [hll2', hlog_gt, hq1]
  have hα_ge_2L : 2 * L ≤ (α : ℝ) := by
    have hq_70 : q ≤ 0.70 := by dsimp [q]; linarith [Real.log_two_lt_d9]
    have hm : q * (α : ℝ) ≤ 0.70 * (α : ℝ) :=
      mul_le_mul_of_nonneg_right hq_70 (Nat.cast_nonneg _)
    change (3 / 2 : ℝ) * L ≤ q * (α : ℝ) at hlo
    linarith only [hlo, hm, hL_pos]
  have hdom :
      (K : ℝ) * (α : ℝ) * (-Y / 30000) + C_diag * (K : ℝ) * Y * (1 - Real.log Y) ≤ 0 := by
    have h1logY : 1 - Real.log Y ≤ 8 * Real.log L := by linarith only [hneg_logY, hll2']
    have hll_le : 8 * C_diag * Real.log L ≤ (α : ℝ) / 30000 := by
      have hm := (div_le_iff₀ hL_pos).mp hrat_diag
      have h1 : 8 * C_diag * Real.log L ≤ (2 / 30000 : ℝ) * L := by
        have hstep : 120000 * C_diag * Real.log L ≤ L := by
          calc
            120000 * C_diag * Real.log L
                ≤ 120000 * C_diag * (1 / (120000 * C_diag) * L) :=
              mul_le_mul_of_nonneg_left hm (by positivity)
            _ = L := by field_simp [hC_diag_pos.ne']
        linarith only [hstep]
      linarith only [h1, hα_ge_2L]
    have hKY_pos : 0 < (K : ℝ) * Y := mul_pos hK_pos hY_pos
    have hrew :
        (K : ℝ) * (α : ℝ) * (-Y / 30000) + C_diag * (K : ℝ) * Y * (1 - Real.log Y) ≤
          ((K : ℝ) * Y) * (-(α : ℝ) / 30000 + 8 * C_diag * Real.log L) := by
      have hm := mul_le_mul_of_nonneg_left h1logY
        (mul_nonneg (mul_nonneg hC_diag_pos.le hK_pos.le) hY_pos.le)
      have hid : (K : ℝ) * (α : ℝ) * (-Y / 30000) + C_diag * (K : ℝ) * Y * (8 * Real.log L) =
          ((K : ℝ) * Y) * (-(α : ℝ) / 30000 + 8 * C_diag * Real.log L) := by ring
      linarith only [hm, hid]
    have hnonpos : ((K : ℝ) * Y) * (-(α : ℝ) / 30000 + 8 * C_diag * Real.log L) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hKY_pos.le (by linarith only [hll_le])
    linarith only [hrew, hnonpos]
  have hsum_split :
      ∑ i : Fin 4,
        (2 * (p i * Real.log (p i)) - 2 * (z i * Real.log (z i)) -
          y i * Real.log (y i) - y i + y i * centralClassErr n i) =
      (∑ i : Fin 4,
        (2 * (p i * Real.log (p i)) - 2 * (z i * Real.log (z i)) -
          y i * Real.log (y i) - y i)) +
        ∑ i : Fin 4, y i * centralClassErr n i := Finset.sum_add_distrib
  rw [hsum_split] at hlogD_stirling
  have hK_inner := mul_le_mul_of_nonneg_left (add_le_add hent_sum hsum_yE) hK_pos.le
  have hKα_rate := mul_le_mul_of_nonneg_left hrate' (mul_nonneg hK_pos.le (Nat.cast_nonneg α))
  have herr_le_Cdiag :
      (K : ℝ) * (Y * (3 - Real.log Y) + (6 * |alphaConst| + 52) * Y) + 6185 * (K : ℝ) * Y ≤
        C_diag * (K : ℝ) * Y * (1 - Real.log Y) := by
    have hKY_nonneg : 0 ≤ (K : ℝ) * Y := mul_nonneg hK_pos.le hY_pos.le
    have hlogY_nonneg : 0 ≤ -Real.log Y := neg_nonneg.mpr (Real.log_nonpos hY_pos.le hY_le1)
    have hc_nonneg : 0 ≤ 6299 + 6 * |alphaConst| := by positivity
    have hextra : 0 ≤ ((K : ℝ) * Y) * ((6299 + 6 * |alphaConst|) * (-Real.log Y) + 60) :=
      mul_nonneg hKY_nonneg (add_nonneg (mul_nonneg hc_nonneg hlogY_nonneg) (by norm_num))
    have hid :
        C_diag * (K : ℝ) * Y * (1 - Real.log Y) -
          ((K : ℝ) * (Y * (3 - Real.log Y) + (6 * |alphaConst| + 52) * Y) + 6185 * (K : ℝ) * Y) =
        ((K : ℝ) * Y) * ((6299 + 6 * |alphaConst|) * (-Real.log Y) + 60) := by
      dsimp [C_diag]; ring
    linarith only [hid, hextra]
  have hid_rate :
      (K : ℝ) * (α : ℝ) * R * Real.log R + (K : ℝ) * ((q * (α : ℝ) / 2) * (T * Y - I_y)) =
        ((K : ℝ) * (α : ℝ)) * (R * Real.log R + (q / 2) * (I_r - T * R)) := by
    rw [hTY_Ir]; ring
  have hid_Kinner :
      (K : ℝ) *
        ((∑ i : Fin 4,
            (2 * (p i * Real.log (p i)) - 2 * (z i * Real.log (z i)) -
              y i * Real.log (y i) - y i)) +
          ∑ i : Fin 4, y i * centralClassErr n i) ≤
      (K : ℝ) * (Y * (3 - Real.log Y) + (6 * |alphaConst| + 52) * Y) +
        (K : ℝ) * ((q * (α : ℝ) / 2) * (T * Y - I_y)) := by
    have hexp :
        (K : ℝ) *
          (Y * (3 - Real.log Y) + ((q * (α : ℝ) / 2) * (T * Y - I_y) + (6 * |alphaConst| + 52) * Y)) =
        (K : ℝ) * (Y * (3 - Real.log Y) + (6 * |alphaConst| + 52) * Y) +
          (K : ℝ) * ((q * (α : ℝ) / 2) * (T * Y - I_y)) := by ring
    linarith only [hK_inner, hexp]
  have hid_rate_mul :
      ((K : ℝ) * (α : ℝ)) * (-Y / 30000) = (K : ℝ) * (α : ℝ) * (-Y / 30000) := by ring
  linarith only [hlogD_stirling, hid_Kinner, hρR_bound, hid_rate, hKα_rate, hid_rate_mul,
    herr_le_Cdiag, hdom]

/-- **Master Partial-Diagonal Sum Bound (`arXiv:2608.30604`, Section 7)**:
There exists a nonnegative sequence `η_pd : ℕ → ℝ` tending to `0` such that eventually
`∑ v ∈ diagBox n, diagWeight n v ≤ Real.exp (η_pd n * n / (log n)^4)`. -/
theorem eventually_sum_diagWeight_le :
    ∃ η_pd : ℕ → ℝ,
      (∀ n, 0 ≤ η_pd n) ∧
      Tendsto η_pd atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∑ v ∈ diagBox n, diagWeight n v ≤
          Real.exp (η_pd n * (n : ℝ) / (Real.log (n : ℝ)) ^ 4) := by
  let η_pd : ℕ → ℝ := fun n => if n ≤ 2 then 0 else 4 / Real.log (n : ℝ)
  have hη_nonneg : ∀ n, 0 ≤ η_pd n := by
    intro n
    dsimp [η_pd]
    split_ifs with h
    · norm_num
    · have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
      exact div_nonneg (by norm_num) (Real.log_pos hn1).le
  have hL : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hη_tendsto : Tendsto η_pd atTop (𝓝 0) := by
    have hdiv : Tendsto (fun n : ℕ => 4 / Real.log (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hL
    refine hdiv.congr' ?_
    filter_upwards [eventually_ge_atTop 3] with n hn3
    dsimp [η_pd]
    split_ifs with h
    · omega
    · rfl
  refine ⟨η_pd, hη_nonneg, hη_tendsto, ?_⟩
  filter_upwards [eventually_alphaNat_regime, eventually_witnessCounts_spec,
    eventually_diagWeight_le_of_central_range,
    eventually_diagWeight_le_one_of_full_corner,
    hL.eventually_ge_atTop 10,
    (tendsto_nat_div_log_pow_atTop 6).eventually_ge_atTop 50] with
      n ⟨hn16, _, _, _, _, hhi⟩ ⟨_, hn, hsize, hcounts, _⟩ hcentral hcorner hL10 hnL6
  set L : ℝ := Real.log (n : ℝ)
  have hL10' : (10 : ℝ) ≤ L := hL10
  have hnL6' : (50 : ℝ) ≤ (n : ℝ) / L ^ 6 := hnL6
  have hL_pos : 0 < L := by linarith only [hL10']
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h44L_le : 44 * L ≤ 3 * (n : ℝ) / L ^ 5 := by
    calc
      44 * L ≤ (3 * ((n : ℝ) / L ^ 6)) * L :=
        mul_le_mul_of_nonneg_right (by linarith only [hnL6']) hL_pos.le
      _ = 3 * (n : ℝ) / L ^ 5 := by field_simp [hL_pos.ne']
  have hpointwise : ∀ v ∈ diagBox n, diagWeight n v ≤ Real.exp (3 * (n : ℝ) / L ^ 5) := by
    intro v hv
    by_cases hsmall : (diagMass n v : ℝ) ≤ (n : ℝ) / L ^ 6
    · have hpow := diagWeight_le_pow_three_diagMass (by omega) hn hsize
        (fun i => (hcounts i).1) hhi hv
      refine hpow.trans ?_
      have hexp_eq : (n : ℝ) ^ (3 * diagMass n v) =
          Real.exp ((3 * (diagMass n v : ℝ)) * L) := by
        rw [show (3 * (diagMass n v : ℝ)) = ((3 * diagMass n v : ℕ) : ℝ) by push_cast; ring,
          Real.exp_nat_mul, Real.exp_log hn_pos]
      rw [hexp_eq]
      apply Real.exp_le_exp.mpr
      calc
        (3 * (diagMass n v : ℝ)) * L
            = 3 * ((diagMass n v : ℝ) * L) := by ring
        _ ≤ 3 * ((n : ℝ) / L ^ 6 * L) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsmall hL_pos.le) (by norm_num)
        _ = 3 * (n : ℝ) / L ^ 5 := by field_simp [hL_pos.ne']
    · push Not at hsmall
      by_cases hfull : 1024 * (n - diagMass n v) ≤ n
      · refine (hcorner v hv hfull).trans ?_
        exact Real.one_le_exp (by positivity)
      · push Not at hfull
        refine (hcentral v hv hsmall hfull).trans ?_
        exact Real.exp_le_exp.mpr h44L_le
  have hcard := card_diagBox_le n hn hsize
  have hcard_exp : ((diagBox n).card : ℝ) ≤ Real.exp ((n : ℝ) / L ^ 5) := by
    have hn1_le : ((n + 1 : ℕ) : ℝ) ≤ Real.exp (2 * L) := by
      have hn_exp : (n : ℝ) = Real.exp L := (Real.exp_log hn_pos).symm
      have heL : 2 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
      have hmul : 2 * Real.exp L ≤ Real.exp (2 * L) := by
        have hm := mul_le_mul_of_nonneg_right heL (Real.exp_pos L).le
        rwa [← Real.exp_add, ← two_mul] at hm
      push_cast
      linarith only [hn_exp, heL, hmul]
    have h8L_le : 8 * L ≤ (n : ℝ) / L ^ 5 := by
      calc
        8 * L ≤ ((n : ℝ) / L ^ 6) * L :=
          mul_le_mul_of_nonneg_right (by linarith only [hnL6']) hL_pos.le
        _ = (n : ℝ) / L ^ 5 := by field_simp [hL_pos.ne']
    calc
      ((diagBox n).card : ℝ) ≤ (((n + 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast hcard
      _ = ((n + 1 : ℕ) : ℝ) ^ 4 := by push_cast; rfl
      _ ≤ (Real.exp (2 * L)) ^ 4 := pow_le_pow_left₀ (by positivity) hn1_le 4
      _ = Real.exp (8 * L) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp ((n : ℝ) / L ^ 5) := Real.exp_le_exp.mpr h8L_le
  have hη_eq : η_pd n * (n : ℝ) / L ^ 4 = 4 * (n : ℝ) / L ^ 5 := by
    dsimp [η_pd]
    split_ifs with h
    · omega
    · change (4 / L) * (n : ℝ) / L ^ 4 = 4 * (n : ℝ) / L ^ 5
      field_simp [hL_pos.ne']
  calc
    ∑ v ∈ diagBox n, diagWeight n v
        ≤ ∑ _v ∈ diagBox n, Real.exp (3 * (n : ℝ) / L ^ 5) :=
      Finset.sum_le_sum hpointwise
    _ = ((diagBox n).card : ℝ) * Real.exp (3 * (n : ℝ) / L ^ 5) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.exp ((n : ℝ) / L ^ 5) * Real.exp (3 * (n : ℝ) / L ^ 5) :=
      mul_le_mul_of_nonneg_right hcard_exp (Real.exp_pos _).le
    _ = Real.exp (4 * (n : ℝ) / L ^ 5) := by
      rw [← Real.exp_add]
      congr 1; ring
    _ = Real.exp (η_pd n * (n : ℝ) / L ^ 4) := by rw [hη_eq]

end JSP000506
