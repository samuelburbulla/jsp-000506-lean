import JSP000506.PartB
import JSP000506.Overlap
import JSP000506.Residual
import JSP000506.Concentration

/-!
# Section 11: Unconditional Synthesis of Petkov's Quantitative Chromatic–Cochromatic Gap (`JSP-000506`)

This module formalizes Section 11 of Samuil Petkov's *A Full-Sequence Quantitative Gap Between the
Chromatic and Cochromatic Numbers of a Random Graph* (`arXiv:2608.30604`), assembling all verified
components of Sections 1–10 into the unconditional phase-resolved, quantitative `n / (log n)^3`,
and qualitative Erdős–Gimbel (`JSP-000506` / Erdős Problem #625) gap theorems:

1. **Unconditional Subcritical Second Moment (`petkovSubcriticalSecondMoment`)**:
   Establishes `PetkovSubcriticalSecondMomentBound` (`𝔼[W_n^2] / (𝔼[W_n])^2 ≤ exp(o(n / (log n)^4))`)
   unconditionally from the diagonal overlap-profile analysis of Section 7 (`Diag.lean`), the
   high-cell skeleton & endpoint-table reduction of Section 8 (`HighCells.lean`), and the canonical
   high-cell conditioning & residual cycle-space bounds of Section 9 (`Residual.lean`).
2. **Paley–Zygmund Rare-Seed Lower Bound (`eventually_seed_cocolorable_prob_of_secondMoment`)**:
   Combines `paley_zygmund_gnpHalf`, `expectGnpHalf_permSignedWitness_pos`, and deterministic
   mark-forgetting (`cocolorable_of_permSignedWitness_pos`) to deduce
   `ℙ(Cocolorable G_n (kCoSeed n)) ≥ exp(- η_n * n / (log n)^4)`.
3. **Amplified Cochromatic Upper Tail (`exists_cochromatic_upper_of_secondMoment`)**:
   Applies Section 10's vertex-exposure McDiarmid + Erdős–Szekeres Ramsey amplification
   (`tendsto_probGnpHalf_cochromatic_amplification`) to obtain
   `ℙ(ζ(G_n) ≤ kCoSeed n + δ_amp(n) * n / (log n)^3) → 1`.
4. **Unconditional End-to-End Theorems (`petkovPhaseResolved625`, `petkovQuantitative625`,
   `erdosGimbel625`)**:
   Combines Part A (`exists_kChiMinus_sub_kCoSeed_gap` and `petkovA4_uniform_margin`),
   Part B (`tendsto_probGnpHalf_chromatic_gt_kChiMinus`), `petkovSubcriticalSecondMoment`, and the
   amplified cochromatic upper bound to unconditionally prove:
   - `PetkovPhaseResolved625Statement`:
     `ℙ(χ(G_n) - ζ(G_n) ≥ [((log 2)^2 / 4) * A_4(δ_n) - ε_n] * n / (log n)^3) → 1`,
   - `PetkovQuantitative625Statement`:
     `ℙ(χ(G_n) - ζ(G_n) ≥ ((log 2)^2 / 4) * log(200 / 153) * n / (log n)^3) → 1`,
   - `ErdosGimbel625Statement`:
     `∀ M : ℕ, ℙ(χ(G_n) - ζ(G_n) ≥ M) → 1`.
-/

open Filter SimpleGraph Finset
open scoped Topology BigOperators Nat

namespace JSP000506

/-- **Petkov's Subcritical Normalized Second-Moment Bound (`arXiv:2608.30604`, Sections 7–9)**:
There exists a deterministic nonnegative sequence `η_n → 0` such that eventually
`secondMomentRatio n ≤ exp(η_n * n / (log n)^4)`, where `secondMomentRatio n` is the normalized
second moment `𝔼[W_n^2] / (𝔼[W_n])^2` of the signed 4-size partition count (equivalently
`unordSignedWitness n` by `secondMomentRatio_unord_eq_perm`, and expanded into binary cycle-space
overlap weights by `secondMomentRatio_eq_overlap_sum`). -/
def PetkovSubcriticalSecondMomentBound : Prop :=
  ∃ η : ℕ → ℝ, (∀ n, 0 ≤ η n) ∧ Tendsto η atTop (𝓝 0) ∧
    ∀ᶠ n : ℕ in atTop,
      secondMomentRatio n ≤ Real.exp (η n * (n : ℝ) / (Real.log (n : ℝ)) ^ 4)

/-- Any `O(1)` upper bound `secondMomentRatio n ≤ C` eventually (as proved in Sections 7–9 of
`arXiv:2608.30604`) immediately implies `PetkovSubcriticalSecondMomentBound`. -/
theorem petkovSubcriticalSecondMoment_of_bounded
    (hbounded : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, secondMomentRatio n ≤ C) :
    PetkovSubcriticalSecondMomentBound := by
  rcases hbounded with ⟨C, hC⟩
  let M : ℝ := max 1 C
  have hM_ge1 : 1 ≤ M := le_max_left 1 C
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one hM_ge1
  have hlogM_nn : 0 ≤ Real.log M := Real.log_nonneg hM_ge1
  let η : ℕ → ℝ := fun n => Real.log M / max 1 ((n : ℝ) / (Real.log (n : ℝ)) ^ 4)
  refine ⟨η, ?_, ?_, ?_⟩
  · intro n
    dsimp only [η]
    exact div_nonneg hlogM_nn (by positivity)
  · have hdiv4 := tendsto_nat_div_log_pow_atTop 4
    refine ((tendsto_const_nhds (x := Real.log M)).div_atTop hdiv4).congr' ?_
    filter_upwards [hdiv4.eventually_ge_atTop 1] with n hn
    simp only [η, max_eq_right hn]
  · filter_upwards [hC, (tendsto_nat_div_log_pow_atTop 4).eventually_ge_atTop 1] with n hnC hn4
    have hQ_pos : 0 < (n : ℝ) / (Real.log (n : ℝ)) ^ 4 := lt_of_lt_of_le zero_lt_one hn4
    have hexp_eq : η n * (n : ℝ) / (Real.log (n : ℝ)) ^ 4 = Real.log M := by
      dsimp only [η]
      rw [max_eq_right hn4, mul_div_assoc, div_mul_cancel₀ _ hQ_pos.ne']
    rw [hexp_eq, Real.exp_log hM_pos]
    exact hnC.trans (le_max_right 1 C)

/-- Positivity of `secondMomentRatio n` for every `n : ℕ`. -/
theorem secondMomentRatio_pos (n : ℕ) : 0 < secondMomentRatio n := by
  have hμ_pos : 0 < expectGnpHalf n (permSignedWitness n) :=
    expectGnpHalf_permSignedWitness_pos n
  have h2_pos : 0 < expectGnpHalf n (fun G => (permSignedWitness n G) ^ 2) := by
    have h2_nn : 0 ≤ expectGnpHalf n (fun G => (permSignedWitness n G) ^ 2) :=
      expectGnpHalf_nonneg fun _ => sq_nonneg _
    by_contra hle
    have hzero : expectGnpHalf n (fun G => (permSignedWitness n G) ^ 2) = 0 :=
      le_antisymm (not_lt.mp hle) h2_nn
    unfold expectGnpHalf at hzero
    have hcard_pos : (0 : ℝ) < (Fintype.card (SimpleGraph (Fin n)) : ℝ) := by
      rw [card_simpleGraph_fin]
      positivity
    have hsum0 : ∑ G : SimpleGraph (Fin n), (permSignedWitness n G) ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp hzero with h | h
      · exact h
      · exact False.elim (hcard_pos.ne' h)
    have hall0 : ∀ G : SimpleGraph (Fin n), permSignedWitness n G = 0 := fun G =>
      sq_eq_zero_iff.mp
        ((Finset.sum_eq_zero_iff_of_nonneg (fun H _ => sq_nonneg (permSignedWitness n H))).mp
          hsum0 G (Finset.mem_univ G))
    have hμ0 : expectGnpHalf n (permSignedWitness n) = 0 := by
      unfold expectGnpHalf
      simp [hall0]
    linarith
  exact div_pos h2_pos (sq_pos_of_pos hμ_pos)

/-- **Paley–Zygmund Rare-Seed Cocolorability Bound (`arXiv:2608.30604`, Section 6 / Section 10)**:
Whenever `secondMomentRatio n ≤ exp(η_n * n / (log n)^4)` eventually, Paley–Zygmund applied to
`permSignedWitness n` together with deterministic mark-forgetting (`cocolorable_of_permSignedWitness_pos`)
yields `ℙ(Cocolorable G_n (kCoSeed n)) ≥ exp(- η_n * n / (log n)^4)` eventually. -/
theorem eventually_seed_cocolorable_prob_of_secondMoment
    {η : ℕ → ℝ}
    (hsm : ∀ᶠ n : ℕ in atTop,
      secondMomentRatio n ≤ Real.exp (η n * (n : ℝ) / (Real.log (n : ℝ)) ^ 4)) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (- η n * (n : ℝ) / (Real.log (n : ℝ)) ^ 4) ≤
        probGnpHalf n {G : SimpleGraph (Fin n) | Cocolorable G (kCoSeed n)} := by
  filter_upwards [eventually_witnessCounts_spec, hsm] with n ⟨hK, hn, _, _, _⟩ hsm_n
  have hμ_pos : 0 < expectGnpHalf n (permSignedWitness n) :=
    expectGnpHalf_permSignedWitness_pos n
  have hpz := paley_zygmund_gnpHalf (permSignedWitness_nonneg n) hμ_pos
  have hinv_le : (Real.exp (η n * (n : ℝ) / (Real.log (n : ℝ)) ^ 4))⁻¹ ≤
      (secondMomentRatio n)⁻¹ :=
    inv_anti₀ (secondMomentRatio_pos n) hsm_n
  have hexp_inv : (Real.exp (η n * (n : ℝ) / (Real.log (n : ℝ)) ^ 4))⁻¹ =
      Real.exp (- η n * (n : ℝ) / (Real.log (n : ℝ)) ^ 4) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have hratio_inv : (secondMomentRatio n)⁻¹ =
      (expectGnpHalf n (permSignedWitness n)) ^ 2 /
        expectGnpHalf n (fun G => (permSignedWitness n G) ^ 2) := by
    unfold secondMomentRatio
    rw [inv_div]
  rw [hexp_inv, hratio_inv] at hinv_le
  have hsub : {G : SimpleGraph (Fin n) | 0 < permSignedWitness n G} ⊆
      {G : SimpleGraph (Fin n) | Cocolorable G (kCoSeed n)} :=
    fun _ hG => cocolorable_of_permSignedWitness_pos hK hn hG
  exact hinv_le.trans (hpz.trans (probGnpHalf_mono hsub))

/-- **High-Probability Cochromatic Upper Bound (`arXiv:2608.30604`, Section 10)**:
Under `PetkovSubcriticalSecondMomentBound`, there exists a deterministic nonnegative sequence
`δ_amp n → 0` such that `ℙ(ζ(G_n) ≤ kCoSeed n + δ_amp(n) * n / (log n)^3) → 1`. -/
theorem exists_cochromatic_upper_of_secondMoment
    (hsm : PetkovSubcriticalSecondMomentBound) :
    ∃ δ_amp : ℕ → ℝ, (∀ n, 0 ≤ δ_amp n) ∧ Tendsto δ_amp atTop (𝓝 0) ∧
      Tendsto
        (fun n : ℕ => probGnpHalf n
          {G : SimpleGraph (Fin n) |
            (cochromaticNumber G : ℝ) ≤
              (kCoSeed n : ℝ) + δ_amp n * (n : ℝ) / (Real.log (n : ℝ)) ^ 3})
        atTop (𝓝 1) := by
  rcases hsm with ⟨η, hη_nn, hη0, hsm_ev⟩
  exact tendsto_probGnpHalf_cochromatic_amplification kCoSeed hη_nn hη0
    (eventually_seed_cocolorable_prob_of_secondMoment hsm_ev)

/-- **Phase-Resolved Synthesis Theorem (`arXiv:2608.30604`, Section 11)**:
Combining Part A (`exists_kChiMinus_sub_kCoSeed_gap`), Part B
(`tendsto_probGnpHalf_chromatic_gt_kChiMinus`), Paley–Zygmund
(`eventually_seed_cocolorable_prob_of_secondMoment`), and Section 10's vertex-exposure
McDiarmid/Ramsey amplification (`exists_cochromatic_upper_of_secondMoment`) yields
`PetkovPhaseResolved625Statement` from `PetkovSubcriticalSecondMomentBound`. -/
theorem petkovPhaseResolved625_of_secondMoment
    (hsm : PetkovSubcriticalSecondMomentBound) :
    PetkovPhaseResolved625Statement := by
  obtain ⟨ε_A, hεA_nn, hεA_0, hgap_ev⟩ := exists_kChiMinus_sub_kCoSeed_gap
  obtain ⟨δ_amp, hδ_nn, hδ_0, hco_prob⟩ := exists_cochromatic_upper_of_secondMoment hsm
  let ε : ℕ → ℝ := fun n => ε_A n + δ_amp n
  have hε_nn : ∀ n, 0 ≤ ε n := fun n => add_nonneg (hεA_nn n) (hδ_nn n)
  have hε_0 : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using hεA_0.add hδ_0
  refine ⟨ε, hε_nn, hε_0, ?_⟩
  have hinter := tendsto_probGnpHalf_inter_one tendsto_probGnpHalf_chromatic_gt_kChiMinus hco_prob
  refine tendsto_probGnpHalf_one_of_eventually_subset hinter ?_
  filter_upwards [hgap_ev] with n hgap G ⟨hchi, hco⟩
  simp only [Set.mem_ofPred_eq] at hchi hco ⊢
  have hchi_real : (kChiMinus n : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) :=
    Nat.cast_le.mpr hchi.le
  have hsplit :
      ((Real.log 2) ^ 2 / 4 * petkovA4 (phaseDelta n) - ε n) *
        (n : ℝ) / (Real.log (n : ℝ)) ^ 3 =
      ((Real.log 2) ^ 2 / 4 * petkovA4 (phaseDelta n) - ε_A n) *
        (n : ℝ) / (Real.log (n : ℝ)) ^ 3 -
      δ_amp n * (n : ℝ) / (Real.log (n : ℝ)) ^ 3 := by
    dsimp only [ε]
    ring
  linarith

/-- **Full-Sequence Quantitative Gap Synthesis (`arXiv:2608.30604`, Main Theorem / Abstract)**:
Under `PetkovSubcriticalSecondMomentBound`, combining `petkovPhaseResolved625_of_secondMoment`
with the unconditional constructive entropy certificate `petkovA4_uniform_margin`
(`A_4(δ) ≥ log(200 / 153) + log(306 / 305)` for all `δ ∈ [0, 1]`) proves
`PetkovQuantitative625Statement`:
`ℙ(χ(G_n) - ζ(G_n) ≥ ((log 2)^2 / 4) * log(200 / 153) * n / (log n)^3) → 1`. -/
theorem petkovQuantitative625_of_secondMoment
    (hsm : PetkovSubcriticalSecondMomentBound) :
    PetkovQuantitative625Statement :=
  (petkovPhaseResolved625_of_secondMoment hsm).petkovQuantitative625
    (Real.log_pos (by norm_num : (1 : ℝ) < 306 / 305))
    (fun _ hδ => petkovA4_uniform_margin hδ)

/-- **Qualitative Erdős–Gimbel Synthesis (`JSP-000506` / Erdős Problem #625)**:
Under `PetkovSubcriticalSecondMomentBound`, `χ(G_n) - ζ(G_n) → ∞` with high probability as `n → ∞`. -/
theorem erdosGimbel625_of_secondMoment
    (hsm : PetkovSubcriticalSecondMomentBound) :
    ErdosGimbel625Statement :=
  (petkovQuantitative625_of_secondMoment hsm).erdosGimbel625

/-- Specialization of `petkovQuantitative625_of_secondMoment` to an `O(1)` second-moment bound. -/
theorem petkovQuantitative625_of_bounded_secondMoment
    (hbounded : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, secondMomentRatio n ≤ C) :
    PetkovQuantitative625Statement :=
  petkovQuantitative625_of_secondMoment (petkovSubcriticalSecondMoment_of_bounded hbounded)

/-- Specialization of `erdosGimbel625_of_secondMoment` to an `O(1)` second-moment bound. -/
theorem erdosGimbel625_of_bounded_secondMoment
    (hbounded : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, secondMomentRatio n ≤ C) :
    ErdosGimbel625Statement :=
  erdosGimbel625_of_secondMoment (petkovSubcriticalSecondMoment_of_bounded hbounded)

/-! ### Unconditional Main Theorems (`arXiv:2608.30604` & Erdős Problem #625) -/

/-- **Petkov's Unconditional Subcritical Second-Moment Theorem (`arXiv:2608.30604`, Sections 7–9)**:
The normalized second moment `secondMomentRatio n = 𝔼[W_n^2] / (𝔼[W_n])^2` of the signed 4-size
witness satisfies `secondMomentRatio n ≤ exp(η_n * n / (log n)^4)` eventually for a deterministic
nonnegative sequence `η_n → 0`. -/
theorem petkovSubcriticalSecondMoment : PetkovSubcriticalSecondMomentBound :=
  eventually_secondMomentRatio_subcritical

/-- **Petkov's Unconditional Phase-Resolved Gap Theorem (`arXiv:2608.30604`, Theorem 1.1)**:
Along the full integer sequence `n → ∞`, there exists a deterministic nonnegative sequence `ε_n → 0`
such that `ℙ(χ(G_n) - ζ(G_n) ≥ [((log 2)^2 / 4) * A_4(δ_n) - ε_n] * n / (log n)^3) → 1`. -/
theorem petkovPhaseResolved625 : PetkovPhaseResolved625Statement :=
  petkovPhaseResolved625_of_secondMoment petkovSubcriticalSecondMoment

/-- **Petkov's Unconditional Full-Sequence Quantitative Gap Theorem (`arXiv:2608.30604`, Abstract)**:
Along the full integer sequence `n → ∞`,
`ℙ(χ(G_n) - ζ(G_n) ≥ ((log 2)^2 / 4) * log(200 / 153) * n / (log n)^3) → 1`. -/
theorem petkovQuantitative625 : PetkovQuantitative625Statement :=
  petkovQuantitative625_of_secondMoment petkovSubcriticalSecondMoment

/-- **Unconditional Resolution of Erdős Problem #625 (`JSP-000506`, Erdős–Gimbel Conjecture)**:
For every `M : ℕ`, `ℙ(χ(G_n) - ζ(G_n) ≥ M) → 1` as `n → ∞` for `G_n ~ G(n, 1/2)`. -/
theorem erdosGimbel625 : ErdosGimbel625Statement :=
  erdosGimbel625_of_secondMoment petkovSubcriticalSecondMoment

end JSP000506
