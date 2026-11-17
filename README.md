# JSP-000506 — Erdős Problem #625: Chromatic vs. Cochromatic Gap in $G(n, 1/2)$

Clean-room Lean 4 (`leanprover/lean4:v4.34.1` + Mathlib `v4.34.1`) formalization of **Erdős Problem #625** (`JSP-000506`, posed by Paul Erdős and John Gimbel) and Samuil Petkov's resolution (*"A Full-Sequence Quantitative Gap Between the Chromatic and Cochromatic Numbers of a Random Graph"*, `arXiv:2608.30604`, August 2026).

---

## 1. Mathematical Overview

For a finite simple graph $G = (V, E)$, let:
- $\chi(G)$ denote the **chromatic number** of $G$ (minimum number of independent sets partitioning $V$), and
- $\zeta(G)$ denote the **cochromatic number** of $G$ (minimum number of **homogeneous sets**—cliques or independent sets—partitioning $V$).

Since every independent set is homogeneous, $\zeta(G) \le \chi(G)$ holds for every finite graph $G$. For the binomial random graph $G_n \sim G(n, 1/2)$, Bollobás (1988) and Heckel (2018)/Matula–Kučera showed that both $\chi(G_n)$ and $\zeta(G_n)$ share the leading asymptotic $\frac{n}{2 \log_2 n} (1 + o(1))$. Erdős and Gimbel asked (**Erdős Problem #625**):

> **Question (Erdős–Gimbel).** Does $\chi(G_n) - \zeta(G_n) \to \infty$ with probability tending to $1$ as $n \to \infty$?

### Petkov's Resolution (`arXiv:2608.30604`)

Petkov (`arXiv:2608.30604`) resolved Erdős Problem #625 affirmatively along the **full integer sequence** $n \to \infty$ with an explicit third-order quantitative gap of scale $\Theta(n / (\log n)^3)$.

Let $q = \log 2$, let $\alpha_0(n) = 2\log_2 n - 2\log_2(\log_2 n) + 2\log_2(e/2) + 1$ be the continuous independence-number scale (`JSP000506.alpha0`), let $\alpha_n = \lfloor \alpha_0(n) \rfloor$ (`JSP000506.alphaFloor` / `JSP000506.alphaNat`), let $\delta_n = \alpha_0(n) - \lfloor \alpha_0(n) \rfloor \in [0, 1)$ (`JSP000506.phaseDelta`) be the fractional phase, and let $T_\delta = 1 + \frac{2}{q} - \delta$ (`JSP000506.targetDeficit`) be the target average class-size deficit below $\alpha_n$.

1. **Free-Energy Separation (Sections 3–4, Part A)**:
   Define the tilted partition functions over all deficits $S_+ = \{-1, 0, 1, 2, \dots\}$ and over the restricted 4-deficit window $S_4 = \{2, 3, 4, 5\}$:
   $$Z_{S_+}(\lambda) = \sum_{i=-1}^{\infty} \exp\!\left(\lambda i - \frac{q}{2} i^2\right), \qquad Z_{S_4}(\lambda) = \sum_{i=2}^{5} \exp\!\left(\lambda i - \frac{q}{2} i^2\right),$$
   their Legendre–Fenchel free energies $\mathcal{F}_{S_+}(T) = \inf_{\lambda \in \mathbb{R}} (\log Z_{S_+}(\lambda) - \lambda T)$ and $\mathcal{F}_{S_4}(T) = \inf_{\lambda \in \mathbb{R}} (\log Z_{S_4}(\lambda) - \lambda T)$, and the phase-resolved entropy gain
   $$A_4(\delta) := \log 2 - \mathcal{F}_{S_+}(T_\delta) + \mathcal{F}_{S_4}(T_\delta).$$
   Here $+\log 2$ comes from the two sign choices (clique vs. independent set) per cocoloring block, while $\mathcal{F}_{S_+}(T_\delta) - \mathcal{F}_{S_4}(T_\delta)$ measures the entropy cost of restricting cocoloring block sizes to $\{\alpha_n - 2, \alpha_n - 3, \alpha_n - 4, \alpha_n - 5\}$. Constructive convexity and tail bounds (**Lemma 5.1**) certify uniformly across all phases $\delta \in [0, 1]$ that
   $$A_4(\delta) \ge \log\!\left(\frac{80}{61}\right) = \log\!\left(\frac{200}{153}\right) + \log\!\left(\frac{306}{305}\right) > \log\!\left(\frac{200}{153}\right) > 0.$$
   Moreover, $A_4$ is nonconstant on $[0, 1]$ (strictly larger at the dyadic symmetry phase $\delta_* = \frac{2}{\log 2} - \frac{5}{2}$ than at $\delta = 1$). Solving the continuous profile equations separates the chromatic threshold $k_\chi^-(n)$ above the signed 4-size cochromatic seed count $k_{\mathrm{co}}^{\mathrm{seed}}(n)$ by
   $$k_\chi^-(n) - k_{\mathrm{co}}^{\mathrm{seed}}(n) \ge \left(\frac{(\log 2)^2}{4} A_4(\delta_n) - o(1)\right) \frac{n}{(\log n)^3}.$$

2. **Chromatic Lower Tail via Capped First Moment (Section 5, Part B)**:
   Truncating on the high-probability independence cap $\alpha(G_n) \le \alpha_n + 1$, every proper $k_\chi^-(n)$-coloring has class deficits in $S_+$. Collapsing ordered proper colorings onto deficit histograms and applying Gibbs' inequality shows that the expected number of capped proper $k_\chi^-(n)$-colorings is $\le \exp(-\Omega(n / (\log n)^2)) \to 0$, whence $\mathbb{P}(\chi(G_n) > k_\chi^-(n)) \to 1$.

3. **Signed 4-Size Witness, Cycle-Space Overlap Analysis, and Rare-Seed Amplification (Sections 6–11, Part C & Synthesis)**:
   Unimodular $(2, 3)$-rounding of the optimal 4-size Gibbs measure produces integer multiplicities $(\kappa_2, \kappa_3, \kappa_4, \kappa_5)$ summing to $K = k_{\mathrm{co}}^{\mathrm{seed}}(n)$ with exact vertex sum $n$ and supercritical first moment $\mathbb{E}[Z_n] \ge \exp(+100 n / (\log n)^2)$. For any two $K$-block partitions $A, B$, **Lemma 6.1** evaluates the exact pair realization probability summed over signs $(\sigma, \tau) \in \{0,1\}^K \times \{0,1\}^K$ in terms of the heavy-overlap graph $M(A, B) = \{(i, j) : |A_i \cap B_j| \ge 2\}$ and its binary cycle-space cardinality $|\ker \partial_M| = 2^{\beta(M)}$ (the number of even-degree bipartite subgraphs $H \subseteq M$). Sections 7–9 bound the normalized second moment unconditionally:
   - **Section 7 (`Diag.lean`)**: Bounds diagonal full-overlap profile weights $D(\ell)$ across the small-support range ($m \le n / (\log n)^6$, forward step recurrence), the central range ($n / (\log n)^6 < m < \frac{31}{32} n$, Robbins–Stirling + strict negativity $\Phi_T(z) \le -Y / 5000$), and the full corner ($n - m \le n / 32$, reverse recurrence).
   - **Section 8 (`HighCells.lean`)**: Shows high-overlap cells exceeding $R_0 = \lfloor (\alpha_n - 2)/2 \rfloor$ form a partial block matching $M$, proves geometric decay in multiplicity deficits $(m_p - j_p)$, and bounds the $4 \times 4$ endpoint-type table sum via the squared diagonal comparison $W(L)^2 \le D(r) D(c) A_L C_L Q^{2L}$ and AM-GM.
   - **Section 9 (`Residual.lean`)**: Reduces the double permutation sum to a single $S_n$ average, conditions on high-cell fibers $(M, j)$, proves matching restriction injectivity $F \mapsto F \setminus M$ on even overlap subgraphs (**Lemma 9.3**) and the joint prescribed-cell bound (**Lemma 6.2**), and bounds conditional residual sums across the $m_0 = 0$, complementary ($m_0^3 < 2^U$), and intrinsic ($2^U \le m_0^3$) regimes to establish $\mathbb{E}[W_n^2]/(\mathbb{E}[W_n])^2 \le \exp(o(n / (\log n)^4))$.

   Combining this unconditional subcritical second-moment bound with Paley–Zygmund yields $\mathbb{P}(\zeta(G_n) \le K) \ge \exp(-o(n / (\log n)^4))$. Finally, two-step **vertex-exposure McDiarmid concentration** (`1`-Lipschitz stability of $\zeta$ and vertex-edit distance) together with **Erdős–Szekeres Ramsey extraction** ($|U|/r + 4^r$ homogeneous sets on edited vertices at $r \asymp \frac{1}{4}\log n$) amplifies this rare seed to $\mathbb{P}(\zeta(G_n) \le K + o(n / (\log n)^3)) \to 1$, unconditionally proving:
   $$\mathbb{P}\!\left(\chi(G_n) - \zeta(G_n) \ge \frac{(\log 2)^2}{4}\log\!\left(\frac{200}{153}\right)\frac{n}{(\log n)^3}\right) \longrightarrow 1 \qquad (n \to \infty).$$

---

## 2. Module Architecture & Verification Status

All code is authored from scratch in Lean 4 (`v4.34.1` + Mathlib `v4.34.1`) with `autoImplicit = false`, **zero unproved hypotheses**, **zero `sorry`**, **zero `admit`**, **zero custom `axiom`s**, **no `native_decide`**, and **zero compiler/linter warnings**.

| Module | Lines | Scope & Unconditional Theorems |
| :--- | ---: | :--- |
| [`JSP000506.lean`](JSP000506.lean) | 70 | Root library entry point re-exporting all 13 `JSP000506.*` modules. |
| [`JSP000506/Defs.lean`](JSP000506/Defs.lean) | 261 | `IsHomogeneousSet`, `IsCocoloring`, `Cocolorable`, `IsCocoloringPartition`, `cochromaticNumber`, function-vs-partition equivalence `cocolorable_iff_exists_partition`, `SatisfiesSign`, mark-forgetting uniqueness `satisfiesSign_unique_of_two_le_card`, `cocolorable_of_signed_cover`. |
| [`JSP000506/Basic.lean`](JSP000506/Basic.lean) | 369 | Unconditional bounds `cochromaticNumber_le_chromaticNumber`, `chromaticNumber_toNat_le_n`, complement symmetry `cochromaticNumber_compl`, vertex-exposure `1`-Lipschitz bound `abs_cochromaticNumber_sub_le_one_of_agreeOffVertex`, and exact evaluations on $\overline{K_n}$, $K_n$, $C_4$, $C_5$, and the 5-vertex `houseGraph` ($\chi = 3, \zeta = 2$, `houseGraph_gap_eq_one`). |
| [`JSP000506/Model.lean`](JSP000506/Model.lean) | 797 | Dual $G(n, 1/2)$ models: uniform graph counting `probGnpHalf` / `expectGnpHalf` and independent fair-coin product `pmfGnpHalf` (`PMF (SimpleGraph (Fin n))`), proved equal on all events (`toOuterMeasure_pmfGnpHalf_eq`); edge-marginal theorem `probGnpHalf_prescribed_edges`; `paley_zygmund_gnpHalf`; phase functions `alpha0`, `phaseDelta`, `targetDeficit`, `freeEnergyPlus`, `freeEnergyFour`, `petkovA4`, `petkovConstant`; formal statements `ErdosGimbel625Statement`, `PetkovQuantitative625Statement`, `PetkovPhaseResolved625Statement`, and unconditional reductions `PetkovQuantitative625Statement.erdosGimbel625` & `PetkovPhaseResolved625Statement.petkovQuantitative625`. |
| [`JSP000506/EntropyCert.lean`](JSP000506/EntropyCert.lean) | 1,560 | Summability, strict monotonicity of tilted means, Legendre–Fenchel attainment `exists_optimal_gibbs_four` & `gibbs_upper_bound_plus`, **Lemma 5.1** (`petkovA4_uniform_margin` & `petkovA4_gt_log_200_153`), and `petkovA4_nonconstant`. |
| [`JSP000506/Phase.lean`](JSP000506/Phase.lean) | 554 | Discrete independence scale `alphaNat`, Robbins–Stirling bounds `log_factorial_bounds`, falling-factorial shifts `falling_shift_upper_all` & `falling_shift_lower_bounded`, and `tendsto_probGnpHalf_indepCapEvent` ($\mathbb{P}(\alpha(G_n) \le \alpha_n + 1) \to 1$). |
| [`JSP000506/PartA.lean`](JSP000506/PartA.lean) | 2,067 | Continuous profile roots `sPlus` & `sFourCo`, root separation `eventually_continuous_roots_separation`, discrete thresholds `kChiMinus` & `kCoSeed`, `exists_kChiMinus_sub_kCoSeed_gap`, `eventually_kChiMinus_subcritical`, and unimodular rounded 4-size multiplicities `eventually_witnessCounts_spec`. |
| [`JSP000506/PartB.lean`](JSP000506/PartB.lean) | 1,061 | Exact proper-coloring first moment `expectGnpHalf_cappedProperCount`, histogram collapse `normalized_cappedProper_le_hist_sum`, and **Part B Main Theorem** `tendsto_probGnpHalf_chromatic_gt_kChiMinus` ($\mathbb{P}(\chi(G_n) > k_\chi^-(n)) \to 1$). |
| [`JSP000506/Overlap.lean`](JSP000506/Overlap.lean) | 1,040 | Signed 4-size witness `permSignedWitness` & `unordSignedWitness`, supercritical first moment `eventually_expectGnpHalf_unordSignedWitness_supercritical`, Walsh–Hadamard cycle-space identity `card_compatible_signs_eq_evenSubgraphs`, **Lemma 6.1** (`signed_overlap_pair_prob_eq`), and exact second-moment expansion `secondMomentRatio_eq_overlap_sum`. |
| [`JSP000506/Diag.lean`](JSP000506/Diag.lean) | 2,197 | **Section 7**: Diagonal full-overlap profile weights `diagWeight`, small-support forward recurrence bound `diagWeight_small_support_le`, central-range Stirling & convex-rate negativity bound `diagWeight_central_le`, full-corner reverse-recurrence bound `diagWeight_corner_le`, and `eventually_sum_diagWeight_le`. |
| [`JSP000506/HighCells.lean`](JSP000506/HighCells.lean) | 2,108 | **Section 8**: High-cell cap `highCap` & threshold `highThresh`, partial block matchings `IsBlockMatching`, deficit geometric decay `sum_highMultBox_highSkeletonWeight_le`, $4 \times 4$ endpoint-type table counting & **Lemma 8.6** squared comparison `tableWeight_sq_le`, and `eventually_sum_highSkeletonWeight_le`. |
| [`JSP000506/Residual.lean`](JSP000506/Residual.lean) | 2,735 | **Section 9**: Single-permutation reduction `secondMomentRatio_eq_single_perm_sum`, **Lemma 9.3** matching restriction injectivity `evenSubgraph_sdiff_matching_inj` & `sum_evenSubgraphs_prod_sdiff_le`, **Lemma 6.2** joint prescribed-cell bound `card_prescribed_absResBij_le`, **Proposition 9.4** & master uniform residual bound `absResSum_le_master`, high-cell fiber conditioning `inv_nfac_mul_sum_permFiber_le`, and `eventually_secondMomentRatio_subcritical`. |
| [`JSP000506/Concentration.lean`](JSP000506/Concentration.lean) | 1,049 | Vertex-exposure bijection `vertexExposureEquiv`, elementary finite-product McDiarmid MGF & tail bounds `mgf_bounded_diff_pi`, `mcdiarmid_gnpHalf_upper`, `mcdiarmid_gnpHalf_lower`, `mcdiarmid_cochromaticNumber_upper`, two-step `vertexEditDist` amplification `probGnpHalf_vertexEditDist_ge_le`, Erdős–Szekeres Ramsey extraction `cochromaticNumber_le_of_agreeOffSet`, and **Section 10 Amplification Theorem** `tendsto_probGnpHalf_cochromatic_amplification`. |
| [`JSP000506/Main.lean`](JSP000506/Main.lean) | 251 | **Section 11 Unconditional Synthesis**: Unconditional subcritical second-moment theorem `petkovSubcriticalSecondMoment`, Paley–Zygmund rare-seed bound `eventually_seed_cocolorable_prob_of_secondMoment`, and unconditional main theorems `petkovPhaseResolved625`, `petkovQuantitative625`, and `erdosGimbel625`. |
| **Total Lean 4** | **16,119** | **100% unconditional: zero `sorry`, zero `admit`, zero custom `axiom`s, zero `native_decide`, zero warnings.** |

### 100% Unconditional Verification Summary

Every section (Sections 1–11) of `arXiv:2608.30604` is formalized and verified unconditionally from standard Lean 4 / Mathlib foundations (`propext`, `Classical.choice`, `Quot.sound` only):
- **Foundations & Sanity Checks (`Defs.lean`, `Basic.lean`, `Model.lean`)**: Equivalent function vs. set-partition cocoloring formulations, equivalent uniform-graph vs. independent fair-coin `PMF` $G(n, 1/2)$ models, $\zeta(G) \le \chi(G)$, $\zeta(G^c) = \zeta(G)$, `1`-Lipschitz vertex stability, and exact evaluations on $\overline{K_n}, K_n, C_4, C_5$, and the 5-vertex `houseGraph` ($\chi - \zeta = 1$).
- **Section 2 (`Phase.lean`)**: Independence cap $\mathbb{P}(\alpha(G_n) \le \alpha_n + 1) \to 1$ and explicit Robbins–Stirling / falling-factorial asymptotics.
- **Sections 3–4 (`EntropyCert.lean` + `PartA.lean`)**: Constructive uniform entropy certificate $A_4(\delta) \ge \log(200/153) + \log(306/305)$ (**Lemma 5.1**), nonconstancy of $A_4$, root separation $k_\chi^-(n) - k_{\mathrm{co}}^{\mathrm{seed}}(n)$, and supercriticality of unimodularly rounded 4-size integer multiplicities.
- **Section 5 (`PartB.lean`)**: Capped proper-coloring histogram collapse and $\mathbb{P}(\chi(G_n) > k_\chi^-(n)) \to 1$.
- **Sections 6–9 (`Overlap.lean`, `Diag.lean`, `HighCells.lean`, `Residual.lean`)**: Exact Walsh–Hadamard cycle-space overlap identity (**Lemma 6.1**), diagonal profile bounds across all three support regimes, canonical high-cell skeleton & $4 \times 4$ type-table reduction, prescribed-cell & residual cycle-space bounds (**Lemmas 6.2 & 9.3**), and the unconditional subcritical second-moment bound `petkovSubcriticalSecondMoment`.
- **Sections 10–11 (`Concentration.lean` + `Main.lean`)**: Two-step vertex-exposure McDiarmid + Erdős–Szekeres Ramsey amplification and unconditional end-to-end theorems `petkovPhaseResolved625`, `petkovQuantitative625`, and `erdosGimbel625`.

---

## 3. Paper-to-Lean Correspondence Table

| `arXiv:2608.30604` Reference | Mathematical Statement | Lean 4 Declaration | File |
| :--- | :--- | :--- | :--- |
| Section 1, Cochromatic number | $\zeta(G) = \min\{k : V \text{ covered by } k \text{ cliques/indep.\ sets}\}$ | `JSP000506.cochromaticNumber` | `Defs.lean` |
| Section 1, Partition equivalence | Function cocoloring $\iff$ pairwise-disjoint homogeneous partition | `JSP000506.cocolorable_iff_exists_partition` | `Defs.lean` |
| Section 1, Erdős–Gimbel #625 | $\forall M,\; \mathbb{P}(\chi(G_n) - \zeta(G_n) \ge M) \to 1$ | `JSP000506.ErdosGimbel625Statement` / `JSP000506.erdosGimbel625` | `Model.lean` / `Main.lean` |
| Theorem 1.1 (Quantitative) | $\mathbb{P}(\chi(G_n) - \zeta(G_n) \ge \frac{(\log 2)^2}{4}\log(\frac{200}{153})\frac{n}{(\log n)^3}) \to 1$ | `JSP000506.PetkovQuantitative625Statement` / `JSP000506.petkovQuantitative625` | `Model.lean` / `Main.lean` |
| Theorem 1.1 (Phase-resolved) | $\mathbb{P}(\chi(G_n) - \zeta(G_n) \ge [\frac{(\log 2)^2}{4}A_4(\delta_n) - \varepsilon_n]\frac{n}{(\log n)^3}) \to 1$ | `JSP000506.PetkovPhaseResolved625Statement` / `JSP000506.petkovPhaseResolved625` | `Model.lean` / `Main.lean` |
| Section 2, Independence cap | $\mathbb{P}(\alpha(G_n) \le \alpha_n + 1) \to 1$ | `JSP000506.tendsto_probGnpHalf_indepCapEvent` | `Phase.lean` |
| Section 3, Dual attainment | Optimal 4-size Gibbs vector attaining $\mathcal{F}_{S_4}(T)$ | `JSP000506.exists_optimal_gibbs_four` | `EntropyCert.lean` |
| Lemma 5.1 (Entropy certificate) | $\forall \delta \in [0,1],\; A_4(\delta) \ge \log(200/153) + \log(306/305)$ | `JSP000506.petkovA4_uniform_margin` | `EntropyCert.lean` |
| Section 3, Phase dependence | $\exists \delta_1, \delta_2 \in [0, 1],\; A_4(\delta_1) \ne A_4(\delta_2)$ | `JSP000506.petkovA4_nonconstant` | `EntropyCert.lean` |
| Section 4, Threshold gap | $k_\chi^-(n) - k_{\mathrm{co}}^{\mathrm{seed}}(n) \ge [\frac{(\log 2)^2}{4}A_4(\delta_n) - \varepsilon_A(n)]\frac{n}{(\log n)^3}$ | `JSP000506.exists_kChiMinus_sub_kCoSeed_gap` | `PartA.lean` |
| Section 4, Rounded 4-size seed | Exact counts $\sum \kappa_j = K$, $\sum s_j \kappa_j = n$, $\log \mathbb{E}[Z_n] \ge \frac{100 n}{(\log n)^2}$ | `JSP000506.eventually_witnessCounts_spec` | `PartA.lean` |
| Proposition 5.1 (Part B) | $\mathbb{P}(\chi(G_n) > k_\chi^-(n)) \to 1$ | `JSP000506.tendsto_probGnpHalf_chromatic_gt_kChiMinus` | `PartB.lean` |
| Section 6, Mark-forgetting | Size $\ge 2$ uniquely determines block sign | `JSP000506.satisfiesSign_unique_of_two_le_card` | `Defs.lean` |
| Lemma 6.1 (Cycle-space overlap) | Exact pair probability $= 4^K 2^{-E_A - E_B} \cdot 2^{\sum (C(r_p, 2) - 1)} \cdot |\ker \partial_M|$ | `JSP000506.signed_overlap_pair_prob_eq` | `Overlap.lean` |
| Lemma 6.2 (Prescribed cells) | Bijections with $r'_{ab} \ge x_{ab}$ bounded by $m_0! \prod \theta_{ab}^{x_{ab}} / x_{ab}!$ | `JSP000506.card_prescribed_absResBij_le` | `Residual.lean` |
| Section 6, Normalized 2nd moment | $\mathbb{E}[W_n^2]/(\mathbb{E}[W_n])^2 = (n!)^{-2} \sum_{\pi_1, \pi_2} \mathrm{overlapPairFactor}$ | `JSP000506.secondMomentRatio_eq_overlap_sum` | `Overlap.lean` |
| Section 7, Diagonal profile sum | $\sum_{v \in \mathcal{V}} D(v) \le \exp(\eta_{\mathrm{diag}}(n) n / (\log n)^4)$, $\eta_{\mathrm{diag}}(n) \to 0$ | `JSP000506.eventually_sum_diagWeight_le` | `Diag.lean` |
| Lemma 8.6 ($4 \times 4$ table bound) | $W(L)^2 \le (D(r) A_L Q^L)(D(c) C_L Q^L)$ | `JSP000506.tableWeight_sq_le` | `HighCells.lean` |
| Section 8, High-skeleton sum | $\sum_{M, j} w(M, j) \le \exp(\eta_{\mathrm{hi}}(n) n / (\log n)^4)$, $\eta_{\mathrm{hi}}(n) \to 0$ | `JSP000506.eventually_sum_highSkeletonWeight_le` | `HighCells.lean` |
| Lemma 9.3 (Matching injectivity) | $F \mapsto F \setminus M$ injective on even overlap subgraphs when $M$ is a matching | `JSP000506.evenSubgraph_sdiff_matching_inj` | `Residual.lean` |
| Proposition 9.4 & Master residual | Conditional residual sum $\le m_0! \exp(n / (\log n)^5)$ uniformly across all $m_0$ | `JSP000506.absResSum_le_master` | `Residual.lean` |
| Sections 7–9, Unconditional 2nd moment | $\mathbb{E}[W_n^2]/(\mathbb{E}[W_n])^2 \le \exp(\eta_n n / (\log n)^4)$, $\eta_n \to 0$ | `JSP000506.petkovSubcriticalSecondMoment` | `Main.lean` |
| Section 10, Vertex Lipschitz | Agreeing away from $v_0 \implies |\zeta(G) - \zeta(G')| \le 1$ | `JSP000506.abs_cochromaticNumber_sub_le_one_of_agreeOffVertex` | `Basic.lean` |
| Section 10, McDiarmid tail | $\mathbb{P}(f(G_n) \ge \mathbb{E}[f] + u) \le \exp(-u^2 / (8n))$ | `JSP000506.mcdiarmid_gnpHalf_upper` | `Concentration.lean` |
| Section 10, Edit amplification | $\mathbb{P}(A) > e^{-u_1^2/(8n)} \implies \mathbb{P}(\mathrm{dist}(G, A) \ge u_1 + u_2) \le e^{-u_2^2/(8n)}$ | `JSP000506.probGnpHalf_vertexEditDist_ge_le` | `Concentration.lean` |
| Section 10, Ramsey leftover | Agreeing with $K$-cocolorable $H$ off $U \implies \zeta(G) \le K + |U|/r + 4^r$ | `JSP000506.cochromaticNumber_le_of_agreeOffSet` | `Concentration.lean` |
| Section 10, Rare-seed theorem | $\mathbb{P}(\zeta \le K_n) \ge e^{-\eta_n n / \log^4 n} \implies \mathbb{P}(\zeta \le K_n + \delta_n n / \log^3 n) \to 1$ | `JSP000506.tendsto_probGnpHalf_cochromatic_amplification` | `Concentration.lean` |
| Section 11, Unconditional Main Theorems | Unconditional Phase-Resolved, Quantitative $n / (\log n)^3$, & Erdős–Gimbel #625 | `JSP000506.petkovPhaseResolved625`, `JSP000506.petkovQuantitative625`, `JSP000506.erdosGimbel625` | `Main.lean` |

---

## 4. Build & Axiom Audit

Build and kernel-replay the entire `JSP000506` library from the repository root:

```bash
lake exe cache get
lake build
lake env leanchecker JSP000506
```

Verified `#print axioms` audit across all primary and unconditional top-level theorems:

```text
'JSP000506.cocolorable_iff_exists_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000506.cochromaticNumber_le_chromaticNumber' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000506.abs_cochromaticNumber_sub_le_one_of_agreeOffVertex' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000506.houseGraph_gap_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000506.toOuterMeasure_pmfGnpHalf_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000506.petkovA4_uniform_margin' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000506.petkovA4_gt_log_200_153' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000506.petkovA4_nonconstant' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000506.tendsto_probGnpHalf_indepCapEvent' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000506.exists_kChiMinus_sub_kCoSeed_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000506.eventually_witnessCounts_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000506.tendsto_probGnpHalf_chromatic_gt_kChiMinus' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000506.signed_overlap_pair_prob_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000506.secondMomentRatio_eq_overlap_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000506.eventually_sum_diagWeight_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000506.eventually_sum_highSkeletonWeight_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000506.eventually_secondMomentRatio_subcritical' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000506.mcdiarmid_gnpHalf_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000506.tendsto_probGnpHalf_cochromatic_amplification' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000506.petkovSubcriticalSecondMoment' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000506.petkovPhaseResolved625' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000506.petkovQuantitative625' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000506.erdosGimbel625' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## 5. Attribution & Clean-Room Provenance

- **Mathematical Problem**: Paul Erdős and John Gimbel (**Erdős Problem #625** / `JSP-000506`), with foundational contributions by Béla Bollobás (1988), Annika Heckel (2018, 2024), and Raphael Steiner (2024).
- **Mathematical Solution**: Samuil Petkov (with AI assistance acknowledged in the manuscript), *"A Full-Sequence Quantitative Gap Between the Chromatic and Cochromatic Numbers of a Random Graph"*, [`arXiv:2608.30604`](https://arxiv.org/abs/2608.30604) (August 2026). All mathematical credit for the proof strategy and quantitative bounds belongs to Petkov.
- **Lean 4 Formalization**: **Samuel Burbulla** ([@samuelburbulla](https://github.com/samuelburbulla)), developed with AI pair-programming assistance (Google DeepMind Antigravity).
  - **100% Clean-Room Authorship**: Every line of Lean 4 code (`16,119` lines across 14 files targeting `leanprover/lean4:v4.34.1` and Mathlib `v4.34.1`) was authored from scratch directly from the public mathematical manuscript `arXiv:2608.30604`, without inspecting, importing, or bootstrapping any third-party Lean repository.
  - **Extended Formal Scope**: In addition to `JSP000506.erdosGimbel625` (`ErdosGimbel625Statement`) and `JSP000506.petkovQuantitative625` (`PetkovQuantitative625Statement`), this formalization unconditionally establishes the full **phase-resolved refinement** `JSP000506.petkovPhaseResolved625` (`PetkovPhaseResolved625Statement` involving $A_4(\delta_n)$, noted in `arXiv:2608.30604` §12 as outside the scope of the manuscript's companion Lean note).
- **License**: Apache-2.0.
