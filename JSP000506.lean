import JSP000506.Defs
import JSP000506.Basic
import JSP000506.Model
import JSP000506.EntropyCert
import JSP000506.Phase
import JSP000506.PartA
import JSP000506.PartB
import JSP000506.Overlap
import JSP000506.Diag
import JSP000506.HighCells
import JSP000506.Residual
import JSP000506.Concentration
import JSP000506.Main

/-!
# JSP-000506 — Erdős Problem #625 (Erdős–Gimbel Chromatic vs. Cochromatic Gap)

Complete, 100% unconditional clean-room Lean 4 (`v4.34.1` + Mathlib `v4.34.1`) formalization of the
Erdős–Gimbel random-graph chromatic vs. cochromatic gap problem (`JSP-000506` / Erdős Problem #625)
and Samuil Petkov's resolution (*A Full-Sequence Quantitative Gap Between the Chromatic and
Cochromatic Numbers of a Random Graph*, `arXiv:2608.30604`, August 2026).

## Module Architecture

* `JSP000506.Defs`: Faithful definitions of homogeneous sets, cocolorings (`IsCocoloring`,
  `Cocolorable`), set partitions (`IsCocoloringPartition`), `cochromaticNumber`, equivalence
  `cocolorable_iff_exists_partition`, and signed homogeneous blocks (`SatisfiesSign`,
  `satisfiesSign_unique_of_two_le_card`).
* `JSP000506.Basic`: Unconditional deterministic properties (`cochromaticNumber_le_chromaticNumber`,
  complement invariance `cochromaticNumber_compl`, vertex-exposure `1`-Lipschitz stability
  `abs_cochromaticNumber_sub_le_one_of_agreeOffVertex`), and exact evaluations on `⊥`, `⊤`,
  `cycleGraph 4`, `cycleGraph 5`, and the 5-vertex `houseGraph` (`houseGraph_gap_eq_one`).
* `JSP000506.Model`: Dual `G(n, 1/2)` constructions (`probGnpHalf` uniform counting and `pmfGnpHalf`
  independent fair-coin `PMF`, proved identical in `toOuterMeasure_pmfGnpHalf_eq`), edge marginal
  identities, Markov and Paley–Zygmund inequalities, phase-function definitions (`alpha0`,
  `phaseDelta`, `targetDeficit`, `freeEnergyPlus`, `freeEnergyFour`, `petkovA4`, `petkovConstant`),
  and formal conjecture statements (`ErdosGimbel625Statement`, `PetkovQuantitative625Statement`,
  `PetkovPhaseResolved625Statement`) with unconditional reductions.
* `JSP000506.EntropyCert`: Constructive convexity/Legendre duality and uniform entropy certificate
  (Lemma 5.1: `petkovA4_uniform_margin`, `petkovA4_gt_log_200_153`, and `petkovA4_nonconstant`).
* `JSP000506.Phase`: Independence-number scale `alphaNat`, explicit Robbins–Stirling and
  falling-factorial asymptotics, and `IndepCapEvent` (`tendsto_probGnpHalf_indepCapEvent`).
* `JSP000506.PartA`: Continuous profile roots `sPlus`, `sFourCo`, `O(log log n / log n)` separation
  (`exists_kChiMinus_sub_kCoSeed_gap`), subcriticality of `kChiMinus`, and unimodular rounded 4-size
  seed multiplicities (`eventually_witnessCounts_spec`).
* `JSP000506.PartB`: Exact proper-coloring first moment, independence-capped histogram collapse,
  and unconditional Part B theorem `tendsto_probGnpHalf_chromatic_gt_kChiMinus`.
* `JSP000506.Overlap`: Signed 4-size witness `permSignedWitness` / `unordSignedWitness`,
  supercritical first moment, Walsh–Hadamard / binary cycle-space counting
  (`card_compatible_signs_eq_evenSubgraphs`), exact signed-overlap pair probability (Lemma 6.1:
  `signed_overlap_pair_prob_eq`), and normalized second-moment expansion
  (`secondMomentRatio_eq_overlap_sum`).
* `JSP000506.Diag`: Section 7 diagonal full-overlap profile weights `diagWeight` across the
  small-support forward recurrence, central Stirling/convex-rate negativity, and full-corner
  reverse-recurrence regimes (`eventually_sum_diagWeight_le`).
* `JSP000506.HighCells`: Section 8 canonical high-cell block matchings (`IsBlockMatching`),
  multiplicity-deficit geometric decay (`sum_highMultBox_highSkeletonWeight_le`), `4 × 4`
  endpoint-type table squared comparison (`tableWeight_sq_le`), and phase-uniform high-skeleton sum
  bound (`eventually_sum_highSkeletonWeight_le`).
* `JSP000506.Residual`: Section 9 single-permutation reduction (`secondMomentRatio_eq_single_perm_sum`),
  matching restriction injectivity (`evenSubgraph_sdiff_matching_inj`), joint prescribed-cell bound
  (`card_prescribed_absResBij_le`), intrinsic/complementary residual regimes (`absResSum_le_master`),
  high-cell fiber conditioning, and `eventually_secondMomentRatio_subcritical`.
* `JSP000506.Concentration`: Vertex-exposure bijection `vertexExposureEquiv`, elementary finite-product
  McDiarmid bounded-differences MGF/tail inequalities (`mcdiarmid_gnpHalf_upper`,
  `mcdiarmid_cochromaticNumber_upper`), two-step `vertexEditDist` amplification, Erdős–Szekeres
  Ramsey extraction, and `tendsto_probGnpHalf_cochromatic_amplification`.
* `JSP000506.Main`: Section 11 unconditional synthesis (`petkovSubcriticalSecondMoment`,
  `petkovPhaseResolved625`, `petkovQuantitative625`, `erdosGimbel625`).
-/
