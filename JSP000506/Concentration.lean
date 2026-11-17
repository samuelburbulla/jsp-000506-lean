import JSP000506.Basic
import JSP000506.Model
import JSP000506.Phase

/-!
# Section 10: Vertex-Exposure McDiarmid Concentration & Rare-Seed Ramsey Amplification

This module formalizes Section 10 of Samuil Petkov's *A Full-Sequence Quantitative Gap Between the
Chromatic and Cochromatic Numbers of a Random Graph* (`arXiv:2608.30604`) **100% unconditionally**:

1. **Vertex-Exposure Product Representation (`vertexExposureEquiv`)**:
   Bijects `SimpleGraph (Fin n)` with the finite product `VertexSpace n = ∀ v : Fin n, Fin v.val → Bool`
   where block `v` exposes all edges `{u, v}` with `u < v`. Updating block `v₀` preserves adjacency
   away from `v₀` (`agreeOffVertex_vertexExposure_update`).
2. **Elementary Finite-Product McDiarmid Bounded-Differences Inequality (`mgf_bounded_diff_pi`,
   `mcdiarmid_gnpHalf_upper`, `mcdiarmid_gnpHalf_lower`)**:
   Proves the moment-generating function bound `𝔼[exp(t(f - 𝔼 f))] ≤ exp(2 n t^2)` and exponential
   upper/lower tail inequalities `≤ exp(-u^2 / (8 n))` for any `1`-Lipschitz vertex-exposure graph
   functional `f`, including the cochromatic number `ζ(G)` (`mcdiarmid_cochromaticNumber_upper/lower`).
3. **Vertex-Edit Distance & Talagrand/McDiarmid Two-Step Amplification (`vertexEditDist`,
   `probGnpHalf_vertexEditDist_ge_le`)**:
   Amplifies any subexponentially rare seed event `ℙ(A) > exp(-u₁^2 / (8 n))` to exponential
   concentration of the vertex-edit distance `vertexEditDist A G < u₁ + u₂`.
4. **Erdős–Szekeres Ramsey Extraction & Leftover Cocoloring (`exists_clique_or_indep_of_two_pow_le`,
   `cochromaticNumber_le_of_agreeOffSet`, `tendsto_probGnpHalf_cochromatic_amplification`)**:
   Covers any edited vertex set `U` by at most `|U| / r + 4^r` cliques and independent sets, turning
   any `exp(-o(n / (log n)^4))` seed `K_n`-cocoloring event into a high-probability bound
   `ζ(G_n) ≤ K_n + o(n / (log n)^3)`.
-/

open Filter SimpleGraph Finset
open scoped Topology BigOperators Nat

namespace JSP000506

/-! ### 1. Vertex-Exposure Product Representation of `G(n, 1/2)` -/

/-- Coordinate `v : Fin n` in the vertex-exposure filtration exposes all edges `{u, v}` with `u < v`. -/
abbrev VertexBlock (n : ℕ) (v : Fin n) : Type :=
  Fin v.val → Bool

instance instNonemptyVertexBlock (n : ℕ) (v : Fin n) : Nonempty (VertexBlock n v) :=
  ⟨fun _ => false⟩

/-- Full `n`-step vertex-exposure product space `∏_{v : Fin n} ({0, 1}^{v})`. -/
abbrev VertexSpace (n : ℕ) : Type :=
  ∀ v : Fin n, VertexBlock n v

/-- Canonical bijection between the `n`-coordinate vertex-exposure product `VertexSpace n` and
`SimpleGraph (Fin n)`. -/
noncomputable def vertexExposureEquiv (n : ℕ) : VertexSpace n ≃ SimpleGraph (Fin n) where
  toFun x := SimpleGraph.fromRel (fun u v => ∃ h : u.val < v.val, x v ⟨u.val, h⟩ = true)
  invFun G v i := by
    classical
    exact decide (G.Adj ⟨i.val, i.isLt.trans v.isLt⟩ v)
  left_inv x := by
    classical
    funext v i
    let u : Fin n := ⟨i.val, i.isLt.trans v.isLt⟩
    have huv_lt : u.val < v.val := i.isLt
    have huv_ne : u ≠ v := Fin.ne_of_val_ne huv_lt.ne
    have hadj : (SimpleGraph.fromRel
        (fun a b : Fin n => ∃ h : a.val < b.val, x b ⟨a.val, h⟩ = true)).Adj u v ↔
        x v i = true := by
      rw [SimpleGraph.fromRel_adj]
      constructor
      · rintro ⟨_, ⟨h, hx⟩ | ⟨h', _⟩⟩
        · have hi : (⟨u.val, h⟩ : Fin v.val) = i := Fin.ext rfl
          rwa [hi] at hx
        · omega
      · intro hx
        exact ⟨huv_ne, Or.inl ⟨huv_lt, hx⟩⟩
    dsimp only
    cases hx : x v i
    · exact @decide_eq_false _ (Classical.propDecidable _) (mt hadj.mp (by simp [hx]))
    · exact @decide_eq_true _ (Classical.propDecidable _) (hadj.mpr hx)
  right_inv G := by
    classical
    ext u v
    rw [SimpleGraph.fromRel_adj]
    by_cases huv : u = v
    · subst huv
      exact ⟨fun ⟨hne, _⟩ => False.elim (hne rfl), fun hadj => False.elim (G.ne_of_adj hadj rfl)⟩
    · rw [and_iff_right huv]
      rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne huv) with hlt | hgt
      · constructor
        · rintro (⟨h, hdec⟩ | ⟨h', _⟩)
          · dsimp only at hdec
            have hu : (⟨u.val, h.trans v.isLt⟩ : Fin n) = u := Fin.ext rfl
            have hadj := of_decide_eq_true hdec
            rwa [hu] at hadj
          · omega
        · intro hadj
          refine Or.inl ⟨hlt, ?_⟩
          dsimp only
          refine decide_eq_true ?_
          have hu : (⟨u.val, hlt.trans v.isLt⟩ : Fin n) = u := Fin.ext rfl
          rwa [hu]
      · constructor
        · rintro (⟨h, _⟩ | ⟨h', hdec⟩)
          · omega
          · dsimp only at hdec
            have hv : (⟨v.val, h'.trans u.isLt⟩ : Fin n) = v := Fin.ext rfl
            have hadj := of_decide_eq_true hdec
            rw [hv] at hadj
            exact hadj.symm
        · intro hadj
          refine Or.inr ⟨hgt, ?_⟩
          dsimp only
          refine decide_eq_true ?_
          have hv : (⟨v.val, hgt.trans u.isLt⟩ : Fin n) = v := Fin.ext rfl
          rw [hv]
          exact hadj.symm

/-- Updating coordinate `v₀` in `VertexSpace n` changes edges incident to `v₀` only. -/
theorem agreeOffVertex_vertexExposure_update {n : ℕ} (x : VertexSpace n) (v₀ : Fin n)
    (b : VertexBlock n v₀) :
    AgreeOffVertex (vertexExposureEquiv n x)
      (vertexExposureEquiv n (Function.update x v₀ b)) v₀ := by
  intro u v hu hv
  simp only [vertexExposureEquiv, Equiv.coe_fn_mk, SimpleGraph.fromRel_adj,
    Function.update_of_ne hu, Function.update_of_ne hv]

/-- Expectation under `G(n, 1/2)` equals the uniform average over `VertexSpace n`. -/
theorem expectGnpHalf_eq_vertexSpace_avg (n : ℕ) (X : SimpleGraph (Fin n) → ℝ) :
    expectGnpHalf n X =
      (∑ x : VertexSpace n, X (vertexExposureEquiv n x)) /
        (Fintype.card (VertexSpace n) : ℝ) := by
  unfold expectGnpHalf
  rw [← Equiv.sum_comp (vertexExposureEquiv n), Fintype.card_congr (vertexExposureEquiv n)]

/-! ### 2. Elementary McDiarmid Bounded-Differences Inequality on Finite Uniform Products -/

/-- Global elementary hyperbolic bound `(exp u + exp (-u)) / 2 ≤ exp (2 * u^2)` proved purely from
`Real.add_one_le_exp`. -/
private lemma cosh_le_exp_two_sq (u : ℝ) :
    (Real.exp u + Real.exp (-u)) / 2 ≤ Real.exp (2 * u ^ 2) := by
  by_cases hu : |u| ≤ 1 / 2
  · rcases abs_le.mp hu with ⟨hlo, hhi⟩
    have h1 : (1 - u) * Real.exp u ≤ 1 := by
      have he := Real.add_one_le_exp (-u)
      have hmul := mul_le_mul_of_nonneg_right he (Real.exp_pos u).le
      have hexp0 : Real.exp (-u) * Real.exp u = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      linarith
    have h2 : (1 + u) * Real.exp (-u) ≤ 1 := by
      have he := Real.add_one_le_exp u
      have hmul := mul_le_mul_of_nonneg_right he (Real.exp_pos (-u)).le
      have hexp0 : Real.exp u * Real.exp (-u) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      linarith
    have h3 : (1 - u ^ 2) * ((Real.exp u + Real.exp (-u)) / 2) ≤ 1 := by
      have h1' : (1 + u) * ((1 - u) * Real.exp u) ≤ 1 + u :=
        (mul_le_mul_of_nonneg_left h1 (by linarith)).trans_eq (mul_one _)
      have h2' : (1 - u) * ((1 + u) * Real.exp (-u)) ≤ 1 - u :=
        (mul_le_mul_of_nonneg_left h2 (by linarith)).trans_eq (mul_one _)
      nlinarith
    have hu2_nn : 0 ≤ u ^ 2 := sq_nonneg u
    have hu2_le : u ^ 2 ≤ 1 / 4 := by nlinarith
    have h4 : 1 ≤ (1 - u ^ 2) * (1 + 2 * u ^ 2) := by
      have hid : (1 - u ^ 2) * (1 + 2 * u ^ 2) - 1 = u ^ 2 * (1 - 2 * u ^ 2) := by ring
      have hprod : 0 ≤ u ^ 2 * (1 - 2 * u ^ 2) := mul_nonneg hu2_nn (by linarith)
      linarith
    have hpos : 0 < 1 - u ^ 2 := by linarith
    have h5 : (Real.exp u + Real.exp (-u)) / 2 ≤ 1 + 2 * u ^ 2 :=
      le_of_mul_le_mul_left (h3.trans h4) hpos
    exact h5.trans (by linarith [Real.add_one_le_exp (2 * u ^ 2)])
  · have habs : 1 / 2 < |u| := not_le.mp hu
    have hsq : |u| ≤ 2 * u ^ 2 := by
      have h2 : |u| ^ 2 = u ^ 2 := sq_abs u
      nlinarith
    have hu_le : Real.exp u ≤ Real.exp (2 * u ^ 2) :=
      Real.exp_le_exp.mpr ((le_abs_self u).trans hsq)
    have hnu_le : Real.exp (-u) ≤ Real.exp (2 * u ^ 2) :=
      Real.exp_le_exp.mpr ((neg_le_abs u).trans hsq)
    linarith

/-- Elementary finite-average Jensen inequality for `Real.exp` proved from `1 + x ≤ exp x`. -/
private lemma exp_sum_div_card_le {β : Type*} [Fintype β] [Nonempty β] (h : β → ℝ) :
    Real.exp ((∑ b : β, h b) / (Fintype.card β : ℝ)) ≤
      (∑ b : β, Real.exp (h b)) / (Fintype.card β : ℝ) := by
  set N : ℝ := (Fintype.card β : ℝ)
  have hN_pos : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  set m : ℝ := (∑ b : β, h b) / N
  have hterm : ∀ b : β, 1 + (h b - m) ≤ Real.exp (h b) * Real.exp (-m) := by
    intro b
    have h1 := Real.add_one_le_exp (h b - m)
    rw [sub_eq_add_neg, Real.exp_add] at h1
    linarith
  have hsum_lhs : ∑ b : β, (1 + (h b - m)) = N := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
    have hNm : N * m = ∑ b : β, h b := mul_div_cancel₀ _ hN_pos.ne'
    linarith
  have hsum_le : N ≤ (∑ b : β, Real.exp (h b)) * Real.exp (-m) := by
    calc
      N = ∑ b : β, (1 + (h b - m)) := hsum_lhs.symm
      _ ≤ ∑ b : β, Real.exp (h b) * Real.exp (-m) := Finset.sum_le_sum fun b _ => hterm b
      _ = (∑ b : β, Real.exp (h b)) * Real.exp (-m) := (Finset.sum_mul _ _ _).symm
  have hmul := mul_le_mul_of_nonneg_right hsum_le (div_nonneg (Real.exp_pos m).le hN_pos.le)
  have hlhs : N * (Real.exp m / N) = Real.exp m := mul_div_cancel₀ _ hN_pos.ne'
  have hrhs : (∑ b : β, Real.exp (h b)) * Real.exp (-m) * (Real.exp m / N) =
      (∑ b : β, Real.exp (h b)) / N := by
    have hexp0 : Real.exp (-m) * Real.exp m = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc
      (∑ b : β, Real.exp (h b)) * Real.exp (-m) * (Real.exp m / N)
          = (∑ b : β, Real.exp (h b)) * (Real.exp (-m) * Real.exp m) / N := by ring
      _ = (∑ b : β, Real.exp (h b)) / N := by rw [hexp0, mul_one]
  linarith

/-- Single-coordinate symmetrization MGF bound for a function `g : β → ℝ` of diameter `≤ 1`. -/
private lemma mgf_coord_le {β : Type*} [Fintype β] [Nonempty β]
    {g : β → ℝ} (hg : ∀ b₁ b₂ : β, |g b₁ - g b₂| ≤ 1) (t : ℝ) :
    (∑ b : β, Real.exp (t * (g b - (∑ b' : β, g b') / (Fintype.card β : ℝ)))) /
      (Fintype.card β : ℝ) ≤ Real.exp (2 * t ^ 2) := by
  set N : ℝ := (Fintype.card β : ℝ)
  have hN_pos : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hpoint : ∀ b : β,
      Real.exp (t * (g b - (∑ b' : β, g b') / N)) ≤
        (∑ b' : β, Real.exp (t * (g b - g b'))) / N := by
    intro b
    have hmean : t * (g b - (∑ b' : β, g b') / N) =
        (∑ b' : β, t * (g b - g b')) / N := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Finset.mul_sum]
      field_simp [hN_pos.ne']
      dsimp only [N]
    rw [hmean]
    exact exp_sum_div_card_le (fun b' => t * (g b - g b'))
  have hjensen :
      (∑ b : β, Real.exp (t * (g b - (∑ b' : β, g b') / N))) / N ≤
        (∑ b : β, ∑ b' : β, Real.exp (t * (g b - g b'))) / N ^ 2 := by
    calc
      (∑ b : β, Real.exp (t * (g b - (∑ b' : β, g b') / N))) / N
          ≤ (∑ b : β, (∑ b' : β, Real.exp (t * (g b - g b'))) / N) / N :=
            div_le_div_of_nonneg_right (Finset.sum_le_sum fun b _ => hpoint b) hN_pos.le
      _ = (∑ b : β, ∑ b' : β, Real.exp (t * (g b - g b'))) / N ^ 2 := by
            rw [← Finset.sum_div, div_div, sq]
  have hsymm :
      (∑ b : β, ∑ b' : β, Real.exp (t * (g b - g b'))) =
        ∑ b : β, ∑ b' : β,
          (Real.exp (t * (g b - g b')) + Real.exp (-(t * (g b - g b')))) / 2 := by
    have hflip :
        (∑ b : β, ∑ b' : β, Real.exp (t * (g b - g b'))) =
          ∑ b : β, ∑ b' : β, Real.exp (-(t * (g b - g b'))) := by
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
      congr 1
      ring
    have h2 :
        2 * (∑ b : β, ∑ b' : β, Real.exp (t * (g b - g b'))) =
          ∑ b : β, ∑ b' : β,
            (Real.exp (t * (g b - g b')) + Real.exp (-(t * (g b - g b')))) := by
      calc
        2 * (∑ b : β, ∑ b' : β, Real.exp (t * (g b - g b')))
            = (∑ b : β, ∑ b' : β, Real.exp (t * (g b - g b'))) +
                (∑ b : β, ∑ b' : β, Real.exp (-(t * (g b - g b')))) := by linarith [hflip]
        _ = ∑ b : β, ∑ b' : β,
              (Real.exp (t * (g b - g b')) + Real.exp (-(t * (g b - g b')))) := by
              rw [← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun b _ => (Finset.sum_add_distrib).symm
    have hdiv2 :
        ∑ b : β, ∑ b' : β,
          (Real.exp (t * (g b - g b')) + Real.exp (-(t * (g b - g b')))) / 2 =
        (∑ b : β, ∑ b' : β,
          (Real.exp (t * (g b - g b')) + Real.exp (-(t * (g b - g b'))))) / 2 := by
      simp_rw [← Finset.sum_div]
    linarith
  have hpair_bound : ∀ b b' : β,
      (Real.exp (t * (g b - g b')) + Real.exp (-(t * (g b - g b')))) / 2 ≤
        Real.exp (2 * t ^ 2) := by
    intro b b'
    refine (cosh_le_exp_two_sq (t * (g b - g b'))).trans (Real.exp_le_exp.mpr ?_)
    have hdiff_sq : (g b - g b') ^ 2 ≤ 1 := by
      have habs := hg b b'
      have hsq : |g b - g b'| ^ 2 ≤ (1 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
      rwa [sq_abs, one_pow] at hsq
    calc
      2 * (t * (g b - g b')) ^ 2 = (2 * t ^ 2) * (g b - g b') ^ 2 := by ring
      _ ≤ (2 * t ^ 2) * 1 := mul_le_mul_of_nonneg_left hdiff_sq (by positivity)
      _ = 2 * t ^ 2 := mul_one _
  have hsum_bound :
      (∑ b : β, ∑ b' : β, Real.exp (t * (g b - g b'))) ≤ N ^ 2 * Real.exp (2 * t ^ 2) := by
    rw [hsymm]
    calc
      ∑ b : β, ∑ b' : β,
          (Real.exp (t * (g b - g b')) + Real.exp (-(t * (g b - g b')))) / 2
          ≤ ∑ _b : β, ∑ _b' : β, Real.exp (2 * t ^ 2) :=
            Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ => hpair_bound b b'
      _ = N ^ 2 * Real.exp (2 * t ^ 2) := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
  refine hjensen.trans ?_
  exact (div_le_div_of_nonneg_right hsum_bound (by positivity)).trans_eq
    (mul_div_cancel_left₀ _ (pow_ne_zero 2 hN_pos.ne'))

/-- **Finite-Product McDiarmid MGF Bound**:
On any finite product `∀ i : Fin m, α i` of nonempty finite types, if changing coordinate `i` alters
`F` by at most `1`, then `𝔼[exp(t (F - 𝔼 F))] ≤ exp(2 m t^2)` for all `t : ℝ`. -/
theorem mgf_bounded_diff_pi :
    ∀ (m : ℕ) (α : Fin m → Type) [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
      (F : (∀ i : Fin m, α i) → ℝ),
      (∀ (i : Fin m) (x : ∀ j : Fin m, α j) (b₁ b₂ : α i),
        |F (Function.update x i b₁) - F (Function.update x i b₂)| ≤ 1) →
      ∀ t : ℝ,
        (∑ x : (∀ i : Fin m, α i),
          Real.exp (t * (F x - (∑ y : (∀ i : Fin m, α i), F y) /
            (Fintype.card (∀ i : Fin m, α i) : ℝ)))) /
          (Fintype.card (∀ i : Fin m, α i) : ℝ) ≤
        Real.exp (2 * (m : ℝ) * t ^ 2) := by
  intro m
  induction m with
  | zero =>
    intro α _ _ F _ t
    have hcard1 : Fintype.card (∀ i : Fin 0, α i) = 1 := by simp
    have huniv1 : (Finset.univ : Finset (∀ i : Fin 0, α i)).card = 1 := by
      rw [Finset.card_univ, hcard1]
    rcases Finset.card_eq_one.mp huniv1 with ⟨x₀, hx₀⟩
    change (∑ x ∈ (Finset.univ : Finset (∀ i : Fin 0, α i)),
        Real.exp (t * (F x - (∑ y ∈ (Finset.univ : Finset (∀ i : Fin 0, α i)), F y) /
          (Fintype.card (∀ i : Fin 0, α i) : ℝ)))) /
        (Fintype.card (∀ i : Fin 0, α i) : ℝ) ≤ Real.exp (2 * ((0 : ℕ) : ℝ) * t ^ 2)
    rw [hx₀, hcard1]
    simp
  | succ m ih =>
    intro α _ _ F hF t
    let α' : Fin m → Type := fun j => α j.succ
    let e : (α 0 × (∀ j : Fin m, α' j)) ≃ (∀ i : Fin (m + 1), α i) :=
      { toFun := fun p => Fin.cons p.1 p.2
        invFun := fun x => (x 0, fun j => x j.succ)
        left_inv := fun ⟨b, y⟩ => by ext <;> simp [Fin.cons_zero, Fin.cons_succ]
        right_inv := fun x => by
          funext i
          cases i using Fin.cases <;> simp [Fin.cons_zero, Fin.cons_succ] }
    set N₀ : ℝ := (Fintype.card (α 0) : ℝ)
    set N' : ℝ := (Fintype.card (∀ j : Fin m, α' j) : ℝ)
    have hN₀_pos : 0 < N₀ := Nat.cast_pos.mpr Fintype.card_pos
    have hN'_pos : 0 < N' := Nat.cast_pos.mpr Fintype.card_pos
    have hcard_tot : (Fintype.card (∀ i : Fin (m + 1), α i) : ℝ) = N₀ * N' := by
      rw [Fintype.card_congr e.symm, Fintype.card_prod, Nat.cast_mul]
    set μ : ℝ := (∑ y : (∀ i : Fin (m + 1), α i), F y) /
      (Fintype.card (∀ i : Fin (m + 1), α i) : ℝ)
    let Fbar : α 0 → ℝ := fun b => (∑ y : (∀ j : Fin m, α' j), F (e (b, y))) / N'
    have hFbar_mean : (∑ b : α 0, Fbar b) / N₀ = μ := by
      simp only [Fbar, μ, hcard_tot]
      rw [← Equiv.sum_comp e, Fintype.sum_prod_type, ← Finset.sum_div, div_div, mul_comm N' N₀]
    -- Diameter `≤ 1` of `Fbar` along coordinate `0`
    have hFbar_lip : ∀ b₁ b₂ : α 0, |Fbar b₁ - Fbar b₂| ≤ 1 := by
      intro b₁ b₂
      have hupd0 : ∀ y : (∀ j : Fin m, α' j),
          e (b₁, y) = Function.update (e (b₂, y)) 0 b₁ ∧
          e (b₂, y) = Function.update (e (b₂, y)) 0 b₂ := by
        intro y
        constructor <;>
        · funext i
          cases i using Fin.cases <;> simp [e]
      have hsum_diff : Fbar b₁ - Fbar b₂ =
          (∑ y : (∀ j : Fin m, α' j), (F (e (b₁, y)) - F (e (b₂, y)))) / N' := by
        simp only [Fbar, ← sub_div, ← Finset.sum_sub_distrib]
      rw [hsum_diff, abs_div, abs_of_pos hN'_pos]
      refine (div_le_one hN'_pos).mpr ?_
      calc
        |∑ y : (∀ j : Fin m, α' j), (F (e (b₁, y)) - F (e (b₂, y)))|
            ≤ ∑ y : (∀ j : Fin m, α' j), |F (e (b₁, y)) - F (e (b₂, y))| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _y : (∀ j : Fin m, α' j), (1 : ℝ) := by
              refine Finset.sum_le_sum fun y _ => ?_
              rcases hupd0 y with ⟨hu1, hu2⟩
              rw [hu1]
              nth_rw 2 [hu2]
              exact hF 0 (e (b₂, y)) b₁ b₂
        _ = N' := by simp [N']
    -- Apply `ih` to each slice `y ↦ F (e (b, y))`
    have hslice : ∀ b : α 0,
        (∑ y : (∀ j : Fin m, α' j), Real.exp (t * (F (e (b, y)) - Fbar b))) / N' ≤
          Real.exp (2 * (m : ℝ) * t ^ 2) := by
      intro b
      refine ih α' (fun y => F (e (b, y))) ?_ t
      intro j y c₁ c₂
      have hupdj : ∀ c : α' j,
          e (b, Function.update y j c) = Function.update (e (b, y)) j.succ c := by
        intro c
        funext i
        cases i using Fin.cases with
        | zero =>
          simp only [e, Equiv.coe_fn_mk]
          rw [Fin.cons_zero, Function.update_of_ne (Fin.succ_ne_zero j).symm, Fin.cons_zero]
        | succ k =>
          simp only [e, Equiv.coe_fn_mk]
          by_cases hkj : k = j
          · subst hkj
            rw [Fin.cons_succ, Function.update_self, Function.update_self]
          · have hne : k.succ ≠ j.succ := mt Fin.succ_inj.mp hkj
            rw [Fin.cons_succ, Function.update_of_ne hkj, Function.update_of_ne hne, Fin.cons_succ]
      rw [hupdj c₁, hupdj c₂]
      exact hF j.succ (e (b, y)) c₁ c₂
    -- Factorize the product sum into outer coordinate `b` and inner slice `y`
    have hfactor :
        (∑ x : (∀ i : Fin (m + 1), α i), Real.exp (t * (F x - μ))) /
          (Fintype.card (∀ i : Fin (m + 1), α i) : ℝ) =
        (∑ b : α 0, Real.exp (t * (Fbar b - μ)) *
          ((∑ y : (∀ j : Fin m, α' j), Real.exp (t * (F (e (b, y)) - Fbar b))) / N')) / N₀ := by
      rw [hcard_tot, ← Equiv.sum_comp e, Fintype.sum_prod_type]
      have hinner_eq : ∀ b : α 0,
          (∑ y : (∀ j : Fin m, α' j), Real.exp (t * (F (e (b, y)) - μ))) =
          Real.exp (t * (Fbar b - μ)) *
            ∑ y : (∀ j : Fin m, α' j), Real.exp (t * (F (e (b, y)) - Fbar b)) := by
        intro b
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← Real.exp_add]
        congr 1
        ring
      simp_rw [hinner_eq]
      rw [mul_comm N₀ N', ← div_div, Finset.sum_div]
      simp_rw [mul_div_assoc]
    rw [hfactor]
    calc
      (∑ b : α 0, Real.exp (t * (Fbar b - μ)) *
          ((∑ y : (∀ j : Fin m, α' j), Real.exp (t * (F (e (b, y)) - Fbar b))) / N')) / N₀
          ≤ (∑ b : α 0, Real.exp (t * (Fbar b - μ)) * Real.exp (2 * (m : ℝ) * t ^ 2)) / N₀ := by
            refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun b _ => ?_) hN₀_pos.le
            exact mul_le_mul_of_nonneg_left (hslice b) (Real.exp_pos _).le
      _ = ((∑ b : α 0, Real.exp (t * (Fbar b - (∑ b' : α 0, Fbar b') / N₀))) / N₀) *
            Real.exp (2 * (m : ℝ) * t ^ 2) := by
            rw [hFbar_mean, ← Finset.sum_mul, mul_div_right_comm]
      _ ≤ Real.exp (2 * t ^ 2) * Real.exp (2 * (m : ℝ) * t ^ 2) :=
            mul_le_mul_of_nonneg_right (mgf_coord_le hFbar_lip t) (Real.exp_pos _).le
      _ = Real.exp (2 * ((m + 1 : ℕ) : ℝ) * t ^ 2) := by
            rw [← Real.exp_add, Nat.cast_add, Nat.cast_one]
            congr 1
            ring

/-- **Vertex-Exposure MGF Bound in `G(n, 1/2)`**:
If `|f G - f G'| ≤ 1` whenever `G, G'` agree away from a single vertex `v`, then
`𝔼[exp(t (f(G) - 𝔼 f))] ≤ exp(2 n t^2)` for all `t : ℝ`. -/
theorem mgf_gnpHalf_le_of_agreeOffVertex {n : ℕ} {f : SimpleGraph (Fin n) → ℝ}
    (hf : ∀ (G G' : SimpleGraph (Fin n)) (v : Fin n),
      AgreeOffVertex G G' v → |f G - f G'| ≤ 1)
    (t : ℝ) :
    expectGnpHalf n (fun G => Real.exp (t * (f G - expectGnpHalf n f))) ≤
      Real.exp (2 * (n : ℝ) * t ^ 2) := by
  rw [expectGnpHalf_eq_vertexSpace_avg]
  simp_rw [expectGnpHalf_eq_vertexSpace_avg n f]
  refine mgf_bounded_diff_pi n (VertexBlock n) (fun x => f (vertexExposureEquiv n x)) ?_ t
  intro v x b₁ b₂
  have h1 := agreeOffVertex_vertexExposure_update x v b₁
  have h2 := agreeOffVertex_vertexExposure_update x v b₂
  have h12 : AgreeOffVertex (vertexExposureEquiv n (Function.update x v b₁))
      (vertexExposureEquiv n (Function.update x v b₂)) v :=
    fun u w hu hw => (h1.symm hu hw).trans (h2 hu hw)
  exact hf _ _ v h12

/-- **McDiarmid Upper Tail Bound for Vertex-Exposure Lipschitz Functionals on `G(n, 1/2)`**:
For `n > 0` and `u ≥ 0`, `ℙ(f(G) ≥ 𝔼[f] + u) ≤ exp(- u^2 / (8 n))`. -/
theorem mcdiarmid_gnpHalf_upper {n : ℕ} (hn : 0 < n) {f : SimpleGraph (Fin n) → ℝ}
    (hf : ∀ (G G' : SimpleGraph (Fin n)) (v : Fin n),
      AgreeOffVertex G G' v → |f G - f G'| ≤ 1)
    {u : ℝ} (hu : 0 ≤ u) :
    probGnpHalf n {G : SimpleGraph (Fin n) | expectGnpHalf n f + u ≤ f G} ≤
      Real.exp (- u ^ 2 / (8 * (n : ℝ))) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  let t : ℝ := u / (4 * (n : ℝ))
  have ht_nonneg : 0 ≤ t := by positivity
  have hsub : {G : SimpleGraph (Fin n) | expectGnpHalf n f + u ≤ f G} ⊆
      {G : SimpleGraph (Fin n) | Real.exp (t * u) ≤ Real.exp (t * (f G - expectGnpHalf n f))} := by
    intro G hG
    simp only [Set.mem_ofPred_eq] at hG ⊢
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) ht_nonneg)
  calc
    probGnpHalf n {G | expectGnpHalf n f + u ≤ f G}
        ≤ probGnpHalf n {G | Real.exp (t * u) ≤ Real.exp (t * (f G - expectGnpHalf n f))} :=
          probGnpHalf_mono hsub
    _ ≤ expectGnpHalf n (fun G => Real.exp (t * (f G - expectGnpHalf n f))) / Real.exp (t * u) :=
          probGnpHalf_ge_le_expect_div (fun _ => (Real.exp_pos _).le) (Real.exp_pos _)
    _ ≤ Real.exp (2 * (n : ℝ) * t ^ 2) / Real.exp (t * u) :=
          div_le_div_of_nonneg_right (mgf_gnpHalf_le_of_agreeOffVertex hf t) (Real.exp_pos _).le
    _ = Real.exp (- u ^ 2 / (8 * (n : ℝ))) := by
          rw [← Real.exp_sub]
          congr 1
          simp only [t]
          field_simp [hn_pos.ne']
          ring

/-- **McDiarmid Lower Tail Bound for Vertex-Exposure Lipschitz Functionals on `G(n, 1/2)`**:
For `n > 0` and `u ≥ 0`, `ℙ(f(G) ≤ 𝔼[f] - u) ≤ exp(- u^2 / (8 n))`. -/
theorem mcdiarmid_gnpHalf_lower {n : ℕ} (hn : 0 < n) {f : SimpleGraph (Fin n) → ℝ}
    (hf : ∀ (G G' : SimpleGraph (Fin n)) (v : Fin n),
      AgreeOffVertex G G' v → |f G - f G'| ≤ 1)
    {u : ℝ} (hu : 0 ≤ u) :
    probGnpHalf n {G : SimpleGraph (Fin n) | f G ≤ expectGnpHalf n f - u} ≤
      Real.exp (- u ^ 2 / (8 * (n : ℝ))) := by
  have hneg_exp : expectGnpHalf n (fun G => - f G) = - expectGnpHalf n f := by
    simpa using expectGnpHalf_mul_const n (-1 : ℝ) f
  have hneg_lip : ∀ (G G' : SimpleGraph (Fin n)) (v : Fin n),
      AgreeOffVertex G G' v → |(- f G) - (- f G')| ≤ 1 := by
    intro G G' v h
    rw [show (- f G) - (- f G') = -(f G - f G') by ring, abs_neg]
    exact hf G G' v h
  have hevent : {G : SimpleGraph (Fin n) | f G ≤ expectGnpHalf n f - u} =
      {G : SimpleGraph (Fin n) | expectGnpHalf n (fun H => - f H) + u ≤ - f G} := by
    ext G
    simp only [Set.mem_ofPred_eq, hneg_exp]
    constructor <;> intro h <;> linarith
  rw [hevent]
  exact mcdiarmid_gnpHalf_upper hn hneg_lip hu

/-- Specialization of McDiarmid's upper tail to `cochromaticNumber` on `G(n, 1/2)`. -/
theorem mcdiarmid_cochromaticNumber_upper {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : 0 ≤ u) :
    probGnpHalf n {G : SimpleGraph (Fin n) |
      expectGnpHalf n (fun H => (cochromaticNumber H : ℝ)) + u ≤ (cochromaticNumber G : ℝ)} ≤
      Real.exp (- u ^ 2 / (8 * (n : ℝ))) := by
  refine mcdiarmid_gnpHalf_upper hn (fun G G' v h => ?_) hu
  have hZ := abs_cochromaticNumber_sub_le_one_of_agreeOffVertex h
  exact_mod_cast hZ

/-! ### 3. Vertex-Edit Distance and Two-Step Rare-Seed Amplification -/

/-- Two graphs `G, H` on `Fin n` agree outside `U : Finset (Fin n)` if they have identical
adjacency on `Fin n \ U`. -/
def AgreeOffSet {n : ℕ} (U : Finset (Fin n)) (G H : SimpleGraph (Fin n)) : Prop :=
  ∀ ⦃u v : Fin n⦄, u ∉ U → v ∉ U → (G.Adj u v ↔ H.Adj u v)

/-- Minimum number of vertices whose incident edges can be modified in `G` to reach `A`. -/
noncomputable def vertexEditDist {n : ℕ} (A : Set (SimpleGraph (Fin n)))
    (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k : ℕ | ∃ U : Finset (Fin n), U.card ≤ k ∧ ∃ H ∈ A, AgreeOffSet U G H}

theorem vertexEditDist_spec {n : ℕ} {A : Set (SimpleGraph (Fin n))} (hA : A.Nonempty)
    (G : SimpleGraph (Fin n)) :
    ∃ U : Finset (Fin n), U.card ≤ vertexEditDist A G ∧ ∃ H ∈ A, AgreeOffSet U G H := by
  rcases hA with ⟨H₀, hH₀⟩
  have hne : {k : ℕ | ∃ U : Finset (Fin n), U.card ≤ k ∧ ∃ H ∈ A, AgreeOffSet U G H}.Nonempty :=
    ⟨(Finset.univ : Finset (Fin n)).card, Finset.univ, le_rfl, H₀, hH₀,
      fun u _ hu _ => False.elim (hu (Finset.mem_univ u))⟩
  exact Nat.sInf_mem hne

theorem vertexEditDist_eq_zero_of_mem {n : ℕ} {A : Set (SimpleGraph (Fin n))}
    {G : SimpleGraph (Fin n)} (hG : G ∈ A) :
    vertexEditDist A G = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact Nat.sInf_le ⟨∅, le_rfl, G, hG, fun _ _ _ _ => Iff.rfl⟩

theorem abs_vertexEditDist_sub_le_one {n : ℕ} {A : Set (SimpleGraph (Fin n))} (hA : A.Nonempty)
    {G G' : SimpleGraph (Fin n)} {v₀ : Fin n} (h : AgreeOffVertex G G' v₀) :
    |(vertexEditDist A G : ℝ) - (vertexEditDist A G' : ℝ)| ≤ 1 := by
  have hstep : ∀ {G₁ G₂ : SimpleGraph (Fin n)}, AgreeOffVertex G₁ G₂ v₀ →
      vertexEditDist A G₁ ≤ vertexEditDist A G₂ + 1 := by
    intro G₁ G₂ h₁₂
    rcases vertexEditDist_spec hA G₂ with ⟨U, hUcard, H, hHA, hagree⟩
    refine Nat.sInf_le ⟨insert v₀ U, (Finset.card_insert_le v₀ U).trans (by omega), H, hHA, ?_⟩
    intro u v hu hv
    have huv₀ : u ≠ v₀ := fun heq => hu (heq ▸ Finset.mem_insert_self v₀ U)
    have hvv₀ : v ≠ v₀ := fun heq => hv (heq ▸ Finset.mem_insert_self v₀ U)
    have huU : u ∉ U := fun hmem => hu (Finset.mem_insert_of_mem hmem)
    have hvU : v ∉ U := fun hmem => hv (Finset.mem_insert_of_mem hmem)
    exact (h₁₂ huv₀ hvv₀).trans (hagree huU hvU)
  have h1 := hstep h
  have h2 := hstep h.symm
  rw [abs_le]
  constructor
  · exact_mod_cast (by omega : - (1 : ℤ) ≤ (vertexEditDist A G : ℤ) - (vertexEditDist A G' : ℤ))
  · exact_mod_cast (by omega : (vertexEditDist A G : ℤ) - (vertexEditDist A G' : ℤ) ≤ 1)

/-- **Two-Step McDiarmid/Talagrand Amplification Lemma (`arXiv:2608.30604`, Section 10)**:
Whenever `ℙ(A) > exp(- u₁^2 / (8 n))` (`u₁, u₂ ≥ 0`, `n > 0`), we have `𝔼[vertexEditDist A] < u₁`
and consequently `ℙ(vertexEditDist A G ≥ u₁ + u₂) ≤ exp(- u₂^2 / (8 n))`. -/
theorem probGnpHalf_vertexEditDist_ge_le {n : ℕ} (hn : 0 < n)
    {A : Set (SimpleGraph (Fin n))} {u₁ u₂ : ℝ} (hu₁ : 0 ≤ u₁) (hu₂ : 0 ≤ u₂)
    (hprobA : Real.exp (- u₁ ^ 2 / (8 * (n : ℝ))) < probGnpHalf n A) :
    probGnpHalf n {G : SimpleGraph (Fin n) | u₁ + u₂ ≤ (vertexEditDist A G : ℝ)} ≤
      Real.exp (- u₂ ^ 2 / (8 * (n : ℝ))) := by
  have hA : A.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty.mp hempty, probGnpHalf_empty] at hprobA
    linarith [Real.exp_pos (- u₁ ^ 2 / (8 * (n : ℝ)))]
  have hlip : ∀ (G G' : SimpleGraph (Fin n)) (v : Fin n),
      AgreeOffVertex G G' v → |(vertexEditDist A G : ℝ) - (vertexEditDist A G' : ℝ)| ≤ 1 :=
    fun _ _ _ h => abs_vertexEditDist_sub_le_one hA h
  set μ : ℝ := expectGnpHalf n (fun G => (vertexEditDist A G : ℝ))
  have hμ_lt : μ < u₁ := by
    by_contra hge
    have hu₁_le_μ : u₁ ≤ μ := not_lt.mp hge
    have hsubA : A ⊆ {G : SimpleGraph (Fin n) | (vertexEditDist A G : ℝ) ≤ μ - u₁} := by
      intro G hG
      simp only [Set.mem_ofPred_eq, vertexEditDist_eq_zero_of_mem hG, Nat.cast_zero]
      linarith
    have hbound := (probGnpHalf_mono hsubA).trans (mcdiarmid_gnpHalf_lower hn hlip hu₁)
    linarith
  have hsub_hi :
      {G : SimpleGraph (Fin n) | u₁ + u₂ ≤ (vertexEditDist A G : ℝ)} ⊆
      {G : SimpleGraph (Fin n) | μ + u₂ ≤ (vertexEditDist A G : ℝ)} := by
    intro G hG
    simp only [Set.mem_ofPred_eq] at hG ⊢
    linarith
  exact (probGnpHalf_mono hsub_hi).trans (mcdiarmid_gnpHalf_upper hn hlip hu₂)

/-! ### 4. Erdős–Szekeres Ramsey Extraction & Leftover Cocoloring -/

/-- **Erdős–Szekeres Asymmetric Ramsey Bound (`2^{a + b}`)**:
Every vertex subset `S` with `2^(a + b) ≤ |S|` contains either an `a`-clique or a `b`-independent set. -/
theorem exists_clique_or_indep_of_two_pow_le {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∀ (s : ℕ) {a b : ℕ}, a + b = s → ∀ (S : Finset (Fin n)), 2 ^ s ≤ S.card →
      (∃ T ⊆ S, a ≤ T.card ∧ G.IsClique (T : Set (Fin n))) ∨
      (∃ T ⊆ S, b ≤ T.card ∧ G.IsIndepSet (T : Set (Fin n))) := by
  intro s
  induction s with
  | zero =>
    intro a b hab S _
    have ha : a = 0 := by omega
    subst ha
    exact Or.inl ⟨∅, Finset.empty_subset S, le_rfl, by simp⟩
  | succ s ih =>
    intro a b hab S hS
    by_cases ha : a = 0
    · subst ha
      exact Or.inl ⟨∅, Finset.empty_subset S, le_rfl, by simp⟩
    · by_cases hb : b = 0
      · subst hb
        exact Or.inr ⟨∅, Finset.empty_subset S, le_rfl, by simp⟩
      · rcases Nat.exists_eq_succ_of_ne_zero ha with ⟨a', rfl⟩
        rcases Nat.exists_eq_succ_of_ne_zero hb with ⟨b', rfl⟩
        have hpow_pos : 0 < 2 ^ (s + 1) := by positivity
        rcases Finset.card_pos.mp (hpow_pos.trans_le hS) with ⟨v, hvS⟩
        classical
        let S' : Finset (Fin n) := S.erase v
        let N₁ : Finset (Fin n) := S'.filter (fun u => G.Adj v u)
        let N₂ : Finset (Fin n) := S'.filter (fun u => ¬ G.Adj v u)
        have hpart : N₁.card + N₂.card = S'.card := by
          rw [← Finset.card_union_of_disjoint
            (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
          congr 1
          ext u
          simp only [Finset.mem_union, Finset.mem_filter]
          tauto
        have herase : S'.card + 1 = S.card := Finset.card_erase_add_one hvS
        have hpow2 : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by
          rw [pow_succ]
          omega
        have hpigeon : 2 ^ s ≤ N₁.card ∨ 2 ^ s ≤ N₂.card := by omega
        rcases hpigeon with hN₁ | hN₂
        · rcases ih (by omega : a' + (b' + 1) = s) N₁ hN₁ with
            ⟨T, hTN₁, ha'T, hcl⟩ | ⟨T, hTN₁, hbT, hind⟩
          · have hvT : v ∉ T := fun hv =>
              Finset.notMem_erase v S ((Finset.mem_filter.mp (hTN₁ hv)).1)
            have hsubS : insert v T ⊆ S :=
              Finset.insert_subset_iff.mpr ⟨hvS, fun u hu =>
                Finset.mem_of_mem_erase ((Finset.mem_filter.mp (hTN₁ hu)).1)⟩
            refine Or.inl ⟨insert v T, hsubS, ?_, ?_⟩
            · rw [Finset.card_insert_of_notMem hvT]
              omega
            · intro x hx y hy hxy
              rw [Finset.mem_coe, Finset.mem_insert] at hx hy
              rcases hx with rfl | hxT <;> rcases hy with rfl | hyT
              · exact False.elim (hxy rfl)
              · exact (Finset.mem_filter.mp (hTN₁ hyT)).2
              · exact ((Finset.mem_filter.mp (hTN₁ hxT)).2).symm
              · exact hcl hxT hyT hxy
          · exact Or.inr ⟨T, fun u hu =>
              Finset.mem_of_mem_erase ((Finset.mem_filter.mp (hTN₁ hu)).1), hbT, hind⟩
        · rcases ih (by omega : (a' + 1) + b' = s) N₂ hN₂ with
            ⟨T, hTN₂, haT, hcl⟩ | ⟨T, hTN₂, hb'T, hind⟩
          · exact Or.inl ⟨T, fun u hu =>
              Finset.mem_of_mem_erase ((Finset.mem_filter.mp (hTN₂ hu)).1), haT, hcl⟩
          · have hvT : v ∉ T := fun hv =>
              Finset.notMem_erase v S ((Finset.mem_filter.mp (hTN₂ hv)).1)
            have hsubS : insert v T ⊆ S :=
              Finset.insert_subset_iff.mpr ⟨hvS, fun u hu =>
                Finset.mem_of_mem_erase ((Finset.mem_filter.mp (hTN₂ hu)).1)⟩
            refine Or.inr ⟨insert v T, hsubS, ?_, ?_⟩
            · rw [Finset.card_insert_of_notMem hvT]
              omega
            · intro x hx y hy hxy hadj
              rw [Finset.mem_coe, Finset.mem_insert] at hx hy
              rcases hx with rfl | hxT <;> rcases hy with rfl | hyT
              · exact hxy rfl
              · exact (Finset.mem_filter.mp (hTN₂ hyT)).2 hadj
              · exact (Finset.mem_filter.mp (hTN₂ hxT)).2 hadj.symm
              · exact hind hxT hyT hxy hadj

/-- Diagonal Ramsey corollary: any subset `S` of size `≥ 4^r` contains a homogeneous subset of
size `≥ r`. -/
theorem exists_homogeneous_of_four_pow_le {n r : ℕ} (G : SimpleGraph (Fin n))
    {S : Finset (Fin n)} (hS : 4 ^ r ≤ S.card) :
    ∃ T ⊆ S, r ≤ T.card ∧ IsHomogeneousSet G (T : Set (Fin n)) := by
  have h2 : 2 ^ (r + r) ≤ S.card := by
    have h4 : 4 ^ r = 2 ^ (r + r) := by
      rw [← two_mul, pow_mul]
      norm_num
    omega
  rcases exists_clique_or_indep_of_two_pow_le G (r + r) rfl S h2 with
    ⟨T, hTS, hrT, hcl⟩ | ⟨T, hTS, hrT, hind⟩
  · exact ⟨T, hTS, hrT, Or.inl hcl⟩
  · exact ⟨T, hTS, hrT, Or.inr hind⟩

/-- Greedy Ramsey extraction covers any subset `U : Finset (Fin n)` by at most `|U| / r + 4^r`
homogeneous subsets when `r ≥ 1`. -/
theorem exists_homogeneous_cover_of_finset {n r : ℕ} (hr : 1 ≤ r) (G : SimpleGraph (Fin n)) :
    ∀ U : Finset (Fin n),
      ∃ m ≤ U.card / r + 4 ^ r,
        ∃ F : Fin m → Set (Fin n),
          (∀ i : Fin m, IsHomogeneousSet G (F i)) ∧
          (∀ v ∈ U, ∃ i : Fin m, v ∈ F i) := by
  suffices hstrong : ∀ c : ℕ, ∀ U : Finset (Fin n), U.card = c →
      ∃ m ≤ c / r + 4 ^ r,
        ∃ F : Fin m → Set (Fin n),
          (∀ i : Fin m, IsHomogeneousSet G (F i)) ∧
          (∀ v ∈ U, ∃ i : Fin m, v ∈ F i) by
    intro U
    exact hstrong U.card U rfl
  intro c
  induction c using Nat.strong_induction_on with
  | h c ih =>
    intro U hUcard
    by_cases hlt : c < 4 ^ r
    · -- Cover `U` by `c < 4^r` singletons
      let e : Fin U.card ≃ U := U.equivFin.symm
      refine ⟨U.card, hUcard ▸ hlt.le.trans (Nat.le_add_left (4 ^ r) (c / r)),
        fun i => ({(e i).1} : Set (Fin n)), ?_, ?_⟩
      · intro i
        exact Or.inl (G.isClique_singleton _)
      · intro v hv
        refine ⟨e.symm ⟨v, hv⟩, ?_⟩
        simp
    · -- Extract one `r`-homogeneous subset `T ⊆ U` and apply `ih` to `U \ T`
      have hge : 4 ^ r ≤ U.card := by omega
      rcases exists_homogeneous_of_four_pow_le G hge with ⟨T, hTU, hrT, hT_hom⟩
      let U' : Finset (Fin n) := U \ T
      have hcard_split : U'.card + T.card = U.card := by
        rw [← Finset.card_union_of_disjoint Finset.sdiff_disjoint,
          Finset.sdiff_union_of_subset hTU]
      have hU'_lt : U'.card < c := by omega
      have hdiv_step : U'.card / r + 1 ≤ c / r := by
        have hle_sub : U'.card ≤ c - r := by omega
        have h1 : U'.card / r ≤ (c - r) / r := Nat.div_le_div_right hle_sub
        have h2 : c = (c - r) + r := (Nat.sub_add_cancel (by omega : r ≤ c)).symm
        have h3 : ((c - r) + r) / r = (c - r) / r + 1 := Nat.add_div_right (c - r) (by omega)
        rw [h2, h3]
        exact Nat.succ_le_succ h1
      rcases ih U'.card hU'_lt U' rfl with ⟨m', hm', F', hF'_hom, hF'_cov⟩
      let F : Fin (m' + 1) → Set (Fin n) := fun i =>
        if hi : i.val < m' then F' ⟨i.val, hi⟩ else (T : Set (Fin n))
      refine ⟨m' + 1, by omega, F, ?_, ?_⟩
      · intro i
        dsimp only [F]
        split_ifs with hi
        · exact hF'_hom ⟨i.val, hi⟩
        · exact hT_hom
      · intro v hvU
        by_cases hvT : v ∈ T
        · refine ⟨⟨m', by omega⟩, ?_⟩
          simp [F, hvT]
        · have hvU' : v ∈ U' := Finset.mem_sdiff.mpr ⟨hvU, hvT⟩
          rcases hF'_cov v hvU' with ⟨j, hj⟩
          refine ⟨⟨j.val, by omega⟩, ?_⟩
          simp [F, j.isLt, hj]

/-- **Leftover Ramsey Cocoloring Bound (`arXiv:2608.30604`, Section 10)**:
If `H` is `K`-cocolorable and `G` agrees with `H` outside `U`, then for every `r ≥ 1`,
`cochromaticNumber G ≤ K + |U| / r + 4^r`. -/
theorem cochromaticNumber_le_of_agreeOffSet {n K r : ℕ} (hr : 1 ≤ r)
    {U : Finset (Fin n)} {G H : SimpleGraph (Fin n)}
    (hagree : AgreeOffSet U G H) (hH : Cocolorable H K) :
    cochromaticNumber G ≤ K + U.card / r + 4 ^ r := by
  classical
  rcases hH with ⟨cH, hcH⟩
  rcases exists_homogeneous_cover_of_finset hr G U with ⟨m, hm, FU, hFU_hom, hFU_cov⟩
  let FH : Fin K → Set (Fin n) := fun i => {v : Fin n | v ∉ U ∧ cH v = i}
  have hFH_hom : ∀ i : Fin K, IsHomogeneousSet G (FH i) := by
    intro i
    rcases hcH i with hcl | hind
    · refine Or.inl (fun x hx y hy hxy => ?_)
      exact (hagree hx.1 hy.1).mpr (hcl hx.2 hy.2 hxy)
    · refine Or.inr (fun x hx y hy hxy hadj => ?_)
      exact hind hx.2 hy.2 hxy ((hagree hx.1 hy.1).mp hadj)
  let Ftot : Fin (K + m) → Set (Fin n) := fun idx =>
    if h : idx.val < K then FH ⟨idx.val, h⟩
    else FU ⟨idx.val - K, by omega⟩
  have hFtot_hom : ∀ idx : Fin (K + m), IsHomogeneousSet G (Ftot idx) := by
    intro idx
    dsimp only [Ftot]
    split_ifs with h
    · exact hFH_hom ⟨idx.val, h⟩
    · exact hFU_hom ⟨idx.val - K, by omega⟩
  have hFtot_cov : ∀ v : Fin n, ∃ idx : Fin (K + m), v ∈ Ftot idx := by
    intro v
    by_cases hvU : v ∈ U
    · rcases hFU_cov v hvU with ⟨j, hj⟩
      refine ⟨⟨K + j.val, by omega⟩, ?_⟩
      have hnot : ¬ (K + j.val < K) := by omega
      simp [Ftot, hnot, hj]
    · let i := cH v
      refine ⟨⟨i.val, by omega⟩, ?_⟩
      simp [Ftot, i.isLt, FH, hvU, i]
  have hG_coco : Cocolorable G (K + m) := by
    refine ⟨fun v => Classical.choose (hFtot_cov v), fun idx => ?_⟩
    have hsub : {v : Fin n | Classical.choose (hFtot_cov v) = idx} ⊆ Ftot idx := by
      intro v hv
      simp only [Set.mem_ofPred_eq] at hv
      rw [← hv]
      exact Classical.choose_spec (hFtot_cov v)
    rcases hFtot_hom idx with hcl | hind
    · exact Or.inl (hcl.subset hsub)
    · exact Or.inr (hind.mono hsub)
  exact (hG_coco.cochromaticNumber_le).trans (by omega)

/-! ### 5. Master Asymptotic Rare-Seed Amplification (`arXiv:2608.30604`, Section 10) -/

/-- **Master Rare-Seed Cochromatic Amplification Theorem (`arXiv:2608.30604`, Section 10)**:
Given any deterministic seed sequence `K : ℕ → ℕ` and any nonnegative sequence `η_n → 0` such that
`ℙ(Cocolorable G_n (K n)) ≥ exp(- η_n * n / (log n)^4)` eventually, there exists a deterministic
nonnegative sequence `δ_amp : ℕ → ℝ` with `δ_amp n → 0` such that
`ℙ(ζ(G_n) ≤ K_n + δ_amp(n) * n / (log n)^3) → 1` as `n → ∞`. -/
theorem tendsto_probGnpHalf_cochromatic_amplification
    (K : ℕ → ℕ) {η : ℕ → ℝ} (hη_nonneg : ∀ n, 0 ≤ η n) (hη0 : Tendsto η atTop (𝓝 0))
    (hseed : ∀ᶠ n : ℕ in atTop,
      Real.exp (- η n * (n : ℝ) / (Real.log (n : ℝ)) ^ 4) ≤
        probGnpHalf n {G : SimpleGraph (Fin n) | Cocolorable G (K n)}) :
    ∃ δ_amp : ℕ → ℝ, (∀ n, 0 ≤ δ_amp n) ∧ Tendsto δ_amp atTop (𝓝 0) ∧
      Tendsto
        (fun n : ℕ => probGnpHalf n
          {G : SimpleGraph (Fin n) |
            (cochromaticNumber G : ℝ) ≤
              (K n : ℝ) + δ_amp n * (n : ℝ) / (Real.log (n : ℝ)) ^ 3})
        atTop (𝓝 1) := by
  let invL : ℕ → ℝ := fun n => 1 / max 1 (Real.log (n : ℝ))
  let ξ : ℕ → ℝ := fun n => Real.sqrt (η n + invL n)
  let δ_amp : ℕ → ℝ := fun n => 16 * ξ n + 5 * invL n
  refine ⟨δ_amp, ?_, ?_, ?_⟩
  · intro n
    have h1 : 0 ≤ ξ n := Real.sqrt_nonneg _
    have h2 : 0 ≤ invL n := by
      dsimp only [invL]
      positivity
    dsimp only [δ_amp]
    linarith
  · -- `δ_amp n → 0`
    have hL_top : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hinvL0 : Tendsto invL atTop (𝓝 0) := by
      refine ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hL_top).congr' ?_
      filter_upwards [hL_top.eventually_ge_atTop 1] with n hn
      simp [invL, max_eq_right hn]
    have hξ0 : Tendsto ξ atTop (𝓝 0) := by
      have hsum0 : Tendsto (fun n => η n + invL n) atTop (𝓝 (0 + 0)) := hη0.add hinvL0
      rw [add_zero] at hsum0
      have hcomp := (Real.continuous_sqrt.tendsto 0).comp hsum0
      rw [Real.sqrt_zero] at hcomp
      exact hcomp
    have hδ0 : Tendsto (fun n => 16 * ξ n + 5 * invL n) atTop (𝓝 (16 * 0 + 5 * 0)) :=
      (hξ0.const_mul 16).add (hinvL0.const_mul 5)
    simpa [δ_amp] using hδ0
  · -- High-probability cochromatic bound via two-step McDiarmid + Ramsey extraction
    have hL_top : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hexp_half : Tendsto
        (fun n : ℕ => Real.exp ((1 / 2 : ℝ) * Real.log (n : ℝ)) /
          ((1 / 2 : ℝ) * Real.log (n : ℝ)) ^ 4) atTop atTop :=
      (Real.tendsto_exp_div_pow_atTop 4).comp
        (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2) hL_top)
    let r : ℕ → ℕ := fun n => ⌊(1 / 4 : ℝ) * Real.log (n : ℝ)⌋₊ + 1
    let u₁ : ℕ → ℝ := fun n => 4 * ξ n * (n : ℝ) / (Real.log (n : ℝ)) ^ 2
    let u₂ : ℕ → ℝ := fun n => (n : ℝ) / (Real.log (n : ℝ)) ^ 3
    let A : (n : ℕ) → Set (SimpleGraph (Fin n)) :=
      fun n => {G : SimpleGraph (Fin n) | Cocolorable G (K n)}
    let Egood : (n : ℕ) → Set (SimpleGraph (Fin n)) :=
      fun n => {G : SimpleGraph (Fin n) | (vertexEditDist (A n) G : ℝ) < u₁ n + u₂ n}
    -- First show `ℙ(Egood n) → 1`
    have hgood : Tendsto (fun n => probGnpHalf n (Egood n)) atTop (𝓝 1) := by
      apply tendsto_probGnpHalf_one_of_compl_tendsto_zero
      have htail0 : Tendsto
          (fun n : ℕ => Real.exp (- (1 / 8 : ℝ) * ((n : ℝ) / (Real.log (n : ℝ)) ^ 6)))
          atTop (𝓝 0) := by
        have hdiv6 : Tendsto
            (fun n : ℕ => (1 / 8 : ℝ) * ((n : ℝ) / (Real.log (n : ℝ)) ^ 6)) atTop atTop :=
          Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 8)
            (tendsto_nat_div_log_pow_atTop 6)
        have hneg : Tendsto
            (fun n : ℕ => - ((1 / 8 : ℝ) * ((n : ℝ) / (Real.log (n : ℝ)) ^ 6))) atTop atBot :=
          tendsto_neg_atTop_atBot.comp hdiv6
        refine (Real.tendsto_exp_atBot.comp hneg).congr (fun n => ?_)
        dsimp only [Function.comp_apply]
        rw [neg_mul]
      refine squeeze_zero' (f := fun n => probGnpHalf n (Egood n)ᶜ)
        (g := fun n => Real.exp (- (1 / 8 : ℝ) * ((n : ℝ) / (Real.log (n : ℝ)) ^ 6)))
        ?_ ?_ htail0
      · filter_upwards with n
        exact probGnpHalf_nonneg n _
      · filter_upwards [eventually_ge_atTop 16, hL_top.eventually_ge_atTop 2, hseed] with
          n hn16 hL2 hseed_n
        have hn_pos : 0 < n := by omega
        have hn_cast : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
        have hL_pos : 0 < Real.log (n : ℝ) := by linarith
        have hinvL_eq : invL n = 1 / Real.log (n : ℝ) := by
          simp [invL, max_eq_right (by linarith : (1 : ℝ) ≤ Real.log (n : ℝ))]
        have hξ_sq : (ξ n) ^ 2 = η n + 1 / Real.log (n : ℝ) := by
          dsimp only [ξ]
          rw [hinvL_eq, Real.sq_sqrt (add_nonneg (hη_nonneg n) (by positivity))]
        have hu₁_nonneg : 0 ≤ u₁ n := by
          have hξ_nn : 0 ≤ ξ n := Real.sqrt_nonneg _
          dsimp only [u₁]
          positivity
        have hu₂_nonneg : 0 ≤ u₂ n := by
          dsimp only [u₂]
          positivity
        -- Verify strict seed margin `exp(- u₁^2 / (8 n)) < ℙ(A n)`
        have hexp_lt : Real.exp (- (u₁ n) ^ 2 / (8 * (n : ℝ))) <
            Real.exp (- η n * (n : ℝ) / (Real.log (n : ℝ)) ^ 4) := by
          apply Real.exp_lt_exp.mpr
          have hu₁_sq : - (u₁ n) ^ 2 / (8 * (n : ℝ)) =
              - 2 * (η n + 1 / Real.log (n : ℝ)) * (n : ℝ) / (Real.log (n : ℝ)) ^ 4 := by
            dsimp only [u₁]
            rw [div_pow, mul_pow, mul_pow, hξ_sq]
            field_simp [hn_cast.ne', hL_pos.ne']
            ring
          rw [hu₁_sq]
          have hη_nn := hη_nonneg n
          have hpos_term : 0 < (1 / Real.log (n : ℝ)) * (n : ℝ) / (Real.log (n : ℝ)) ^ 4 := by
            positivity
          have hnonneg_η : 0 ≤ η n * (n : ℝ) / (Real.log (n : ℝ)) ^ 4 := by positivity
          have hdecomp :
              - 2 * (η n + 1 / Real.log (n : ℝ)) * (n : ℝ) / (Real.log (n : ℝ)) ^ 4 =
                - η n * (n : ℝ) / (Real.log (n : ℝ)) ^ 4 -
                  η n * (n : ℝ) / (Real.log (n : ℝ)) ^ 4 -
                  2 * ((1 / Real.log (n : ℝ)) * (n : ℝ) / (Real.log (n : ℝ)) ^ 4) := by ring
          linarith
        have hcompl_eq : (Egood n)ᶜ =
            {G : SimpleGraph (Fin n) | u₁ n + u₂ n ≤ (vertexEditDist (A n) G : ℝ)} := by
          ext G
          simp [Egood, not_lt]
        rw [hcompl_eq]
        have hmcd := probGnpHalf_vertexEditDist_ge_le hn_pos hu₁_nonneg hu₂_nonneg
          (hexp_lt.trans_le hseed_n)
        have hu₂_sq : - (u₂ n) ^ 2 / (8 * (n : ℝ)) =
            - (1 / 8 : ℝ) * ((n : ℝ) / (Real.log (n : ℝ)) ^ 6) := by
          dsimp only [u₂]
          field_simp [hn_cast.ne', hL_pos.ne']
        rwa [hu₂_sq] at hmcd
    -- Finally show `Egood n` is eventually contained in the target cochromatic event
    refine tendsto_probGnpHalf_one_of_eventually_subset hgood ?_
    filter_upwards [eventually_ge_atTop 16, hL_top.eventually_ge_atTop 8,
      hexp_half.eventually_ge_atTop 64, hseed] with n hn16 hL8 hexp64 hseed_n G hG
    simp only [Set.mem_ofPred_eq, Egood] at hG ⊢
    have hn_cast : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hL_pos : 0 < Real.log (n : ℝ) := by linarith
    have hA_ne : (A n).Nonempty := by
      by_contra hempty
      have hempty' : {G : SimpleGraph (Fin n) | Cocolorable G (K n)} = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hempty
      rw [hempty', probGnpHalf_empty] at hseed_n
      linarith [Real.exp_pos (- η n * (n : ℝ) / (Real.log (n : ℝ)) ^ 4)]
    rcases vertexEditDist_spec hA_ne G with ⟨U, hUcard, H, hHA, hagree⟩
    have hr_pos : 1 ≤ r n := Nat.succ_pos _
    have hco_le : cochromaticNumber G ≤ K n + U.card / r n + 4 ^ (r n) :=
      cochromaticNumber_le_of_agreeOffSet hr_pos hagree hHA
    have hco_real : (cochromaticNumber G : ℝ) ≤
        (K n : ℝ) + ((U.card / r n : ℕ) : ℝ) + ((4 ^ (r n) : ℕ) : ℝ) := by
      exact_mod_cast hco_le
    -- Bound `(U.card / r n : ℝ)`
    have hr_cast_gt : (1 / 4 : ℝ) * Real.log (n : ℝ) < (r n : ℝ) := by
      dsimp only [r]
      rw [Nat.cast_add, Nat.cast_one]
      exact Nat.lt_floor_add_one _
    have hr_cast_pos : 0 < (r n : ℝ) := by linarith
    have hU_div_le : ((U.card / r n : ℕ) : ℝ) ≤
        (16 * ξ n + 4 * invL n) * (n : ℝ) / (Real.log (n : ℝ)) ^ 3 := by
      have hU_le_u : (U.card : ℝ) ≤ u₁ n + u₂ n :=
        (Nat.cast_le.mpr hUcard).trans hG.le
      have hdiv1 : ((U.card / r n : ℕ) : ℝ) ≤ (U.card : ℝ) / (r n : ℝ) :=
        Nat.cast_div_le
      have hdiv2 : (U.card : ℝ) / (r n : ℝ) ≤
          (u₁ n + u₂ n) / ((1 / 4 : ℝ) * Real.log (n : ℝ)) := by
        have h1 : (U.card : ℝ) / (r n : ℝ) ≤ (u₁ n + u₂ n) / (r n : ℝ) :=
          div_le_div_of_nonneg_right hU_le_u hr_cast_pos.le
        have h2 : (u₁ n + u₂ n) / (r n : ℝ) ≤
            (u₁ n + u₂ n) / ((1 / 4 : ℝ) * Real.log (n : ℝ)) :=
          div_le_div_of_nonneg_left ((Nat.cast_nonneg U.card).trans hU_le_u)
            (by positivity) hr_cast_gt.le
        exact h1.trans h2
      have hinvL_eq : invL n = 1 / Real.log (n : ℝ) := by
        simp [invL, max_eq_right (by linarith : (1 : ℝ) ≤ Real.log (n : ℝ))]
      have halg : (u₁ n + u₂ n) / ((1 / 4 : ℝ) * Real.log (n : ℝ)) =
          (16 * ξ n + 4 * invL n) * (n : ℝ) / (Real.log (n : ℝ)) ^ 3 := by
        dsimp only [u₁, u₂]
        rw [hinvL_eq]
        field_simp [hL_pos.ne']
        ring
      exact hdiv1.trans (hdiv2.trans_eq halg)
    -- Bound `(4 ^ r n : ℝ) ≤ invL n * (n / (log n)^3)`
    have h4r_le : ((4 ^ (r n) : ℕ) : ℝ) ≤
        invL n * (n : ℝ) / (Real.log (n : ℝ)) ^ 3 := by
      have hlog4_le : Real.log 4 ≤ 2 := by
        have hlog2_le : Real.log 2 ≤ 1 := by
          linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
        have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
        rw [h4, Real.log_pow]
        push_cast
        linarith
      have hfl_le : (⌊(1 / 4 : ℝ) * Real.log (n : ℝ)⌋₊ : ℝ) ≤
          (1 / 4 : ℝ) * Real.log (n : ℝ) := Nat.floor_le (by positivity)
      have hpow_exp : ((4 ^ (r n) : ℕ) : ℝ) ≤
          4 * Real.exp ((1 / 2 : ℝ) * Real.log (n : ℝ)) := by
        dsimp only [r]
        rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ, mul_comm _ (4 : ℝ)]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        rw [← Real.exp_log (by positivity : (0 : ℝ) < (4 : ℝ) ^ ⌊(1 / 4 : ℝ) * Real.log (n : ℝ)⌋₊),
          Real.log_pow]
        apply Real.exp_le_exp.mpr
        have hfl_nn : (0 : ℝ) ≤ (⌊(1 / 4 : ℝ) * Real.log (n : ℝ)⌋₊ : ℝ) := Nat.cast_nonneg _
        have hm1 : (⌊(1 / 4 : ℝ) * Real.log (n : ℝ)⌋₊ : ℝ) * Real.log 4 ≤
            (⌊(1 / 4 : ℝ) * Real.log (n : ℝ)⌋₊ : ℝ) * 2 :=
          mul_le_mul_of_nonneg_left hlog4_le hfl_nn
        linarith
      -- From `hexp64`, `4 * (log n)^4 ≤ exp((1/2) log n)`
      have h4L4 : 4 * (Real.log (n : ℝ)) ^ 4 ≤
          Real.exp ((1 / 2 : ℝ) * Real.log (n : ℝ)) := by
        have hden_pos : 0 < ((1 / 2 : ℝ) * Real.log (n : ℝ)) ^ 4 := by positivity
        have hm := (le_div_iff₀ hden_pos).mp hexp64
        linarith [show 64 * ((1 / 2 : ℝ) * Real.log (n : ℝ)) ^ 4 =
          4 * (Real.log (n : ℝ)) ^ 4 by ring]
      have hprod_n : 4 * Real.exp ((1 / 2 : ℝ) * Real.log (n : ℝ)) *
          (Real.log (n : ℝ)) ^ 4 ≤ (n : ℝ) := by
        have hm := mul_le_mul_of_nonneg_left h4L4
          (Real.exp_pos ((1 / 2 : ℝ) * Real.log (n : ℝ))).le
        have hexp_n : Real.exp ((1 / 2 : ℝ) * Real.log (n : ℝ)) *
            Real.exp ((1 / 2 : ℝ) * Real.log (n : ℝ)) = (n : ℝ) := by
          rw [← Real.exp_add, show (1 / 2 : ℝ) * Real.log (n : ℝ) +
            (1 / 2 : ℝ) * Real.log (n : ℝ) = Real.log (n : ℝ) by ring, Real.exp_log hn_cast]
        linarith
      have hinvL_eq : invL n = 1 / Real.log (n : ℝ) := by
        simp [invL, max_eq_right (by linarith : (1 : ℝ) ≤ Real.log (n : ℝ))]
      rw [hinvL_eq]
      have hrhs_eq : (1 / Real.log (n : ℝ)) * (n : ℝ) / (Real.log (n : ℝ)) ^ 3 =
          (n : ℝ) / (Real.log (n : ℝ)) ^ 4 := by
        field_simp [hL_pos.ne']
      rw [hrhs_eq, le_div_iff₀ (by positivity)]
      exact (mul_le_mul_of_nonneg_right hpow_exp (by positivity)).trans hprod_n
    have hcombine :
        (16 * ξ n + 4 * invL n) * (n : ℝ) / (Real.log (n : ℝ)) ^ 3 +
          invL n * (n : ℝ) / (Real.log (n : ℝ)) ^ 3 =
        δ_amp n * (n : ℝ) / (Real.log (n : ℝ)) ^ 3 := by
      dsimp only [δ_amp]
      ring
    linarith

end JSP000506
