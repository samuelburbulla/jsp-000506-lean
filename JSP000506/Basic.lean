import JSP000506.Defs
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# Basic Structural Properties of the Cochromatic Number

This module proves unconditional structural properties and concrete evaluations of `ζ(G)`:
1. `cochromaticNumber_le_chromaticNumber`: `ζ(G) ≤ χ(G)` (both in `ℕ∞` and in `ℕ` on finite graphs)
   and `G.chromaticNumber ≤ n` on `Fin n`.
2. `cochromaticNumber_compl`: complement invariance `ζ(Gᶜ) = ζ(G)`.
3. `abs_cochromaticNumber_sub_le_one_of_agreeOffVertex`: vertex-exposure `1`-Lipschitz bound
   `|(ζ(G) : ℤ) - (ζ(G') : ℤ)| ≤ 1` when `G` and `G'` agree on all vertex pairs avoiding `v₀`
   (together with the induced-subgraph lemma used in Section 10's McDiarmid amplification).
4. Concrete graph evaluations:
   - Empty graph `⊥` on `Fin n` (`n ≥ 1`): `χ = 1`, `ζ = 1`.
   - Complete graph `⊤` on `Fin n` (`n ≥ 1`): `χ = n`, `ζ = 1` (so `χ(K_n) - ζ(K_n) = n - 1`).
   - 4-cycle `cycleGraph 4` (`C_4`): `χ = 2`, `ζ = 2`.
   - 5-cycle `cycleGraph 5` (`C_5`): `χ = 3`, `ζ = 3` (Ramsey `(3,3)` witness: `α = ω = 2`).
   - Explicit 5-vertex graph `houseGraph` (`C_5` plus one chord): `χ = 3`, `ζ = 2`,
     witnessing `χ - ζ = 1 > 0` on `5` vertices.
-/

namespace JSP000506

open SimpleGraph

/-! ### 1. Comparison with Chromatic Number and Trivial Upper Bounds -/

/-- For every simple graph `G` (finite or infinite), `(ζ(G) : ℕ∞) ≤ χ(G)`. -/
theorem cochromaticNumber_le_chromaticNumber {V : Type*} (G : SimpleGraph V) :
    (cochromaticNumber G : ℕ∞) ≤ G.chromaticNumber := by
  rw [chromaticNumber_eq_biInf, le_iInf₂_iff]
  intro k hk
  exact Nat.cast_le.mpr (cocolorable_of_colorable hk).cochromaticNumber_le

/-- On a finite vertex type, `G.chromaticNumber` is finite and equals `(G.chromaticNumber.toNat : ℕ∞)`. -/
theorem coe_chromaticNumber_toNat {V : Type*} [Finite V] (G : SimpleGraph V) :
    (G.chromaticNumber.toNat : ℕ∞) = G.chromaticNumber := by
  cases nonempty_fintype V
  have hlt : G.chromaticNumber < ⊤ :=
    (G.chromaticNumber_le_card).trans_lt (ENat.natCast_lt_top _)
  exact ENat.natCast_toNat hlt.ne

/-- On a finite vertex type, `ζ(G) ≤ χ(G).toNat` in `ℕ`. -/
theorem cochromaticNumber_le_chromaticNumber_toNat {V : Type*} [Finite V] (G : SimpleGraph V) :
    cochromaticNumber G ≤ G.chromaticNumber.toNat := by
  have hc : G.Colorable G.chromaticNumber.toNat := G.colorable_chromaticNumber_of_fintype
  exact (cocolorable_of_colorable hc).cochromaticNumber_le

/-- On `Fin n`, `χ(G) ≤ n` in `ℕ∞`. -/
theorem chromaticNumber_le_n {n : ℕ} (G : SimpleGraph (Fin n)) :
    G.chromaticNumber ≤ n := by
  simpa using G.chromaticNumber_le_card

/-- On `Fin n`, `χ(G).toNat ≤ n` in `ℕ`. -/
theorem chromaticNumber_toNat_le_n {n : ℕ} (G : SimpleGraph (Fin n)) :
    G.chromaticNumber.toNat ≤ n := by
  have h := chromaticNumber_le_n G
  rw [← coe_chromaticNumber_toNat G, Nat.cast_le] at h
  exact h

/-- On `Fin n`, `ζ(G) ≤ n` in `ℕ`. -/
theorem cochromaticNumber_le_n {n : ℕ} (G : SimpleGraph (Fin n)) :
    cochromaticNumber G ≤ n :=
  (cochromaticNumber_le_chromaticNumber_toNat G).trans (chromaticNumber_toNat_le_n G)

/-! ### 2. Complement Symmetry -/

@[simp]
theorem isCocoloring_compl {V α : Type*} (G : SimpleGraph V) (c : V → α) :
    IsCocoloring Gᶜ c ↔ IsCocoloring G c := by
  unfold IsCocoloring
  refine forall_congr' fun _ => ?_
  rw [isClique_compl, isIndepSet_compl, or_comm]

@[simp]
theorem cocolorable_compl {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    Cocolorable Gᶜ k ↔ Cocolorable G k :=
  exists_congr fun c => isCocoloring_compl G c

/-- Complement invariance of the cochromatic number: `ζ(Gᶜ) = ζ(G)`. -/
@[simp]
theorem cochromaticNumber_compl {V : Type*} (G : SimpleGraph V) :
    cochromaticNumber Gᶜ = cochromaticNumber G := by
  unfold cochromaticNumber
  simp only [cocolorable_compl]

/-! ### 3. Vertex-Exposure Lipschitz Bound -/

/-- Two graphs `G, G'` on `V` *agree away from `v₀`* if they have identical adjacency on all
vertex pairs `{u, v}` with `u ≠ v₀` and `v ≠ v₀`. -/
def AgreeOffVertex {V : Type*} (G G' : SimpleGraph V) (v₀ : V) : Prop :=
  ∀ ⦃u v : V⦄, u ≠ v₀ → v ≠ v₀ → (G.Adj u v ↔ G'.Adj u v)

lemma AgreeOffVertex.symm {V : Type*} {G G' : SimpleGraph V} {v₀ : V}
    (h : AgreeOffVertex G G' v₀) : AgreeOffVertex G' G v₀ :=
  fun _ _ hu hv => (h hu hv).symm

lemma AgreeOffVertex.isClique_iff {V : Type*} {G G' : SimpleGraph V} {v₀ : V}
    (h : AgreeOffVertex G G' v₀) {s : Set V} (hv₀ : v₀ ∉ s) :
    G.IsClique s ↔ G'.IsClique s := by
  refine ⟨fun hc u hu v hv huv => ?_, fun hc u hu v hv huv => ?_⟩
  · exact (h (fun e => hv₀ (e ▸ hu)) (fun e => hv₀ (e ▸ hv))).mp (hc hu hv huv)
  · exact (h (fun e => hv₀ (e ▸ hu)) (fun e => hv₀ (e ▸ hv))).mpr (hc hu hv huv)

lemma AgreeOffVertex.isIndepSet_iff {V : Type*} {G G' : SimpleGraph V} {v₀ : V}
    (h : AgreeOffVertex G G' v₀) {s : Set V} (hv₀ : v₀ ∉ s) :
    G.IsIndepSet s ↔ G'.IsIndepSet s := by
  refine ⟨fun hi u hu v hv huv hadj => ?_, fun hi u hu v hv huv hadj => ?_⟩
  · exact hi hu hv huv ((h (fun e => hv₀ (e ▸ hu)) (fun e => hv₀ (e ▸ hv))).mpr hadj)
  · exact hi hu hv huv ((h (fun e => hv₀ (e ▸ hu)) (fun e => hv₀ (e ▸ hv))).mp hadj)

/-- Isolating `v₀` into its own singleton color class turns any `k`-cocoloring of `G'` into a
`(k + 1)`-cocoloring of `G` whenever `G` and `G'` agree away from `v₀`. -/
theorem cocolorable_succ_of_agreeOffVertex {V : Type*} {G G' : SimpleGraph V} {v₀ : V}
    (h : AgreeOffVertex G G' v₀) {k : ℕ} (hc : Cocolorable G' k) :
    Cocolorable G (k + 1) := by
  classical
  rcases hc with ⟨c, hc⟩
  let c' : V → Fin (k + 1) := fun v =>
    if v = v₀ then Fin.last k else Fin.castSucc (c v)
  refine ⟨c', fun i => ?_⟩
  by_cases hi : i = Fin.last k
  · subst hi
    have hsub : {v : V | c' v = Fin.last k} ⊆ ({v₀} : Set V) := by
      intro v hv
      simp only [Set.mem_ofPred_eq, c'] at hv
      by_cases hvv : v = v₀
      · exact hvv
      · simp only [hvv, ↓reduceIte] at hv
        exact False.elim ((Fin.castSucc_lt_last (c v)).ne hv)
    exact Or.inl ((G.isClique_singleton v₀).subset hsub)
  · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    have hv₀_not : v₀ ∉ {v : V | c' v = Fin.castSucc j} := by
      simp [c', (Fin.castSucc_lt_last j).ne']
    have hsub : {v : V | c' v = Fin.castSucc j} ⊆ {v : V | c v = j} := by
      intro v hv
      simp only [Set.mem_ofPred_eq, c'] at hv ⊢
      by_cases hvv : v = v₀
      · simp only [hvv, ↓reduceIte] at hv
        exact False.elim ((Fin.castSucc_lt_last j).ne hv.symm)
      · simp only [hvv, ↓reduceIte, Fin.castSucc_inj] at hv
        exact hv
    rcases hc j with hcl | hind
    · exact Or.inl ((h.isClique_iff hv₀_not).mpr (hcl.subset hsub))
    · exact Or.inr ((h.isIndepSet_iff hv₀_not).mpr (hind.mono hsub))

theorem cochromaticNumber_le_add_one_of_agreeOffVertex {V : Type*} [Finite V]
    {G G' : SimpleGraph V} {v₀ : V} (h : AgreeOffVertex G G' v₀) :
    cochromaticNumber G ≤ cochromaticNumber G' + 1 :=
  (cocolorable_succ_of_agreeOffVertex h (cocolorable_cochromaticNumber G')).cochromaticNumber_le

/-- **Vertex-exposure Lipschitz bound**: if `G, G'` on a finite vertex set agree on all pairs not
containing `v₀`, then `|(ζ(G) : ℤ) - (ζ(G') : ℤ)| ≤ 1`. -/
theorem abs_cochromaticNumber_sub_le_one_of_agreeOffVertex {V : Type*} [Finite V]
    {G G' : SimpleGraph V} {v₀ : V} (h : AgreeOffVertex G G' v₀) :
    |(cochromaticNumber G : ℤ) - (cochromaticNumber G' : ℤ)| ≤ 1 := by
  have h1 : cochromaticNumber G ≤ cochromaticNumber G' + 1 :=
    cochromaticNumber_le_add_one_of_agreeOffVertex h
  have h2 : cochromaticNumber G' ≤ cochromaticNumber G + 1 :=
    cochromaticNumber_le_add_one_of_agreeOffVertex h.symm
  rw [abs_le]
  omega

/-- Induced-subset cocolorability transfers from `W` in `G` to `W \ {v₀}` in `G'` with the same
budget `k` whenever `G` and `G'` agree away from `v₀`. -/
theorem cocolorable_induce_sdiff_singleton_of_agreeOffVertex {V : Type*}
    {G G' : SimpleGraph V} {v₀ : V} (h : AgreeOffVertex G G' v₀)
    (W : Set V) {k : ℕ} (hc : Cocolorable (G.induce W) k) :
    Cocolorable (G'.induce (W \ {v₀})) k := by
  rcases hc with ⟨c, hc⟩
  let emb : ↑(W \ {v₀}) → ↑W := fun x => ⟨x.1, x.2.1⟩
  have hemb_inj : Function.Injective emb := fun _ _ hxy =>
    Subtype.ext (congrArg (Subtype.val : ↑W → V) hxy)
  refine ⟨fun x => c (emb x), fun i => ?_⟩
  rcases hc i with hcl | hind
  · left
    intro x hx y hy hxy
    have hadj_ind : (G.induce W).Adj (emb x) (emb y) :=
      hcl hx hy (fun e => hxy (hemb_inj e))
    exact (h x.2.2 y.2.2).mp hadj_ind
  · right
    intro x hx y hy hxy hadj'
    have hGadj : G.Adj x.1 y.1 := (h x.2.2 y.2.2).mpr hadj'
    exact hind hx hy (fun e => hxy (hemb_inj e)) hGadj

/-! ### 4. Characterization of `ζ(G) = 1` and Concrete Graph Evaluations -/

theorem cocolorable_one_iff {V : Type*} (G : SimpleGraph V) :
    Cocolorable G 1 ↔ G = ⊥ ∨ G = ⊤ := by
  constructor
  · rintro ⟨c, hc⟩
    have huniv : {v : V | c v = 0} = Set.univ := by
      ext v
      simp [Subsingleton.elim (c v) 0]
    have h0 := hc 0
    rw [huniv] at h0
    rcases h0 with hcl | hind
    · exact Or.inr (isClique_univ.mp hcl)
    · left
      rw [eq_bot_iff_forall_not_adj]
      intro u v hadj
      exact hind trivial trivial (G.ne_of_adj hadj) hadj
  · rintro (rfl | rfl)
    · refine ⟨fun _ => 0, fun _ => Or.inr ?_⟩
      intro _ _ _ _ _ hadj
      exact hadj
    · refine ⟨fun _ => 0, fun _ => Or.inl ?_⟩
      exact IsClique.top _

theorem cochromaticNumber_eq_one_iff {V : Type*} [Finite V] [Nonempty V] (G : SimpleGraph V) :
    cochromaticNumber G = 1 ↔ G = ⊥ ∨ G = ⊤ := by
  have hpos : 1 ≤ cochromaticNumber G := cochromaticNumber_pos G
  rw [le_antisymm_iff, and_iff_left hpos, cochromaticNumber_le_iff_cocolorable,
    cocolorable_one_iff]

/-- Empty graph `⊥` on `Fin n` (`n ≥ 1`): `χ(⊥) = 1` and `ζ(⊥) = 1`. -/
theorem chromaticNumber_emptyGraph_fin {n : ℕ} (hn : 1 ≤ n) :
    (⊥ : SimpleGraph (Fin n)).chromaticNumber = 1 := by
  have _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact chromaticNumber_bot

theorem cochromaticNumber_emptyGraph_fin {n : ℕ} (hn : 1 ≤ n) :
    cochromaticNumber (⊥ : SimpleGraph (Fin n)) = 1 := by
  have _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact (cochromaticNumber_eq_one_iff _).mpr (Or.inl rfl)

/-- Complete graph `⊤` on `Fin n` (`n ≥ 1`): `χ(K_n) = n` and `ζ(K_n) = 1`. -/
theorem chromaticNumber_completeGraph_fin (n : ℕ) :
    (⊤ : SimpleGraph (Fin n)).chromaticNumber = n := by
  simp

theorem cochromaticNumber_completeGraph_fin {n : ℕ} (hn : 1 ≤ n) :
    cochromaticNumber (⊤ : SimpleGraph (Fin n)) = 1 := by
  have _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact (cochromaticNumber_eq_one_iff _).mpr (Or.inr rfl)

/-- 4-cycle `C_4`: `χ(C_4) = 2`. -/
theorem chromaticNumber_cycleGraph_four :
    (cycleGraph 4).chromaticNumber = 2 :=
  chromaticNumber_cycleGraph_of_even 4 (by omega) ⟨2, rfl⟩

/-- 4-cycle `C_4`: `ζ(C_4) = 2`. -/
theorem cochromaticNumber_cycleGraph_four :
    cochromaticNumber (cycleGraph 4) = 2 := by
  apply le_antisymm
  · have hχ : (cycleGraph 4).chromaticNumber.toNat = 2 := by
      rw [chromaticNumber_cycleGraph_four]
      rfl
    exact hχ ▸ cochromaticNumber_le_chromaticNumber_toNat (cycleGraph 4)
  · have hpos : 1 ≤ cochromaticNumber (cycleGraph 4) := cochromaticNumber_pos (cycleGraph 4)
    have hne1 : cochromaticNumber (cycleGraph 4) ≠ 1 := by
      rw [Ne, cochromaticNumber_eq_one_iff]
      rintro (hbot | htop)
      · have hadj : (cycleGraph 4).Adj 0 1 := by decide
        rw [hbot] at hadj
        exact hadj
      · have hnadj : ¬ (cycleGraph 4).Adj 0 2 := by decide
        rw [htop] at hnadj
        exact hnadj (by decide)
    omega

/-- 5-cycle `C_5`: `χ(C_5) = 3`. -/
theorem chromaticNumber_cycleGraph_five :
    (cycleGraph 5).chromaticNumber = 3 :=
  chromaticNumber_cycleGraph_of_odd 5 (by omega) ⟨2, rfl⟩

private lemma card_le_two_of_homogeneous_cycleGraph_five (s : Finset (Fin 5))
    (hs : (cycleGraph 5).IsClique (s : Set (Fin 5)) ∨
          (cycleGraph 5).IsIndepSet (s : Set (Fin 5))) :
    s.card ≤ 2 := by
  revert s
  decide

/-- 5-cycle `C_5` (the Ramsey `(3, 3)` extremal graph with `α(C_5) = ω(C_5) = 2`):
`ζ(C_5) = 3 = χ(C_5)`. -/
theorem cochromaticNumber_cycleGraph_five :
    cochromaticNumber (cycleGraph 5) = 3 := by
  apply le_antisymm
  · have hχ : (cycleGraph 5).chromaticNumber.toNat = 3 := by
      rw [chromaticNumber_cycleGraph_five]
      rfl
    exact hχ ▸ cochromaticNumber_le_chromaticNumber_toNat (cycleGraph 5)
  · by_contra hlt
    have hc2 : Cocolorable (cycleGraph 5) 2 :=
      (cochromaticNumber_le_iff_cocolorable (cycleGraph 5)).mp (by omega)
    rcases hc2 with ⟨c, hc⟩
    let s₀ : Finset (Fin 5) := Finset.univ.filter (fun v => c v = 0)
    let s₁ : Finset (Fin 5) := Finset.univ.filter (fun v => c v = 1)
    have hs₀ : s₀.card ≤ 2 := by
      apply card_le_two_of_homogeneous_cycleGraph_five s₀
      have hset : (s₀ : Set (Fin 5)) = {v | c v = 0} := by ext v; simp [s₀]
      rw [hset]
      exact hc 0
    have hs₁ : s₁.card ≤ 2 := by
      apply card_le_two_of_homogeneous_cycleGraph_five s₁
      have hset : (s₁ : Set (Fin 5)) = {v | c v = 1} := by ext v; simp [s₁]
      rw [hset]
      exact hc 1
    have hunion : s₀ ∪ s₁ = Finset.univ := by
      ext v
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true, s₀, s₁]
      rcases c v with ⟨_ | _ | _, hval⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · omega
    have hcard5 : 5 ≤ s₀.card + s₁.card := by
      calc
        5 = (Finset.univ : Finset (Fin 5)).card := by decide
        _ = (s₀ ∪ s₁).card := by rw [hunion]
        _ ≤ s₀.card + s₁.card := Finset.card_union_le s₀ s₁
    omega

/-- Explicit 5-vertex *house graph* (`C_5` plus chord `{0, 2}`): `{0, 1, 2}` is a `3`-clique and
`{3, 4}` is a `2`-clique, so `χ = 3` and `ζ = 2`. -/
def houseGraph : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel (fun u v =>
    (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2) ∨ (u = 0 ∧ v = 2) ∨
    (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 4) ∨ (u = 4 ∧ v = 0))

instance : DecidableRel houseGraph.Adj := by
  unfold houseGraph
  infer_instance

theorem chromaticNumber_houseGraph : houseGraph.chromaticNumber = 3 := by
  apply le_antisymm
  · rw [show (3 : ℕ∞) = ((3 : ℕ) : ℕ∞) from rfl, chromaticNumber_le_iff_colorable]
    let c : Fin 5 → Fin 3 := ![0, 1, 2, 0, 1]
    refine ⟨Coloring.mk c ?_⟩
    intro u v hadj
    revert u v hadj
    decide
  · have hclique : Pairwise (fun i j : Fin 3 => houseGraph.Adj ⟨i.1, by omega⟩ ⟨j.1, by omega⟩) := by
      intro i j hij
      revert i j hij
      decide
    exact le_chromaticNumber_of_pairwise_adj (by simp) (fun i : Fin 3 => ⟨i.1, by omega⟩) hclique

theorem cochromaticNumber_houseGraph : cochromaticNumber houseGraph = 2 := by
  apply le_antisymm
  · rw [cochromaticNumber_le_iff_cocolorable]
    let c : Fin 5 → Fin 2 := ![0, 0, 0, 1, 1]
    refine ⟨c, fun i => Or.inl ?_⟩
    intro u hu v hv huv
    simp only [Set.mem_ofPred_eq] at hu hv
    subst hu
    revert u v hv huv
    decide
  · have hpos : 1 ≤ cochromaticNumber houseGraph := cochromaticNumber_pos houseGraph
    have hne1 : cochromaticNumber houseGraph ≠ 1 := by
      rw [Ne, cochromaticNumber_eq_one_iff]
      rintro (hbot | htop)
      · have hadj : houseGraph.Adj 0 1 := by decide
        rw [hbot] at hadj
        exact hadj
      · have hnadj : ¬ houseGraph.Adj 0 3 := by decide
        rw [htop] at hnadj
        exact hnadj (by decide)
    omega

/-- Explicit 5-vertex witness of strict chromatic-cochromatic gap `χ(G) - ζ(G) = 1 > 0`. -/
theorem houseGraph_gap_eq_one :
    houseGraph.chromaticNumber.toNat - cochromaticNumber houseGraph = 1 := by
  have hχ : houseGraph.chromaticNumber.toNat = 3 := by
    rw [chromaticNumber_houseGraph]
    rfl
  rw [hχ, cochromaticNumber_houseGraph]

end JSP000506
