import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Set.Card

/-!
# Cochromatic Number and Cocoloring Definitions

This module defines cocolorings, cocolorability, the cochromatic number `ζ(G)` of a simple graph,
and signed cocoloring witnesses (used in the first- and second-moment arguments for `G(n, 1/2)`).

We provide both the function-coloring formulation (`c : V → α` whose fibers are cliques or
independent sets) and the set-partition formulation (`Setoid.IsPartition P` into cliques and
independent sets), proving their exact equivalence.
-/

namespace JSP000506

open SimpleGraph

section Cocoloring

/-- A subset `s` of vertices is homogeneous (cochromatic-valid) in `G` if it is either a clique
or an independent set. -/
def IsHomogeneousSet {V : Type*} (G : SimpleGraph V) (s : Set V) : Prop :=
  G.IsClique s ∨ G.IsIndepSet s

lemma isHomogeneousSet_empty {V : Type*} (G : SimpleGraph V) : IsHomogeneousSet G ∅ :=
  Or.inl G.isClique_empty

lemma isHomogeneousSet_singleton {V : Type*} (G : SimpleGraph V) (v : V) :
    IsHomogeneousSet G {v} :=
  Or.inl (G.isClique_singleton v)

lemma IsHomogeneousSet.subset {V : Type*} {G : SimpleGraph V} {s t : Set V}
    (h : IsHomogeneousSet G s) (ht : t ⊆ s) : IsHomogeneousSet G t := by
  rcases h with hc | hi
  · exact Or.inl (hc.subset ht)
  · exact Or.inr (hi.mono ht)

lemma isHomogeneousSet_compl {V : Type*} (G : SimpleGraph V) {s : Set V} :
    IsHomogeneousSet Gᶜ s ↔ IsHomogeneousSet G s := by
  unfold IsHomogeneousSet
  rw [isClique_compl, isIndepSet_compl, or_comm]

/-- A function `c : V → α` is a *cocoloring* of `G` if every color class `{v | c v = i}` is
either a clique or an independent set in `G`. -/
def IsCocoloring {V α : Type*} (G : SimpleGraph V) (c : V → α) : Prop :=
  ∀ i : α, G.IsClique {v : V | c v = i} ∨ G.IsIndepSet {v : V | c v = i}

/-- `G` is `k`-cocolorable if there exists a cocoloring `c : V → Fin k`. -/
def Cocolorable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, IsCocoloring G c

/-- A set of vertex subsets `P` is a *cocoloring partition* of `G` if `P` is a partition of `V`
into nonempty pairwise-disjoint subsets (`Setoid.IsPartition P`) and every part `s ∈ P` is either
a clique or an independent set in `G`. -/
def IsCocoloringPartition {V : Type*} (G : SimpleGraph V) (P : Set (Set V)) : Prop :=
  Setoid.IsPartition P ∧ ∀ s ∈ P, G.IsClique s ∨ G.IsIndepSet s

lemma IsCocoloring.comp_injective {V α β : Type*} {G : SimpleGraph V} {c : V → α}
    (hc : IsCocoloring G c) {f : α → β} (hf : Function.Injective f) :
    IsCocoloring G (f ∘ c) := by
  intro b
  by_cases hb : ∃ a, f a = b
  · rcases hb with ⟨a, rfl⟩
    have hset : {v : V | (f ∘ c) v = f a} = {v : V | c v = a} := by
      ext v
      simp [hf.eq_iff]
    rw [hset]
    exact hc a
  · push Not at hb
    have hset : {v : V | (f ∘ c) v = b} = ∅ := by
      ext v
      simp [hb (c v)]
    rw [hset]
    exact Or.inl G.isClique_empty

lemma Cocolorable.mono {V : Type*} {G : SimpleGraph V} {k m : ℕ} (hkm : k ≤ m)
    (hc : Cocolorable G k) : Cocolorable G m := by
  rcases hc with ⟨c, hc⟩
  exact ⟨Fin.castLE hkm ∘ c, hc.comp_injective (Fin.castLE_injective hkm)⟩

lemma cocolorable_of_colorable {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (hc : G.Colorable k) : Cocolorable G k := by
  rcases hc with ⟨C⟩
  exact ⟨C, fun i => Or.inr (C.isIndepSet_colorClass i)⟩

lemma cocolorable_of_isEmpty {V : Type*} [IsEmpty V] (G : SimpleGraph V) (k : ℕ) :
    Cocolorable G k :=
  ⟨isEmptyElim, fun _ => by
    convert Or.inl G.isClique_empty
    exact Set.eq_empty_of_isEmpty _⟩

@[simp]
lemma cocolorable_zero_iff {V : Type*} (G : SimpleGraph V) :
    Cocolorable G 0 ↔ IsEmpty V :=
  ⟨fun ⟨c, _⟩ => ⟨fun v => (c v).elim0⟩, fun _ => cocolorable_of_isEmpty G 0⟩

lemma cocolorable_of_finite {V : Type*} [Finite V] (G : SimpleGraph V) :
    ∃ k : ℕ, Cocolorable G k := by
  cases nonempty_fintype V
  exact ⟨Fintype.card V, cocolorable_of_colorable G.colorable_of_fintype⟩

lemma cocolorable_card {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Cocolorable G (Fintype.card V) :=
  cocolorable_of_colorable G.colorable_of_fintype

lemma IsCocoloring.isCocoloringPartition_ker {V α : Type*} {G : SimpleGraph V} {c : V → α}
    (hc : IsCocoloring G c) : IsCocoloringPartition G (Setoid.ker c).classes := by
  refine ⟨Setoid.isPartition_classes (Setoid.ker c), ?_⟩
  rintro s ⟨v, rfl⟩
  exact hc (c v)

/-- Equivalence between `k`-cocolorability via functions `V → Fin k` and the existence of a finite
set-partition of `V` into at most `k` nonempty cliques or independent sets. -/
theorem cocolorable_iff_exists_partition {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    Cocolorable G k ↔
      ∃ P : Set (Set V), IsCocoloringPartition G P ∧ P.Finite ∧ P.ncard ≤ k := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨(Setoid.ker c).classes, hc.isCocoloringPartition_ker, Setoid.finite_classes_ker c, ?_⟩
    classical
    let ft : Fintype (Setoid.ker c).classes := (Setoid.finite_classes_ker c).fintype
    rw [← Nat.card_coe_set_eq, @Nat.card_eq_fintype_card _ ft]
    exact (@Setoid.card_classes_ker_le _ _ _ c ft).trans (by simp)
  · rintro ⟨P, ⟨hpart, hhom⟩, hfin, hcard⟩
    by_cases hV : IsEmpty V
    · exact cocolorable_of_isEmpty G k
    rw [not_isEmpty_iff] at hV
    let ft : Fintype P := hfin.fintype
    have hcardP : @Fintype.card P ft ≤ k := by
      rwa [← Nat.card_coe_set_eq, @Nat.card_eq_fintype_card _ ft] at hcard
    have hinj : ∃ f : P → Fin k, Function.Injective f := by
      have hle : @Fintype.card P ft ≤ Fintype.card (Fin k) := by simpa using hcardP
      obtain ⟨f⟩ := @Function.Embedding.nonempty_of_card_le P (Fin k) ft _ hle
      exact ⟨f, f.injective⟩
    rcases hinj with ⟨f, hf⟩
    let partOf : V → P := fun v =>
      ⟨Classical.choose (hpart.2 v), (Classical.choose_spec (hpart.2 v)).1.1⟩
    have hmem_partOf : ∀ v : V, v ∈ (partOf v : Set V) :=
      fun v => (Classical.choose_spec (hpart.2 v)).1.2
    have hpartOf_eq : ∀ {v : V} {s : P}, v ∈ (s : Set V) → partOf v = s := by
      intro v s hvs
      apply Subtype.ext
      exact ((Classical.choose_spec (hpart.2 v)).2 (s : Set V) ⟨s.2, hvs⟩).symm
    refine ⟨fun v => f (partOf v), fun i => ?_⟩
    by_cases hi : ∃ s : P, f s = i
    · rcases hi with ⟨s, rfl⟩
      have hset : {v : V | f (partOf v) = f s} = (s : Set V) := by
        ext v
        simp only [Set.mem_ofPred_eq, hf.eq_iff]
        exact ⟨fun h => h ▸ hmem_partOf v, fun h => hpartOf_eq h⟩
      rw [hset]
      exact hhom s s.2
    · push Not at hi
      have hset : {v : V | f (partOf v) = i} = ∅ := by
        ext v
        simp [hi (partOf v)]
      rw [hset]
      exact Or.inl G.isClique_empty

/-- The *cochromatic number* `ζ(G)` of a simple graph `G` is the minimum number of parts in a
vertex partition of `G` in which every part induces either a clique or an independent set.
For graphs without any finite cocoloring, `sInf ∅ = 0` by Lean's convention on `ℕ`. -/
noncomputable def cochromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | Cocolorable G k}

lemma cochromaticNumber_bddBelow {V : Type*} (G : SimpleGraph V) :
    BddBelow {k : ℕ | Cocolorable G k} :=
  ⟨0, fun _ _ => Nat.zero_le _⟩

lemma Cocolorable.cochromaticNumber_le {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (hc : Cocolorable G k) : cochromaticNumber G ≤ k :=
  Nat.sInf_le hc

lemma cocolorable_cochromaticNumber {V : Type*} [Finite V] (G : SimpleGraph V) :
    Cocolorable G (cochromaticNumber G) :=
  Nat.sInf_mem (cocolorable_of_finite G)

theorem cochromaticNumber_le_iff_cocolorable {V : Type*} [Finite V] (G : SimpleGraph V) {k : ℕ} :
    cochromaticNumber G ≤ k ↔ Cocolorable G k :=
  ⟨fun h => (cocolorable_cochromaticNumber G).mono h, Cocolorable.cochromaticNumber_le⟩

theorem le_cochromaticNumber_iff {V : Type*} [Finite V] (G : SimpleGraph V) {k : ℕ} :
    k ≤ cochromaticNumber G ↔ ∀ m : ℕ, Cocolorable G m → k ≤ m :=
  ⟨fun hk _ hm => hk.trans hm.cochromaticNumber_le,
   fun h => h (cochromaticNumber G) (cocolorable_cochromaticNumber G)⟩

@[simp]
theorem cochromaticNumber_eq_zero_iff {V : Type*} [Finite V] (G : SimpleGraph V) :
    cochromaticNumber G = 0 ↔ IsEmpty V := by
  rw [← Nat.le_zero, cochromaticNumber_le_iff_cocolorable, cocolorable_zero_iff]

theorem cochromaticNumber_pos {V : Type*} [Finite V] [Nonempty V] (G : SimpleGraph V) :
    0 < cochromaticNumber G := by
  rw [Nat.pos_iff_ne_zero, Ne, cochromaticNumber_eq_zero_iff]
  exact not_isEmpty_of_nonempty V

end Cocoloring

/-! ### Signed Cocoloring Witnesses and Mark-Forgetting Injectivity -/

section SignedWitness

/-- A declaration (`false` = independent set, `true` = clique) is satisfied by a vertex subset `s`
in `G` when `s` induces an independent set or a clique accordingly. -/
def SatisfiesSign {V : Type*} (G : SimpleGraph V) (sign : Bool) (s : Set V) : Prop :=
  match sign with
  | false => G.IsIndepSet s
  | true => G.IsClique s

lemma SatisfiesSign.isHomogeneousSet {V : Type*} {G : SimpleGraph V} {sign : Bool} {s : Set V}
    (h : SatisfiesSign G sign s) : IsHomogeneousSet G s := by
  cases sign
  · exact Or.inr h
  · exact Or.inl h

/-- No subset of cardinality at least `2` can simultaneously be both a clique and an independent
set in the same simple graph `G`. -/
theorem not_isClique_and_isIndepSet_of_two_le_card {V : Type*} {G : SimpleGraph V} {s : Finset V}
    (hs : 2 ≤ s.card) : ¬ (G.IsClique (s : Set V) ∧ G.IsIndepSet (s : Set V)) := by
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (Nat.one_lt_two.trans_le hs)
  rintro ⟨hcl, hind⟩
  exact hind hu hv huv (hcl hu hv huv)

/-- **Mark-forgetting injectivity**: On any subset of size at least `2`, at most one `I`/`K` sign
declaration can be realized by `G`. Consequently, forgetting the signs on any partition whose
classes all have size at least `2` is injective on realized signed witnesses. -/
theorem satisfiesSign_unique_of_two_le_card {V : Type*} {G : SimpleGraph V} {s : Finset V}
    (hs : 2 ≤ s.card) {b₁ b₂ : Bool}
    (h₁ : SatisfiesSign G b₁ (s : Set V)) (h₂ : SatisfiesSign G b₂ (s : Set V)) :
    b₁ = b₂ := by
  cases b₁ <;> cases b₂
  · rfl
  · exfalso
    exact not_isClique_and_isIndepSet_of_two_le_card hs ⟨h₂, h₁⟩
  · exfalso
    exact not_isClique_and_isIndepSet_of_two_le_card hs ⟨h₁, h₂⟩
  · rfl

/-- Given a finite family of signed parts covering `V`, `G` is cocolorable with at most the
number of parts. -/
theorem cocolorable_of_signed_cover {V ι : Type*} [Fintype ι] (G : SimpleGraph V)
    (parts : ι → Finset V) (signs : ι → Bool)
    (hcover : ∀ v : V, ∃ i : ι, v ∈ parts i)
    (hvalid : ∀ i : ι, SatisfiesSign G (signs i) (parts i : Set V)) :
    Cocolorable G (Fintype.card ι) := by
  let equiv := Fintype.equivFin ι
  let chooseIdx : V → ι := fun v => Classical.choose (hcover v)
  have hmem : ∀ v : V, v ∈ parts (chooseIdx v) := fun v => Classical.choose_spec (hcover v)
  refine ⟨fun v => equiv (chooseIdx v), fun j => ?_⟩
  let i := equiv.symm j
  have hsub : {v : V | equiv (chooseIdx v) = j} ⊆ (parts i : Set V) := by
    intro v hv
    have hci : chooseIdx v = i := by
      simpa [i] using congrArg equiv.symm hv
    simpa [hci] using hmem v
  exact (hvalid i).isHomogeneousSet.subset hsub

end SignedWitness

end JSP000506
