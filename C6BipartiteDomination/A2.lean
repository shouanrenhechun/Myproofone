/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import C6BipartiteDomination.Basic

/-! # A2: exact irreducibility of the responsibility region -/

namespace C6BipartiteDomination

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

/-- The responsibility region `V \ N[D \ X]`, using the closed neighborhood.
In particular, a retained vertex itself is excluded from the region. -/
noncomputable def responsibilityRegion (D X : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter (Responsible G D X)

theorem mem_responsibilityRegion (D X : Finset V) (v : V) :
    v ∈ responsibilityRegion G D X ↔ Responsible G D X v := by
  classical
  simp [responsibilityRegion]

/-- A bipartite dominating set for the graph induced by the finite vertex set
`R`. Selected vertices need not dominate each other. -/
def BipartiteDominatingOn (R Y : Finset V) : Prop :=
  Y ⊆ R ∧
    (∀ ⦃v⦄, v ∈ R → v ∉ Y → ∃ y ∈ Y, G.Adj y v) ∧
    IsBipartiteOn G Y

/-- First-level optimum: a minimum-cardinality bipartite dominating set. -/
def MinimumBipartiteDominatingSet (D : Finset V) : Prop :=
  IsBipartiteDominatingSet G D ∧
    ∀ E, IsBipartiteDominatingSet G E → D.card ≤ E.card

/-- Minimum bipartite domination restricted to an induced vertex set. -/
def MinimumBipartiteDominatingOn (R Y : Finset V) : Prop :=
  BipartiteDominatingOn G R Y ∧
    ∀ E, BipartiteDominatingOn G R E → Y.card ≤ E.card

/-- An `X` consisting of vertices isolated in the selected induced graph. -/
def IsolatedSubset (D X : Finset V) : Prop :=
  X ⊆ D ∧ ∀ ⦃x u⦄, x ∈ X → u ∈ D → ¬ G.Adj x u

theorem isolatedSubset_region_subset
    {D X : Finset V} (hX : IsolatedSubset G D X) :
    X ⊆ responsibilityRegion G D X := by
  classical
  intro x hx
  rw [mem_responsibilityRegion]
  refine ⟨?_, ?_⟩
  · intro hxret
    exact (Finset.mem_sdiff.mp hxret).2 hx
  · intro u hu hAdj
    exact hX.2 hx (Finset.mem_sdiff.mp hu).1 (hAdj.symm)

theorem isolatedSubset_dominates_region
    {D X : Finset V} (hD : IsBipartiteDominatingSet G D)
    (hX : IsolatedSubset G D X) : BipartiteDominatingOn G (responsibilityRegion G D X) X := by
  classical
  refine ⟨isolatedSubset_region_subset G hX, ?_, ?_⟩
  · intro v hvR hvX
    have hvD : v ∉ D := by
      intro hvD
      have hvRet : v ∈ D \ X := Finset.mem_sdiff.mpr ⟨hvD, by
        intro hvX'
        exact hvX hvX'
      ⟩
      exact (mem_responsibilityRegion G D X v).mp hvR |>.1 hvRet
    obtain ⟨u, huD, huAdj⟩ := hD.1 hvD
    have huNotRet : u ∉ D \ X := by
      intro huRet
      exact ((mem_responsibilityRegion G D X v).mp hvR).2 u huRet huAdj
    have huX : u ∈ X := by
      by_contra h
      exact huNotRet (Finset.mem_sdiff.mpr ⟨huD, h⟩)
    exact ⟨u, huX, huAdj⟩
  · refine ⟨fun _ => false, ?_⟩
    intro x y hx hy hxy
    exact (hX.2 hx (hX.1 hy) hxy).elim

/-- Lemma 2.3: every bipartite dominating set of the induced responsibility
region has at least `|X|` vertices. Together with the preceding witness
lemma, this gives the exact local optimum `γ_bip(G[R_D(X)]) = |X|`. -/
theorem responsibilityRegion_irreducible
    {D X Y : Finset V}
    (hD : MinimumBipartiteDominatingSet G D)
    (hX : IsolatedSubset G D X)
    (hY : BipartiteDominatingOn G (responsibilityRegion G D X) Y) :
    X.card ≤ Y.card := by
  classical
  let D' := (D \ X) ∪ Y
  have hcover : ∀ ⦃v⦄, Responsible G D X v → v ∈ Y ∨ ∃ y ∈ Y, G.Adj y v := by
    intro v hv
    have hvR : v ∈ responsibilityRegion G D X := (mem_responsibilityRegion G D X v).2 hv
    by_cases hvY : v ∈ Y
    · exact Or.inl hvY
    · obtain ⟨y, hy, hadj⟩ := hY.2.1 hvR hvY
      exact Or.inr ⟨y, hy, hadj⟩
  have hbip : IsBipartiteOn G D' := by
    rcases hD.1.2 with ⟨c, hc⟩
    rcases hY.2.2 with ⟨d, hd⟩
    refine ⟨fun v => if v ∈ D \ X then c v else d v, ?_⟩
    intro u v hu hv hadj
    rcases Finset.mem_union.mp hu with huRet | huY
    · rcases Finset.mem_union.mp hv with hvRet | hvY
      · have huD := (Finset.mem_sdiff.mp huRet).1
        have hvD := (Finset.mem_sdiff.mp hvRet).1
        simpa [huRet, hvRet] using hc huD hvD hadj
      · have hvR : v ∈ responsibilityRegion G D X := hY.1 hvY
        have hnotAdj := (mem_responsibilityRegion G D X v).mp hvR |>.2 u huRet
        exact (hnotAdj hadj).elim
    · rcases Finset.mem_union.mp hv with hvRet | hvY
      · have huR : u ∈ responsibilityRegion G D X := hY.1 huY
        have hnotAdj := (mem_responsibilityRegion G D X u).mp huR |>.2 v hvRet
        exact (hnotAdj hadj.symm).elim
      · have huR : u ∈ responsibilityRegion G D X := hY.1 huY
        have hvR : v ∈ responsibilityRegion G D X := hY.1 hvY
        have huNotRet := (mem_responsibilityRegion G D X u).mp huR |>.1
        have hvNotRet := (mem_responsibilityRegion G D X v).mp hvR |>.1
        simpa [huNotRet, hvNotRet] using hd huY hvY hadj
  have hD' : IsBipartiteDominatingSet G D' :=
    collective_exchange G hcover hbip
  have hmin := hD.2 D' hD'
  have hdisj : Disjoint (D \ X) Y := by
    refine Finset.disjoint_left.mpr ?_
    intro v hvRet hvY
    have hvR : v ∈ responsibilityRegion G D X := hY.1 hvY
    exact (mem_responsibilityRegion G D X v).mp hvR |>.1 hvRet
  have hcardD' : D'.card = D.card - X.card + Y.card := by
    dsimp [D']
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_sdiff_of_subset hX.1]
  rw [hcardD'] at hmin
  have hXcard : X.card ≤ D.card := Finset.card_le_card hX.1
  omega

/-- The exact equality in Lemma 2.3, expressed as a local witness together
with minimality against every local bipartite dominating set. -/
theorem lemma_2_3_exact
    {D X : Finset V}
    (hD : MinimumBipartiteDominatingSet G D)
    (hX : IsolatedSubset G D X) :
    BipartiteDominatingOn G (responsibilityRegion G D X) X ∧
      ∀ Y, BipartiteDominatingOn G (responsibilityRegion G D X) Y → X.card ≤ Y.card := by
  refine ⟨isolatedSubset_dominates_region G hD.1 hX, ?_⟩
  intro Y hY
  exact responsibilityRegion_irreducible G hD hX hY

/-- Lemma 2.4 in the form used by the proof: a globally minimum set restricts
to minimum bipartite dominating sets on two anticomplete parts. The final
cardinality identity is the additivity of `γ_bip` for a disjoint union. -/
private theorem lemma_2_4_left_minimum
    {A B D : Finset V}
    (hparts : A ∪ B = Finset.univ)
    (hdisj : Disjoint A B)
    (hcross : ∀ ⦃a b⦄, a ∈ A → b ∈ B → ¬ G.Adj a b)
    (hD : MinimumBipartiteDominatingSet G D) :
    MinimumBipartiteDominatingOn G A (D ∩ A) ∧
      D.card = (D ∩ A).card + (D ∩ B).card := by
  classical
  have hDsub : D ⊆ A ∪ B := by rw [hparts]; exact Finset.subset_univ _
  have hDA : D ∩ A ⊆ D := Finset.inter_subset_left
  have hDB : D ∩ B ⊆ D := Finset.inter_subset_left
  have hDAA : D ∩ A ⊆ A := Finset.inter_subset_right
  have hDBB : D ∩ B ⊆ B := Finset.inter_subset_right
  have hDBip : IsBipartiteOn G (D ∩ A) := by
    rcases hD.1.2 with ⟨c, hc⟩
    exact ⟨c, fun hu hv huD hvD hadj => hc (hDA huD) (hDA hvD) hadj⟩
  have hDomA : ∀ ⦃v⦄, v ∈ A → v ∉ D ∩ A →
      ∃ y ∈ D ∩ A, G.Adj y v := by
    intro v hvA hvNot
    have hvD : v ∉ D := by
      intro hvD
      exact hvNot (Finset.mem_inter.mpr ⟨hvD, hvA⟩)
    obtain ⟨d, hdD, hdv⟩ := hD.1.1 hvD
    have hdParts : d ∈ A ∪ B := hDsub hdD
    rcases Finset.mem_union.mp hdParts with hdA | hdB
    · exact ⟨d, Finset.mem_inter.mpr ⟨hdD, hdA⟩, hdv⟩
    · have hcross' := hcross hvA hdB
      exact (hcross' hdv.symm).elim
  have hLocA : BipartiteDominatingOn G A (D ∩ A) :=
    ⟨hDAA, hDomA, hDBip⟩
  have hLocMinA : ∀ E, BipartiteDominatingOn G A E → (D ∩ A).card ≤ E.card := by
    intro E hE
    let D' := E ∪ (D ∩ B)
    have hEdisj : Disjoint E (D ∩ B) := by
      rw [Finset.disjoint_left]
      intro v hvE hvDB
      have hvA := hE.1 hvE
      have hvB := hDBB hvDB
      exact (Finset.disjoint_left.mp hdisj hvA hvB).elim
    have hDom' : Dominates G D' := by
      intro v hvD'
      by_cases hvA : v ∈ A
      · have hvE : v ∉ E := by
          intro hvE
          exact hvD' (Finset.mem_union_left _ hvE)
        obtain ⟨e, heE, hev⟩ := hE.2.1 hvA hvE
        exact ⟨e, Finset.mem_union_left _ heE, hev⟩
      · have hvB : v ∈ B := by
          have hvParts : v ∈ A ∪ B := by rw [hparts]; exact Finset.mem_univ _
          rcases Finset.mem_union.mp hvParts with h | h
          · exact (hvA h).elim
          · exact h
        have hvD : v ∉ D := by
          intro hvD
          have hvDB : v ∈ D ∩ B := Finset.mem_inter.mpr ⟨hvD, hvB⟩
          exact hvD' (Finset.mem_union_right E hvDB)
        obtain ⟨d, hdD, hdv⟩ := hD.1.1 hvD
        have hdParts : d ∈ A ∪ B := hDsub hdD
        rcases Finset.mem_union.mp hdParts with hdA | hdB
        · have hcross' := hcross hdA hvB
          exact (hcross' hdv).elim
        · exact ⟨d, Finset.mem_union_right E
            (Finset.mem_inter.mpr ⟨hdD, hdB⟩), hdv⟩
    have hBip' : IsBipartiteOn G D' := by
      rcases hE.2.2 with ⟨eColor, heColor⟩
      rcases hD.1.2 with ⟨dColor, hdColor⟩
      refine ⟨fun v => if v ∈ E then eColor v else dColor v, ?_⟩
      intro u v hu hv hadj
      rcases Finset.mem_union.mp hu with huE | huDB
      · rcases Finset.mem_union.mp hv with hvE | hvDB
        · simpa [huE, hvE] using heColor huE hvE hadj
        · have hcross' := hcross (hE.1 huE) (hDBB hvDB)
          exact (hcross' hadj).elim
      · rcases Finset.mem_union.mp hv with hvE | hvDB
        · have hcross' := hcross (hE.1 hvE) (hDBB huDB)
          exact (hcross' hadj.symm).elim
        · have huNotE : u ∉ E := by
            intro huE
            exact (Finset.disjoint_left.mp hEdisj huE huDB).elim
          have hvNotE : v ∉ E := by
            intro hvE
            exact (Finset.disjoint_left.mp hEdisj hvE hvDB).elim
          simpa [huNotE, hvNotE] using hdColor (hDB huDB) (hDB hvDB) hadj
    have hDdom' : IsBipartiteDominatingSet G D' := ⟨hDom', hBip'⟩
    have hmin := hD.2 D' hDdom'
    have hDpart : D.card = (D ∩ A).card + (D ∩ B).card := by
      have hDdisj : Disjoint (D ∩ A) (D ∩ B) := by
        rw [Finset.disjoint_left]
        intro v hvA hvB
        exact (Finset.disjoint_left.mp hdisj (hDAA hvA) (hDBB hvB)).elim
      have hDeq : (D ∩ A) ∪ (D ∩ B) = D := by
        ext v
        constructor
        · intro hv
          rcases Finset.mem_union.mp hv with h | h
          · exact (Finset.mem_inter.mp h).1
          · exact (Finset.mem_inter.mp h).1
        · intro hvD
          have hvParts : v ∈ A ∪ B := hDsub hvD
          rcases Finset.mem_union.mp hvParts with hvA | hvB
          · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvD, hvA⟩)
          · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvD, hvB⟩)
      calc
        D.card = ((D ∩ A) ∪ (D ∩ B)).card := congrArg Finset.card hDeq.symm
        _ = (D ∩ A).card + (D ∩ B).card :=
          Finset.card_union_of_disjoint hDdisj
    have hD'card : D'.card = E.card + (D ∩ B).card := by
      dsimp [D']
      rw [Finset.card_union_of_disjoint hEdisj]
    rw [hDpart, hD'card] at hmin
    omega
  have hDcard : D.card = (D ∩ A).card + (D ∩ B).card := by
    have hDdisj : Disjoint (D ∩ A) (D ∩ B) := by
      rw [Finset.disjoint_left]
      intro v hvA hvB
      exact (Finset.disjoint_left.mp hdisj (hDAA hvA) (hDBB hvB)).elim
    have hDeq : (D ∩ A) ∪ (D ∩ B) = D := by
      ext v
      constructor
      · intro hv
        rcases Finset.mem_union.mp hv with h | h
        · exact (Finset.mem_inter.mp h).1
        · exact (Finset.mem_inter.mp h).1
      · intro hvD
        have hvParts : v ∈ A ∪ B := hDsub hvD
        rcases Finset.mem_union.mp hvParts with hvA | hvB
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvD, hvA⟩)
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvD, hvB⟩)
    calc
      D.card = ((D ∩ A) ∪ (D ∩ B)).card := congrArg Finset.card hDeq.symm
      _ = (D ∩ A).card + (D ∩ B).card := Finset.card_union_of_disjoint hDdisj
  exact ⟨⟨hLocA, hLocMinA⟩, hDcard⟩

theorem lemma_2_4_component_additivity
    {A B D : Finset V}
    (hparts : A ∪ B = Finset.univ)
    (hdisj : Disjoint A B)
    (hcross : ∀ ⦃a b⦄, a ∈ A → b ∈ B → ¬ G.Adj a b)
    (hD : MinimumBipartiteDominatingSet G D) :
    MinimumBipartiteDominatingOn G A (D ∩ A) ∧
      MinimumBipartiteDominatingOn G B (D ∩ B) ∧
      D.card = (D ∩ A).card + (D ∩ B).card := by
  classical
  have hswapCross : ∀ ⦃b a⦄, b ∈ B → a ∈ A → ¬ G.Adj b a := by
    intro b a hb ha hAdj
    exact hcross ha hb hAdj.symm
  have hswapParts : B ∪ A = Finset.univ := by
    rw [Finset.union_comm, hparts]
  have hswapDisj : Disjoint B A := by
    rw [Finset.disjoint_left]
    intro x hxB hxA
    exact (Finset.disjoint_left.mp hdisj hxA hxB).elim
  have hleft := lemma_2_4_left_minimum G hparts hdisj hcross hD
  have hright := lemma_2_4_left_minimum G hswapParts hswapDisj hswapCross hD
  exact ⟨hleft.1, hright.1, hleft.2⟩

end C6BipartiteDomination

