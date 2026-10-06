/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import C6BipartiteDomination.A8

/-! # A9: compensation regions (Lemmas 8.4 and 8.5) -/

namespace C6BipartiteDomination

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

/-- The open neighborhood of `q` restricted to the selected set `D`. -/
noncomputable def neighborhoodIn (D : Finset V) (q : V) : Finset V := by
  classical
  exact D.filter fun d => G.Adj q d

theorem mem_neighborhoodIn (D : Finset V) (q d : V) :
    d ∈ neighborhoodIn G D q ↔ d ∈ D ∧ G.Adj q d := by
  classical
  simp [neighborhoodIn]

/-- The local compensation region around a chosen repair edge `(u,w)`. -/
noncomputable def compensationRegion (D X : Finset V) (u w : V) : Finset V :=
  responsibilityRegion G D (X ∪ {u}) \ X

/-- Vertices privately dominated by `u`; this is exactly the existing
private external neighborhood from Lemma 3.1. -/
noncomputable def privateCompensation (D : Finset V) (u : V) : Finset V :=
  privateExternalNeighbors G D u

/-- Vertices with selected neighborhood `{u,z}` for some `z ∈ X`. -/
noncomputable def sharedCompensation (D X : Finset V) (u : V) : Finset V := by
  classical
  exact (Finset.univ \ D).filter fun q =>
    ∃ z ∈ X, neighborhoodIn G D q = {u, z}

theorem mem_privateCompensation (D : Finset V) (u q : V) :
    u ∈ D → (q ∈ privateCompensation G D u ↔
      q ∉ D ∧ neighborhoodIn G D q = {u}) := by
  classical
  intro huD
  rw [privateCompensation, mem_privateExternalNeighbors]
  constructor
  · rintro ⟨hqD, hpriv⟩
    refine ⟨hqD, Finset.ext fun d => ?_⟩
    constructor
    · intro hdN
      have hdD := (mem_neighborhoodIn G D q d).mp hdN |>.1
      have hdq := (mem_neighborhoodIn G D q d).mp hdN |>.2
      exact Finset.mem_singleton.mpr ((hpriv d hdD).mp hdq.symm)
    · intro hdu
      have hdu' := Finset.mem_singleton.mp hdu
      subst d
      have huq : G.Adj u q := (hpriv u huD).mpr rfl
      exact (mem_neighborhoodIn G D q u).mpr ⟨huD, huq.symm⟩
  · rintro ⟨hqD, hN⟩
    refine ⟨hqD, ?_⟩
    intro d hdD
    constructor
    · intro hqd
      have hdN : d ∈ neighborhoodIn G D q :=
        (mem_neighborhoodIn G D q d).mpr ⟨hdD, hqd.symm⟩
      have : d ∈ ({u} : Finset V) := by simpa [hN] using hdN
      exact Finset.mem_singleton.mp this
    · intro hdu
      subst d
      have huN : u ∈ neighborhoodIn G D q := by simpa [hN]
      exact ((mem_neighborhoodIn G D q u).mp huN).2.symm

theorem mem_sharedCompensation (D X : Finset V) (u q : V) :
    q ∈ sharedCompensation G D X u ↔
      q ∉ D ∧ ∃ z ∈ X, neighborhoodIn G D q = {u, z} := by
  classical
  simp [sharedCompensation]

theorem ZPart_disjoint_BPart (D : Finset V) :
    Disjoint (ZPart G D) (BPart G D) := by
  rw [Finset.disjoint_left]
  intro z hz hb
  exact (mem_BPart G D z).mp hb |>.2 hz

/-- Adding a vertex with exactly one neighbor to a bipartite induced set
preserves bipartiteness. -/
theorem bipartite_add_with_single_neighbor
    {S : Finset V} {q u : V}
    (hS : IsBipartiteOn G S) (hu : u ∈ S) (hqu : G.Adj q u)
    (hqS : q ∉ S)
    (honly : ∀ v ∈ S, G.Adj q v → v = u) :
    IsBipartiteOn G (S ∪ {q}) := by
  classical
  rcases hS with ⟨c, hc⟩
  refine ⟨fun v => if v = q then !c u else c v, ?_⟩
  intro a b ha hb hab
  rcases Finset.mem_union.mp ha with haS | haq
  · rcases Finset.mem_union.mp hb with hbS | hbq
    · have haq' : a ≠ q := fun h => hqS (h ▸ haS)
      have hbq' : b ≠ q := fun h => hqS (h ▸ hbS)
      simpa [haq', hbq'] using hc haS hbS hab
    · have hbEq : b = q := Finset.mem_singleton.mp hbq
      subst b
      have haq' : a ≠ q := fun h => hqS (h ▸ haS)
      have hau : a = u := honly a haS hab.symm
      subst a
      simp [haq']
  · have haEq : a = q := Finset.mem_singleton.mp haq
    subst a
    rcases Finset.mem_union.mp hb with hbS | hbq
    · have hbq' : b ≠ q := fun h => hqS (h ▸ hbS)
      have hbu : b = u := honly b hbS hab
      subst b
      simp [hbq']
    · have hbEq : b = q := Finset.mem_singleton.mp hbq
      subst b
      exact (G.irrefl hab).elim

/-- Basic consequences of the closed-neighborhood responsibility region for
the compensation set `R_D(X ∪ {u}) \ X`. -/
theorem compensation_vertex_properties
    {D X : Finset V} {u w q : V}
    (hDom : Dominates G D)
    (hX : X ⊆ Z0Part G D)
    (huB : u ∈ BPart G D)
    (hq : q ∈ compensationRegion G D X u w) :
    q ∉ D ∧ G.Adj q u ∧
      neighborhoodIn G D q ⊆ X ∪ {u} ∧
      (neighborhoodIn G D q).Nonempty := by
  classical
  let T := X ∪ {u}
  have hqR : q ∈ responsibilityRegion G D T :=
    (Finset.mem_sdiff.mp hq).1
  have hqX : q ∉ X := (Finset.mem_sdiff.mp hq).2
  have huD : u ∈ D := (mem_BPart G D u).mp huB |>.1
  have huNotZ : u ∉ ZPart G D := (mem_BPart G D u).mp huB |>.2
  have huNoniso : ∃ v ∈ D, G.Adj u v := by
    by_contra hn
    apply huNotZ
    rw [mem_ZPart]
    refine ⟨huD, ?_⟩
    intro v hv huv
    exact hn ⟨v, hv, huv⟩
  have hqNotD : q ∉ D := by
    intro hqD
    have hqNotRet := (mem_responsibilityRegion G D T q).mp hqR |>.1
    have hqT : q ∈ T := by
      by_contra hqT
      exact hqNotRet (Finset.mem_sdiff.mpr ⟨hqD, hqT⟩)
    have hqEq : q = u := by
      rcases Finset.mem_union.mp hqT with hqX' | hqU
      · exact (hqX hqX').elim
      · exact Finset.mem_singleton.mp hqU
    subst q
    obtain ⟨v, hvD, huv⟩ := huNoniso
    have hvNotX : v ∉ X := by
      intro hvX
      have hvZ0 := hX hvX
      have hvZ := (mem_Z0Part G D v).mp hvZ0 |>.1
      have hvIso := (mem_ZPart G D v).mp hvZ
      exact hvIso.2 u huD huv.symm
    have hvNeU : v ≠ u := by
      intro heq
      subst v
      exact G.irrefl huv
    have hvRet : v ∈ D \ T := by
      refine Finset.mem_sdiff.mpr ⟨hvD, ?_⟩
      intro hvT
      rcases Finset.mem_union.mp hvT with hvX | hvU
      · exact hvNotX hvX
      · exact hvNeU (Finset.mem_singleton.mp hvU)
    exact ((mem_responsibilityRegion G D T u).mp hqR).2 v hvRet huv.symm
  have hqNsub : neighborhoodIn G D q ⊆ T := by
    intro d hd
    have hdN := (mem_neighborhoodIn G D q d).mp hd
    have hqNoRet := (mem_responsibilityRegion G D T q).mp hqR |>.2 d
    by_contra hdT
    exact hqNoRet (Finset.mem_sdiff.mpr ⟨hdN.1, hdT⟩) hdN.2.symm
  have hqNne : (neighborhoodIn G D q).Nonempty := by
    obtain ⟨d, hdD, hdAdj⟩ := hDom hqNotD
    exact ⟨d, (mem_neighborhoodIn G D q d).mpr ⟨hdD, hdAdj.symm⟩⟩
  have hquN : u ∈ neighborhoodIn G D q := by
    by_contra huN
    have hqW0 : q ∈ W0Part G D := by
      rw [mem_W0Part]
      refine ⟨hqNotD, ?_⟩
      intro b hb hbq
      have hbT : b ∈ T := hqNsub ((mem_neighborhoodIn G D q b).mpr ⟨
        (mem_BPart G D b).mp hb |>.1, hbq.symm⟩)
      rcases Finset.mem_union.mp hbT with hbX | hbU
      · exact (Finset.disjoint_left.mp (Z0_disjoint_B G) (hX hbX) hb).elim
      · exact huN (Finset.mem_singleton.mp hbU ▸
          (mem_neighborhoodIn G D q b).mpr ⟨(mem_BPart G D b).mp hb |>.1,
            hbq.symm⟩)
    obtain ⟨d, hdN⟩ := hqNne
    have hdX : d ∈ X := by
      have hdT := hqNsub hdN
      rcases Finset.mem_union.mp hdT with hdX | hdU
      · exact hdX
      · exact (huN (Finset.mem_singleton.mp hdU ▸ hdN)).elim
    have hdz0 := (mem_Z0Part G D d).mp (hX hdX)
    exact hdz0.2 q hqW0 ((mem_neighborhoodIn G D q d).mp hdN).2.symm
  refine ⟨hqNotD, ?_, ?_, hqNne⟩
  · exact ((mem_neighborhoodIn G D q u).mp hquN).2
  · intro d hd
    rcases Finset.mem_union.mp (hqNsub hd) with hdX | hdU
    · exact Finset.mem_union_left _ hdX
    · exact Finset.mem_union_right _ hdU

/-- A compensation vertex cannot have two distinct neighbors in the isolated
support `X`: replacing those two selected vertices by it would improve `D`. -/
theorem compensation_has_at_most_one_X_neighbor
    {D X : Finset V} {u w q x y : V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hX : X ⊆ Z0Part G D)
    (huB : u ∈ BPart G D)
    (hq : q ∈ compensationRegion G D X u w)
    (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) :
    ¬ (G.Adj q x ∧ G.Adj q y) := by
  classical
  intro hqxy
  let Y : Finset V := neighborhoodIn G D q ∩ X
  have hxY : x ∈ Y := by
    simp only [Y, Finset.mem_inter]
    exact ⟨(mem_neighborhoodIn G D q x).mpr ⟨
      (mem_ZPart G D x).mp ((mem_Z0Part G D x).mp (hX hx) |>.1) |>.1,
      hqxy.1⟩, hx⟩
  have hyY : y ∈ Y := by
    simp only [Y, Finset.mem_inter]
    exact ⟨(mem_neighborhoodIn G D q y).mpr ⟨
      (mem_ZPart G D y).mp ((mem_Z0Part G D y).mp (hX hy) |>.1) |>.1,
      hqxy.2⟩, hy⟩
  have hYsubX : Y ⊆ X := by
    exact Finset.inter_subset_right
  have hYsubD : Y ⊆ D := by
    intro z hz
    have hzX := hYsubX hz
    exact (mem_ZPart G D z).mp
      ((mem_Z0Part G D z).mp (hX hzX) |>.1) |>.1
  have hYreg : responsibilityRegion G D Y = Y :=
    lemma_5_1_responsibility_eq G hCan.1 (hYsubX.trans hX)
  have hprops := compensation_vertex_properties G hCan.1.1 hX huB hq
  have hqD := hprops.1
  have hqu := hprops.2.1
  have hqNsub := hprops.2.2.1
  have hqNotY : q ∉ Y := by
    intro hqY
    have hqN := (Finset.mem_inter.mp hqY).1
    exact hqD ((mem_neighborhoodIn G D q q).mp hqN).1
  have hS : IsBipartiteOn G (D \ Y) :=
    bipartiteOn_subset G Finset.sdiff_subset hCan.1.2
  have huS : u ∈ D \ Y := by
    refine Finset.mem_sdiff.mpr ⟨(mem_BPart G D u).mp huB |>.1, ?_⟩
    intro huY
    have huXY := hYsubX huY
    exact (Finset.disjoint_left.mp (Z0_disjoint_B G) (hX huXY) huB)
  have hqAdjU : G.Adj q u := hqu
  have hqOnlyU : ∀ v ∈ D \ Y, G.Adj q v → v = u := by
    intro v hv hadj
    have hvND : v ∈ neighborhoodIn G D q :=
      (mem_neighborhoodIn G D q v).mpr ⟨(Finset.mem_sdiff.mp hv).1, hadj⟩
    have hvXT := hqNsub hvND
    rcases Finset.mem_union.mp hvXT with hvX | hvU
    · have hvY : v ∈ Y := by
        exact Finset.mem_inter.mpr ⟨hvND, hvX⟩
      exact (Finset.mem_sdiff.mp hv).2 hvY |>.elim
    · exact Finset.mem_singleton.mp hvU
  have hbip : IsBipartiteOn G ((D \ Y) ∪ {q}) :=
    bipartite_add_with_single_neighbor G hS huS hqAdjU
      (by intro h; exact hqD ((Finset.mem_sdiff.mp h).1)) hqOnlyU
  have hcover : ∀ ⦃v⦄, Responsible G D Y v →
      v ∈ ({q} : Finset V) ∨ ∃ z ∈ ({q} : Finset V), G.Adj z v := by
    intro v hv
    have hvY : v ∈ Y := by
      have hvR : v ∈ responsibilityRegion G D Y :=
        (mem_responsibilityRegion G D Y v).mpr hv
      rw [hYreg] at hvR
      exact hvR
    have hvX := hYsubX hvY
    have hvN := (Finset.mem_inter.mp hvY).1
    have hadj : G.Adj q v := (mem_neighborhoodIn G D q v).mp hvN |>.2
    exact Or.inr ⟨q, by simp, hadj⟩
  have hnew : IsBipartiteDominatingSet G ((D \ Y) ∪ {q}) :=
    collective_exchange G hcover hbip
  have hYcard : 2 ≤ Y.card := by
    have hpair : ({x, y} : Finset V) ⊆ Y := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hzx | hzy
      · exact hzx ▸ hxY
      · exact hzy ▸ hyY
    have hcard := Finset.card_le_card hpair
    simpa [hxy] using hcard
  have hcardD : (D \ Y).card + Y.card = D.card :=
    Finset.card_sdiff_add_card_eq_card hYsubD
  have hdisj : Disjoint (D \ Y) ({q} : Finset V) := by
    rw [Finset.disjoint_singleton_right]
    intro hqRet
    exact hqD (Finset.mem_sdiff.mp hqRet).1
  have hcardNew : ((D \ Y) ∪ ({q} : Finset V)).card + Y.card = D.card + 1 := by
    rw [Finset.card_union_of_disjoint hdisj]
    simp only [Finset.card_singleton]
    omega
  have hminimal := hCan.2.1 ((D \ Y) ∪ {q}) hnew
  omega

/-- The exact decomposition in Lemma 8.4. -/
theorem lemma_8_4_compensation_decomposition
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    {w : V}
    {R : Finset V} {u : V}
    (hChosen : ChosenRepairRelation G D w R u) :
    let X := supportX G D w
    let Q := compensationRegion G D X u w
    Q = privateCompensation G D u ∪ sharedCompensation G D X u ∧
      Disjoint (privateCompensation G D u) (sharedCompensation G D X u) ∧
      ∀ q ∈ Q, q ∉ D ∧ G.Adj u q := by
  classical
  let X := supportX G D w
  let Q := compensationRegion G D X u w
  let T := X ∪ {u}
  have hXsub : X ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D w z).mp hz |>.1
  have huB : u ∈ BPart G D := hChosen.2.1
  have huD : u ∈ D := (mem_BPart G D u).mp huB |>.1
  have hDom : Dominates G D := hCan.1.1
  have hqProps : ∀ q ∈ Q,
      q ∉ D ∧ G.Adj q u ∧ neighborhoodIn G D q ⊆ X ∪ {u} ∧
        (neighborhoodIn G D q).Nonempty := by
    intro q hq
    exact compensation_vertex_properties G hDom hXsub huB hq
  have hNoTwo : ∀ q ∈ Q, ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
      ¬ (G.Adj q x ∧ G.Adj q y) := by
    intro q hq x hx y hy hxy
    exact compensation_has_at_most_one_X_neighbor G hCan hXsub huB hq hx hy hxy
  have hQeq : Q = privateCompensation G D u ∪ sharedCompensation G D X u := by
    ext q
    constructor
    · intro hq
      have hp := hqProps q hq
      have hqD := hp.1
      have hqu := hp.2.1
      have hNsub := hp.2.2.1
      by_cases hex : ∃ z ∈ X, G.Adj q z
      · obtain ⟨z, hzX, hqz⟩ := hex
        have hN : neighborhoodIn G D q = {u, z} := by
          apply Finset.ext
          intro d
          constructor
          · intro hd
            have hdT := hNsub hd
            rcases Finset.mem_union.mp hdT with hdX | hdU
            · have hdAdj := (mem_neighborhoodIn G D q d).mp hd |>.2
              have hdEq : d = z ∨ d = u := by
                by_cases hdeq : d = z
                · exact Or.inl hdeq
                · have := hNoTwo q hq d hdX z hzX hdeq
                  exact (this ⟨hdAdj, hqz⟩).elim
              rcases hdEq with hdEq | hdEq
              · subst d
                simp
              · subst d
                simp
            · have hdEq : d = u := Finset.mem_singleton.mp hdU
              subst d
              simp
          · intro hd
            simp only [Finset.mem_insert, Finset.mem_singleton] at hd
            rcases hd with hd | hd
            · subst d
              exact (mem_neighborhoodIn G D q u).mpr ⟨huD, hqu⟩
            · subst d
              have hzD := (mem_ZPart G D z).mp
                ((mem_Z0Part G D z).mp (hXsub hzX) |>.1) |>.1
              exact (mem_neighborhoodIn G D q z).mpr ⟨hzD, hqz⟩
        exact Finset.mem_union.mpr (Or.inr
          ((mem_sharedCompensation G D X u q).mpr ⟨hqD, z, hzX, hN⟩))
      · have hN : neighborhoodIn G D q = {u} := by
          apply Finset.ext
          intro d
          constructor
          · intro hd
            have hdT := hNsub hd
            rcases Finset.mem_union.mp hdT with hdX | hdU
            · have hdAdj := (mem_neighborhoodIn G D q d).mp hd |>.2
              exact (hex ⟨d, hdX, hdAdj⟩).elim
            · exact Finset.mem_singleton.mpr (Finset.mem_singleton.mp hdU)
          · intro hd
            have hdEq := Finset.mem_singleton.mp hd
            subst d
            exact (mem_neighborhoodIn G D q u).mpr ⟨huD, hqu⟩
        exact Finset.mem_union.mpr (Or.inl
          ((mem_privateCompensation G D u q huD).mpr ⟨hqD, hN⟩))
    · intro h
      rcases Finset.mem_union.mp h with hp | hl
      · have hpi := (mem_privateCompensation G D u q huD).mp hp
        have hnotRet : ∀ d ∈ D \ T, ¬ G.Adj d q := by
          intro d hd hAdj
          have hdN := (mem_neighborhoodIn G D q d).mpr
            ⟨(Finset.mem_sdiff.mp hd).1, hAdj.symm⟩
          have hdEq := Finset.mem_singleton.mp (by simpa [hpi.2] using hdN)
          exact (Finset.mem_sdiff.mp hd).2 (hdEq ▸ Finset.mem_union_right X (by simp))
        have hqD := hpi.1
        have hqX : q ∉ X := by
          intro hqX
          exact hqD ((mem_ZPart G D q).mp
            ((mem_Z0Part G D q).mp (hXsub hqX) |>.1) |>.1)
        have hqQ : q ∈ Q := by
          apply Finset.mem_sdiff.mpr
          refine ⟨(mem_responsibilityRegion G D T q).mpr ?_, hqX⟩
          exact ⟨by
            intro hqRet
            exact hqD (Finset.mem_sdiff.mp hqRet).1,
            hnotRet⟩
        exact hqQ
      · have hli := (mem_sharedCompensation G D X u q).mp hl
        have hqD := hli.1
        obtain ⟨z, hzX, hN⟩ := hli.2
        have hqX : q ∉ X := by
          intro hqX
          exact hqD ((mem_ZPart G D q).mp
            ((mem_Z0Part G D q).mp (hXsub hqX) |>.1) |>.1)
        have hnotRet : ∀ d ∈ D \ T, ¬ G.Adj d q := by
          intro d hd hAdj
          have hdN := (mem_neighborhoodIn G D q d).mpr
            ⟨(Finset.mem_sdiff.mp hd).1, hAdj.symm⟩
          have hdEq : d = u ∨ d = z := by
            have hmem : d ∈ ({u, z} : Finset V) := by simpa [hN] using hdN
            simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
          rcases hdEq with heq | heq
          · exact (Finset.mem_sdiff.mp hd).2 (heq ▸ Finset.mem_union_right X (by simp))
          · have hzT : z ∈ T := Finset.mem_union_left _ hzX
            exact (Finset.mem_sdiff.mp hd).2 (heq ▸ hzT)
        have hqQ : q ∈ Q := by
          apply Finset.mem_sdiff.mpr
          refine ⟨(mem_responsibilityRegion G D T q).mpr ?_, hqX⟩
          exact ⟨by
            intro hqRet
            exact hqD (Finset.mem_sdiff.mp hqRet).1,
            hnotRet⟩
        exact hqQ
  have hdisj : Disjoint (privateCompensation G D u)
      (sharedCompensation G D X u) := by
    rw [Finset.disjoint_left]
    intro q hp hl
    have hpN := (mem_privateCompensation G D u q huD).mp hp |>.2
    obtain ⟨_, z, hzX, hLN⟩ := (mem_sharedCompensation G D X u q).mp hl
    have hzInPair : z ∈ ({u, z} : Finset V) := by simp
    have hzN : z ∈ neighborhoodIn G D q := (Finset.ext_iff.mp hLN z).mpr hzInPair
    have hzD := (mem_ZPart G D z).mp
      ((mem_Z0Part G D z).mp (hXsub hzX) |>.1) |>.1
    have hzAdj := (mem_neighborhoodIn G D q z).mp hzN |>.2
    have hzN' := (mem_neighborhoodIn G D q z).mpr ⟨hzD, hzAdj⟩
    have hzU : z = u := Finset.mem_singleton.mp (by simpa [hpN] using hzN')
    exact (Finset.disjoint_left.mp (Z0_disjoint_B G) (hXsub hzX)
      (hzU ▸ huB)).elim
  have hQneighbors : ∀ q ∈ Q, q ∉ D ∧ G.Adj u q := by
    intro q hq
    have hp := hqProps q hq
    exact ⟨hp.1, hp.2.1.symm⟩
  exact ⟨by simpa [Q] using hQeq, hdisj, by simpa [Q] using hQneighbors⟩

/-- An independent set whose only possible edges into a bipartite base meet a
single vertex can be added by assigning it the opposite color. -/
theorem bipartite_add_independent_set_at_vertex
    {S U : Finset V} {w : V}
    (hS : IsBipartiteOn G S) (hwS : w ∈ S)
    (hU : Independent G U) (hwU : w ∉ U)
    (hdisj : Disjoint S U)
    (hboundary : ∀ ⦃u v⦄, u ∈ U → v ∈ S → G.Adj u v → v = w) :
    IsBipartiteOn G (S ∪ U) := by
  classical
  rcases hS with ⟨c, hc⟩
  refine ⟨fun v => if v ∈ U then !c w else c v, ?_⟩
  intro a b ha hb hab
  rcases Finset.mem_union.mp ha with haS | haU
  · rcases Finset.mem_union.mp hb with hbS | hbU
    · have haNotU : a ∉ U := by
        intro h
        exact (Finset.disjoint_left.mp hdisj haS h).elim
      have hbNotU : b ∉ U := by
        intro h
        exact (Finset.disjoint_left.mp hdisj hbS h).elim
      simpa [haNotU, hbNotU] using hc haS hbS hab
    · have hvEq : a = w := hboundary hbU haS hab.symm
      subst a
      have haNotU : w ∉ U := hwU
      simp [haNotU, hbU]
  · rcases Finset.mem_union.mp hb with hbS | hbU
    · have hvEq : b = w := hboundary haU hbS hab
      subst b
      have hbNotU : w ∉ U := hwU
      simp [haU, hbNotU]
    · exact (hU haU hbU hab).elim

/-- Lemma 8.5: the induced compensation graph has an independent set of size
at least the support size. The proof builds the paper's replacement set and
uses only the explicitly chosen repair pair. -/
theorem lemma_8_5_independent_set_lower_bound
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {w : V} (hw : w ∈ SPart G D)
    (ha : externalCharge G D w < 0)
    {R : Finset V} {u : V}
    (hChosen : ChosenRepairRelation G D w R u) :
    ∃ J : Finset V,
      J ⊆ compensationRegion G D (supportX G D w) u w ∧
      Independent G J ∧ kCharge G D w ≤ J.card := by
  classical
  let X := supportX G D w
  let Q := compensationRegion G D X u w
  let T := X ∪ {u}
  have hXsub : X ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D w z).mp hz |>.1
  have huB : u ∈ BPart G D := hChosen.2.1
  have huD : u ∈ D := (mem_BPart G D u).mp huB |>.1
  have hwu : G.Adj w u := hChosen.2.2.1
  have hClass := lemma_7_2_negative_charge_classification G hCan hmax hw ha
  have hk : 3 ≤ kCharge G D w := by
    rcases hClass with ⟨hk, _⟩ | ⟨hk, _⟩ | ⟨hk, _⟩ <;> omega
  have hbeta : 2 ≤ betaCharge G D w := by
    rcases hClass with ⟨_, hβ⟩ | ⟨_, hβ⟩ | ⟨_, hβ⟩ <;> omega
  have hDom : Dominates G D := hCan.1.1
  have hProps : ∀ q ∈ Q,
      q ∉ D ∧ G.Adj q u ∧ neighborhoodIn G D q ⊆ X ∪ {u} ∧
        (neighborhoodIn G D q).Nonempty := by
    intro q hq
    exact compensation_vertex_properties G hDom hXsub huB hq
  obtain ⟨J, hJQ, hJind, hJmax⟩ := exists_maximal_independent_subset G Q
  have hJQ' : J ⊆ compensationRegion G D (supportX G D w) u w := by
    simpa [Q, X] using hJQ
  refine ⟨J, hJQ', hJind, ?_⟩
  by_contra hsmall
  have hJsmall : J.card < kCharge G D w := by omega
  have hsupportCard : 2 ≤ (supportB G D w).card := by
    rw [supportB_card]
    exact hbeta
  have huSupport : u ∈ supportB G D w := by
    change u ∈ (BPart G D).filter (fun b => G.Adj w b)
    exact Finset.mem_filter.mpr ⟨huB, hwu⟩
  have hErasePos : 0 < ((supportB G D w).erase u).card := by
    rw [Finset.card_erase_of_mem huSupport]
    omega
  obtain ⟨v, hvErase⟩ := Finset.card_pos.mp hErasePos
  have hvNeU : v ≠ u := (Finset.mem_erase.mp hvErase).1
  have hvSupport : v ∈ supportB G D w := (Finset.mem_erase.mp hvErase).2
  have hvB : v ∈ BPart G D := (Finset.mem_filter.mp hvSupport).1
  have hvw : G.Adj w v := (Finset.mem_filter.mp hvSupport).2
  have hvNotX : v ∉ X := by
    intro hvX
    exact (Finset.disjoint_left.mp (Z0_disjoint_B G) (hXsub hvX) hvB).elim
  have hvRet : v ∈ D \ T := by
    refine Finset.mem_sdiff.mpr ⟨(mem_BPart G D v).mp hvB |>.1, ?_⟩
    intro hvT
    rcases Finset.mem_union.mp hvT with hvX | hvU
    · exact hvNotX hvX
    · exact hvNeU (Finset.mem_singleton.mp hvU)
  have hwNotR : w ∉ responsibilityRegion G D T := by
    intro hwR
    exact ((mem_responsibilityRegion G D T w).mp hwR).2 v hvRet hvw.symm
  have hwNotQ : w ∉ Q := by
    intro hwQ
    exact hwNotR (Finset.mem_sdiff.mp hwQ).1
  have hwNotD : w ∉ D := (mem_WBPart G D w).mp
    ((mem_SPart G D w).mp hw |>.1) |>.1
  let K := D \ T
  let S := (BPart G D).erase u ∪ {w}
  let Zret := ZPart G D ∩ K
  let U := Zret ∪ J
  have mem_Zret (z : V) : z ∈ Zret ↔ z ∈ ZPart G D ∧ z ∈ K := by
    simp [Zret]
  have hBase : IsBipartiteOn G S := hChosen.2.2.2
  have hwS : w ∈ S := by simp [S]
  have hwU : w ∉ U := by
    intro hwU
    rcases Finset.mem_union.mp hwU with hwZ | hwJ
    · have hwZ' : w ∈ ZPart G D ∧ w ∈ K := (mem_Zret w).mp hwZ
      exact hwNotD ((mem_ZPart G D w).mp hwZ'.1 |>.1)
    · exact hwNotQ (hJQ hwJ)
  have hZretD : Zret ⊆ D := by
    intro z hz
    exact (mem_ZPart G D z).mp (mem_Zret z |>.mp hz |>.1) |>.1
  have hZretK : Zret ⊆ K := Finset.inter_subset_right
  have hJoutside : ∀ q ∈ J, q ∉ D ∧ q ∈ responsibilityRegion G D T := by
    intro q hqJ
    have hqQ := hJQ hqJ
    have hqProps := hProps q hqQ
    exact ⟨hqProps.1, (Finset.mem_sdiff.mp hqQ).1⟩
  have hUind : Independent G U := by
    intro a b ha hb hab
    rcases Finset.mem_union.mp ha with haZ | haJ
    · rcases Finset.mem_union.mp hb with hbZ | hbJ
      · have haZpart := (mem_Zret a).mp haZ |>.1
        exact selected_Z_isolated G haZpart (hZretD hbZ) hab
      · have hbinfo := hJoutside b hbJ
        exact ((mem_responsibilityRegion G D T b).mp hbinfo.2).2 a
          (by simpa [K] using (mem_Zret a).mp haZ |>.2) hab
    · rcases Finset.mem_union.mp hb with hbZ | hbJ
      · have hainfo := hJoutside a haJ
        exact ((mem_responsibilityRegion G D T a).mp hainfo.2).2 b
          (by simpa [K] using (mem_Zret b).mp hbZ |>.2) hab.symm
      · exact hJind haJ hbJ hab
  have hBoundary : ∀ ⦃a b⦄, a ∈ U → b ∈ S → G.Adj a b → b = w := by
    intro a b ha hb hab
    rcases Finset.mem_union.mp ha with haZ | haJ
    · rcases Finset.mem_union.mp hb with hbB | hbW
      · have hbB' : b ∈ BPart G D := Finset.mem_erase.mp hbB |>.2
        exact (selected_Z_isolated G (mem_Zret a |>.mp haZ |>.1)
          (mem_BPart G D b |>.mp hbB' |>.1) hab).elim
      · exact Finset.mem_singleton.mp hbW
    · have haInfo := hJoutside a haJ
      rcases Finset.mem_union.mp hb with hbB | hbW
      · have hbRet : b ∈ K := by
          refine Finset.mem_sdiff.mpr ⟨(mem_BPart G D b |>.mp
            (Finset.mem_erase.mp hbB |>.2)).1, ?_⟩
          intro hbT
          rcases Finset.mem_union.mp hbT with hbX | hbU
          · exact (Finset.disjoint_left.mp (Z0_disjoint_B G) (hXsub hbX)
              (Finset.mem_erase.mp hbB |>.2)).elim
          · exact (Finset.mem_erase.mp hbB).1
              (Finset.mem_singleton.mp hbU)
        exact False.elim (((mem_responsibilityRegion G D T a).mp haInfo.2).2
          b hbRet hab.symm)
      · exact Finset.mem_singleton.mp hbW
  have hSdisjU : Disjoint S U := by
    rw [Finset.disjoint_left]
    intro z hzS hzU
    rcases Finset.mem_union.mp hzS with hzB | hzw
    · have hzB' := (Finset.mem_erase.mp hzB).2
      rcases Finset.mem_union.mp hzU with hzZ | hzJ
      · exact (Finset.disjoint_left.mp (ZPart_disjoint_BPart G D)
          ((mem_Zret z).mp hzZ |>.1) hzB').elim
      · exact (hJoutside z hzJ).1 ((mem_BPart G D z).mp hzB' |>.1)
    · have hzEq : z = w := Finset.mem_singleton.mp hzw
      subst z
      rcases Finset.mem_union.mp hzU with hzZ | hzJ
      · exact hwNotD ((mem_ZPart G D w).mp ((mem_Zret w).mp hzZ |>.1) |>.1)
      · exact hwNotQ (hJQ hzJ)
  have hbipExpanded : IsBipartiteOn G (S ∪ U) :=
    bipartite_add_independent_set_at_vertex G hBase (by simp [S]) hUind hwU
      hSdisjU hBoundary
  have hDnewEq : (D \ T ∪ {w}) ∪ J = S ∪ U := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_union.mp hz with hzK | hzJ
      · rcases Finset.mem_union.mp hzK with hzK | hzw
        · by_cases hzZ : z ∈ ZPart G D
          · exact Finset.mem_union_right S (Finset.mem_union_left J
              (Finset.mem_inter.mpr ⟨hzZ, hzK⟩))
          · have hzB : z ∈ BPart G D := by
              rw [mem_BPart]
              exact ⟨(Finset.mem_sdiff.mp hzK).1, hzZ⟩
            have hzNe : z ≠ u := by
              intro hEq
              subst z
              exact (Finset.mem_sdiff.mp hzK).2
                (Finset.mem_union_right X (by simp))
            exact Finset.mem_union_left U (Finset.mem_union_left _
              (Finset.mem_erase.mpr ⟨hzNe, hzB⟩))
        · exact Finset.mem_union_left U (Finset.mem_union_right _ (by simpa using hzw))
      · exact Finset.mem_union_right S (Finset.mem_union_right Zret hzJ)
    · intro hz
      rcases Finset.mem_union.mp hz with hzS | hzU
      · rcases Finset.mem_union.mp hzS with hzB | hzw
        · have hzB' := Finset.mem_erase.mp hzB |>.2
          exact Finset.mem_union_left J (Finset.mem_union_left _
            (Finset.mem_sdiff.mpr ⟨(mem_BPart G D z).mp hzB' |>.1, by
              intro hzT
              rcases Finset.mem_union.mp hzT with hzX | hzU
              · exact (Finset.disjoint_left.mp (Z0_disjoint_B G) (hXsub hzX) hzB').elim
              · exact (Finset.mem_erase.mp hzB).1 (Finset.mem_singleton.mp hzU)⟩))
        · exact Finset.mem_union_left J (Finset.mem_union_right _ hzw)
      · rcases Finset.mem_union.mp hzU with hzZ | hzJ
        · exact Finset.mem_union_left J (Finset.mem_union_left _
            (by simpa [K] using (mem_Zret z).mp hzZ |>.2))
        · exact Finset.mem_union_right _ hzJ
  have hDnewEq' : K ∪ ({w} ∪ J) = S ∪ U := by
    calc
      K ∪ ({w} ∪ J) = (K ∪ {w}) ∪ J := (Finset.union_assoc K {w} J).symm
      _ = S ∪ U := by simpa [K] using hDnewEq
  have hbipNew : IsBipartiteOn G (K ∪ ({w} ∪ J)) := by
    rw [hDnewEq']
    exact hbipExpanded
  have hRegionX : responsibilityRegion G D X = X :=
    lemma_5_1_responsibility_eq G hCan.1 hXsub
  have hCover : ∀ ⦃v⦄, Responsible G D T v →
      v ∈ ({w} ∪ J) ∨ ∃ z ∈ ({w} ∪ J), G.Adj z v := by
    intro z hz
    have hzR : z ∈ responsibilityRegion G D T :=
      (mem_responsibilityRegion G D T z).mpr hz
    by_cases hzX : z ∈ X
    · have hzw : G.Adj w z := (mem_supportX G D w z).mp hzX |>.2
      exact Or.inr ⟨w, Finset.mem_union_left _ (by simp), hzw⟩
    · have hzQ : z ∈ Q := Finset.mem_sdiff.mpr ⟨hzR, hzX⟩
      by_cases hzJ : z ∈ J
      · exact Or.inl (Finset.mem_union_right _ hzJ)
      · obtain ⟨j, hj, hjz⟩ := hJmax hzQ hzJ
        exact Or.inr ⟨j, Finset.mem_union_right _ hj, hjz⟩
  have hnew : IsBipartiteDominatingSet G (K ∪ ({w} ∪ J)) :=
    collective_exchange G hCover hbipNew
  have hXsubsetD : X ⊆ D := by
    intro z hz
    exact (mem_ZPart G D z).mp ((mem_Z0Part G D z).mp (hXsub hz) |>.1) |>.1
  have hTsubD : T ⊆ D := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzX | hzU
    · exact hXsubsetD hzX
    · have hzEq : z = u := Finset.mem_singleton.mp hzU
      simpa [hzEq] using huD
  have hTDcard : T.card = kCharge G D w + 1 := by
    have hdisj : Disjoint X ({u} : Finset V) := by
      rw [Finset.disjoint_singleton_right]
      intro huX
      exact (Finset.disjoint_left.mp (Z0_disjoint_B G) (hXsub huX) huB).elim
    rw [show T = X ∪ ({u} : Finset V) by rfl, Finset.card_union_of_disjoint hdisj]
    have hXcard' : X.card = kCharge G D w := by
      simpa [X] using supportX_card G D w
    simp [hXcard']
  have hKcard : K.card + T.card = D.card := Finset.card_sdiff_add_card_eq_card hTsubD
  have hwNotD : w ∉ D := (mem_WBPart G D w).mp
    ((mem_SPart G D w).mp hw |>.1) |>.1
  have hKdisjW : Disjoint K ({w} : Finset V) := by
    rw [Finset.disjoint_singleton_right]
    intro hwK
    exact hwNotD (Finset.mem_sdiff.mp hwK).1
  have hKdisjJ : Disjoint K J := by
    rw [Finset.disjoint_left]
    intro z hzK hzJ
    have hzQ := hJQ hzJ
    exact ((mem_responsibilityRegion G D T z).mp
      (Finset.mem_sdiff.mp hzQ).1).1 hzK
  have hWdisjJ : Disjoint ({w} : Finset V) J := by
    rw [Finset.disjoint_singleton_left]
    intro hwJ
    exact hwNotQ (hJQ hwJ)
  have hKWdisjJ : Disjoint (K ∪ {w}) J := by
    rw [Finset.disjoint_left]
    intro z hz hzJ
    rcases Finset.mem_union.mp hz with hzK | hzw
    · exact (Finset.disjoint_left.mp hKdisjJ hzK hzJ).elim
    · exact (Finset.disjoint_left.mp hWdisjJ hzw hzJ).elim
  have hNewcard : ((K ∪ {w}) ∪ J).card + T.card = D.card + 1 + J.card := by
    rw [Finset.card_union_of_disjoint hKWdisjJ,
      Finset.card_union_of_disjoint hKdisjW]
    simp only [Finset.card_singleton]
    omega
  have hNewcard' : (K ∪ ({w} ∪ J)).card + T.card = D.card + 1 + J.card := by
    simpa [Finset.union_assoc] using hNewcard
  have hmin := hCan.2.1 (K ∪ ({w} ∪ J)) hnew
  have hsmaller : (K ∪ ({w} ∪ J)).card < D.card := by
    rw [← hKcard, hTDcard] at hNewcard'
    omega
  exact (Nat.not_lt_of_ge hmin) hsmaller

/-- The numerical compensation bound (12): the private surplus at `u` and
the shared compensation vertices together pay for the support size beyond
the two private neighbors. -/
theorem lemma_8_5_compensation_lower_bound
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {w : V} (hw : w ∈ SPart G D)
    (ha : externalCharge G D w < 0)
    {R : Finset V} {u : V}
    (hChosen : ChosenRepairRelation G D w R u) :
    kCharge G D w - 2 ≤
      xCharge G D u + (sharedCompensation G D (supportX G D w) u).card := by
  classical
  have hInd := lemma_8_5_independent_set_lower_bound G hCan hmax hw ha hChosen
  obtain ⟨J, hJQ, hJind, hJlarge⟩ := hInd
  have hDec := lemma_8_4_compensation_decomposition G hCan hChosen
  have huB := hChosen.2.1
  have hPrivate := private_card_eq_two_add_x G hCan huB
  have hQcard : kCharge G D w ≤
      (compensationRegion G D (supportX G D w) u w).card := by
    exact hJlarge.trans (Finset.card_le_card hJQ)
  have hsum : kCharge G D w ≤
      (privateCompensation G D u).card +
        (sharedCompensation G D (supportX G D w) u).card := by
    rw [hDec.1, Finset.card_union_of_disjoint hDec.2.1] at hQcard
    exact hQcard
  have hPrivate' : (privateCompensation G D u).card = 2 + xCharge G D u := by
    simpa [privateCompensation] using hPrivate
  rw [hPrivate'] at hsum
  omega

end C6BipartiteDomination

