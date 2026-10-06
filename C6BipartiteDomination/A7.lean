/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import C6BipartiteDomination.A6

/-! # A7: negative-charge support classification -/

namespace C6BipartiteDomination

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

/-- The `Z₀`-neighbors supported by an external vertex. -/
noncomputable def supportX (D : Finset V) (w : V) : Finset V := by
  classical
  exact (Z0Part G D).filter fun z => G.Adj w z

noncomputable def supportB (D : Finset V) (w : V) : Finset V := by
  classical
  exact (BPart G D).filter fun b => G.Adj w b

theorem mem_supportX (D : Finset V) (w z : V) :
    z ∈ supportX G D w ↔ z ∈ Z0Part G D ∧ G.Adj w z := by
  classical
  simp [supportX]

theorem supportX_card (D : Finset V) (w : V) :
    (supportX G D w).card = kCharge G D w := by
  classical
  simp [supportX, kCharge, degreeTo, G.adj_comm]

theorem supportB_card (D : Finset V) (w : V) :
    (supportB G D w).card = betaCharge G D w := by
  rfl

/-- A vertex outside `D` which is in `W_B` has a `B`-neighbor. -/
theorem beta_pos_of_mem_SPart {D : Finset V} {w : V}
    (hw : w ∈ SPart G D) : 1 ≤ betaCharge G D w := by
  classical
  have hwWB := (mem_SPart G D w).mp hw |>.1
  have hw0 := (mem_WBPart G D w).mp hwWB |>.2
  unfold betaCharge degreeTo
  have hneigh : ∃ b ∈ BPart G D, G.Adj w b := by
    by_contra h
    apply hw0
    rw [mem_W0Part]
    refine ⟨(mem_WBPart G D w).mp hwWB |>.1, ?_⟩
    intro b hb hbw
    exact h ⟨b, hb, hbw.symm⟩
  rcases hneigh with ⟨b, hb, hwb⟩
  have hpos : 0 < ((BPart G D).filter (fun u => G.Adj w u)).card :=
    Finset.card_pos.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, hwb⟩⟩
  omega

theorem selected_Z_isolated {D : Finset V} {z v : V}
    (hz : z ∈ ZPart G D) (hv : v ∈ D) : ¬ G.Adj z v :=
  (mem_ZPart G D z).mp hz |>.2 v hv

theorem Z0_disjoint_B {D : Finset V} :
    Disjoint (Z0Part G D) (BPart G D) := by
  rw [Finset.disjoint_left]
  intro z hz0 hb
  have hz := (mem_Z0Part G D z).mp hz0 |>.1
  exact (mem_BPart G D z).mp hb |>.2 hz

/-- A two-colouring of `B ∪ {w}` extends over the retained isolated selected
vertices after replacing a subset of `Z₀` by `w`. -/
theorem bipartite_replacement_of_base
    {D X : Finset V} {w : V}
    (hX : X ⊆ ZPart G D) (hwD : w ∉ D)
    (hbase : IsBipartiteOn G (BPart G D ∪ {w})) :
    IsBipartiteOn G ((D \ X) ∪ {w}) := by
  classical
  rcases hbase with ⟨c, hc⟩
  have hwZ : w ∉ ZPart G D := by
    intro hz
    exact hwD ((mem_ZPart G D w).mp hz).1
  refine ⟨fun v => if v ∈ ZPart G D then !(c w) else c v, ?_⟩
  intro u v hu hv hadj
  have hu' : u ∈ D \ X ∨ u = w := by
    simpa only [Finset.mem_union, Finset.mem_singleton] using hu
  have hv' : v ∈ D \ X ∨ v = w := by
    simpa only [Finset.mem_union, Finset.mem_singleton] using hv
  rcases hu' with huK | huW
  · rcases hv' with hvK | hvW
    · have huD := (Finset.mem_sdiff.mp huK).1
      have hvD := (Finset.mem_sdiff.mp hvK).1
      by_cases huZ : u ∈ ZPart G D
      · exact (selected_Z_isolated G huZ hvD hadj).elim
      · by_cases hvZ : v ∈ ZPart G D
        · exact (selected_Z_isolated G hvZ huD hadj.symm).elim
        · have huB : u ∈ BPart G D := by
            rw [mem_BPart]
            exact ⟨huD, huZ⟩
          have hvB : v ∈ BPart G D := by
            rw [mem_BPart]
            exact ⟨hvD, hvZ⟩
          exact (hc (Finset.mem_union_left _ huB)
            (Finset.mem_union_left _ hvB) hadj)
            |> (fun h => by simpa [huZ, hvZ] using h)
    · subst v
      have huD := (Finset.mem_sdiff.mp huK).1
      by_cases huZ : u ∈ ZPart G D
      · simpa [huZ, hwZ]
      · have huB : u ∈ BPart G D := by
          rw [mem_BPart]
          exact ⟨huD, huZ⟩
        have hbase' := hc (Finset.mem_union_left _ huB)
          (Finset.mem_union_right _ (by simp)) hadj
        simpa [huZ, hwZ] using hbase'
  · subst u
    rcases hv' with hvK | hvW
    · have hvD := (Finset.mem_sdiff.mp hvK).1
      by_cases hvZ : v ∈ ZPart G D
      · have hflip : (if v ∈ ZPart G D then !(c w) else c v) ≠ c w := by
          simp [hvZ, hwZ]
        simpa [hvZ, hwZ] using hflip
      · have hvB : v ∈ BPart G D := by
          rw [mem_BPart]
          exact ⟨hvD, hvZ⟩
        have hbase' := hc (Finset.mem_union_right _ (by simp))
          (Finset.mem_union_left _ hvB) hadj
        simpa [hvZ, hwZ] using hbase'
    · subst v
      exact (G.irrefl hadj).elim

/-- With at most one `B`-neighbor, adding `w` to the bipartite graph on `B`
preserves bipartiteness. -/
theorem bipartite_base_of_beta_eq_one
    {D : Finset V} {w : V}
    (hD : IsBipartiteOn G D)
    (hwD : w ∉ D)
    (hβ : betaCharge G D w = 1) :
    IsBipartiteOn G (BPart G D ∪ {w}) := by
  classical
  have hB : IsBipartiteOn G (BPart G D) :=
    bipartiteOn_subset G (Finset.sdiff_subset) hD
  rcases hB with ⟨c, hc⟩
  have hsupp : (supportB G D w).card = 1 := by
    rw [supportB_card]
    exact hβ
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hsupp
  have hbB : b ∈ BPart G D := by
    have : b ∈ supportB G D w := by rw [hb]; simp
    exact (Finset.mem_filter.mp this).1
  have hbNeW : b ≠ w := by
    intro heq
    exact hwD (heq ▸ (mem_BPart G D b).mp hbB |>.1)
  refine ⟨fun v => if v = w then !(c b) else c v, ?_⟩
  intro u v hu hv hadj
  rcases Finset.mem_union.mp hu with huB | huW
  · rcases Finset.mem_union.mp hv with hvB | hvW
    · have huNe : u ≠ w := by
        intro heq
        exact hwD (heq ▸ (mem_BPart G D u).mp huB |>.1)
      have hvNe : v ≠ w := by
        intro heq
        exact hwD (heq ▸ (mem_BPart G D v).mp hvB |>.1)
      simpa [huNe, hvNe] using hc huB hvB hadj
    · have hvEq : v = w := Finset.mem_singleton.mp hvW
      subst v
      have huSupp : u ∈ supportB G D w := by
        apply Finset.mem_filter.mpr
        refine ⟨huB, ?_⟩
        exact hadj.symm
      have huEq : u = b := by
        rw [hb] at huSupp
        simpa using huSupp
      subst u
      simp [hbNeW]
  · have huEq : u = w := Finset.mem_singleton.mp huW
    subst u
    rcases Finset.mem_union.mp hv with hvB | hvW
    · have hvSupp : v ∈ supportB G D w := by
        apply Finset.mem_filter.mpr
        refine ⟨hvB, ?_⟩
        exact hadj
      have hvEq : v = b := by
        rw [hb] at hvSupp
        simpa using hvSupp
      subst v
      simp [hbNeW]
    · have hvEq : v = w := Finset.mem_singleton.mp hvW
      subst v
      exact (G.irrefl hadj).elim

/-- Lemma 7.1: two or more `Z₀`-neighbors of a vertex in `S` would permit a
strictly smaller bipartite dominating set. -/
theorem lemma_7_1_odd_cycle
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    {w : V} (hw : w ∈ SPart G D)
    (hk : 2 ≤ kCharge G D w) :
    ¬ IsBipartiteOn G (BPart G D ∪ {w}) := by
  classical
  intro hbase
  let X := supportX G D w
  let E := (D \ X) ∪ {w}
  have hXZ0 : X ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D w z).mp hz |>.1
  have hXZ : X ⊆ ZPart G D := by
    intro z hz
    exact (mem_Z0Part G D z).mp (hXZ0 hz) |>.1
  have hRegion := lemma_5_1_responsibility_eq G hCan.1 hXZ0
  have hCover : ∀ ⦃v⦄, Responsible G D X v →
      v ∈ ({w} : Finset V) ∨ ∃ y ∈ ({w} : Finset V), G.Adj y v := by
    intro v hv
    have hvX : v ∈ X := by
      have hvR : v ∈ responsibilityRegion G D X :=
        (mem_responsibilityRegion G D X v).2 hv
      rw [hRegion] at hvR
      exact hvR
    rcases (mem_supportX G D w v).mp hvX with ⟨_, hvw⟩
    by_cases heq : v = w
    · exact Or.inl (by simpa [heq])
    · exact Or.inr ⟨w, by simp, hvw⟩
  have hbip : IsBipartiteOn G E := by
    have hwNotD : w ∉ D := by
      have hwWB := (mem_SPart G D w).mp hw |>.1
      exact (mem_WBPart G D w).mp hwWB |>.1
    exact bipartite_replacement_of_base G hXZ hwNotD hbase
  have hNew : IsBipartiteDominatingSet G E := by
    have := collective_exchange G hCover hbip
    simpa [E] using this
  have hMin := hCan.2.1 E hNew
  have hXsubD : X ⊆ D := by
    intro z hz
    exact (mem_ZPart G D z).mp (hXZ hz) |>.1
  have hXcard : X.card = kCharge G D w := supportX_card G D w
  have hDcard : (D \ X).card + X.card = D.card :=
    Finset.card_sdiff_add_card_eq_card hXsubD
  have hEcard : E.card + X.card = D.card + 1 := by
    have hwNotD : w ∉ D := by
      have := (mem_SPart G D w).mp hw |>.1
      exact (mem_WBPart G D w).mp this |>.1
    have hdisj : Disjoint (D \ X) ({w} : Finset V) := by
      rw [Finset.disjoint_singleton_right]
      intro h
      exact hwNotD ((Finset.mem_sdiff.mp h).1)
    rw [show E = (D \ X) ∪ ({w} : Finset V) by rfl]
    rw [Finset.card_union_of_disjoint hdisj]
    simp only [Finset.card_singleton]
    have hdiff := hDcard
    omega
  rw [hXcard] at hEcard
  rw [hXcard] at hDcard
  have hsmall : kCharge G D w < 2 := by omega
  exact (Nat.not_lt_of_ge hk) hsmall

theorem beta_ge_two_of_k_ge_two
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    {w : V} (hw : w ∈ SPart G D)
    (hk : 2 ≤ kCharge G D w) :
    2 ≤ betaCharge G D w := by
  by_contra h
  have hβ : betaCharge G D w = 1 := by
    have hpos := beta_pos_of_mem_SPart G hw
    omega
  have hwD : w ∉ D := by
    have hwWB := (mem_SPart G D w).mp hw |>.1
    exact (mem_WBPart G D w).mp hwWB |>.1
  have hbase := bipartite_base_of_beta_eq_one G hCan.1.2 hwD hβ
  exact (lemma_7_1_odd_cycle G hCan hw hk) hbase

theorem support_union_card_le_degree
    {D : Finset V} {w : V} :
    kCharge G D w + betaCharge G D w ≤ degreeTo G Finset.univ w := by
  classical
  have hdisj : Disjoint (supportX G D w) (supportB G D w) := by
    rw [Finset.disjoint_left]
    intro z hzX hzB
    have hsep := Finset.disjoint_left.mp (Z0_disjoint_B G (D := D))
    exact hsep ((mem_supportX G D w z).mp hzX |>.1)
      ((Finset.mem_filter.mp hzB).1)
  have hsub : supportX G D w ∪ supportB G D w ⊆
      Finset.univ.filter (fun z => G.Adj w z) := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzX | hzB
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (mem_supportX G D w z).mp hzX |>.2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hzB).2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, supportX_card, supportB_card] at hcard
  simpa [degreeTo] using hcard

/-- Lemma 7.2: under the maximum-degree-six hypothesis, a negative external
charge has exactly one of the three paper-listed `(k, β)` types. -/
theorem lemma_7_2_negative_charge_classification
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {w : V} (hw : w ∈ SPart G D)
    (ha : externalCharge G D w < 0) :
    (kCharge G D w = 3 ∧ betaCharge G D w = 2) ∨
    (kCharge G D w = 3 ∧ betaCharge G D w = 3) ∨
    (kCharge G D w = 4 ∧ betaCharge G D w = 2) := by
  have hβpos := beta_pos_of_mem_SPart G hw
  have hk : 2 ≤ kCharge G D w := by
    by_contra h
    have hkle : kCharge G D w ≤ 1 := by omega
    unfold externalCharge at ha
    push_cast at ha
    omega
  have hβtwo := beta_ge_two_of_k_ge_two G hCan hw hk
  have hsum := support_union_card_le_degree G (D := D) (w := w)
  have hbound : kCharge G D w + betaCharge G D w ≤ 6 := by
    exact hsum.trans (hmax w)
  have hneg : 8 + 3 * betaCharge G D w < 7 * kCharge G D w := by
    unfold externalCharge at ha
    push_cast at ha
    omega
  omega

theorem lemma_7_2_charge_values
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {w : V} (hw : w ∈ SPart G D)
    (ha : externalCharge G D w < 0) :
    (kCharge G D w = 3 ∧ betaCharge G D w = 2 ∧ externalCharge G D w = -7) ∨
    (kCharge G D w = 3 ∧ betaCharge G D w = 3 ∧ externalCharge G D w = -4) ∨
    (kCharge G D w = 4 ∧ betaCharge G D w = 2 ∧ externalCharge G D w = -14) := by
  rcases lemma_7_2_negative_charge_classification G hCan hmax hw ha with h | h | h
  · left
    rcases h with ⟨hk, hβ⟩
    simp [externalCharge, hk, hβ]
  · right; left
    rcases h with ⟨hk, hβ⟩
    simp [externalCharge, hk, hβ]
  · right; right
    rcases h with ⟨hk, hβ⟩
    simp [externalCharge, hk, hβ]

end C6BipartiteDomination


