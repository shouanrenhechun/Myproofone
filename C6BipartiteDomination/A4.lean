/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import C6BipartiteDomination.A3

/-! # A4: canonical two-level optimum and Lemma 3.1 -/

namespace C6BipartiteDomination

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

/-- Ordered adjacency pairs induced by `D`; this counts each undirected edge
twice, which is sufficient for the secondary minimization. -/
noncomputable def internalArcs (D : Finset V) : Finset (V × V) := by
  classical
  exact Finset.univ.filter fun p => p.1 ∈ D ∧ p.2 ∈ D ∧ G.Adj p.1 p.2

theorem mem_internalArcs (D : Finset V) (u v : V) :
    (u, v) ∈ internalArcs G D ↔ u ∈ D ∧ v ∈ D ∧ G.Adj u v := by
  classical
  simp [internalArcs]

/-- A canonical optimum first minimizes cardinality, then the number of
internal adjacency pairs. -/
def CanonicalTwoLevelOptimum (D : Finset V) : Prop :=
  IsBipartiteDominatingSet G D ∧
    (∀ E, IsBipartiteDominatingSet G E → D.card ≤ E.card) ∧
    (∀ E, IsBipartiteDominatingSet G E → E.card = D.card →
      (internalArcs G D).card ≤ (internalArcs G E).card)

/-- Every finite graph has an independent dominating set, hence the family of
bipartite dominating sets is nonempty and admits the two-level optimum. -/
theorem exists_canonical_two_level_optimum :
    ∃ D : Finset V, CanonicalTwoLevelOptimum G D := by
  classical
  obtain ⟨I, hIall, hIind, hImax⟩ := exists_maximal_independent_subset G Finset.univ
  have hIdom : Dominates G I := by
    intro v hv
    have hvAll : v ∈ (Finset.univ : Finset V) := Finset.mem_univ _
    exact hImax hvAll hv
  have hIbip : IsBipartiteOn G I := by
    refine ⟨fun _ => false, ?_⟩
    intro u v hu hv hadj
    exact (hIind hu hv hadj).elim
  let feasible := Finset.univ.powerset.filter (IsBipartiteDominatingSet G)
  have hIfeas : I ∈ feasible := by
    simp only [feasible, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.subset_univ I, ⟨hIdom, hIbip⟩⟩
  obtain ⟨D₀, hD₀mem, hD₀min⟩ :=
    Finset.exists_min_image feasible Finset.card ⟨I, hIfeas⟩
  let cooptimal := feasible.filter fun E => E.card = D₀.card
  have hD₀co : D₀ ∈ cooptimal := by
    simp [cooptimal, hD₀mem]
  obtain ⟨D, hDmem, hDarcmin⟩ :=
    Finset.exists_min_image cooptimal (fun E => (internalArcs G E).card) ⟨D₀, hD₀co⟩
  have hDfeas : D ∈ feasible := (Finset.mem_filter.mp hDmem).1
  have hDprop : IsBipartiteDominatingSet G D := (Finset.mem_filter.mp hDfeas).2
  have hDcard : D.card = D₀.card := (Finset.mem_filter.mp hDmem).2
  refine ⟨D, hDprop, ?_, ?_⟩
  · intro E hE
    have hEmem : E ∈ feasible := by simp [feasible, hE]
    rw [hDcard]
    exact hD₀min E hEmem
  · intro E hE hEq
    have hEmem : E ∈ feasible := by simp [feasible, hE]
    have hEco : E ∈ cooptimal := by
      simp [cooptimal, hEmem, hEq, (Finset.mem_filter.mp hDmem).2]
    exact hDarcmin E hEco

/-- `b` is non-isolated in the selected induced graph. -/
def NonisolatedIn (D : Finset V) (b : V) : Prop :=
  b ∈ D ∧ ∃ u ∈ D, G.Adj b u

/-- External private neighbors of `b`: their open neighborhood within `D` is
exactly `{b}`. -/
noncomputable def privateExternalNeighbors (D : Finset V) (b : V) : Finset V := by
  classical
  exact (Finset.univ \ D).filter fun w => ∀ u ∈ D, G.Adj u w ↔ u = b

theorem mem_privateExternalNeighbors (D : Finset V) (b w : V) :
    w ∈ privateExternalNeighbors G D b ↔
      w ∉ D ∧ ∀ u ∈ D, G.Adj u w ↔ u = b := by
  classical
  simp [privateExternalNeighbors]

theorem bipartiteOn_subset {D E : Finset V} (hE : E ⊆ D)
    (hD : IsBipartiteOn G D) : IsBipartiteOn G E := by
  rcases hD with ⟨c, hc⟩
  exact ⟨c, fun {u v} hu hv hAdj => hc (hE hu) (hE hv) hAdj⟩

theorem empty_privateExternalNeighbors_contradiction
    {D : Finset V} {b : V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hb : NonisolatedIn G D b)
    (hP : privateExternalNeighbors G D b = ∅) : False := by
  classical
  let E := D.erase b
  have hED : E ⊆ D := Finset.erase_subset b D
  have hEd : Dominates G E := by
    intro v hvE
    by_cases hvD : v ∈ D
    · have hvb : v = b := by
        by_contra hne
        exact hvE (Finset.mem_erase.mpr ⟨hne, hvD⟩)
      subst v
      obtain ⟨u, hu, hAdj⟩ := hb.2
      have hub : u ≠ b := by
        intro heq
        subst u
        exact G.irrefl hAdj
      exact ⟨u, Finset.mem_erase.mpr ⟨hub, hu⟩, hAdj.symm⟩
    · obtain ⟨d, hd, hAdj⟩ := hCan.1.1 hvD
      by_cases hret : ∃ u ∈ E, G.Adj u v
      · exact hret
      · have hdb : d = b := by
          by_contra hne
          exact hret ⟨d, Finset.mem_erase.mpr ⟨hne, hd⟩, hAdj⟩
        subst d
        have hvP : v ∈ privateExternalNeighbors G D b := by
          rw [mem_privateExternalNeighbors]
          refine ⟨hvD, ?_⟩
          intro u hu
          constructor
          · intro huv
            by_cases hub : u = b
            · exact hub
            · exact False.elim (hret ⟨u, Finset.mem_erase.mpr ⟨hub, hu⟩, huv⟩)
          · intro hub
            rw [hub]
            exact hAdj
        rw [hP] at hvP
        simp at hvP
  have hEbip : IsBipartiteOn G E := bipartiteOn_subset G hED hCan.1.2
  have hEbd : IsBipartiteDominatingSet G E := ⟨hEd, hEbip⟩
  have hmin := hCan.2.1 E hEbd
  have hcard : E.card + 1 = D.card := Finset.card_erase_add_one hb.1
  dsimp [E] at hmin hcard
  omega

theorem singleton_privateExternalNeighbors_contradiction
    {D : Finset V} {b p : V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hb : NonisolatedIn G D b)
    (hP : privateExternalNeighbors G D b = {p}) : False := by
  classical
  let E := insert p (D.erase b)
  have hpP : p ∈ privateExternalNeighbors G D b := by rw [hP]; simp
  have hpInfo := (mem_privateExternalNeighbors G D b p).mp hpP
  have hpNotD : p ∉ D := hpInfo.1
  have hpPriv := hpInfo.2
  have hEd : Dominates G E := by
    intro v hvE
    by_cases hvD : v ∈ D
    · by_cases hvb : v = b
      · subst v
        obtain ⟨u, hu, hAdj⟩ := hb.2
        have hub : u ≠ b := by
          intro heq
          subst u
          exact G.irrefl hAdj
        exact ⟨u, by simp [E, hub, hu], hAdj.symm⟩
      · have hvErase : v ∈ D.erase b := Finset.mem_erase.mpr ⟨hvb, hvD⟩
        exact (hvE (by simpa [E] using Finset.mem_insert_of_mem hvErase)).elim
    · by_cases hret : ∃ d ∈ D.erase b, G.Adj d v
      · rcases hret with ⟨d, hd, hAdj⟩
        exact ⟨d, by simp [E, hd], hAdj⟩
      · obtain ⟨d, hd, hAdj⟩ := hCan.1.1 hvD
        have hdb : d = b := by
          by_contra hne
          exact hret ⟨d, Finset.mem_erase.mpr ⟨hne, hd⟩, hAdj⟩
        subst d
        have hvP : v ∈ privateExternalNeighbors G D b := by
          rw [mem_privateExternalNeighbors]
          refine ⟨hvD, ?_⟩
          intro u hu
          constructor
          · intro huv
            by_cases hub : u = b
            · exact hub
            · exact False.elim (hret ⟨u, Finset.mem_erase.mpr ⟨hub, hu⟩, huv⟩)
          · intro hub
            rw [hub]
            exact hAdj
        have hvSingle : v ∈ ({p} : Finset V) := by rwa [← hP]
        have hvEq : v = p := Finset.mem_singleton.mp hvSingle
        subst v
        exact (hvE (by simp [E])).elim
  have hEbip : IsBipartiteOn G E := by
    rcases hCan.1.2 with ⟨c, hc⟩
    refine ⟨fun v => if v ∈ D.erase b then c v else false, ?_⟩
    intro u v hu hv hAdj
    change u ∈ insert p (D.erase b) at hu
    change v ∈ insert p (D.erase b) at hv
    rcases Finset.mem_insert.mp hu with huP | huErase
    · subst u
      rcases Finset.mem_insert.mp hv with hvP | hvErase
      · subst v
        exact (G.irrefl hAdj).elim
      · have hvD : v ∈ D := Finset.erase_subset b D hvErase
        have hvNe : v ≠ b := (Finset.mem_erase.mp hvErase).1
        have hnot : ¬ G.Adj v p := by
          intro hadj
          exact hvNe ((hpPriv v hvD).mp hadj)
        exact (hnot hAdj.symm).elim
    · rcases Finset.mem_insert.mp hv with hvP | hvErase
      · subst v
        have huD : u ∈ D := Finset.erase_subset b D huErase
        have huNe : u ≠ b := (Finset.mem_erase.mp huErase).1
        have hnot : ¬ G.Adj u p := by
          intro hadj
          exact huNe ((hpPriv u huD).mp hadj)
        exact (hnot hAdj).elim
      · simpa only [if_pos huErase, if_pos hvErase] using
          hc (Finset.erase_subset b D huErase) (Finset.erase_subset b D hvErase) hAdj
  have hEbd : IsBipartiteDominatingSet G E := ⟨hEd, hEbip⟩
  have hpNotErase : p ∉ D.erase b := fun hpE => hpNotD (Finset.erase_subset b D hpE)
  have hEcard : E.card = D.card := by
    dsimp [E]
    rw [Finset.card_insert_of_notMem hpNotErase, Finset.card_erase_add_one hb.1]
  have hArcsSub : internalArcs G E ⊆ internalArcs G D := by
    intro q hq
    rcases q with ⟨u, v⟩
    change (u, v) ∈ internalArcs G (insert p (D.erase b)) at hq
    rw [mem_internalArcs] at hq ⊢
    rcases hq with ⟨hu, hv, hAdj⟩
    change u ∈ insert p (D.erase b) at hu
    change v ∈ insert p (D.erase b) at hv
    rcases Finset.mem_insert.mp hu with huP | huErase
    · subst u
      rcases Finset.mem_insert.mp hv with hvP | hvErase
      · subst v
        exact (G.irrefl hAdj).elim
      · have hvD : v ∈ D := Finset.erase_subset b D hvErase
        have hvNe : v ≠ b := (Finset.mem_erase.mp hvErase).1
        have hnot : ¬ G.Adj v p := by
          intro hadj
          have heq := (hpPriv v hvD).mp hadj
          exact hvNe heq
        exact (hnot hAdj.symm).elim
    · rcases Finset.mem_insert.mp hv with hvP | hvErase
      · subst v
        have huD : u ∈ D := Finset.erase_subset b D huErase
        have huNe : u ≠ b := (Finset.mem_erase.mp huErase).1
        have hnot : ¬ G.Adj u p := by
          intro hadj
          have heq := (hpPriv u huD).mp hadj
          exact huNe heq
        exact (hnot hAdj).elim
      · exact ⟨Finset.erase_subset b D huErase, Finset.erase_subset b D hvErase, hAdj⟩
  obtain ⟨u, hu, hbu⟩ := hb.2
  have hMissing : (b, u) ∈ internalArcs G D :=
    (mem_internalArcs G D b u).mpr ⟨hb.1, hu, hbu⟩
  have hArcNe : internalArcs G E ≠ internalArcs G D := by
    intro heq
    have hmemE : (b, u) ∈ internalArcs G E := by
      rw [heq]
      exact hMissing
    have hbE : b ∈ E := (mem_internalArcs G E b u).mp hmemE |>.1
    have hbE' : b ∈ insert p (D.erase b) := by simpa [E] using hbE
    rcases Finset.mem_insert.mp hbE' with hbp | hbErase
    · subst p
      exact hpNotD hb.1
    · exact (Finset.mem_erase.mp hbErase).1 rfl
  have hArcLt : (internalArcs G E).card < (internalArcs G D).card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hArcsSub, hArcNe⟩)
  have hsecondary := hCan.2.2 E hEbd hEcard
  omega

/-- Lemma 3.1: every selected vertex that is non-isolated in the induced
selected graph has at least two external private neighbors. -/
theorem lemma_3_1_private_neighbors
    {D : Finset V} {b : V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hb : NonisolatedIn G D b) :
    2 ≤ (privateExternalNeighbors G D b).card := by
  classical
  by_contra hsmall
  have hcases : (privateExternalNeighbors G D b).card = 0 ∨
      (privateExternalNeighbors G D b).card = 1 := by omega
  rcases hcases with hzero | hone
  · have hPempty : privateExternalNeighbors G D b = ∅ :=
      Finset.card_eq_zero.mp hzero
    exact (empty_privateExternalNeighbors_contradiction G hCan hb hPempty).elim
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hone
    have hPsingle : privateExternalNeighbors G D b = {p} := hp
    exact (singleton_privateExternalNeighbors_contradiction G hCan hb hPsingle).elim

end C6BipartiteDomination


