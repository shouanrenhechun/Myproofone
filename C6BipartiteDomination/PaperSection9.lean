/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import C6BipartiteDomination.A9

/-! # Paper section 9: repair graph and local resources

This file follows the paper's section order. It starts with the neighbor
partition needed in the proof of Lemma 9.1; later results will be added here
in the order they occur in the paper.
-/

namespace C6BipartiteDomination

open Finset BigOperators
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

/-- Explicit A8 witness with every member certified as a legal repair. The
cardinality profile is the paper's 8.3 conclusion restricted to the negative
support vertices used by the subsequent argument. -/
theorem paper8_chosen_repair_witness
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {w : V} (hw : w ∈ SPart G D)
    (ha : externalCharge G D w < 0) :
    ∃ R : Finset V,
      (∀ u ∈ R, IsRepairVertex G D w u) ∧
      ((kCharge G D w = 3 ∧ betaCharge G D w = 2 ∧ R.card = 2) ∨
       (kCharge G D w = 3 ∧ betaCharge G D w = 3 ∧ R.card = 1) ∨
       (kCharge G D w = 4 ∧ betaCharge G D w = 2 ∧ R.card = 2)) := by
  classical
  rcases lemma_7_2_negative_charge_classification G hCan hmax hw ha with
    ⟨hk, hβ⟩ | ⟨hk, hβ⟩ | ⟨hk, hβ⟩
  · obtain ⟨R, hcard, hlegal⟩ := chosen_repairs_beta_two G hCan hw (by omega) hβ
    exact ⟨R, hlegal, Or.inl ⟨hk, hβ, hcard⟩⟩
  · obtain ⟨u, hlegal⟩ := chosen_repair_beta_three G hCan hw hβ
    refine ⟨{u}, ?_, Or.inr (Or.inl ⟨hk, hβ, by simp⟩)⟩
    intro v hv
    have hvEq : v = u := Finset.mem_singleton.mp hv
    simpa [hvEq] using hlegal
  · obtain ⟨R, hcard, hlegal⟩ := chosen_repairs_beta_two G hCan hw (by omega) hβ
    exact ⟨R, hlegal, Or.inr (Or.inr ⟨hk, hβ, hcard⟩)⟩

/-- A globally fixed choice of repair set for each negative high-support
vertex. This is obtained from A8, so downstream graph edges really belong to
the chosen relation rather than to the set of all possible repairs. -/
noncomputable def paperChosenRepairSet
    (D : Finset V) (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (w : V) : Finset V := by
  classical
  exact if h : w ∈ SPart G D ∧ externalCharge G D w < 0 then
    Classical.choose (paper8_chosen_repair_witness G hCan hmax h.1 h.2)
  else ∅

theorem paperChosenRepairSet_legal
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {w : V} (hw : w ∈ SPart G D)
    (ha : externalCharge G D w < 0) :
    ∀ u ∈ paperChosenRepairSet G D hCan hmax w,
      IsRepairVertex G D w u := by
  classical
  have hcond : w ∈ SPart G D ∧ externalCharge G D w < 0 := ⟨hw, ha⟩
  simp only [paperChosenRepairSet, dif_pos hcond]
  exact (Classical.choose_spec
    (paper8_chosen_repair_witness G hCan hmax hw ha)).1

/-- The neighbors of a selected `B`-vertex split into its selected neighbors,
its private external neighbors, and its `S`-neighbors. -/
theorem paper9_neighbor_partition
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    {u : V} (huB : u ∈ BPart G D) :
    (Finset.univ.filter fun q => G.Adj u q) =
      (D.filter fun q => G.Adj u q) ∪
        (privateExternalNeighbors G D u ∪
          (SPart G D).filter fun q => G.Adj u q) := by
  classical
  apply Finset.ext
  intro q
  constructor
  · intro hq
    have hadj : G.Adj u q := (Finset.mem_filter.mp hq).2
    by_cases hqD : q ∈ D
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hqD, hadj⟩)
    · have hqWB : q ∈ WBPart G D := by
        rw [mem_WBPart]
        refine ⟨hqD, ?_⟩
        intro hq0
        exact ((mem_W0Part G D q).mp hq0).2 u huB hadj
      by_cases hqP : q ∈ PPart G D
      · rcases (mem_PPart G D q).mp hqP with ⟨b, hbB, hqPriv⟩
        have hbD := (mem_BPart G D b).mp hbB |>.1
        have hpriv := (mem_privateExternalNeighbors G D b q).mp hqPriv |>.2
        have hbu : b = u := ((hpriv u (mem_BPart G D u |>.mp huB |>.1)).mp
          hadj).symm
        subst b
        exact Finset.mem_union_right _ (Finset.mem_union_left _ hqPriv)
      · have hqS : q ∈ SPart G D := by
          rw [mem_SPart]
          exact ⟨hqWB, hqP⟩
        exact Finset.mem_union_right _
          (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hqS, hadj⟩))
  · intro hq
    rcases Finset.mem_union.mp hq with hqD | hqRest
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hqD).2⟩
    · rcases Finset.mem_union.mp hqRest with hqPriv | hqS
      · have hqInfo := (mem_privateExternalNeighbors G D u q).mp hqPriv
        have huD := (mem_BPart G D u).mp huB |>.1
        have hadj := (hqInfo.2 u huD).mpr rfl
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩
      · have hadj := (Finset.mem_filter.mp hqS).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩

/-- The three parts in the neighbor partition are pairwise disjoint. -/
theorem paper9_neighbor_partition_disjoint
    {D : Finset V} {u : V} (huB : u ∈ BPart G D) :
    Disjoint (D.filter fun q => G.Adj u q)
        (privateExternalNeighbors G D u ∪
          (SPart G D).filter fun q => G.Adj u q) ∧
    Disjoint (privateExternalNeighbors G D u)
        ((SPart G D).filter fun q => G.Adj u q) := by
  classical
  constructor
  · rw [Finset.disjoint_left]
    intro q hqD hqR
    rcases Finset.mem_union.mp hqR with hqP | hqS
    · exact (mem_privateExternalNeighbors G D u q).mp hqP |>.1
        ((Finset.mem_filter.mp hqD).1)
    · have hqWB := (mem_SPart G D q).mp (Finset.mem_filter.mp hqS).1 |>.1
      exact (mem_WBPart G D q).mp hqWB |>.1 ((Finset.mem_filter.mp hqD).1)
  · rw [Finset.disjoint_left]
    intro q hqP hqS
    have hqInP : q ∈ PPart G D := by
      apply (mem_PPart G D q).mpr
      exact ⟨u, huB, hqP⟩
    exact (mem_SPart G D q).mp (Finset.mem_filter.mp hqS).1 |>.2 hqInP

/-- Every `B`-vertex has an internal neighbor in the canonical selected set. -/
theorem paper9_selected_neighbor_nonempty
    {D : Finset V} {u : V} (hCan : CanonicalTwoLevelOptimum G D)
    (huB : u ∈ BPart G D) :
    0 < (D.filter fun q => G.Adj u q).card := by
  classical
  obtain ⟨v, hvD, huv⟩ := (nonisolated_of_mem_BPart G huB).2
  apply Finset.card_pos.mpr
  exact ⟨v, Finset.mem_filter.mpr ⟨hvD, huv⟩⟩

/-- The local degree budget used at the start of Lemma 9.1. -/
theorem paper9_sCharge_add_xCharge_le_three
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {u : V} (huB : u ∈ BPart G D) :
    sCharge G D u + xCharge G D u ≤ 3 := by
  classical
  have hpart := paper9_neighbor_partition G hCan huB
  have hdisj := paper9_neighbor_partition_disjoint G huB
  have hcard := congrArg Finset.card hpart
  rw [Finset.card_union_of_disjoint hdisj.1,
    Finset.card_union_of_disjoint hdisj.2] at hcard
  have hdeg : (Finset.univ.filter fun q => G.Adj u q).card =
      degreeTo G Finset.univ u := by
    simp [degreeTo, G.adj_comm]
  have hSle : ((SPart G D).filter fun q => G.Adj u q).card =
      degreeTo G (SPart G D) u := by
    simp [degreeTo, G.adj_comm]
  rw [hdeg, hSle, private_card_eq_two_add_x G hCan huB] at hcard
  have hselected := paper9_selected_neighbor_nonempty G hCan huB
  have hmaxu := hmax u
  change degreeTo G (SPart G D) u + xCharge G D u ≤ 3
  omega

/-- A shared compensation vertex is an `S`-neighbor of its repair vertex and
has exactly one `Z₀`-neighbor. This is the local incidence fact used in the
paper's repair-graph degree argument. -/
theorem paper9_shared_compensation_profile
    {D X : Finset V} {u q : V}
    (hX : X ⊆ Z0Part G D) (huB : u ∈ BPart G D)
    (hq : q ∈ sharedCompensation G D X u) :
    q ∈ SPart G D ∧ G.Adj u q ∧ kCharge G D q = 1 := by
  classical
  have hqInfo := (mem_sharedCompensation G D X u q).mp hq
  obtain ⟨z, hzX, hN⟩ := hqInfo.2
  have hz0 := hX hzX
  have hzD := (mem_ZPart G D z).mp ((mem_Z0Part G D z).mp hz0 |>.1) |>.1
  have hzNeU : z ≠ u := by
    intro hEq
    subst z
    exact (Finset.disjoint_left.mp (Z0_disjoint_B G) hz0 huB).elim
  have huD := (mem_BPart G D u).mp huB |>.1
  have hqAdjU : G.Adj q u := by
    have hmem : u ∈ ({u, z} : Finset V) := by simp
    have hmemN : u ∈ neighborhoodIn G D q := by
      rw [hN]
      exact hmem
    exact (mem_neighborhoodIn G D q u).mp hmemN |>.2
  have hqAdjZ : G.Adj q z := by
    have hmem : z ∈ ({u, z} : Finset V) := by simp
    have hmemN : z ∈ neighborhoodIn G D q := by
      rw [hN]
      exact hmem
    exact (mem_neighborhoodIn G D q z).mp hmemN |>.2
  have hqN_z : z ∈ neighborhoodIn G D q := by
    exact (mem_neighborhoodIn G D q z).mpr ⟨hzD, hqAdjZ⟩
  have hqNotP : q ∉ PPart G D := by
    intro hqP
    obtain ⟨b, hbB, hpriv⟩ := (mem_PPart G D q).mp hqP
    have hbD := (mem_BPart G D b).mp hbB |>.1
    have hpriv' := (mem_privateExternalNeighbors G D b q).mp hpriv |>.2
    have hbu : b = u := ((hpriv' u huD).mp hqAdjU.symm).symm
    subst b
    have hzu : z = u := (hpriv' z hzD).mp hqAdjZ.symm
    exact hzNeU hzu
  have hqWB : q ∈ WBPart G D := by
    rw [mem_WBPart]
    refine ⟨hqInfo.1, ?_⟩
    intro hq0
    exact ((mem_W0Part G D q).mp hq0).2 u huB hqAdjU.symm
  have hqS : q ∈ SPart G D := by
    rw [mem_SPart]
    exact ⟨hqWB, hqNotP⟩
  have hfilter : (Z0Part G D).filter (fun x => G.Adj q x) = {z} := by
    ext x
    constructor
    · intro hx
      have hx0 := (Finset.mem_filter.mp hx).1
      have hxD := (mem_ZPart G D x).mp ((mem_Z0Part G D x).mp hx0 |>.1) |>.1
      have hxN : x ∈ neighborhoodIn G D q := by
        exact (mem_neighborhoodIn G D q x).mpr
          ⟨hxD, (Finset.mem_filter.mp hx).2⟩
      have hxPair : x ∈ ({u, z} : Finset V) := by rw [← hN]; exact hxN
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxPair
      rcases hxPair with hxU | hxZ
      · subst x
        exact False.elim ((Finset.disjoint_left.mp (Z0_disjoint_B G) hx0 huB).elim)
      · simpa [hxZ]
    · intro hx
      have hxZ : x = z := Finset.mem_singleton.mp hx
      subst x
      exact Finset.mem_filter.mpr ⟨hz0, hqAdjZ⟩
  have hk : kCharge G D q = 1 := by
    unfold kCharge degreeTo
    rw [hfilter]
    simp
  exact ⟨hqS, hqAdjU.symm, hk⟩

/-- The shared compensation set lies among the `S`-neighbors of `u`, and is
disjoint from any set of support-at-least-two vertices. -/
theorem paper9_shared_set_incidence
    {D X : Finset V} {u : V}
    (hX : X ⊆ Z0Part G D) (huB : u ∈ BPart G D) :
    sharedCompensation G D X u ⊆ (SPart G D).filter (fun q => G.Adj u q) ∧
      ∀ T : Finset V, (∀ w ∈ T, 2 ≤ kCharge G D w) →
        Disjoint T (sharedCompensation G D X u) := by
  constructor
  · intro q hq
    obtain ⟨hqS, hAdj, _⟩ := paper9_shared_compensation_profile G hX huB hq
    exact Finset.mem_filter.mpr ⟨hqS, hAdj⟩
  · intro T hT
    rw [Finset.disjoint_left]
    intro q hqT hqL
    have hkq := (paper9_shared_compensation_profile G hX huB hqL).2.2
    exact Nat.not_le_of_gt (by omega) (hT q hqT)

/-- A shared compensation vertex has exactly one neighbor in `B`, namely its
repair vertex. -/
theorem paper9_shared_beta_eq_one
    {D X : Finset V} {u q : V}
    (hX : X ⊆ Z0Part G D) (huB : u ∈ BPart G D)
    (hq : q ∈ sharedCompensation G D X u) :
    betaCharge G D q = 1 := by
  classical
  have hqInfo := (mem_sharedCompensation G D X u q).mp hq
  obtain ⟨z, hzX, hN⟩ := hqInfo.2
  have hz0 := hX hzX
  have hzNeU : z ≠ u := by
    intro hEq
    subst z
    exact (Finset.disjoint_left.mp (Z0_disjoint_B G) hz0 huB).elim
  have huD := (mem_BPart G D u).mp huB |>.1
  have hzD := (mem_ZPart G D z).mp ((mem_Z0Part G D z).mp hz0 |>.1) |>.1
  have huAdj : G.Adj q u := by
    have hm : u ∈ ({u, z} : Finset V) := by simp
    have hn : u ∈ neighborhoodIn G D q := by rw [hN]; exact hm
    exact (mem_neighborhoodIn G D q u).mp hn |>.2
  have hfilter : (BPart G D).filter (fun b => G.Adj q b) = {u} := by
    ext b
    constructor
    · intro hb
      have hbB := (Finset.mem_filter.mp hb).1
      have hbD := (mem_BPart G D b).mp hbB |>.1
      have hbN : b ∈ neighborhoodIn G D q :=
        (mem_neighborhoodIn G D q b).mpr
          ⟨hbD, (Finset.mem_filter.mp hb).2⟩
      have hbPair : b ∈ ({u, z} : Finset V) := by rw [← hN]; exact hbN
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbPair
      rcases hbPair with hbu | hbz
      · simpa [hbu]
      · subst b
        exact False.elim ((Finset.disjoint_left.mp (Z0_disjoint_B G) hz0 hbB).elim)
    · intro hb
      have hbEq : b = u := Finset.mem_singleton.mp hb
      subst b
      exact Finset.mem_filter.mpr ⟨huB, huAdj⟩
  unfold betaCharge degreeTo
  rw [hfilter]
  simp

/-- Every shared compensation vertex contributes the paper's positive charge
`a(q)=4`. -/
theorem paper9_shared_external_charge_eq_four
    {D X : Finset V} {u q : V}
    (hX : X ⊆ Z0Part G D) (huB : u ∈ BPart G D)
    (hq : q ∈ sharedCompensation G D X u) :
    externalCharge G D q = 4 := by
  have hprof := paper9_shared_compensation_profile G hX huB hq
  have hβ := paper9_shared_beta_eq_one G hX huB hq
  unfold externalCharge
  rw [hprof.2.2, hβ]
  norm_num

/-- Paper Lemma 9.3's compensation estimate. The degree-one hypothesis is not
needed once a particular chosen repair edge is fixed: the local budget and
Lemma 8.5 already give the same bound for each such edge. -/
theorem paper9_single_repair_resource_bound
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {u w : V} (huB : u ∈ BPart G D) (hw : w ∈ SPart G D)
    (ha : externalCharge G D w < 0)
    (hChosen : ChosenRepairRelation G D w
      (paperChosenRepairSet G D hCan hmax w) u)
    (hk : kCharge G D w = 3 ∨ kCharge G D w = 4) :
    (kCharge G D w = 3 ∧
      vertexCharge G D u +
        ∑ q ∈ sharedCompensation G D (supportX G D w) u,
          externalCharge G D q ≥ 4) ∨
    (kCharge G D w = 4 ∧
      vertexCharge G D u +
        ∑ q ∈ sharedCompensation G D (supportX G D w) u,
          externalCharge G D q ≥ 8) := by
  classical
  let L := sharedCompensation G D (supportX G D w) u
  have hX : supportX G D w ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D w z).mp hz |>.1
  have hbudget := paper9_sCharge_add_xCharge_le_three G hCan hmax huB
  have hC : 11 * (xCharge G D u : ℤ) ≤ vertexCharge G D u := by
    have hbudgetZ : (degreeTo G (SPart G D) u : ℤ) +
        (xCharge G D u : ℤ) ≤ 3 := by
      exact_mod_cast hbudget
    unfold vertexCharge at hbudgetZ ⊢
    omega
  have hsum : (∑ q ∈ L, externalCharge G D q) =
      4 * (L.card : ℤ) := by
    calc
      _ = ∑ q ∈ L, (4 : ℤ) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact paper9_shared_external_charge_eq_four G hX huB (by simpa [L] using hq)
      _ = 4 * (L.card : ℤ) := by simp; ring
  have hbound := lemma_8_5_compensation_lower_bound G hCan hmax hw ha hChosen
  have hbound' : kCharge G D w - 2 ≤ xCharge G D u + L.card := by
    simpa [L] using hbound
  rcases hk with hk3 | hk4
  · left
    refine ⟨hk3, ?_⟩
    by_cases hx0 : xCharge G D u = 0
    · have hL : 1 ≤ L.card := by rw [hk3] at hbound'; rw [hx0] at hbound'; omega
      rw [hsum]
      have hC0 : 0 ≤ vertexCharge G D u := by omega
      have hLZ : 1 ≤ (L.card : ℤ) := by exact_mod_cast hL
      have hsum4 : 4 ≤ 4 * (L.card : ℤ) := by nlinarith
      omega
    · have hxpos : 1 ≤ xCharge G D u := by omega
      have hsumNonneg : 0 ≤ ∑ q ∈ L, externalCharge G D q := by rw [hsum]; positivity
      nlinarith [hC, hsumNonneg, hxpos]
  · right
    refine ⟨hk4, ?_⟩
    by_cases hx0 : xCharge G D u = 0
    · have hL : 2 ≤ L.card := by rw [hk4] at hbound'; rw [hx0] at hbound'; omega
      rw [hsum]
      have hC0 : 0 ≤ vertexCharge G D u := by omega
      have hLZ : 2 ≤ (L.card : ℤ) := by exact_mod_cast hL
      have hsum8 : 8 ≤ 4 * (L.card : ℤ) := by nlinarith
      omega
    · have hxpos : 1 ≤ xCharge G D u := by omega
      have hsumNonneg : 0 ≤ ∑ q ∈ L, externalCharge G D q := by rw [hsum]; positivity
      nlinarith [hC, hsumNonneg, hxpos]

/-- Count a high-support neighbor set and a shared compensation set together
inside the `S`-neighbors of `u`. -/
theorem paper9_union_resource_bound
    {D T L : Finset V} {u : V}
    (hT : T ⊆ (SPart G D).filter (fun q => G.Adj u q))
    (hL : L ⊆ (SPart G D).filter (fun q => G.Adj u q))
    (hdisj : Disjoint T L) :
    T.card + L.card ≤ sCharge G D u := by
  have hsub : T ∪ L ⊆ (SPart G D).filter (fun q => G.Adj u q) := by
    intro q hq
    rcases Finset.mem_union.mp hq with hqT | hqL
    · exact hT hqT
    · exact hL hqL
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  simpa [sCharge, degreeTo] using hcard

/-- With two fixed high-support neighbors and at most three `S`-neighbors in
total, there is at most one further `S`-neighbor outside the pair. -/
theorem paper9_unique_extra_S_neighbor
    {D T : Finset V} {u q r : V}
    (hT : T ⊆ (SPart G D).filter (fun v => G.Adj u v))
    (hTcard : T.card = 2)
    (hq : q ∈ (SPart G D).filter (fun v => G.Adj u v))
    (hr : r ∈ (SPart G D).filter (fun v => G.Adj u v))
    (hqT : q ∉ T) (hrT : r ∉ T)
    (hs : sCharge G D u ≤ 3) : q = r := by
  classical
  by_contra hqr
  let P : Finset V := {q, r}
  have hPcard : P.card = 2 := by simp [P, hqr]
  have hPsub : P ⊆ (SPart G D).filter (fun v => G.Adj u v) := by
    intro v hv
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hvq | hvr
    · simpa [hvq] using hq
    · simpa [hvr] using hr
  have hdisj : Disjoint T P := by
    rw [Finset.disjoint_left]
    intro v hvT hvP
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hvP
    rcases hvP with hvq | hvr
    · exact hqT (hvq ▸ hvT)
    · exact hrT (hvr ▸ hvT)
  have hbound := paper9_union_resource_bound G hT hPsub hdisj
  rw [hTcard, hPcard] at hbound
  omega

/-- The isolated support vertex in a shared-compensation description is
unique, even when the same compensation vertex is shared by two supports. -/
theorem paper9_shared_support_witness_agrees
    {D X Y : Finset V} {u q : V}
    (huB : u ∈ BPart G D)
    (hX : X ⊆ Z0Part G D) (hY : Y ⊆ Z0Part G D)
    (hqX : q ∈ sharedCompensation G D X u)
    (hqY : q ∈ sharedCompensation G D Y u) :
    ∃ z, z ∈ X ∧ z ∈ Y ∧ neighborhoodIn G D q = {u, z} := by
  classical
  obtain ⟨z₁, hz₁, hN₁⟩ := (mem_sharedCompensation G D X u q).mp hqX |>.2
  obtain ⟨z₂, hz₂, hN₂⟩ := (mem_sharedCompensation G D Y u q).mp hqY |>.2
  have hz₁0 := hX hz₁
  have hz₂0 := hY hz₂
  have hz₁NeU : z₁ ≠ u := by
    intro hEq
    subst z₁
    exact (Finset.disjoint_left.mp (Z0_disjoint_B G (D := D)) hz₁0 huB).elim
  have hz₁Pair : z₁ ∈ ({u, z₂} : Finset V) := by
    have hz₁N : z₁ ∈ neighborhoodIn G D q := by rw [hN₁]; simp
    rw [hN₂] at hz₁N
    exact hz₁N
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz₁Pair
  have hzEq : z₁ = z₂ := by
    rcases hz₁Pair with hzu | hzz
    · exact False.elim (hz₁NeU hzu)
    · exact hzz
  subst z₂
  exact ⟨z₁, hz₁, hz₂, hN₁⟩

/-- Paper Lemma 9.1, right degree at most two, stated for any finite family
of chosen repair edges incident with the same `B`-vertex. -/
theorem paper9_repair_degree_le_two
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {u : V} (huB : u ∈ BPart G D) (T : Finset V)
    (hTsub : T ⊆ SPart G D)
    (hTnegative : ∀ w ∈ T, externalCharge G D w < 0)
    (hTrepair : ∀ w ∈ T,
      u ∈ paperChosenRepairSet G D hCan hmax w) :
    T.card ≤ 2 := by
  classical
  have hThigh : ∀ w ∈ T, 3 ≤ kCharge G D w := by
    intro w hw
    rcases lemma_7_2_negative_charge_classification G hCan hmax
        (hTsub hw) (hTnegative w hw) with h | h | h <;> omega
  have hTadj : ∀ w ∈ T, G.Adj w u := by
    intro w hw
    have hLegal := paperChosenRepairSet_legal G hCan hmax
      (hTsub hw) (hTnegative w hw) u (hTrepair w hw)
    exact hLegal.2.1
  have hTneighbors : T ⊆ (SPart G D).filter (fun q => G.Adj u q) := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨hTsub hw, (hTadj w hw).symm⟩
  have hTleS : T.card ≤ sCharge G D u := by
    have hcard := Finset.card_le_card hTneighbors
    simpa [sCharge, degreeTo] using hcard
  have hbudget := paper9_sCharge_add_xCharge_le_three G hCan hmax huB
  by_contra hnot
  have hTthree : 3 ≤ T.card := by omega
  have hxzero : xCharge G D u = 0 := by omega
  obtain ⟨w, hwT⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  have hChosen : ChosenRepairRelation G D w
      (paperChosenRepairSet G D hCan hmax w) u :=
    ⟨hTrepair w hwT,
      paperChosenRepairSet_legal G hCan hmax (hTsub hwT)
        (hTnegative w hwT) u (hTrepair w hwT)⟩
  have hLbound := lemma_8_5_compensation_lower_bound G hCan hmax
    (hTsub hwT) (hTnegative w hwT) hChosen
  have hLpos : 0 <
      (sharedCompensation G D (supportX G D w) u).card := by
    rw [hxzero] at hLbound
    have hk := hThigh w hwT
    omega
  let L := sharedCompensation G D (supportX G D w) u
  obtain ⟨q, hqL⟩ := Finset.card_pos.mp (by simpa [L] using hLpos)
  have hX : supportX G D w ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D w z).mp hz |>.1
  have hLinc := paper9_shared_set_incidence G hX huB
  have hLsub : L ⊆ (SPart G D).filter (fun q => G.Adj u q) := by
    simpa [L] using hLinc.1
  have hdisj : Disjoint T L := by
    apply hLinc.2 T
    exact fun v hv => le_trans (by decide : 2 ≤ 3) (hThigh v hv)
  have hTL := paper9_union_resource_bound G hTneighbors hLsub hdisj
  rw [hxzero] at hbudget
  have hLcard : 1 ≤ L.card := by
    have : 0 < L.card := by simpa [L] using hLpos
    omega
  omega

/-- The strengthened clause of Lemma 9.1: if the incident family contains a
chosen repair edge for a negative vertex with `k=4`, then it has size at most
one. -/
theorem paper9_repair_degree_le_one_at_k4
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {u w₄ : V} (huB : u ∈ BPart G D) (T : Finset V)
    (hTsub : T ⊆ SPart G D)
    (hTnegative : ∀ w ∈ T, externalCharge G D w < 0)
    (hTrepair : ∀ w ∈ T,
      u ∈ paperChosenRepairSet G D hCan hmax w)
    (hw₄ : w₄ ∈ T) (hk₄ : kCharge G D w₄ = 4) :
    T.card ≤ 1 := by
  classical
  have hThigh : ∀ w ∈ T, 2 ≤ kCharge G D w := by
    intro w hw
    rcases lemma_7_2_negative_charge_classification G hCan hmax
        (hTsub hw) (hTnegative w hw) with h | h | h <;> omega
  have hTadj : ∀ w ∈ T, G.Adj w u := by
    intro w hw
    have hLegal := paperChosenRepairSet_legal G hCan hmax
      (hTsub hw) (hTnegative w hw) u (hTrepair w hw)
    exact hLegal.2.1
  have hTneighbors : T ⊆ (SPart G D).filter (fun q => G.Adj u q) := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨hTsub hw, (hTadj w hw).symm⟩
  have hTleS : T.card ≤ sCharge G D u := by
    have hcard := Finset.card_le_card hTneighbors
    simpa [sCharge, degreeTo] using hcard
  have hbudget := paper9_sCharge_add_xCharge_le_three G hCan hmax huB
  by_contra hnot
  have hTtwo : 2 ≤ T.card := by omega
  have hChosen : ChosenRepairRelation G D w₄
      (paperChosenRepairSet G D hCan hmax w₄) u :=
    ⟨hTrepair w₄ hw₄,
      paperChosenRepairSet_legal G hCan hmax (hTsub hw₄)
        (hTnegative w₄ hw₄) u (hTrepair w₄ hw₄)⟩
  have hLbound := lemma_8_5_compensation_lower_bound G hCan hmax
    (hTsub hw₄) (hTnegative w₄ hw₄) hChosen
  have hX : supportX G D w₄ ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D w₄ z).mp hz |>.1
  let L := sharedCompensation G D (supportX G D w₄) u
  have hLbound' : 2 ≤ xCharge G D u + L.card := by
    simpa [L, hk₄] using hLbound
  have hLsub : L ⊆ (SPart G D).filter (fun q => G.Adj u q) := by
    exact (paper9_shared_set_incidence G hX huB).1
  have hdisj : Disjoint T L := by
    apply (paper9_shared_set_incidence G hX huB).2 T
    exact hThigh
  have hTL := paper9_union_resource_bound G hTneighbors hLsub hdisj
  by_cases hx0 : xCharge G D u = 0
  · have hLtwo : 2 ≤ L.card := by
      rw [hx0] at hLbound'
      omega
    omega
  · by_cases hx1 : xCharge G D u = 1
    · have hLone : 1 ≤ L.card := by
        rw [hx1] at hLbound'
        omega
      omega
    · have hxge2 : 2 ≤ xCharge G D u := by omega
      omega

/-- The paper's exact `k=4` clause follows because the specified vertex is
itself an incident repair neighbor. -/
theorem paper9_repair_degree_eq_one_at_k4
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {u w₄ : V} (huB : u ∈ BPart G D) (T : Finset V)
    (hTsub : T ⊆ SPart G D)
    (hTnegative : ∀ w ∈ T, externalCharge G D w < 0)
    (hTrepair : ∀ w ∈ T,
      u ∈ paperChosenRepairSet G D hCan hmax w)
    (hw₄ : w₄ ∈ T) (hk₄ : kCharge G D w₄ = 4) :
    T.card = 1 := by
  have hle := paper9_repair_degree_le_one_at_k4 G hCan hmax huB T
    hTsub hTnegative hTrepair hw₄ hk₄
  have hpos : 0 < T.card := Finset.card_pos.mpr ⟨w₄, hw₄⟩
  omega

/-- Paper Lemma 9.2 for a degree-two vertex in the chosen repair graph. The
two alternatives record the exact compensation sets, charges, and shared
support point from cases (a) and (b). -/
theorem paper9_lemma_9_2
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {u : V} (huB : u ∈ BPart G D) (T : Finset V)
    (hTsub : T ⊆ SPart G D)
    (hTnegative : ∀ w ∈ T, externalCharge G D w < 0)
    (hTrepair : ∀ w ∈ T,
      u ∈ paperChosenRepairSet G D hCan hmax w)
    (hTcard : T.card = 2) :
    (∀ w ∈ T, kCharge G D w = 3) ∧
      ((xCharge G D u = 1 ∧ sCharge G D u = 2 ∧
          vertexCharge G D u = 11 ∧
          ∀ w ∈ T, sharedCompensation G D (supportX G D w) u = ∅) ∨
       (xCharge G D u = 0 ∧ sCharge G D u = 3 ∧
          vertexCharge G D u = 0 ∧
          ∃ q z, (∀ w ∈ T,
              sharedCompensation G D (supportX G D w) u = {q}) ∧
            q ∈ SPart G D ∧ betaCharge G D q = 1 ∧
            kCharge G D q = 1 ∧ externalCharge G D q = 4 ∧
            z ∈ Z0Part G D ∧ neighborhoodIn G D q = {u, z} ∧
            ∀ w ∈ T, z ∈ supportX G D w)) := by
  classical
  let L : V → Finset V := fun w =>
    sharedCompensation G D (supportX G D w) u
  have hTadj : ∀ w ∈ T, G.Adj w u := by
    intro w hw
    have hLegal := paperChosenRepairSet_legal G hCan hmax
      (hTsub hw) (hTnegative w hw) u (hTrepair w hw)
    exact hLegal.2.1
  have hTneighbors : T ⊆ (SPart G D).filter (fun q => G.Adj u q) := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨hTsub hw, (hTadj w hw).symm⟩
  have hTleS : T.card ≤ sCharge G D u := by
    have hcard := Finset.card_le_card hTneighbors
    simpa [sCharge, degreeTo] using hcard
  have hbudget := paper9_sCharge_add_xCharge_le_three G hCan hmax huB
  have hsle : sCharge G D u ≤ 3 := by omega
  have hxle : xCharge G D u ≤ 1 := by rw [hTcard] at hTleS; omega
  have hThigh : ∀ w ∈ T, 2 ≤ kCharge G D w := by
    intro w hw
    rcases lemma_7_2_negative_charge_classification G hCan hmax
        (hTsub hw) (hTnegative w hw) with h | h | h <;> omega
  have hTclass : ∀ w ∈ T,
      kCharge G D w = 3 ∧
        (betaCharge G D w = 2 ∨ betaCharge G D w = 3) := by
    intro w hw
    have hk4 : kCharge G D w ≠ 4 := by
      intro hk
      have hone := paper9_repair_degree_eq_one_at_k4 G hCan hmax huB T
        hTsub hTnegative hTrepair hw hk
      rw [hTcard] at hone
      omega
    rcases lemma_7_2_negative_charge_classification G hCan hmax
        (hTsub hw) (hTnegative w hw) with h | h | h
    · exact ⟨h.1, Or.inl h.2⟩
    · exact ⟨h.1, Or.inr h.2⟩
    · exact False.elim (hk4 h.1)
  have hLsub : ∀ w ∈ T, L w ⊆ (SPart G D).filter (fun q => G.Adj u q) := by
    intro w hw
    have hX : supportX G D w ⊆ Z0Part G D := by
      intro z hz
      exact (mem_supportX G D w z).mp hz |>.1
    simpa [L] using (paper9_shared_set_incidence G hX huB).1
  have hLdisj : ∀ w ∈ T, Disjoint T (L w) := by
    intro w hw
    have hX : supportX G D w ⊆ Z0Part G D := by
      intro z hz
      exact (mem_supportX G D w z).mp hz |>.1
    simpa [L] using (paper9_shared_set_incidence G hX huB).2 T hThigh
  have hLbound : ∀ w ∈ T, kCharge G D w - 2 ≤ xCharge G D u + (L w).card := by
    intro w hw
    have hChosen : ChosenRepairRelation G D w
        (paperChosenRepairSet G D hCan hmax w) u :=
      ⟨hTrepair w hw,
        paperChosenRepairSet_legal G hCan hmax (hTsub hw)
          (hTnegative w hw) u (hTrepair w hw)⟩
    have h := lemma_8_5_compensation_lower_bound G hCan hmax
      (hTsub hw) (hTnegative w hw) hChosen
    simpa [L] using h
  have hTpositive : 0 < T.card := by omega
  obtain ⟨w₀, hw₀⟩ := Finset.card_pos.mp hTpositive
  by_cases hx1 : xCharge G D u = 1
  · have hs2 : sCharge G D u = 2 := by rw [hTcard] at hTleS; omega
    have hLempty : ∀ w ∈ T, L w = ∅ := by
      intro w hw
      have hle := paper9_union_resource_bound G hTneighbors (hLsub w hw)
        (hLdisj w hw)
      rw [hTcard, hs2] at hle
      have hzero : (L w).card = 0 := by omega
      exact Finset.card_eq_zero.mp hzero
    have hvertex : vertexCharge G D u = 11 := by
      unfold vertexCharge
      rw [hx1, hs2]
      norm_num
    exact ⟨(fun w hw => (hTclass w hw).1), Or.inl ⟨hx1, hs2, hvertex, hLempty⟩⟩
  · have hx0 : xCharge G D u = 0 := by omega
    have hLpositive : ∀ w ∈ T, 1 ≤ (L w).card := by
      intro w hw
      have h := hLbound w hw
      rw [(hTclass w hw).1, hx0] at h
      omega
    have hX₀ : supportX G D w₀ ⊆ Z0Part G D := by
      intro z hz
      exact (mem_supportX G D w₀ z).mp hz |>.1
    have hL₀pos : 0 < (L w₀).card := by
      have := hLpositive w₀ hw₀
      omega
    obtain ⟨q, hqL₀⟩ := Finset.card_pos.mp hL₀pos
    have hqN : q ∈ (SPart G D).filter (fun v => G.Adj u v) := hLsub w₀ hw₀ hqL₀
    have hqNotT : q ∉ T := by
      intro hqT
      exact (Finset.disjoint_left.mp (hLdisj w₀ hw₀) hqT hqL₀).elim
    have hqProfile := paper9_shared_compensation_profile G hX₀ huB hqL₀
    have hqCharge := paper9_shared_external_charge_eq_four G hX₀ huB hqL₀
    have hs3 : sCharge G D u = 3 := by
      have hle := paper9_union_resource_bound G hTneighbors
        (hLsub w₀ hw₀) (hLdisj w₀ hw₀)
      rw [hTcard] at hle
      have hLone : (L w₀).card = 1 := by
        have hpos := hLpositive w₀ hw₀
        omega
      rw [hLone] at hle
      omega
    have hvertex : vertexCharge G D u = 0 := by
      unfold vertexCharge
      rw [hx0, hs3]
      norm_num
    have hqInAll : ∀ w ∈ T, q ∈ L w := by
      intro w hw
      have hpos := hLpositive w hw
      obtain ⟨r, hrL⟩ := Finset.card_pos.mp (by omega : 0 < (L w).card)
      have hrN := hLsub w hw hrL
      have hrNotT : r ∉ T := by
        intro hrT
        exact (Finset.disjoint_left.mp (hLdisj w hw) hrT hrL).elim
      have hqr := paper9_unique_extra_S_neighbor G hTneighbors hTcard hqN hrN
        hqNotT hrNotT hsle
      simpa [hqr] using hrL
    have hLeq : ∀ w ∈ T, L w = {q} := by
      intro w hw
      have hqW := hqInAll w hw
      apply Finset.ext
      intro r
      constructor
      · intro hr
        have hrNotT : r ∉ T := by
          intro hrT
          exact (Finset.disjoint_left.mp (hLdisj w hw) hrT hr).elim
        have hrN := hLsub w hw hr
        have hqr := paper9_unique_extra_S_neighbor G hTneighbors hTcard hqN hrN
          hqNotT hrNotT hsle
        simp [hqr]
      · intro hr
        have hrEq : r = q := Finset.mem_singleton.mp hr
        simpa [hrEq] using hqW
    have hwitness : ∀ w ∈ T, ∃ z, z ∈ Z0Part G D ∧
        z ∈ supportX G D w ∧ neighborhoodIn G D q = {u, z} := by
      intro w hw
      have hX : supportX G D w ⊆ Z0Part G D := by
        intro z hz
        exact (mem_supportX G D w z).mp hz |>.1
      have hqW : q ∈ L w := hqInAll w hw
      obtain ⟨z, hzSupport, hzY, hN⟩ := paper9_shared_support_witness_agrees
        (G := G) huB hX₀ hX hqL₀ hqW
      exact ⟨z, (mem_supportX G D w z).mp hzY |>.1, hzY, hN⟩
    obtain ⟨z, hzZ0, hzSupport₀, hN⟩ := hwitness w₀ hw₀
    have hzSupportAll : ∀ w ∈ T, z ∈ supportX G D w := by
      intro w hw
      obtain ⟨z', hzZ0', hzSupport', hN'⟩ := hwitness w hw
      have hzNeU : z ≠ u := by
        intro hEq
        subst z
        exact (Finset.disjoint_left.mp (Z0_disjoint_B G) hzZ0 huB).elim
      have hpair : z ∈ ({u, z'} : Finset V) := by rw [← hN']; rw [hN]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpair
      rcases hpair with hzu | hzz
      · exact False.elim (hzNeU hzu)
      · simpa [hzz] using hzSupport'
    have hqBeta := paper9_shared_beta_eq_one G hX₀ huB hqL₀
    exact ⟨(fun w hw => (hTclass w hw).1), Or.inr
      ⟨hx0, hs3, hvertex, q, z, hLeq, hqProfile.1, hqBeta,
        hqProfile.2.2, hqCharge, hzZ0, hN, hzSupportAll⟩⟩

end C6BipartiteDomination

