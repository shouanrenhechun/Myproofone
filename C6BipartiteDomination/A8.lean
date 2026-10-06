/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import C6BipartiteDomination.A7

/-! # A8: chosen repair vertices -/

namespace C6BipartiteDomination

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

/-- `u` repairs `w` when deleting `u` from `B` permits `w` to be added while
preserving bipartiteness. -/
def IsRepairVertex (D : Finset V) (w u : V) : Prop :=
  u ∈ BPart G D ∧ G.Adj w u ∧
    IsBipartiteOn G ((BPart G D).erase u ∪ {w})

/-- The only repair edges used downstream: an explicit chosen finite set of
`B`-neighbors, together with the fact that every chosen edge is a legal
repair pair. -/
def ChosenRepairRelation (D : Finset V) (w : V) (R : Finset V) (u : V) : Prop :=
  u ∈ R ∧ IsRepairVertex G D w u

/-- A fixed coloring of a bipartite base extends when all remaining neighbors
of the new vertex have one color. -/
theorem bipartite_add_of_uniform_neighbors
    {B S : Finset V} {w : V}
    (hSB : S ⊆ B) (hwS : w ∉ S)
    (c : V → Bool)
    (hc : ∀ ⦃u v⦄, u ∈ B → v ∈ B → G.Adj u v → c u ≠ c v)
    (c₀ : Bool)
    (huniform : ∀ v ∈ S, G.Adj w v → c v = c₀) :
    IsBipartiteOn G (S ∪ {w}) := by
  classical
  refine ⟨fun v => if v = w then !c₀ else c v, ?_⟩
  intro u v hu hv hadj
  rcases Finset.mem_union.mp hu with huS | huW
  · rcases Finset.mem_union.mp hv with hvS | hvW
    · have huNe : u ≠ w := fun h => hwS (h ▸ huS)
      have hvNe : v ≠ w := fun h => hwS (h ▸ hvS)
      simpa [huNe, hvNe] using hc (hSB huS) (hSB hvS) hadj
    · have hvEq : v = w := Finset.mem_singleton.mp hvW
      subst v
      have huNe : u ≠ w := fun h => hwS (h ▸ huS)
      have hc₀ := huniform u huS hadj.symm
      simp [huNe, hc₀]
  · have huEq : u = w := Finset.mem_singleton.mp huW
    subst u
    rcases Finset.mem_union.mp hv with hvS | hvW
    · have hvNe : v ≠ w := fun h => hwS (h ▸ hvS)
      have hc₀ := huniform v hvS hadj
      simp [hvNe, hc₀]
    · have hvEq : v = w := Finset.mem_singleton.mp hvW
      subst v
      exact (G.irrefl hadj).elim

/-- Lemma 8.1, in an equivalent coloring formulation: adding `w` preserves
bipartiteness exactly when the coloring of `B` can be chosen so every
`B`-neighbor of `w` lies on one side. Independent components may be flipped
separately to obtain such a coloring. -/
theorem lemma_8_1_add_vertex_criterion
    {B : Finset V} {w : V} (hwB : w ∉ B) :
    IsBipartiteOn G (B ∪ {w}) ↔
      ∃ c : V → Bool, ∃ c₀ : Bool,
        (∀ ⦃u v⦄, u ∈ B → v ∈ B → G.Adj u v → c u ≠ c v) ∧
        ∀ v ∈ B, G.Adj w v → c v = c₀ := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, !c w, ?_⟩
    constructor
    · intro u v hu hv hadj
      exact hc (Finset.mem_union_left _ hu) (Finset.mem_union_left _ hv) hadj
    · intro v hv hadj
      have hne : c v ≠ c w := hc (Finset.mem_union_left _ hv)
        (Finset.mem_union_right B (Finset.mem_singleton_self w)) hadj.symm
      cases hcv : c v <;> cases hcw : c w <;> simp_all
  · rintro ⟨c, c₀, hc, huniform⟩
    exact bipartite_add_of_uniform_neighbors G
      (B := B) (S := B) Finset.Subset.rfl hwB c hc c₀ huniform

theorem repair_of_uniform_remaining_neighbors
    {D : Finset V} {w u : V}
    (hwD : w ∉ D) (hu : u ∈ BPart G D) (hwu : G.Adj w u)
    (c : V → Bool)
    (hc : ∀ ⦃x y⦄, x ∈ BPart G D → y ∈ BPart G D →
      G.Adj x y → c x ≠ c y)
    (c₀ : Bool)
    (huniform : ∀ v ∈ (BPart G D).erase u, G.Adj w v → c v = c₀) :
    IsRepairVertex G D w u := by
  have hwErase : w ∉ (BPart G D).erase u := by
    intro hw
    exact hwD ((mem_BPart G D w).mp (Finset.erase_subset u _ hw) |>.1)
  have hbip := bipartite_add_of_uniform_neighbors G
    (Finset.erase_subset u (BPart G D)) hwErase c hc c₀ huniform
  exact ⟨hu, hwu, hbip⟩

theorem chosen_repairs_beta_two
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    {w : V} (hw : w ∈ SPart G D)
    (hk : 2 ≤ kCharge G D w) (hβ : betaCharge G D w = 2) :
    ∃ R : Finset V, R.card = 2 ∧
      ∀ u ∈ R, IsRepairVertex G D w u := by
  classical
  let R := supportB G D w
  have hcard : R.card = 2 := by
    change (supportB G D w).card = 2
    rw [supportB_card]
    exact hβ
  obtain ⟨a, b, hab, hR⟩ := Finset.card_eq_two.mp hcard
  have haR : a ∈ R := by rw [hR]; simp
  have hbR : b ∈ R := by rw [hR]; simp
  have haInfo := Finset.mem_filter.mp (show a ∈ supportB G D w by simpa [R] using haR)
  have hbInfo := Finset.mem_filter.mp (show b ∈ supportB G D w by simpa [R] using hbR)
  have hwD : w ∉ D := by
    exact (mem_WBPart G D w).mp ((mem_SPart G D w).mp hw |>.1) |>.1
  have hBD : BPart G D ⊆ D := by
    intro v hv
    exact (mem_BPart G D v).mp hv |>.1
  obtain ⟨c, hc⟩ := bipartiteOn_subset G hBD hCan.1.2
  have hnot := lemma_7_1_odd_cycle G hCan hw hk
  have habColor : c a ≠ c b := by
    intro heq
    have huniform : ∀ v ∈ BPart G D, G.Adj w v → c v = c a := by
      intro v hv hadj
      have hvR : v ∈ R := by
        change v ∈ (BPart G D).filter (fun x => G.Adj w x)
        exact Finset.mem_filter.mpr ⟨hv, hadj⟩
      change v ∈ supportB G D w at hvR
      have hR' : supportB G D w = {a, b} := by simpa [R] using hR
      rw [hR'] at hvR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvR
      rcases hvR with h | h
      · exact h ▸ rfl
      · exact h ▸ heq.symm
    have hbase := bipartite_add_of_uniform_neighbors G
      (B := BPart G D) (S := BPart G D) (w := w)
      Finset.Subset.rfl (by
        intro hwB
        exact hwD ((mem_BPart G D w).mp hwB |>.1)) c hc (c a) huniform
    exact hnot hbase
  have hRepairA : IsRepairVertex G D w a := by
    apply repair_of_uniform_remaining_neighbors G hwD haInfo.1 haInfo.2 c hc (c b)
    intro v hv hadj
    have hvR : v ∈ R := by
      change v ∈ (BPart G D).filter (fun x => G.Adj w x)
      exact Finset.mem_filter.mpr ⟨Finset.erase_subset a _ hv, hadj⟩
    change v ∈ supportB G D w at hvR
    have hR' : supportB G D w = {a, b} := by simpa [R] using hR
    rw [hR'] at hvR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvR
    rcases hvR with h | h
    · exact False.elim ((Finset.mem_erase.mp hv).1 h)
    · exact h ▸ rfl
  have hRepairB : IsRepairVertex G D w b := by
    apply repair_of_uniform_remaining_neighbors G hwD hbInfo.1 hbInfo.2 c hc (c a)
    intro v hv hadj
    have hvR : v ∈ R := by
      change v ∈ (BPart G D).filter (fun x => G.Adj w x)
      exact Finset.mem_filter.mpr ⟨Finset.erase_subset b _ hv, hadj⟩
    rw [hR] at hvR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvR
    rcases hvR with h | h
    · exact h ▸ rfl
    · exact False.elim ((Finset.mem_erase.mp hv).1 h)
  refine ⟨R, hcard, ?_⟩
  intro u hu
  have hu' : u = a ∨ u = b := by
    rw [hR] at hu
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hu
  rcases hu' with rfl | rfl
  · exact hRepairA
  · exact hRepairB

theorem two_bool_values_have_equal_pair (a b d : Bool) :
    a = b ∨ a = d ∨ b = d := by
  cases a <;> cases b <;> cases d <;> simp

theorem chosen_repair_beta_three
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    {w : V} (hw : w ∈ SPart G D)
    (hβ : betaCharge G D w = 3) :
    ∃ u, IsRepairVertex G D w u := by
  classical
  let R := supportB G D w
  have hcard : R.card = 3 := by
    change (supportB G D w).card = 3
    rw [supportB_card, hβ]
  obtain ⟨a, b, d, hab, had, hbd, hR⟩ := Finset.card_eq_three.mp hcard
  have hRsupport : supportB G D w = {a, b, d} := by simpa [R] using hR
  have haR : a ∈ R := by rw [hR]; simp
  have hbR : b ∈ R := by rw [hR]; simp
  have hdR : d ∈ R := by rw [hR]; simp
  have haInfo := Finset.mem_filter.mp (show a ∈ supportB G D w by simpa [R] using haR)
  have hbInfo := Finset.mem_filter.mp (show b ∈ supportB G D w by simpa [R] using hbR)
  have hdInfo := Finset.mem_filter.mp (show d ∈ supportB G D w by simpa [R] using hdR)
  have hwD : w ∉ D := by
    exact (mem_WBPart G D w).mp ((mem_SPart G D w).mp hw |>.1) |>.1
  have hBD : BPart G D ⊆ D := by
    intro v hv
    exact (mem_BPart G D v).mp hv |>.1
  obtain ⟨c, hc⟩ := bipartiteOn_subset G hBD hCan.1.2
  have hequal := two_bool_values_have_equal_pair (c a) (c b) (c d)
  rcases hequal with habc | hacd | hbcd
  · refine ⟨d, ?_⟩
    apply repair_of_uniform_remaining_neighbors G hwD hdInfo.1 hdInfo.2 c hc (c a)
    intro v hv hadj
    have hvR : v ∈ R := by
      change v ∈ (BPart G D).filter (fun x => G.Adj w x)
      exact Finset.mem_filter.mpr ⟨Finset.erase_subset d _ hv, hadj⟩
    change v ∈ supportB G D w at hvR
    rw [hRsupport] at hvR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvR
    rcases hvR with h | h | h
    · exact h ▸ rfl
    · exact h ▸ habc.symm
    · exact False.elim ((Finset.mem_erase.mp hv).1 h)
  · refine ⟨b, ?_⟩
    apply repair_of_uniform_remaining_neighbors G hwD hbInfo.1 hbInfo.2 c hc (c a)
    intro v hv hadj
    have hvR : v ∈ R := by
      change v ∈ (BPart G D).filter (fun x => G.Adj w x)
      exact Finset.mem_filter.mpr ⟨Finset.erase_subset b _ hv, hadj⟩
    change v ∈ supportB G D w at hvR
    rw [hRsupport] at hvR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvR
    rcases hvR with h | h | h
    · exact h ▸ rfl
    · exact False.elim ((Finset.mem_erase.mp hv).1 h)
    · exact h ▸ hacd.symm
  · refine ⟨a, ?_⟩
    apply repair_of_uniform_remaining_neighbors G hwD haInfo.1 haInfo.2 c hc (c b)
    intro v hv hadj
    have hvR : v ∈ R := by
      change v ∈ (BPart G D).filter (fun x => G.Adj w x)
      exact Finset.mem_filter.mpr ⟨Finset.erase_subset a _ hv, hadj⟩
    change v ∈ supportB G D w at hvR
    rw [hRsupport] at hvR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvR
    rcases hvR with h | h | h
    · exact False.elim ((Finset.mem_erase.mp hv).1 h)
    · exact h ▸ rfl
    · exact h ▸ hbcd.symm

theorem chosen_repair_set
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {w : V} (hw : w ∈ SPart G D)
    (ha : externalCharge G D w < 0) :
    ∃ R : Finset V,
      (∀ u, ChosenRepairRelation G D w R u → IsRepairVertex G D w u) ∧
      ((kCharge G D w = 3 ∧ R.card = 2) ∨
       (kCharge G D w = 4 ∧ R.card = 2) ∨
       (kCharge G D w = 3 ∧ R.card = 1)) := by
  classical
  rcases lemma_7_2_negative_charge_classification G hCan hmax hw ha with
    ⟨hk, hβ⟩ | ⟨hk, hβ⟩ | ⟨hk, hβ⟩
  · obtain ⟨R, hcard, hR⟩ := chosen_repairs_beta_two G hCan hw (by omega) hβ
    refine ⟨R, ?_, Or.inl ⟨hk, hcard⟩⟩
    intro u hChosen
    exact hR u hChosen.1
  · obtain ⟨u, hu⟩ := chosen_repair_beta_three G hCan hw hβ
    refine ⟨{u}, ?_, Or.inr (Or.inr ⟨hk, by simp⟩)⟩
    intro v hChosen
    have hEq : v = u := Finset.mem_singleton.mp hChosen.1
    simpa [hEq] using hu
  · obtain ⟨R, hcard, hR⟩ := chosen_repairs_beta_two G hCan hw (by omega) hβ
    refine ⟨R, ?_, Or.inr (Or.inl ⟨hk, hcard⟩)⟩
    intro u hChosen
    exact hR u hChosen.1

end C6BipartiteDomination

