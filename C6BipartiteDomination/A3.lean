/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import C6BipartiteDomination.A2

/-! # A3: Hall-deficiency exchange for an independent optimum

The paper's ambient hypothesis that the graph has no isolated vertices is
included explicitly here. It is needed to ensure that a selected vertex in an
independent dominating set has a neighbor in its complement.
-/

namespace C6BipartiteDomination

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

/-- The graph has no isolated vertices. -/
def HasNoIsolatedVertices : Prop := ∀ v, ∃ u, G.Adj v u

/-- A finite set is independent in `G`. -/
def Independent (D : Finset V) : Prop :=
  ∀ ⦃u v⦄, u ∈ D → v ∈ D → G.Adj u v → False

/-- Neighbors of `S` that lie in `T`. -/
noncomputable def neighborsIn (S T : Finset V) : Finset V := by
  classical
  exact T.filter fun w => ∃ v ∈ S, G.Adj v w

theorem mem_neighborsIn (S T : Finset V) (w : V) :
    w ∈ neighborsIn G S T ↔ w ∈ T ∧ ∃ v ∈ S, G.Adj v w := by
  classical
  simp [neighborsIn]

theorem neighborsIn_mono_left {S₁ S₂ T : Finset V} (h : S₁ ⊆ S₂) :
    neighborsIn G S₁ T ⊆ neighborsIn G S₂ T := by
  classical
  intro w hw
  rw [mem_neighborsIn] at hw ⊢
  refine ⟨hw.1, ?_⟩
  rcases hw.2 with ⟨v, hv, hadj⟩
  exact ⟨v, h hv, hadj⟩

theorem neighborsIn_mono_right {S T₁ T₂ : Finset V} (h : T₁ ⊆ T₂) :
    neighborsIn G S T₁ ⊆ neighborsIn G S T₂ := by
  classical
  intro w hw
  rw [mem_neighborsIn] at hw ⊢
  exact ⟨h hw.1, hw.2⟩

theorem neighborsIn_self_subset (S T : Finset V) :
    neighborsIn G S T ⊆ T := by
  classical
  intro w hw
  exact (mem_neighborsIn G S T w).mp hw |>.1

/-- If `D` is independent, a neighbor of one of its vertices lies outside it. -/
theorem neighbor_of_independent_outside {D : Finset V} (hD : Independent G D)
    {u v : V} (hu : u ∈ D) (hadj : G.Adj u v) : v ∉ D := by
  intro hv
  exact hD hu hv hadj

/-- A vertex in an independent dominating set has an external neighbor when
the graph has no isolated vertices. -/
theorem independent_vertex_has_external_neighbor {D : Finset V}
    (hD : Independent G D) (hNoIso : HasNoIsolatedVertices G)
    {v : V} (hv : v ∈ D) : ∃ w ∈ (Finset.univ \ D), G.Adj v w := by
  obtain ⟨w, hadj⟩ := hNoIso v
  have hw : w ∉ D := neighbor_of_independent_outside G hD hv hadj
  exact ⟨w, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hw⟩, hadj⟩

theorem neighborsIn_eq_of_dominates
    {D W : Finset V}
    (hdom : ∀ ⦃w⦄, w ∈ W → ∃ d ∈ D, G.Adj d w) :
    neighborsIn G D W = W := by
  classical
  ext w
  constructor
  · intro hw
    exact neighborsIn_self_subset G D W hw
  · intro hw
    rw [mem_neighborsIn]
    obtain ⟨d, hd, hadj⟩ := hdom hw
    exact ⟨hw, d, hd, hadj⟩

theorem exists_minimal_deficient_subset
    (D W : Finset V) (hCover : neighborsIn G D W = W)
    (hlarge : W.card < D.card) :
    ∃ X ∈ D.powerset,
      (neighborsIn G X W).card < X.card ∧
      ∀ Y, Y ⊆ X → (neighborsIn G Y W).card < Y.card → X.card ≤ Y.card := by
  classical
  let bad := D.powerset.filter fun X => (neighborsIn G X W).card < X.card
  have hDmem : D ∈ D.powerset := Finset.mem_powerset.mpr (by intro _ hx; exact hx)
  have hDneighbors : neighborsIn G D W = W := hCover
  have hbad : D ∈ bad := by
    simp only [bad, Finset.mem_filter]
    exact ⟨hDmem, by simpa [hDneighbors] using hlarge⟩
  obtain ⟨X, hXbad, hmin⟩ := Finset.exists_min_image bad Finset.card ⟨D, hbad⟩
  refine ⟨X, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hXbad).1
  · exact (Finset.mem_filter.mp hXbad).2
  · intro Y hYX hYbad
    have hYpow : Y ∈ D.powerset := Finset.mem_powerset.mpr (hYX.trans (Finset.mem_powerset.mp ((Finset.mem_filter.mp hXbad).1)))
    have hYmem : Y ∈ bad := Finset.mem_filter.mpr ⟨hYpow, hYbad⟩
    exact hmin Y hYmem

theorem minimal_deficient_card_ge_two
    {D X : Finset V} (hXsub : X ⊆ D)
    (hDind : Independent G D) (hNoIso : HasNoIsolatedVertices G)
    (hdef : (neighborsIn G X (Finset.univ \ D)).card < X.card) :
    2 ≤ X.card := by
  classical
  have hpos : 0 < X.card := Nat.zero_lt_of_lt hdef
  by_contra hnot
  have hsmall : X.card = 0 ∨ X.card = 1 := by omega
  rcases hsmall with hzero | hone
  · have : X = ∅ := Finset.card_eq_zero.mp hzero
    simp [this] at hdef
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hone
    have hxX : x ∈ X := by rw [hx]; simp
    have hxD : x ∈ D := hXsub hxX
    obtain ⟨w, hw, hadj⟩ := independent_vertex_has_external_neighbor G hDind hNoIso hxD
    have hneigh : w ∈ neighborsIn G X (Finset.univ \ D) := by
      rw [mem_neighborsIn]
      refine ⟨hw, ?_⟩
      exact ⟨x, by simpa [hx], hadj⟩
    have hcard : 0 < (neighborsIn G X (Finset.univ \ D)).card :=
      Finset.card_pos.mpr ⟨w, hneigh⟩
    rw [hone] at hdef
    omega

theorem minimal_deficient_neighbor_card
    {X W : Finset V}
    (hXne : X.Nonempty)
    (hdef : (neighborsIn G X W).card < X.card)
    (hmin : ∀ Y, Y ⊆ X → (neighborsIn G Y W).card < Y.card → X.card ≤ Y.card) :
    (neighborsIn G X W).card + 1 = X.card := by
  classical
  obtain ⟨x, hx⟩ := hXne
  have hsub : X.erase x ⊆ X := Finset.erase_subset x X
  have hnotdef : ¬ (neighborsIn G (X.erase x) W).card < (X.erase x).card := by
    intro hbad
    have hcard := hmin (X.erase x) hsub hbad
    have hlt : (X.erase x).card < X.card := Finset.card_erase_lt_of_mem hx
    omega
  have hlow : (X.erase x).card ≤ (neighborsIn G (X.erase x) W).card := by omega
  have hmono : neighborsIn G (X.erase x) W ⊆ neighborsIn G X W :=
    neighborsIn_mono_left G (Finset.erase_subset x X)
  have hlow' : (X.erase x).card ≤ (neighborsIn G X W).card :=
    le_trans hlow (Finset.card_le_card hmono)
  have herase : (X.erase x).card + 1 = X.card := by
    rw [Finset.card_erase_of_mem hx]
    omega
  omega

/-- A cardinality-maximal independent subset of `A` is maximal by inclusion,
so it dominates every vertex of `A` that it does not contain. -/
theorem exists_maximal_independent_subset (A : Finset V) :
    ∃ I ⊆ A, Independent G I ∧
      ∀ ⦃a⦄, a ∈ A → a ∉ I → ∃ i ∈ I, G.Adj i a := by
  classical
  let indeps := A.powerset.filter (Independent G)
  have hempty : (∅ : Finset V) ∈ indeps := by
    simp [indeps, Independent]
  obtain ⟨I, hI, hmax⟩ := Finset.exists_max_image indeps Finset.card ⟨∅, hempty⟩
  have hIsub : I ⊆ A := Finset.mem_powerset.mp (Finset.mem_filter.mp hI).1
  have hIind : Independent G I := (Finset.mem_filter.mp hI).2
  refine ⟨I, hIsub, hIind, ?_⟩
  intro a ha haI
  by_contra hno
  push Not at hno
  have hinsertSub : insert a I ⊆ A := by
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hxI
    · exact ha
    · exact hIsub hxI
  have hinsertInd : Independent G (insert a I) := by
    intro u v hu hv hadj
    simp only [Finset.mem_insert] at hu hv
    rcases hu with rfl | huI <;> rcases hv with rfl | hvI
    · exact G.irrefl hadj
    · exact (hno v hvI) hadj.symm
    · exact (hno u huI) hadj
    · exact hIind huI hvI hadj
  have hinsertMem : insert a I ∈ indeps := by
    simp [indeps, hinsertSub, hinsertInd]
  have hle := hmax (insert a I) hinsertMem
  have hlt : I.card < (insert a I).card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_insert a I, by
    intro heq
    have : a ∈ insert a I := by simp
    rw [← heq] at this
    exact haI this
  ⟩)
  omega

theorem minimal_deficient_subset_bound
    {X W S : Finset V}
    (hAcard : (neighborsIn G X W).card + 1 = X.card)
    (hmin : ∀ Y, Y ⊆ X → (neighborsIn G Y W).card < Y.card → X.card ≤ Y.card)
    (hS : S ⊆ neighborsIn G X W) (hSne : S.Nonempty) :
    (neighborsIn G S X).card ≥ S.card + 1 := by
  classical
  let T := neighborsIn G S X
  let Y := X \ T
  have hTsub : T ⊆ X := by
    exact neighborsIn_self_subset G S X
  have hTne : T.Nonempty := by
    obtain ⟨s, hs⟩ := hSne
    have hsA : s ∈ neighborsIn G X W := hS hs
    obtain ⟨w, hwX, hAdj⟩ := (mem_neighborsIn G X W s).mp hsA |>.2
    refine ⟨w, ?_⟩
    rw [mem_neighborsIn]
    exact ⟨hwX, s, hs, hAdj.symm⟩
  have hYsub : Y ⊆ X := Finset.sdiff_subset
  have hYcard : Y.card + T.card = X.card := by
    dsimp [Y]
    exact Finset.card_sdiff_add_card_eq_card hTsub
  have hYlt : Y.card < X.card := by
    have hTpos : 0 < T.card := Finset.card_pos.mpr hTne
    omega
  have hYnotbad : ¬ (neighborsIn G Y W).card < Y.card := by
    intro hbad
    have := hmin Y hYsub hbad
    omega
  have hYdom : Y.card ≤ (neighborsIn G Y W).card := by omega
  have hNWsub : neighborsIn G Y W ⊆ (neighborsIn G X W) \ S := by
    intro w hw
    rw [mem_neighborsIn] at hw
    rcases hw.2 with ⟨y, hy, hAdj⟩
    have hyX : y ∈ X := hYsub hy
    simp only [Finset.mem_sdiff]
    refine ⟨?_, ?_⟩
    · rw [mem_neighborsIn]
      exact ⟨hw.1, y, hyX, hAdj⟩
    intro hws
    have hyT : y ∈ T := by
      dsimp [T]
      rw [mem_neighborsIn]
      exact ⟨hyX, w, hws, hAdj.symm⟩
    have hyNotT : y ∉ T := (Finset.mem_sdiff.mp hy).2
    exact hyNotT hyT
  have hSsub : S ⊆ neighborsIn G X W := hS
  have hNWcard : (neighborsIn G Y W).card ≤ ((neighborsIn G X W) \ S).card :=
    Finset.card_le_card hNWsub
  have hAminus : ((neighborsIn G X W) \ S).card + S.card = (neighborsIn G X W).card :=
    Finset.card_sdiff_add_card_eq_card hSsub
  dsimp [T] at hYcard ⊢
  omega

/-- Proposition 4.1 (the local Hall-deficiency step). The no-isolated-vertices
hypothesis is the ambient assumption of the paper; it ensures every selected
vertex has an external neighbor. -/
theorem proposition_4_1
    {D : Finset V}
    (hD : IsBipartiteDominatingSet G D)
    (hmin : ∀ E, IsBipartiteDominatingSet G E → D.card ≤ E.card)
    (hDind : Independent G D)
    (hNoIso : HasNoIsolatedVertices G) :
    D.card ≤ (Finset.univ \ D).card := by
  classical
  by_contra hnot
  have hlarge : (Finset.univ \ D).card < D.card := by omega
  let W := Finset.univ \ D
  have hcover : neighborsIn G D W = W := by
    apply neighborsIn_eq_of_dominates G
    intro w hw
    have hwD : w ∉ D := (Finset.mem_sdiff.mp (show w ∈ Finset.univ \ D from hw)).2
    exact hD.1 hwD
  obtain ⟨X, hXsub, hXdef, hXmin⟩ :=
    exists_minimal_deficient_subset G D W hcover (by simpa [W] using hlarge)
  have hXD : X ⊆ D := Finset.mem_powerset.mp hXsub
  have hXcard : 2 ≤ X.card := by
    apply minimal_deficient_card_ge_two G hXD hDind hNoIso
    simpa [W] using hXdef
  have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
  have hAcard : (neighborsIn G X W).card + 1 = X.card :=
    minimal_deficient_neighbor_card G hXne hXdef hXmin
  let A := neighborsIn G X W
  obtain ⟨I, hIA, hIind, hImax⟩ := exists_maximal_independent_subset G A
  have hAne : A.Nonempty := Finset.card_pos.mp (by dsimp [A]; omega)
  have hIne : I.Nonempty := by
    by_contra h
    push Not at h
    have hIeq : I = ∅ := h
    obtain ⟨a, ha⟩ := hAne
    obtain ⟨i, hi, _⟩ := hImax ha (by simp [hIeq])
    simp [hIeq] at hi
  have hNbound : (neighborsIn G I X).card ≥ I.card + 1 := by
    apply minimal_deficient_subset_bound G hAcard hXmin
    · intro i hi
      simpa [A] using hIA hi
    · exact hIne
  let NXI := neighborsIn G I X
  let D' := (D \ NXI) ∪ I
  have hI_W : I ⊆ W := by
    intro i hi
    have hiA : i ∈ A := hIA hi
    have hiA' : i ∈ neighborsIn G X W := by simpa [A] using hiA
    exact (mem_neighborsIn G X W i).mp hiA' |>.1
  have hI_Ddisj : Disjoint (D \ NXI) I := by
    refine Finset.disjoint_left.mpr ?_
    intro v hvD' hvI
    have hvD : v ∈ D := (Finset.mem_sdiff.mp hvD').1
    have hvW : v ∈ W := hI_W hvI
    exact (Finset.mem_sdiff.mp hvW).2 hvD
  have hD'dom : Dominates G D' := by
    intro v hvD'
    by_cases hvD : v ∈ D
    · have hvN : v ∈ NXI := by
        by_contra hn
        apply hvD'
        exact Finset.mem_union_left I (Finset.mem_sdiff.mpr ⟨hvD, hn⟩)
      obtain ⟨i, hi, hadj⟩ := (mem_neighborsIn G I X v).mp (by simpa [NXI] using hvN) |>.2
      exact ⟨i, Finset.mem_union_right (D \ NXI) hi, hadj⟩
    · obtain ⟨d, hd, hAdj⟩ := hD.1 hvD
      by_cases hvA : v ∈ A
      · have hvI : v ∉ I := by
          intro hvI
          exact hvD' (Finset.mem_union_right (D \ NXI) hvI)
        obtain ⟨i, hi, hiv⟩ := hImax hvA hvI
        exact ⟨i, Finset.mem_union_right (D \ NXI) hi, hiv⟩
      · have hdX : d ∉ NXI := by
          intro hdN
          have hdX' : d ∈ X := neighborsIn_self_subset G I X (by simpa [NXI] using hdN)
          have hvW : v ∈ W := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvD⟩
          have hvA' : v ∈ neighborsIn G X W := (mem_neighborsIn G X W v).mpr ⟨hvW, d, hdX', hAdj⟩
          exact hvA (by simpa [A] using hvA')
        exact ⟨d, Finset.mem_union_left I (Finset.mem_sdiff.mpr ⟨hd, hdX⟩), hAdj⟩
  have hD'bip : IsBipartiteOn G D' := by
    refine ⟨fun v => v ∈ I, ?_⟩
    intro u v hu hv hAdj
    rcases Finset.mem_union.mp hu with huD | huI
    · rcases Finset.mem_union.mp hv with hvD | hvI
      · exact (hDind (Finset.mem_sdiff.mp huD).1 (Finset.mem_sdiff.mp hvD).1 hAdj).elim
      ·
        have huW : u ∉ I := by
          intro huI
          have huD' := (Finset.mem_sdiff.mp huD).1
          exact (Finset.mem_sdiff.mp (hI_W huI)).2 huD'
        simp [huW, hvI]
    · rcases Finset.mem_union.mp hv with hvD | hvI
      · have hvW : v ∉ I := by
          intro hvI
          exact (Finset.mem_sdiff.mp (hI_W hvI)).2 (Finset.mem_sdiff.mp hvD).1
        simp [huI, hvW]
      · exact (hIind huI hvI hAdj).elim
  have hD' : IsBipartiteDominatingSet G D' := ⟨hD'dom, hD'bip⟩
  have hmin' := hmin D' hD'
  have hcardD' : D'.card = D.card - NXI.card + I.card := by
    dsimp [D']
    rw [Finset.card_union_of_disjoint hI_Ddisj,
      Finset.card_sdiff_of_subset (show NXI ⊆ D from fun x hx =>
        hXD (neighborsIn_self_subset G I X (by simpa [NXI] using hx)))]
  rw [hcardD'] at hmin'
  have hNXIle : NXI.card ≤ D.card := Finset.card_le_card (show NXI ⊆ D from fun x hx =>
    hXD (neighborsIn_self_subset G I X (by simpa [NXI] using hx)))
  have hsubadd : D.card - NXI.card + NXI.card = D.card := Nat.sub_add_cancel hNXIle
  have hNbound' : I.card + 1 ≤ NXI.card := by simpa [NXI] using hNbound
  have hstrict : D.card - NXI.card + I.card < D.card := by omega
  omega

end C6BipartiteDomination

