/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import C6BipartiteDomination.PaperSection11_2

/-! # Main theorem and sharpness

This module will close the induced-subgraph induction, establish the extremal
corona example, and identify the paper's supremum constant.
-/

namespace C6BipartiteDomination

open Finset
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

noncomputable def liftFinsetToSubtype (S E : Finset V)
    (hES : E ⊆ S) : Finset {v // v ∈ S} := by
  classical
  exact E.attach.image fun x => (⟨x.1, hES x.2⟩ : {v // v ∈ S})

theorem mem_liftFinsetToSubtype {S E : Finset V} (hES : E ⊆ S)
    (x : {v // v ∈ S}) :
    x ∈ liftFinsetToSubtype S E hES ↔ x.1 ∈ E := by
  classical
  change x ∈ E.attach.image
      (fun y => (⟨y.1, hES y.2⟩ : {v // v ∈ S})) ↔ x.1 ∈ E
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, hEq⟩
    exact (congrArg Subtype.val hEq) ▸ y.2
  · intro hx
    refine ⟨⟨x.1, hx⟩, Finset.mem_attach _ _, ?_⟩
    exact Subtype.ext rfl

theorem card_liftFinsetToSubtype {S E : Finset V} (hES : E ⊆ S) :
    (liftFinsetToSubtype S E hES).card = E.card := by
  classical
  unfold liftFinsetToSubtype
  have hinj : Function.Injective
      (fun x : {v // v ∈ E} => (⟨x.1, hES x.2⟩ : {v // v ∈ S})) := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : {v // v ∈ S} => z.1) h
  rw [Finset.card_image_of_injective E.attach hinj]
  simp

noncomputable def projectFinsetFromSubtype {S : Finset V}
    (F : Finset {v // v ∈ S}) : Finset V := by
  classical
  exact F.image Subtype.val

theorem mem_projectFinsetFromSubtype {S : Finset V}
    (F : Finset {v // v ∈ S}) (v : V) :
    v ∈ projectFinsetFromSubtype (S := S) F ↔
      ∃ x ∈ F, x.1 = v := by
  classical
  simp only [projectFinsetFromSubtype, Finset.mem_image]

theorem card_projectFinsetFromSubtype {S : Finset V}
    (F : Finset {v // v ∈ S}) :
    (projectFinsetFromSubtype (S := S) F).card = F.card := by
  classical
  unfold projectFinsetFromSubtype
  have hinj : Function.Injective (fun x : {v // v ∈ S} => x.1) := by
    intro x y h
    exact Subtype.ext h
  exact Finset.card_image_of_injective F hinj

theorem degreeTo_induce_eq_degreeWithinSet (S : Finset V)
    (x : {v // v ∈ S}) :
    degreeTo (G.induce (S : Set V)) Finset.univ x =
      degreeWithinSet G S x.1 := by
  classical
  let H := G.induce (S : Set V)
  let A := Finset.univ.filter fun y : {v // v ∈ S} => H.Adj x y
  let f : {v // v ∈ S} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : A.map f = S.filter fun y => G.Adj x.1 y := by
    ext y
    simp [A, f, H, SimpleGraph.induce, and_comm]
  have hcard : A.card = (S.filter fun y => G.Adj x.1 y).card := by
    calc
      A.card = (A.map f).card := by simp
      _ = (S.filter fun y => G.Adj x.1 y).card := by rw [hmap]
  simpa [degreeTo, degreeWithinSet, A, H] using hcard

theorem minimumOn_lift_toSubtype {S E : Finset V}
    (hE : MinimumBipartiteDominatingOn G S E) :
    MinimumBipartiteDominatingSet (G.induce (S : Set V))
      (liftFinsetToSubtype S E hE.1.1) := by
  classical
  let H := G.induce (S : Set V)
  let E' := liftFinsetToSubtype S E hE.1.1
  refine ⟨?_, ?_⟩
  · constructor
    · intro x hx
      have hxNotE : x.1 ∉ E := by
        intro hxE
        exact hx ((mem_liftFinsetToSubtype hE.1.1 x).2 hxE)
      obtain ⟨y, hyE, hyx⟩ := hE.1.2.1 x.2 hxNotE
      refine ⟨⟨y, hE.1.1 hyE⟩, ?_, ?_⟩
      · exact (mem_liftFinsetToSubtype hE.1.1 _).2 hyE
      · simpa [H, SimpleGraph.induce] using hyx
    · obtain ⟨c, hc⟩ := hE.1.2.2
      refine ⟨fun x => c x.1, ?_⟩
      intro x y hx hy hadj
      apply hc
      · exact (mem_liftFinsetToSubtype hE.1.1 x).mp hx
      · exact (mem_liftFinsetToSubtype hE.1.1 y).mp hy
      · simpa [H, SimpleGraph.induce] using hadj
  · intro F hF
    let F' := projectFinsetFromSubtype (S := S) F
    have hFsub : F' ⊆ S := by
      intro v hv
      obtain ⟨x, hx, rfl⟩ := (mem_projectFinsetFromSubtype (S := S) F v).mp hv
      exact x.2
    have hFdom : ∀ ⦃v⦄, v ∈ S → v ∉ F' →
        ∃ y ∈ F', G.Adj y v := by
      intro v hvS hvNot
      let x : {v // v ∈ S} := ⟨v, hvS⟩
      have hxNot : x ∉ F := by
        intro hx
        apply hvNot
        apply (mem_projectFinsetFromSubtype (S := S) F v).mpr
        exact ⟨x, hx, rfl⟩
      obtain ⟨y, hyF, hyx⟩ := hF.1 hxNot
      refine ⟨y.1, ?_, ?_⟩
      · exact (mem_projectFinsetFromSubtype (S := S) F y.1).mpr ⟨y, hyF, rfl⟩
      · simpa [H, SimpleGraph.induce] using hyx
    have hFbip : IsBipartiteOn G F' := by
      obtain ⟨c, hc⟩ := hF.2
      refine ⟨fun v => if hv : v ∈ S then c ⟨v, hv⟩ else false, ?_⟩
      intro a b ha hb hadj
      obtain ⟨xa, hxa, rfl⟩ :=
        (mem_projectFinsetFromSubtype (S := S) F a).mp ha
      obtain ⟨xb, hxb, rfl⟩ :=
        (mem_projectFinsetFromSubtype (S := S) F b).mp hb
      have hadj' : H.Adj xa xb := by
        simpa [H, SimpleGraph.induce] using hadj
      simpa using hc hxa hxb hadj'
    have hFLocal : BipartiteDominatingOn G S F' := ⟨hFsub, hFdom, hFbip⟩
    have hmin := hE.2 F' hFLocal
    have hcardE : E'.card = E.card := by
      simpa [E'] using card_liftFinsetToSubtype hE.1.1
    have hcardF : F'.card = F.card := by
      simpa [F'] using card_projectFinsetFromSubtype (S := S) F
    calc
      E'.card = E.card := hcardE
      _ ≤ F'.card := hmin
      _ = F.card := hcardF

theorem zpart_subset_selected (D : Finset V) : ZPart G D ⊆ D := by
  intro z hz
  exact (mem_ZPart G D z).mp hz |>.1

theorem bpart_zpart_partition (D : Finset V) :
    D = BPart G D ∪ ZPart G D := by
  classical
  ext v
  constructor
  · intro hvD
    by_cases hvZ : v ∈ ZPart G D
    · exact Finset.mem_union_right _ hvZ
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hvD, hvZ⟩)
  · intro hv
    rcases Finset.mem_union.mp hv with hvB | hvZ
    · exact (Finset.mem_sdiff.mp (by simpa [BPart] using hvB)).1
    · exact zpart_subset_selected G D hvZ

theorem selected_partition_card (D : Finset V) :
    D.card = (BPart G D).card + (Z0Part G D).card + (Z1Part G D).card := by
  classical
  have hBZ : Disjoint (BPart G D) (ZPart G D) := by
    rw [Finset.disjoint_left]
    intro v hvB hvZ
    exact ((Finset.mem_sdiff.mp (show v ∈ D \ ZPart G D from hvB)).2) hvZ
  have hBunion := bpart_zpart_partition G D
  calc
    D.card = (BPart G D ∪ ZPart G D).card := by rw [← hBunion]
    _ = (BPart G D).card + (ZPart G D).card :=
      Finset.card_union_of_disjoint hBZ
    _ = (BPart G D).card +
        ((Z0Part G D).card + (Z1Part G D).card) := by
      rw [ZPart_eq_Z0_union_Z1 G D]
      rw [Finset.card_union_of_disjoint (Z0_Z1_disjoint G D)]
    _ = _ := by omega

theorem outside_partition_card (D : Finset V) :
    (Finset.univ \ D).card = (W0Part G D).card + (WBPart G D).card := by
  classical
  have hdisj : Disjoint (W0Part G D) (WBPart G D) := by
    rw [Finset.disjoint_left]
    intro v hv0 hvb
    exact ((mem_WBPart G D v).mp hvb).2 hv0
  have hunion : W0Part G D ∪ WBPart G D = Finset.univ \ D := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · rintro (hv0 | hvb)
      · exact (mem_W0Part G D v).mp hv0 |>.1
      · exact (mem_WBPart G D v).mp hvb |>.1
    · intro hvD
      by_cases hv0 : v ∈ W0Part G D
      · exact Or.inl hv0
      · exact Or.inr ((mem_WBPart G D v).mpr ⟨hvD, hv0⟩)
  calc
    (Finset.univ \ D).card = (W0Part G D ∪ WBPart G D).card := by
      rw [hunion]
    _ = (W0Part G D).card + (WBPart G D).card :=
      Finset.card_union_of_disjoint hdisj

/-- Strong-induction form of the main bound; the vertex type may change to
the subtype used for a proper induced subgraph. -/
theorem main_bound_strong_induction :
    ∀ n : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V), Fintype.card V = n →
      HasNoIsolatedVertices G →
      (∀ v, degreeTo G Finset.univ v ≤ 6) →
      ∀ D, MinimumBipartiteDominatingSet G D → 15 * D.card ≤ 8 * n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro V instF instD G hcard hNoIso hmax D hmin
      classical
      obtain ⟨D₀, hCan⟩ := exists_canonical_two_level_optimum G
      have hmin₀ : MinimumBipartiteDominatingSet G D₀ :=
        ⟨hCan.1, hCan.2.1⟩
      have hsame : D.card = D₀.card := by
        exact le_antisymm (hmin.2 D₀ hmin₀.1) (hmin₀.2 D hmin.1)
      have hmaxWithin : ∀ v, degreeWithinSet G Finset.univ v ≤ 6 := by
        intro v
        simpa [degreeWithinSet, degreeTo] using hmax v
      by_cases hBne : (BPart G D₀).Nonempty
      · have hInd : ProperInducedMainBound G := by
          intro S hSproper hSno hSdeg E hE
          let H : SimpleGraph {v // v ∈ S} := G.induce (S : Set V)
          let E' := liftFinsetToSubtype S E hE.1.1
          have hcardS : Fintype.card {v // v ∈ S} = S.card := by
            classical
            simpa using Finset.card_attach S
          have hNoIsoH : HasNoIsolatedVertices H := by
            intro x
            obtain ⟨y, hyS, hadj⟩ := hSno x.1 x.2
            exact ⟨⟨y, hyS⟩, by simpa [H, SimpleGraph.induce] using hadj⟩
          have hmaxH : ∀ x, degreeTo H Finset.univ x ≤ 6 := by
            intro x
            rw [degreeTo_induce_eq_degreeWithinSet G S x]
            exact hSdeg x x.2
          have hE' : MinimumBipartiteDominatingSet H E' :=
            minimumOn_lift_toSubtype G hE
          have hsmall : S.card < n := by
            simpa [hcard] using hSproper
          have hIH := ih S.card hsmall H hcardS hNoIsoH hmaxH E' hE'
          have hEcard : E'.card = E.card :=
            card_liftFinsetToSubtype hE.1.1
          calc
            15 * E.card = 15 * E'.card := by rw [hEcard]
            _ ≤ 8 * S.card := by simpa [hcardS] using hIH
        have h5 : 8 * (W0Part G D₀).card ≥ 7 * (Z1Part G D₀).card :=
          lemma_5_2_inductive_step G hCan hBne hmaxWithin hInd
        have h11 : 8 * (WBPart G D₀).card ≥
            7 * ((BPart G D₀).card + (Z0Part G D₀).card) :=
          paper11_lemma_11_2_global_inequality G hCan hmax hNoIso
        have hDebt : 8 * (Finset.univ \ D₀).card ≥ 7 * D₀.card := by
          rw [outside_partition_card G D₀, selected_partition_card G D₀]
          omega
        have hratio := ratio_from_complement_bound hDebt
        have htotal : (Finset.univ \ D₀).card + D₀.card = n := by
          have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D₀)
          simpa [hcard] using h
        omega
      · have hDind : Independent G D₀ := by
          intro u v hu hv hadj
          have huZ : u ∈ ZPart G D₀ := by
            by_contra huZ
            have huB : u ∈ BPart G D₀ := by
              simpa [BPart] using (Finset.mem_sdiff.mpr ⟨hu, huZ⟩)
            exact hBne ⟨u, huB⟩
          have huZinfo := (mem_ZPart G D₀ u).mp huZ
          exact huZinfo.2 v hv hadj
        have hHall := proposition_4_1 G hCan.1 hCan.2.1 hDind hNoIso
        have hDebt : 8 * (Finset.univ \ D₀).card ≥ 7 * D₀.card := by
          omega
        have hratio := ratio_from_complement_bound hDebt
        have htotal : (Finset.univ \ D₀).card + D₀.card = n := by
          have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D₀)
          simpa [hcard] using h
        omega

theorem main_upper_bound_minimum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hNoIso : HasNoIsolatedVertices G)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    (D : Finset V) (hmin : MinimumBipartiteDominatingSet G D) :
    15 * D.card ≤ 8 * Fintype.card V := by
  exact main_bound_strong_induction (Fintype.card V) G rfl hNoIso hmax D hmin


end C6BipartiteDomination

