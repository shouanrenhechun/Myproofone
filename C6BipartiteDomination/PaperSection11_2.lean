/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import C6BipartiteDomination.PaperSection11

/-! # Paper section 11.2: global charge accounting

This module closes the charge identity using only the chosen repair relation.
Compensation points are grouped by their unique selected `B`-owner; no global
resource disjointness is assumed.
-/

namespace C6BipartiteDomination

open Finset BigOperators
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

noncomputable def paper11K4IncidentSupports (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (u : V) : Finset V := by
  classical
  exact (paper11K4Supports G D).filter fun w =>
    u ∈ paperChosenRepairSet G D hCan hmax w

noncomputable def paper11K4RightVertices (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) : Finset V := by
  classical
  exact (BPart G D).filter fun u =>
    (paper11K4IncidentSupports G D hCan hmax u).Nonempty

noncomputable def paper11K4Edges (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) : Finset (V × V) := by
  classical
  exact (paper11K4Supports G D).biUnion fun w =>
    (paperChosenRepairSet G D hCan hmax w).image fun u => (w, u)

noncomputable def paper11K4Compensation (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (u : V) : Finset V := by
  classical
  exact (paper11K4IncidentSupports G D hCan hmax u).biUnion fun w =>
    sharedCompensation G D (supportX G D w) u

theorem paper11K4_edge_mem {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w u : V} :
    (w, u) ∈ paper11K4Edges G D hCan hmax ↔
      w ∈ paper11K4Supports G D ∧
        u ∈ paperChosenRepairSet G D hCan hmax w := by
  classical
  simp [paper11K4Edges]

theorem paper11K4Edges_subset_product {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    paper11K4Edges G D hCan hmax ⊆
      (paper11K4Supports G D).product
        (paper11K4RightVertices G D hCan hmax) := by
  classical
  intro e he
  obtain ⟨w, hw, u, hu, heq⟩ := by
    simpa [paper11K4Edges] using Finset.mem_biUnion.mp he
  subst e
  have hwInfo := mem_paper11K4Supports G hw
  have hlegal := paperChosenRepairSet_legal G hCan hmax hwInfo.1 hwInfo.2.1 u hu
  have hInc : w ∈ paper11K4IncidentSupports G D hCan hmax u := by
    simp [paper11K4IncidentSupports, hw, hu]
  have huR : u ∈ paper11K4RightVertices G D hCan hmax := by
    rw [paper11K4RightVertices]
    simp only [Finset.mem_filter]
    exact ⟨hlegal.1, ⟨w, hInc⟩⟩
  exact Finset.mem_product.mpr ⟨hw, huR⟩

theorem paper11K4_left_degree_eq_chosen_card {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w : V}
    (hw : w ∈ paper11K4Supports G D) :
    paper11LeftDegree (paper11K4Edges G D hCan hmax)
      (paper11K4RightVertices G D hCan hmax) w =
        (paperChosenRepairSet G D hCan hmax w).card := by
  classical
  let R := paperChosenRepairSet G D hCan hmax w
  have hImage :
      (paper11K4Edges G D hCan hmax).filter (fun e => e.1 = w) =
        R.image (fun u : V => (w, u)) := by
    ext e
    rcases e with ⟨a, b⟩
    simp only [Finset.mem_filter]
    rw [paper11K4_edge_mem G hCan hmax]
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨⟨ha, hb⟩, hab⟩
      subst a
      exact ⟨b, hb, rfl⟩
    · rintro ⟨u, hu, heq⟩
      cases heq
      exact ⟨⟨hw, hu⟩, rfl⟩
  rw [paper11LeftDegree, hImage]
  have hinj : Function.Injective (fun u : V => (w, u)) := by
    intro a b hab
    exact congrArg Prod.snd hab
  simpa [R] using Finset.card_image_of_injective R hinj

theorem paper11K4_right_degree_eq_incident_card {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V} :
    paper11RightDegree (paper11K4Edges G D hCan hmax)
      (paper11K4Supports G D) u =
        (paper11K4IncidentSupports G D hCan hmax u).card := by
  classical
  let T := paper11K4IncidentSupports G D hCan hmax u
  have hImage :
      (paper11K4Edges G D hCan hmax).filter (fun e => e.2 = u) =
        T.image (fun w : V => (w, u)) := by
    ext e
    rcases e with ⟨a, b⟩
    simp only [Finset.mem_filter]
    rw [paper11K4_edge_mem G hCan hmax]
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨⟨ha, hb⟩, hbu⟩
      subst b
      exact ⟨a, Finset.mem_filter.mpr ⟨ha, hb⟩, rfl⟩
    · rintro ⟨w, hw, heq⟩
      cases heq
      have hw' : a ∈ paper11K4IncidentSupports G D hCan hmax u := by
        simpa [T] using hw
      simp only [paper11K4IncidentSupports, Finset.mem_filter] at hw'
      exact ⟨⟨hw'.1, hw'.2⟩, rfl⟩
  rw [paper11RightDegree, hImage]
  have hinj : Function.Injective (fun w : V => (w, u)) := by
    intro a b hab
    exact congrArg Prod.fst hab
  simpa [T] using Finset.card_image_of_injective T hinj

theorem paper11K4_left_degree_eq_two {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w : V}
    (hw : w ∈ paper11K4Supports G D) :
    paper11LeftDegree (paper11K4Edges G D hCan hmax)
      (paper11K4RightVertices G D hCan hmax) w = 2 := by
  rw [paper11K4_left_degree_eq_chosen_card G hCan hmax hw]
  have hwInfo := mem_paper11K4Supports G hw
  have hprofile := paper11_chosen_profile G hCan hmax hwInfo.1 hwInfo.2.1
  rcases hprofile with h | h | h <;> omega

theorem paper11K4_right_degree_eq_one {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V}
    (hu : u ∈ paper11K4RightVertices G D hCan hmax) :
    paper11RightDegree (paper11K4Edges G D hCan hmax)
      (paper11K4Supports G D) u = 1 := by
  have hB : u ∈ BPart G D := (Finset.mem_filter.mp hu).1
  have hInc : (paper11K4IncidentSupports G D hCan hmax u).Nonempty :=
    (Finset.mem_filter.mp hu).2
  obtain ⟨w, hw⟩ := hInc
  have hwInfo := mem_paper11K4Supports G (Finset.mem_filter.mp hw).1
  let T := paper11NegativeIncidentSupports G D hCan hmax u
  have hTsub : T ⊆ SPart G D := by
    intro v hv
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).1
  have hTneg : ∀ v ∈ T, externalCharge G D v < 0 := by
    intro v hv
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2
  have hTrepair : ∀ v ∈ T, u ∈ paperChosenRepairSet G D hCan hmax v := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hwT : w ∈ T := by
    simp [T, paper11NegativeIncidentSupports, paper11NegativeSupports,
      hwInfo.1, hwInfo.2.1, (Finset.mem_filter.mp hw).2]
  have hTall : T.card = 1 :=
    paper9_repair_degree_eq_one_at_k4 G hCan hmax (w₄ := w) hB T
      hTsub hTneg hTrepair hwT hwInfo.2.2
  have hT4sub : paper11K4IncidentSupports G D hCan hmax u ⊆ T := by
    intro v hv
    have hi := Finset.mem_filter.mp hv
    have info := mem_paper11K4Supports G hi.1
    simp only [T, paper11NegativeIncidentSupports, paper11NegativeSupports,
      Finset.mem_filter]
    exact ⟨⟨info.1, info.2.1⟩, hi.2⟩
  have hT4pos : 0 < (paper11K4IncidentSupports G D hCan hmax u).card :=
    Finset.card_pos.mpr ⟨w, hw⟩
  have hT4card : (paper11K4IncidentSupports G D hCan hmax u).card = 1 := by
    have := Finset.card_le_card hT4sub
    omega
  rw [paper11K4_right_degree_eq_incident_card G hCan hmax]
  exact hT4card

theorem paper11K4_owner_excludes_k3 {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V}
    (hu : u ∈ paper11K4RightVertices G D hCan hmax) :
    u ∉ paper11K3RightVertices G D hCan hmax := by
  intro hu3
  have hB : u ∈ BPart G D := (Finset.mem_filter.mp hu).1
  obtain ⟨w4, hw4⟩ := (Finset.mem_filter.mp hu).2
  obtain ⟨w3, hw3⟩ := (Finset.mem_filter.mp hu3).2
  have hw4Info := mem_paper11K4Supports G (Finset.mem_filter.mp hw4).1
  have hw3Info := mem_paper11K3Supports G (Finset.mem_filter.mp hw3).1
  have hTcard : (paper11NegativeIncidentSupports G D hCan hmax u).card = 1 := by
    have hw4T : w4 ∈ paper11NegativeIncidentSupports G D hCan hmax u := by
      simp [paper11NegativeIncidentSupports, paper11NegativeSupports,
        hw4Info.1, hw4Info.2.1, (Finset.mem_filter.mp hw4).2]
    exact paper9_repair_degree_eq_one_at_k4 G hCan hmax (w₄ := w4) hB
      (paper11NegativeIncidentSupports G D hCan hmax u)
      (by intro v hv; exact (Finset.mem_filter.mp
        (Finset.mem_filter.mp hv).1).1)
      (by intro v hv; exact (Finset.mem_filter.mp
        (Finset.mem_filter.mp hv).1).2)
      (by intro v hv; exact (Finset.mem_filter.mp hv).2)
      hw4T hw4Info.2.2
  have hmem4 : w4 ∈ paper11NegativeIncidentSupports G D hCan hmax u := by
    simp [paper11NegativeIncidentSupports, paper11NegativeSupports,
      hw4Info.1, hw4Info.2.1, (Finset.mem_filter.mp hw4).2]
  have hmem3 : w3 ∈ paper11NegativeIncidentSupports G D hCan hmax u := by
    simp [paper11NegativeIncidentSupports, paper11NegativeSupports,
      hw3Info.1, hw3Info.2.1, (Finset.mem_filter.mp hw3).2]
  have hEqSet : paper11NegativeIncidentSupports G D hCan hmax u = {w4} := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hTcard
    have haw4 : a = w4 := by
      have : w4 ∈ ({a} : Finset V) := by simpa [ha] using hmem4
      exact (Finset.mem_singleton.mp this).symm
    simpa [haw4] using ha
  have hw3eq : w3 = w4 := by
    rw [hEqSet] at hmem3
    exact Finset.mem_singleton.mp hmem3
  have hk3 : kCharge G D w3 = 3 := hw3Info.2.2
  have hk4 : kCharge G D w4 = 4 := hw4Info.2.2
  rw [hw3eq] at hk3
  omega

theorem paper11K3_K4_right_disjoint {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    Disjoint (paper11K3RightVertices G D hCan hmax)
      (paper11K4RightVertices G D hCan hmax) := by
  rw [Finset.disjoint_left]
  intro u hu3 hu4
  exact paper11K4_owner_excludes_k3 G hCan hmax hu4 hu3

noncomputable def paper11K4Resource (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (u : V) : ℤ := by
  classical
  exact vertexCharge G D u +
    ∑ q ∈ paper11K4Compensation G D hCan hmax u,
      externalCharge G D q

theorem paper11K4_right_resource_bound {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V}
    (hu : u ∈ paper11K4RightVertices G D hCan hmax) :
    8 ≤ paper11K4Resource G D hCan hmax u := by
  classical
  have hTcard := paper11K4_right_degree_eq_incident_card G hCan hmax (u := u)
  rw [paper11K4_right_degree_eq_one G hCan hmax hu] at hTcard
  have hTcard' : (paper11K4IncidentSupports G D hCan hmax u).card = 1 :=
    hTcard.symm
  have hTne : (paper11K4IncidentSupports G D hCan hmax u).Nonempty :=
    (Finset.mem_filter.mp hu).2
  obtain ⟨w, hw⟩ := hTne
  have hTsing : paper11K4IncidentSupports G D hCan hmax u = {w} := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hTcard'
    have haw : a = w := by
      have : w ∈ ({a} : Finset V) := by simpa [ha] using hw
      exact (Finset.mem_singleton.mp this).symm
    simpa [haw] using ha
  have hwInfo := mem_paper11K4Supports G (Finset.mem_filter.mp hw).1
  have hwChosen := (Finset.mem_filter.mp hw).2
  have hLegal := paperChosenRepairSet_legal G hCan hmax hwInfo.1 hwInfo.2.1 u
    hwChosen
  have hChosen : ChosenRepairRelation G D w
      (paperChosenRepairSet G D hCan hmax w) u :=
    ⟨hwChosen, hLegal⟩
  have hbound := paper9_single_repair_resource_bound G hCan hmax hLegal.1
    hwInfo.1 hwInfo.2.1 hChosen (Or.inr hwInfo.2.2)
  have hComp : paper11K4Compensation G D hCan hmax u =
      sharedCompensation G D (supportX G D w) u := by
    simp [paper11K4Compensation, hTsing]
  unfold paper11K4Resource
  rw [hComp]
  rcases hbound with h3 | h4
  · omega
  · exact h4.2

theorem paper11K4_total_debt_bound {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ w ∈ paper11K4Supports G D, -externalCharge G D w) ≤
      ∑ u ∈ paper11K4RightVertices G D hCan hmax,
        paper11K4Resource G D hCan hmax u := by
  classical
  let L := paper11K4Supports G D
  let R := paper11K4RightVertices G D hCan hmax
  let E := paper11K4Edges G D hCan hmax
  have hE : E ⊆ L.product R := by
    simpa [L, R, E] using paper11K4Edges_subset_product G hCan hmax
  obtain ⟨hLsum, hRsum⟩ := paper11_incidence_degree_sum L R E hE
  have hLdeg : ∀ w ∈ L, paper11LeftDegree E R w = 2 := by
    intro w hw
    simpa [L, E, R] using paper11K4_left_degree_eq_two G hCan hmax hw
  have hRdeg : ∀ u ∈ R, paper11RightDegree E L u = 1 := by
    intro u hu
    simpa [L, E, R] using paper11K4_right_degree_eq_one G hCan hmax hu
  have hLsum' : (2 * L.card : ℕ) = E.card := by
    calc
      2 * L.card = ∑ w ∈ L, (2 : ℕ) := by simp; ring
      _ = ∑ w ∈ L, paper11LeftDegree E R w := by
        apply Finset.sum_congr rfl
        intro w hw
        exact (hLdeg w hw).symm
      _ = E.card := hLsum
  have hRsum' : R.card = E.card := by
    calc
      R.card = ∑ u ∈ R, (1 : ℕ) := by simp
      _ = ∑ u ∈ R, paper11RightDegree E L u := by
        apply Finset.sum_congr rfl
        intro u hu
        exact (hRdeg u hu).symm
      _ = E.card := hRsum
  have hRcard : R.card = 2 * L.card := by omega
  have hDebt :
      (∑ w ∈ L, -externalCharge G D w) = 14 * (L.card : ℤ) := by
    calc
      _ = ∑ w ∈ L, (14 : ℤ) := by
        apply Finset.sum_congr rfl
        intro w hw
        have hinfo := mem_paper11K4Supports G hw
        have hvalues := lemma_7_2_charge_values G hCan hmax
          hinfo.1 hinfo.2.1
        rcases hvalues with h | h | h
        · omega
        · omega
        · omega
      _ = 14 * (L.card : ℤ) := by simp; ring
  have hRes : (8 * (R.card : ℤ)) ≤
      ∑ u ∈ R, paper11K4Resource G D hCan hmax u := by
    have hpoint : ∀ u ∈ R, (8 : ℤ) ≤ paper11K4Resource G D hCan hmax u := by
      intro u hu
      simpa [R] using paper11K4_right_resource_bound G hCan hmax hu
    have hsum := Finset.sum_le_sum hpoint
    calc
      8 * (R.card : ℤ) = ∑ u ∈ R, (8 : ℤ) := by simp; ring
      _ ≤ ∑ u ∈ R, paper11K4Resource G D hCan hmax u := hsum
  have hcalc : (14 * (L.card : ℤ)) ≤ 8 * (R.card : ℤ) := by
    rw [hRcard]
    norm_num
    nlinarith [show (0 : ℤ) ≤ (L.card : ℤ) by positivity]
  calc
    (∑ w ∈ paper11K4Supports G D, -externalCharge G D w) =
        14 * (L.card : ℤ) := by simpa [L] using hDebt
    _ ≤ 8 * (R.card : ℤ) := hcalc
    _ ≤ ∑ u ∈ paper11K4RightVertices G D hCan hmax,
        paper11K4Resource G D hCan hmax u := by simpa [R] using hRes

noncomputable def paper11OwnerCompensation (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (u : V) : Finset V := by
  classical
  exact (paper11NegativeIncidentSupports G D hCan hmax u).biUnion fun w =>
    sharedCompensation G D (supportX G D w) u

theorem paper11K3_negative_incident_eq {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V}
    (hu : u ∈ paper11K3RightVertices G D hCan hmax) :
    paper11NegativeIncidentSupports G D hCan hmax u =
      paper11K3IncidentSupports G D hCan hmax u := by
  classical
  apply Finset.ext
  intro w
  constructor
  · intro hw
    have hneg := Finset.mem_filter.mp hw
    have hsup := Finset.mem_filter.mp hneg.1
    have hclass := lemma_7_2_negative_charge_classification G hCan hmax
      hsup.1 hsup.2
    rcases hclass with h3 | h3 | h4
    · simp only [paper11K3IncidentSupports, paper11K3Supports,
        paper11NegativeSupports, Finset.mem_filter]
      exact ⟨⟨⟨hsup.1, hsup.2⟩, h3.1⟩, hneg.2⟩
    · simp only [paper11K3IncidentSupports, paper11K3Supports,
        paper11NegativeSupports, Finset.mem_filter]
      exact ⟨⟨⟨hsup.1, hsup.2⟩, h3.1⟩, hneg.2⟩
    · have hu4 : u ∈ paper11K4RightVertices G D hCan hmax := by
        rw [paper11K4RightVertices]
        simp only [Finset.mem_filter]
        refine ⟨(Finset.mem_filter.mp hu).1, ⟨w, ?_⟩⟩
        simp only [paper11K4IncidentSupports, paper11K4Supports,
          paper11NegativeSupports, Finset.mem_filter]
        exact ⟨⟨⟨hsup.1, hsup.2⟩, h4.1⟩, hneg.2⟩
      exact (paper11K4_owner_excludes_k3 G hCan hmax hu4 hu).elim
  · intro hw
    have hi := Finset.mem_filter.mp hw
    have hs := Finset.mem_filter.mp hi.1
    have hN := Finset.mem_filter.mp hs.1
    simp only [paper11NegativeIncidentSupports, paper11NegativeSupports,
      Finset.mem_filter]
    exact ⟨hN, hi.2⟩

theorem paper11K4_negative_incident_eq {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V}
    (hu : u ∈ paper11K4RightVertices G D hCan hmax) :
    paper11NegativeIncidentSupports G D hCan hmax u =
      paper11K4IncidentSupports G D hCan hmax u := by
  classical
  apply Finset.ext
  intro w
  constructor
  · intro hw
    have hneg := Finset.mem_filter.mp hw
    have hsup := Finset.mem_filter.mp hneg.1
    rcases lemma_7_2_negative_charge_classification G hCan hmax
        hsup.1 hsup.2 with h3 | h3 | h4
    · have hu3 : u ∈ paper11K3RightVertices G D hCan hmax := by
        rw [paper11K3RightVertices]
        simp only [Finset.mem_filter]
        refine ⟨(Finset.mem_filter.mp hu).1, ⟨w, ?_⟩⟩
        simp only [paper11K3IncidentSupports, paper11K3Supports,
          paper11NegativeSupports, Finset.mem_filter]
        exact ⟨⟨⟨hsup.1, hsup.2⟩, h3.1⟩, hneg.2⟩
      exact (paper11K4_owner_excludes_k3 G hCan hmax hu hu3).elim
    · have hu3 : u ∈ paper11K3RightVertices G D hCan hmax := by
        rw [paper11K3RightVertices]
        simp only [Finset.mem_filter]
        refine ⟨(Finset.mem_filter.mp hu).1, ⟨w, ?_⟩⟩
        simp only [paper11K3IncidentSupports, paper11K3Supports,
          paper11NegativeSupports, Finset.mem_filter]
        exact ⟨⟨⟨hsup.1, hsup.2⟩, h3.1⟩, hneg.2⟩
      exact (paper11K4_owner_excludes_k3 G hCan hmax hu hu3).elim
    · simp only [paper11K4IncidentSupports, paper11K4Supports,
        paper11NegativeSupports, Finset.mem_filter]
      exact ⟨⟨⟨hsup.1, hsup.2⟩, h4.1⟩, hneg.2⟩
  · intro hw
    have hi := Finset.mem_filter.mp hw
    have hs := Finset.mem_filter.mp hi.1
    have hN := Finset.mem_filter.mp hs.1
    simp only [paper11NegativeIncidentSupports, paper11NegativeSupports,
      Finset.mem_filter]
    exact ⟨hN, hi.2⟩

theorem paper11OwnerCompensation_eq_K3 {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V}
    (hu : u ∈ paper11K3RightVertices G D hCan hmax) :
    paper11OwnerCompensation G D hCan hmax u =
      paper11K3Compensation G D hCan hmax u := by
  simp [paper11OwnerCompensation, paper11K3Compensation,
    paper11K3IncidentSupports, paper11K3Supports, paper11NegativeSupports,
    paper11K3_negative_incident_eq G hCan hmax hu]

theorem paper11OwnerCompensation_eq_K4 {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V}
    (hu : u ∈ paper11K4RightVertices G D hCan hmax) :
    paper11OwnerCompensation G D hCan hmax u =
      paper11K4Compensation G D hCan hmax u := by
  simp [paper11OwnerCompensation, paper11K4Compensation,
    paper11K4IncidentSupports, paper11K4Supports, paper11NegativeSupports,
    paper11K4_negative_incident_eq G hCan hmax hu]

noncomputable def paper11AllRepairOwners (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) : Finset V :=
  paper11K3RightVertices G D hCan hmax ∪
    paper11K4RightVertices G D hCan hmax

noncomputable def paper11AllCompensation (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) : Finset V := by
  classical
  exact (paper11AllRepairOwners G D hCan hmax).biUnion fun u =>
    paper11OwnerCompensation G D hCan hmax u

theorem paper11OwnerCompensation_subset_S {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u q : V}
    (huB : u ∈ BPart G D)
    (hq : q ∈ paper11OwnerCompensation G D hCan hmax u) :
    q ∈ SPart G D := by
  classical
  obtain ⟨w, hw, hq⟩ := Finset.mem_biUnion.mp hq
  have hwInfo := Finset.mem_filter.mp hw
  have hX : supportX G D w ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D w z).mp hz |>.1
  exact (paper9_shared_compensation_profile G hX huB hq).1

theorem paper11OwnerCompensation_charge_four {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u q : V}
    (huB : u ∈ BPart G D)
    (hq : q ∈ paper11OwnerCompensation G D hCan hmax u) :
    externalCharge G D q = 4 := by
  classical
  obtain ⟨w, hw, hq⟩ := Finset.mem_biUnion.mp hq
  have hX : supportX G D w ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D w z).mp hz |>.1
  exact paper9_shared_external_charge_eq_four G hX huB hq

theorem paper11OwnerCompensation_disjoint {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u v : V}
    (huB : u ∈ BPart G D) (hvB : v ∈ BPart G D) (hne : u ≠ v) :
    Disjoint (paper11OwnerCompensation G D hCan hmax u)
      (paper11OwnerCompensation G D hCan hmax v) := by
  classical
  rw [Finset.disjoint_left]
  intro q hqu hqv
  obtain ⟨w, hw, hqU⟩ := Finset.mem_biUnion.mp hqu
  obtain ⟨w', hw', hqV⟩ := Finset.mem_biUnion.mp hqv
  have hX : supportX G D w ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D w z).mp hz |>.1
  have hY : supportX G D w' ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D w' z).mp hz |>.1
  exact hne (paper11_compensation_unique_B_owner G hX hY huB hvB hqU hqV)

theorem paper11AllRepairOwners_subset_B {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    paper11AllRepairOwners G D hCan hmax ⊆ BPart G D := by
  intro u hu
  rcases Finset.mem_union.mp hu with hu | hu
  · exact (Finset.mem_filter.mp hu).1
  · exact (Finset.mem_filter.mp hu).1

theorem paper11OwnerCompensation_family_disjoint {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (paper11AllRepairOwners G D hCan hmax : Set V).PairwiseDisjoint
      (paper11OwnerCompensation G D hCan hmax) := by
  classical
  rw [Finset.pairwiseDisjoint_iff]
  intro u hu v hv hne
  have huB := paper11AllRepairOwners_subset_B G hCan hmax hu
  have hvB := paper11AllRepairOwners_subset_B G hCan hmax hv
  rcases hne with ⟨q, hq⟩
  have hqBoth := Finset.mem_inter.mp hq
  obtain ⟨w, hw, hqU⟩ := Finset.mem_biUnion.mp hqBoth.1
  obtain ⟨w', hw', hqV⟩ := Finset.mem_biUnion.mp hqBoth.2
  have hX : supportX G D w ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D w z).mp hz |>.1
  have hY : supportX G D w' ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D w' z).mp hz |>.1
  exact paper11_compensation_unique_B_owner G hX hY huB hvB hqU hqV

theorem paper11AllCompensation_subset_S {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    paper11AllCompensation G D hCan hmax ⊆ SPart G D := by
  intro q hq
  obtain ⟨u, hu, hq⟩ := Finset.mem_biUnion.mp hq
  exact paper11OwnerCompensation_subset_S G hCan hmax
    (paper11AllRepairOwners_subset_B G hCan hmax hu) hq

theorem paper11AllCompensation_charge_four {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {q : V}
    (hq : q ∈ paper11AllCompensation G D hCan hmax) :
    externalCharge G D q = 4 := by
  obtain ⟨u, hu, hq⟩ := Finset.mem_biUnion.mp hq
  exact paper11OwnerCompensation_charge_four G hCan hmax
    (paper11AllRepairOwners_subset_B G hCan hmax hu) hq

theorem paper11AllCompensation_sum_eq_owner_sums {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ u ∈ paper11AllRepairOwners G D hCan hmax,
      ∑ q ∈ paper11OwnerCompensation G D hCan hmax u,
        externalCharge G D q) =
      ∑ q ∈ paper11AllCompensation G D hCan hmax,
        externalCharge G D q := by
  classical
  let O := paper11AllRepairOwners G D hCan hmax
  let C := paper11OwnerCompensation G D hCan hmax
  let U := paper11AllCompensation G D hCan hmax
  have hpair : (O : Set V).PairwiseDisjoint C := by
    simpa [O, C] using paper11OwnerCompensation_family_disjoint G hCan hmax
  have hcard : U.card = ∑ u ∈ O, (C u).card := by
    simpa [O, C, U, paper11AllCompensation] using Finset.card_biUnion hpair
  have hinner : ∀ u ∈ O,
      (∑ q ∈ C u, externalCharge G D q) = 4 * ((C u).card : ℤ) := by
    intro u hu
    calc
      _ = ∑ q ∈ C u, (4 : ℤ) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact paper11OwnerCompensation_charge_four G hCan hmax
          (paper11AllRepairOwners_subset_B G hCan hmax hu) hq
      _ = 4 * ((C u).card : ℤ) := by simp; ring
  have hsumOwner :
      (∑ u ∈ O, ∑ q ∈ C u, externalCharge G D q) =
        4 * (∑ u ∈ O, ((C u).card : ℤ)) := by
    calc
      _ = ∑ u ∈ O, 4 * ((C u).card : ℤ) := by
        apply Finset.sum_congr rfl
        intro u hu
        exact hinner u hu
      _ = 4 * (∑ u ∈ O, ((C u).card : ℤ)) := by
        calc
          _ = ∑ u ∈ O, ((C u).card : ℤ) * 4 := by
            apply Finset.sum_congr rfl
            intro u hu
            ring
          _ = (∑ u ∈ O, ((C u).card : ℤ)) * 4 := by rw [Finset.sum_mul]
          _ = 4 * (∑ u ∈ O, ((C u).card : ℤ)) := by ring
  have hcardZ : (U.card : ℤ) =
      ∑ u ∈ O, ((C u).card : ℤ) := by exact_mod_cast hcard
  calc
    _ = 4 * (∑ u ∈ O, ((C u).card : ℤ)) := hsumOwner
    _ = 4 * (U.card : ℤ) := by rw [← hcardZ]
    _ = ∑ q ∈ U, externalCharge G D q := by
      symm
      calc
        _ = ∑ q ∈ U, (4 : ℤ) := by
          apply Finset.sum_congr rfl
          intro q hq
          exact paper11AllCompensation_charge_four G hCan hmax hq
        _ = 4 * (U.card : ℤ) := by simp; ring

theorem paper11_negative_supports_eq_k3_union_k4 {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    paper11NegativeSupports G D =
      paper11K3Supports G D ∪ paper11K4Supports G D := by
  classical
  ext w
  constructor
  · intro hw
    have hi := Finset.mem_filter.mp hw
    rcases lemma_7_2_negative_charge_classification G hCan hmax hi.1 hi.2 with
      h3 | h3 | h4
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, h3.1⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, h3.1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, h4.1⟩)
  · intro hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact (Finset.mem_filter.mp hw).1
    · exact (Finset.mem_filter.mp hw).1

theorem paper11_k3_k4_supports_disjoint {D : Finset V} :
    Disjoint (paper11K3Supports G D) (paper11K4Supports G D) := by
  rw [Finset.disjoint_left]
  intro w hw3 hw4
  have h3 := (Finset.mem_filter.mp hw3).2
  have h4 := (Finset.mem_filter.mp hw4).2
  omega

theorem paper11_negative_debt_split {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ w ∈ paper11NegativeSupports G D, -externalCharge G D w) =
      (∑ w ∈ paper11K3Supports G D, -externalCharge G D w) +
      (∑ w ∈ paper11K4Supports G D, -externalCharge G D w) := by
  rw [paper11_negative_supports_eq_k3_union_k4 G hCan hmax,
    Finset.sum_union (paper11_k3_k4_supports_disjoint G)]

noncomputable def paper11NonnegativeSupports (D : Finset V) : Finset V :=
  SPart G D \ paper11NegativeSupports G D

theorem paper11_charge_nonnegative_on_B {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V}
    (hu : u ∈ BPart G D) :
    0 ≤ vertexCharge G D u := by
  have hbudget := paper9_sCharge_add_xCharge_le_three G hCan hmax hu
  have hbudgetZ : (sCharge G D u : ℤ) + (xCharge G D u : ℤ) ≤ 3 := by
    exact_mod_cast hbudget
  have hx : 0 ≤ (xCharge G D u : ℤ) := by positivity
  unfold vertexCharge
  nlinarith

theorem paper11_nonnegative_charge_partition {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    SPart G D = paper11NegativeSupports G D ∪
      paper11NonnegativeSupports G D := by
  classical
  ext w
  constructor
  · intro hw
    by_cases hneg : externalCharge G D w < 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, hneg⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
        ⟨hw, by
          intro hN
          exact hneg (Finset.mem_filter.mp hN).2⟩)
  · intro hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact (Finset.mem_filter.mp hw).1
    · exact (Finset.mem_sdiff.mp hw).1

theorem paper11_all_compensation_subset_nonnegative {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    paper11AllCompensation G D hCan hmax ⊆
      paper11NonnegativeSupports G D := by
  intro q hq
  have hS := paper11AllCompensation_subset_S G hCan hmax hq
  have hq4 := paper11AllCompensation_charge_four G hCan hmax hq
  apply Finset.mem_sdiff.mpr
  refine ⟨hS, ?_⟩
  intro hneg
  have hneg' := (Finset.mem_filter.mp hneg).2
  omega

theorem paper11_external_charge_sum_split {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ w ∈ SPart G D, externalCharge G D w) =
      (∑ w ∈ paper11NegativeSupports G D, externalCharge G D w) +
      (∑ q ∈ paper11AllCompensation G D hCan hmax,
        externalCharge G D q) +
      (∑ q ∈ paper11NonnegativeSupports G D \
        paper11AllCompensation G D hCan hmax, externalCharge G D q) := by
  classical
  let N := paper11NegativeSupports G D
  let P := paper11NonnegativeSupports G D
  let C := paper11AllCompensation G D hCan hmax
  have hNP : SPart G D = N ∪ P := by simpa [N, P] using
    paper11_nonnegative_charge_partition G hCan hmax
  have hdisjNP : Disjoint N P := by
    rw [Finset.disjoint_left]
    intro w hwN hwP
    exact (Finset.mem_sdiff.mp hwP).2 hwN
  have hCP : C ⊆ P := by simpa [C, P] using
    paper11_all_compensation_subset_nonnegative G hCan hmax
  have hsplitP : P = C ∪ (P \ C) := by
    ext q
    constructor
    · intro hq
      by_cases hqC : q ∈ C
      · exact Finset.mem_union_left _ hqC
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hq, hqC⟩)
    · intro hq
      rcases Finset.mem_union.mp hq with hqC | hqPC
      · exact hCP hqC
      · exact (Finset.mem_sdiff.mp hqPC).1
  have hdisjCP : Disjoint C (P \ C) := by
    rw [Finset.disjoint_left]
    intro q hqC hqPC
    exact (Finset.mem_sdiff.mp hqPC).2 hqC
  have hsumP : (∑ q ∈ P, externalCharge G D q) =
      (∑ q ∈ C, externalCharge G D q) +
        ∑ q ∈ P \ C, externalCharge G D q := by
    calc
      _ = ∑ q ∈ C ∪ (P \ C), externalCharge G D q := by
        apply Finset.sum_congr hsplitP
        intro q hq
        rfl
      _ = _ := Finset.sum_union hdisjCP
  calc
    _ = ∑ w ∈ N ∪ P, externalCharge G D w := by rw [hNP]
    _ = (∑ w ∈ N, externalCharge G D w) +
        ∑ w ∈ P, externalCharge G D w := Finset.sum_union hdisjNP
    _ = (∑ w ∈ N, externalCharge G D w) +
        ((∑ q ∈ C, externalCharge G D q) +
          ∑ q ∈ P \ C, externalCharge G D q) := by
      rw [hsumP]
    _ = (∑ w ∈ N, externalCharge G D w) +
        (∑ q ∈ C, externalCharge G D q) +
          ∑ q ∈ P \ C, externalCharge G D q := by ring

theorem paper11_nonnegative_residual_charge {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    0 ≤ ∑ q ∈ paper11NonnegativeSupports G D \
        paper11AllCompensation G D hCan hmax, externalCharge G D q := by
  apply Finset.sum_nonneg
  intro q hq
  have hP := (Finset.mem_sdiff.mp hq).1
  have hS := (Finset.mem_sdiff.mp hP).1
  have hnotneg := (Finset.mem_sdiff.mp hP).2
  have hnotN : q ∉ paper11NegativeSupports G D := by
    intro hN
    exact hnotneg hN
  have hnotlt : ¬ externalCharge G D q < 0 := by
    intro hlt
    exact hnotN (Finset.mem_filter.mpr ⟨hS, hlt⟩)
  omega

theorem paper11_base_charge_sum_bound {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ u ∈ paper11AllRepairOwners G D hCan hmax, vertexCharge G D u) ≤
      ∑ u ∈ BPart G D, vertexCharge G D u := by
  classical
  let O := paper11AllRepairOwners G D hCan hmax
  let B := BPart G D
  have hsub : O ⊆ B := by simpa [O, B] using
    paper11AllRepairOwners_subset_B G hCan hmax
  have hdecomp : B = O ∪ (B \ O) := by
    ext u
    constructor
    · intro huB
      by_cases huO : u ∈ O
      · exact Finset.mem_union_left _ huO
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨huB, huO⟩)
    · intro hu
      rcases Finset.mem_union.mp hu with huO | huBO
      · exact hsub huO
      · exact (Finset.mem_sdiff.mp huBO).1
  have hdisj : Disjoint O (B \ O) := by
    rw [Finset.disjoint_left]
    intro u huO huBO
    exact (Finset.mem_sdiff.mp huBO).2 huO
  have hrem : 0 ≤ ∑ u ∈ B \ O, vertexCharge G D u := by
    apply Finset.sum_nonneg
    intro u hu
    exact paper11_charge_nonnegative_on_B G hCan hmax
      (Finset.mem_sdiff.mp hu).1
  calc
    _ ≤ (∑ u ∈ O, vertexCharge G D u) +
        ∑ u ∈ B \ O, vertexCharge G D u := by linarith
    _ = ∑ u ∈ B, vertexCharge G D u := by
      calc
        _ = ∑ u ∈ O ∪ (B \ O), vertexCharge G D u :=
          (Finset.sum_union hdisj).symm
        _ = ∑ u ∈ B, vertexCharge G D u := by
          congr 1
          exact hdecomp.symm

noncomputable def paper11OwnerResource (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (u : V) : ℤ := by
  classical
  exact vertexCharge G D u +
    ∑ q ∈ paper11OwnerCompensation G D hCan hmax u,
      externalCharge G D q

theorem paper11OwnerResource_sum_decomposition {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ u ∈ paper11AllRepairOwners G D hCan hmax,
      paper11OwnerResource G D hCan hmax u) =
      (∑ u ∈ paper11AllRepairOwners G D hCan hmax,
        vertexCharge G D u) +
      ∑ q ∈ paper11AllCompensation G D hCan hmax,
        externalCharge G D q := by
  classical
  simp only [paper11OwnerResource, Finset.sum_add_distrib]
  exact congrArg (fun x : ℤ => (∑ u ∈ paper11AllRepairOwners G D hCan hmax,
      vertexCharge G D u) + x)
    (paper11AllCompensation_sum_eq_owner_sums G hCan hmax)

theorem paper11_owner_resource_sums_union {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ u ∈ paper11K3RightVertices G D hCan hmax,
      paper11OwnerResource G D hCan hmax u) +
      ∑ u ∈ paper11K4RightVertices G D hCan hmax,
        paper11OwnerResource G D hCan hmax u =
      ∑ u ∈ paper11AllRepairOwners G D hCan hmax,
        paper11OwnerResource G D hCan hmax u := by
  classical
  rw [paper11AllRepairOwners, Finset.sum_union
    (paper11K3_K4_right_disjoint G hCan hmax)]

theorem paper11K3_base_resource_eq_owner {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ u ∈ paper11K3RightVertices G D hCan hmax,
      (vertexCharge G D u +
        ∑ q ∈ paper11K3Compensation G D hCan hmax u,
          externalCharge G D q)) =
      ∑ u ∈ paper11K3RightVertices G D hCan hmax,
        paper11OwnerResource G D hCan hmax u := by
  apply Finset.sum_congr rfl
  intro u hu
  unfold paper11OwnerResource
  rw [paper11OwnerCompensation_eq_K3 G hCan hmax hu]

theorem paper11K4_resource_eq_owner {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ u ∈ paper11K4RightVertices G D hCan hmax,
      paper11K4Resource G D hCan hmax u) =
      ∑ u ∈ paper11K4RightVertices G D hCan hmax,
        paper11OwnerResource G D hCan hmax u := by
  apply Finset.sum_congr rfl
  intro u hu
  simp only [paper11K4Resource, paper11OwnerResource]
  rw [paper11OwnerCompensation_eq_K4 G hCan hmax hu]

theorem paper11_negative_debt_paid {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    (hNoIso : HasNoIsolatedVertices G) :
    (∑ w ∈ paper11NegativeSupports G D, -externalCharge G D w) ≤
      (∑ u ∈ paper11AllRepairOwners G D hCan hmax,
        vertexCharge G D u) +
      (∑ q ∈ paper11AllCompensation G D hCan hmax,
        externalCharge G D q) +
      7 * ((incidenceTotal G D - (Z0Part G D).card : ℕ) : ℤ) := by
  classical
  have hK3 := paper11_chosen_k3_charge_balance G hCan hmax
  have hK4 := paper11K4_total_debt_bound G hCan hmax
  have hsplit := paper11_negative_debt_split G hCan hmax
  have hK3base := paper11K3_base_resource_eq_owner G hCan hmax
  have hK4base := paper11K4_resource_eq_owner G hCan hmax
  have hOwnerUnion := paper11_owner_resource_sums_union G hCan hmax
  have hOwnerDecomp := paper11OwnerResource_sum_decomposition G hCan hmax
  have hAvailable := paper11K3AvailableResource_sum_decomposition G hCan hmax
  have hSpecial := paper11K3SpecialBudget_cost_bound G hCan hmax hNoIso
  calc
    (∑ w ∈ paper11NegativeSupports G D, -externalCharge G D w) =
        (∑ w ∈ paper11K3Supports G D, -externalCharge G D w) +
          ∑ w ∈ paper11K4Supports G D, -externalCharge G D w := hsplit
    _ ≤ (∑ u ∈ paper11K3RightVertices G D hCan hmax,
          paper11K3AvailableResource G D hCan hmax u) +
        ∑ u ∈ paper11K4RightVertices G D hCan hmax,
          paper11K4Resource G D hCan hmax u := add_le_add hK3 hK4
    _ = ((∑ u ∈ paper11K3RightVertices G D hCan hmax,
          (vertexCharge G D u +
            ∑ q ∈ paper11K3Compensation G D hCan hmax u,
              externalCharge G D q)) +
          7 * ((paper11K3SpecialBudgetVertices G D hCan hmax).card : ℤ)) +
        ∑ u ∈ paper11K4RightVertices G D hCan hmax,
          paper11K4Resource G D hCan hmax u := by rw [hAvailable]
    _ = ((∑ u ∈ paper11K3RightVertices G D hCan hmax,
          paper11OwnerResource G D hCan hmax u) +
          ∑ u ∈ paper11K4RightVertices G D hCan hmax,
            paper11OwnerResource G D hCan hmax u) +
          7 * ((paper11K3SpecialBudgetVertices G D hCan hmax).card : ℤ) := by
        rw [hK3base, hK4base]
        ring
    _ = (∑ u ∈ paper11AllRepairOwners G D hCan hmax,
          paper11OwnerResource G D hCan hmax u) +
          7 * ((paper11K3SpecialBudgetVertices G D hCan hmax).card : ℤ) := by
        rw [hOwnerUnion]
    _ = (∑ u ∈ paper11AllRepairOwners G D hCan hmax,
          vertexCharge G D u) +
          ∑ q ∈ paper11AllCompensation G D hCan hmax,
            externalCharge G D q +
          7 * ((paper11K3SpecialBudgetVertices G D hCan hmax).card : ℤ) := by
        rw [hOwnerDecomp]
    _ ≤ (∑ u ∈ paper11AllRepairOwners G D hCan hmax,
          vertexCharge G D u) +
          ∑ q ∈ paper11AllCompensation G D hCan hmax,
            externalCharge G D q +
          7 * ((incidenceTotal G D - (Z0Part G D).card : ℕ) : ℤ) := by
        linarith

theorem paper11_Z0_card_le_incidence {D : Finset V}
    (hNoIso : HasNoIsolatedVertices G) :
    (Z0Part G D).card ≤ incidenceTotal G D := by
  classical
  have hlocal : ∀ z ∈ Z0Part G D, 1 ≤ degreeTo G (SPart G D) z := by
    intro z hz
    obtain ⟨q, hqS, hqAdj⟩ := paper10_z0_has_S_neighbor G hNoIso hz
    have hmem : q ∈ (SPart G D).filter (fun v => G.Adj z v) :=
      Finset.mem_filter.mpr ⟨hqS, hqAdj⟩
    have hpos : 0 < ((SPart G D).filter (fun v => G.Adj z v)).card :=
      Finset.card_pos.mpr ⟨q, hmem⟩
    unfold degreeTo
    simpa [G.adj_comm] using hpos
  have hsum := Finset.sum_le_sum hlocal
  have hinc := sum_degreeTo_symm G (Z0Part G D) (SPart G D)
  have hinc' :
      (∑ z ∈ Z0Part G D, degreeTo G (SPart G D) z) = incidenceTotal G D := by
    rw [hinc]
    simp [incidenceTotal, kCharge]
  calc
    (Z0Part G D).card = ∑ z ∈ Z0Part G D, (1 : ℕ) := by simp
    _ ≤ ∑ z ∈ Z0Part G D, degreeTo G (SPart G D) z := hsum
    _ = incidenceTotal G D := hinc'

/-- Lemma 11.2: all positive vertex charges, chosen compensation charges,
and the Section 10 incidence surplus cover every negative external charge.
Combining this with the exact Section 6 identity gives the asserted global
inequality. -/
theorem paper11_lemma_11_2_global_inequality {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    (hNoIso : HasNoIsolatedVertices G) :
    8 * (WBPart G D).card ≥
      7 * ((BPart G D).card + (Z0Part G D).card) := by
  classical
  let N := paper11NegativeSupports G D
  let C := paper11AllCompensation G D hCan hmax
  let O := paper11AllRepairOwners G D hCan hmax
  let Pspec := paper11K3SpecialBudgetVertices G D hCan hmax
  let surplus := incidenceTotal G D - (Z0Part G D).card
  have hDebt := paper11_negative_debt_paid G hCan hmax hNoIso
  have hBase := paper11_base_charge_sum_bound G hCan hmax
  have hResidual := paper11_nonnegative_residual_charge G hCan hmax
  have hSplit := paper11_external_charge_sum_split G hCan hmax
  have hSpecial := paper11K3SpecialBudget_cost_bound G hCan hmax hNoIso
  have hNegCast :
      (∑ w ∈ N, externalCharge G D w) =
        - (∑ w ∈ N, -externalCharge G D w) := by
    rw [← Finset.sum_neg_distrib]
    simp
  have hAlloc :
      0 ≤ (∑ w ∈ N, externalCharge G D w) +
        (∑ u ∈ BPart G D, vertexCharge G D u) +
        (∑ q ∈ C, externalCharge G D q) +
        7 * (surplus : ℤ) := by
    have hDebt' :
        (∑ w ∈ N, -externalCharge G D w) ≤
          (∑ u ∈ O, vertexCharge G D u) +
            (∑ q ∈ C, externalCharge G D q) + 7 * (surplus : ℤ) := by
      simpa [N, O, C, surplus] using hDebt
    have hBase' :
        (∑ u ∈ O, vertexCharge G D u) ≤
          ∑ u ∈ BPart G D, vertexCharge G D u := by
      simpa [O] using hBase
    have hSpecial' : 7 * (Pspec.card : ℤ) ≤ 7 * (surplus : ℤ) := by
      simpa [Pspec, surplus] using hSpecial
    rw [hNegCast]
    linarith
  have hCharges :
      0 ≤ (∑ u ∈ BPart G D, vertexCharge G D u) +
        (∑ w ∈ SPart G D, externalCharge G D w) +
        7 * ((incidenceTotal G D - (Z0Part G D).card : ℕ) : ℤ) := by
    rw [hSplit]
    have hResidual' :
        0 ≤ ∑ q ∈ paper11NonnegativeSupports G D \ C,
          externalCharge G D q := by
      simpa [C] using hResidual
    have hAlloc' := hAlloc
    dsimp [surplus] at hAlloc'
    dsimp [N, C] at hAlloc'
    linarith
  have hIdentity := lemma_6_1_charge_identity G hCan
  have hDifferenceAdd :
      0 ≤ (8 : ℤ) * ((WBPart G D).card : ℤ) -
        7 * (((BPart G D).card : ℤ) + ((Z0Part G D).card : ℤ)) := by
    rw [hIdentity]
    have hZ0le := paper11_Z0_card_le_incidence G (D := D) hNoIso
    simpa only [Nat.cast_sub hZ0le] using hCharges
  have hDifference :
      0 ≤ (8 : ℤ) * ((WBPart G D).card : ℤ) -
        7 * (((BPart G D).card + (Z0Part G D).card : ℕ) : ℤ) := by
    simpa only [Nat.cast_add] using hDifferenceAdd
  have hInt :
      (7 * ((BPart G D).card + (Z0Part G D).card) : ℤ) ≤
        8 * ((WBPart G D).card : ℤ) := by linarith
  exact_mod_cast hInt

end C6BipartiteDomination

