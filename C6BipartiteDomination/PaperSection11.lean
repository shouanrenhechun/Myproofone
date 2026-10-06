/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import C6BipartiteDomination.PaperSection10

/-! # Paper section 11: repair-graph charge accounting -/

namespace C6BipartiteDomination

open Finset BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Degree on the left side of a finite bipartite incidence set. -/
def paper11LeftDegree (E : Finset (V × V)) (R : Finset V) (w : V) : ℕ :=
  (E.filter fun e => e.1 = w).card

/-- Degree on the right side of a finite bipartite incidence set. -/
def paper11RightDegree (E : Finset (V × V)) (L : Finset V) (u : V) : ℕ :=
  (E.filter fun e => e.2 = u).card

/-- The finite incidence-count identity needed for charge balance. -/
theorem paper11_incidence_degree_sum
    (L R : Finset V) (E : Finset (V × V))
    (hE : E ⊆ L.product R) :
    (∑ w ∈ L, paper11LeftDegree E R w) = E.card ∧
      (∑ u ∈ R, paper11RightDegree E L u) = E.card := by
  classical
  constructor
  · have hmap : (E : Set (V × V)).MapsTo Prod.fst (L : Set V) := by
      intro e he
      have he' := hE he
      exact (Finset.mem_product.mp he').1
    have hcard := Finset.card_eq_sum_card_fiberwise (s := E) (t := L)
      (f := Prod.fst) hmap
    calc
      _ = ∑ w ∈ L, #{e ∈ E | e.1 = w} := by simp [paper11LeftDegree]
      _ = E.card := hcard.symm
  · have hmap : (E : Set (V × V)).MapsTo Prod.snd (R : Set V) := by
      intro e he
      have he' := hE he
      exact (Finset.mem_product.mp he').2
    have hcard := Finset.card_eq_sum_card_fiberwise (s := E) (t := R)
      (f := Prod.snd) hmap
    calc
      _ = ∑ u ∈ R, #{e ∈ E | e.2 = u} := by simp [paper11RightDegree]
      _ = E.card := hcard.symm

/-- Numeric form of Lemma 11.1. It applies to any finite bipartite
incidence graph (hence to a pure `k=3` repair component): left degrees 1 and 2
carry debts at most 4 and 7; right degrees 1 and 2 carry resources at least
4 and 11. Connectivity is unnecessary for this stronger union statement. -/
theorem paper11_pure_k3_charge_balance
    (L R : Finset V) (E : Finset (V × V))
    (hE : E ⊆ L.product R)
    (debt : V → ℤ) (resource : V → ℤ)
    (hLdegree : ∀ w ∈ L,
      paper11LeftDegree E R w = 1 ∨ paper11LeftDegree E R w = 2)
    (hRdegree : ∀ u ∈ R,
      paper11RightDegree E L u = 1 ∨ paper11RightDegree E L u = 2)
    (hDebt : ∀ w ∈ L,
      debt w ≤ if paper11LeftDegree E R w = 1 then 4 else 7)
    (hResource : ∀ u ∈ R,
      (if paper11RightDegree E L u = 1 then 4 else 11) ≤ resource u) :
    (∑ w ∈ L, debt w) ≤ ∑ u ∈ R, resource u := by
  classical
  obtain ⟨hLsum, hRsum⟩ := paper11_incidence_degree_sum L R E hE
  have hLpositive : ∀ w ∈ L, 1 ≤ paper11LeftDegree E R w := by
    intro w hw
    rcases hLdegree w hw with h | h <;> omega
  have hRpositive : ∀ u ∈ R, 1 ≤ paper11RightDegree E L u := by
    intro u hu
    rcases hRdegree u hu with h | h <;> omega
  have hLcard : (L.card : ℤ) ≤ (E.card : ℤ) := by
    have hsum := Finset.sum_le_sum hLpositive
    have hsum' : (L.card : ℤ) ≤
        (∑ w ∈ L, (paper11LeftDegree E R w : ℤ)) := by
      exact_mod_cast (by simpa using hsum)
    calc
      (L.card : ℤ) ≤ ∑ w ∈ L, (paper11LeftDegree E R w : ℤ) := hsum'
      _ = (E.card : ℤ) := by exact_mod_cast hLsum
  have hRcard : (R.card : ℤ) ≤ (E.card : ℤ) := by
    have hsum := Finset.sum_le_sum hRpositive
    have hsum' : (R.card : ℤ) ≤
        (∑ u ∈ R, (paper11RightDegree E L u : ℤ)) := by
      exact_mod_cast (by simpa using hsum)
    calc
      (R.card : ℤ) ≤ ∑ u ∈ R, (paper11RightDegree E L u : ℤ) := hsum'
      _ = (E.card : ℤ) := by exact_mod_cast hRsum
  have hDebtAffine : (∑ w ∈ L, debt w) ≤
      3 * (E.card : ℤ) + L.card := by
    have hpoint : ∀ w ∈ L,
        debt w ≤ 3 * (paper11LeftDegree E R w : ℤ) + 1 := by
      intro w hw
      rcases hLdegree w hw with h | h
      · rw [h]
        have hdebt := hDebt w hw
        simp [h] at hdebt
        norm_num at hdebt ⊢
        exact hdebt
      · rw [h]
        have hdebt := hDebt w hw
        have hne : paper11LeftDegree E R w ≠ 1 := by omega
        simp [hne] at hdebt
        norm_num at hdebt ⊢
        exact hdebt
    have hsum := Finset.sum_le_sum hpoint
    calc
      _ ≤ ∑ w ∈ L, (3 * (paper11LeftDegree E R w : ℤ) + 1) := hsum
      _ = 3 * (∑ w ∈ L, (paper11LeftDegree E R w : ℤ)) + L.card := by
        simp [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = 3 * (E.card : ℤ) + L.card := by
        rw [show (∑ w ∈ L, (paper11LeftDegree E R w : ℤ)) =
          (E.card : ℤ) by exact_mod_cast hLsum]
  have hResourceAffine : 7 * (E.card : ℤ) - 3 * R.card ≤
      ∑ u ∈ R, resource u := by
    have hpoint : ∀ u ∈ R,
        7 * (paper11RightDegree E L u : ℤ) - 3 ≤ resource u := by
      intro u hu
      rcases hRdegree u hu with h | h
      · rw [h]
        have hres := hResource u hu
        simp [h] at hres
        norm_num at hres ⊢
        exact hres
      · rw [h]
        have hres := hResource u hu
        have hne : paper11RightDegree E L u ≠ 1 := by omega
        simp [hne] at hres
        norm_num at hres ⊢
        exact hres
    have hsum := Finset.sum_le_sum hpoint
    have hsumEq :
        (∑ u ∈ R, (7 * (paper11RightDegree E L u : ℤ) - 3)) =
          7 * (E.card : ℤ) - 3 * R.card := by
      calc
        _ = (∑ u ∈ R, (7 * (paper11RightDegree E L u : ℤ))) -
            ∑ u ∈ R, (3 : ℤ) := by rw [Finset.sum_sub_distrib]
        _ = 7 * (∑ u ∈ R, (paper11RightDegree E L u : ℤ)) - 3 * R.card := by
            simp [← Finset.mul_sum]
            ring
        _ = 7 * (E.card : ℤ) - 3 * R.card := by
            rw [show (∑ u ∈ R, (paper11RightDegree E L u : ℤ)) =
              (E.card : ℤ) by exact_mod_cast hRsum]
    rw [← hsumEq]
    exact hsum
  have harithmetic :
      3 * (E.card : ℤ) + L.card ≤ 7 * (E.card : ℤ) - 3 * R.card := by
    nlinarith
  exact le_trans (le_trans hDebtAffine harithmetic) hResourceAffine

variable (G : SimpleGraph V)

/-! ## Adapter for the fixed chosen repair relation

The definitions below turn the fixed A8 choices into the finite incidence
graph used above.  Compensation is unioned per right vertex, so a point
shared by two incident edges is counted once at its unique `B`-owner.
-/

noncomputable def paper11NegativeSupports (D : Finset V) : Finset V := by
  classical
  exact (SPart G D).filter fun w => externalCharge G D w < 0

noncomputable def paper11K3Supports (D : Finset V) : Finset V := by
  classical
  exact (paper11NegativeSupports G D).filter fun w => kCharge G D w = 3

noncomputable def paper11K4Supports (D : Finset V) : Finset V := by
  classical
  exact (paper11NegativeSupports G D).filter fun w => kCharge G D w = 4

noncomputable def paper11K3IncidentSupports (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (u : V) : Finset V := by
  classical
  exact (paper11K3Supports G D).filter fun w =>
    u ∈ paperChosenRepairSet G D hCan hmax w

noncomputable def paper11NegativeIncidentSupports (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (u : V) : Finset V := by
  classical
  exact (paper11NegativeSupports G D).filter fun w =>
    u ∈ paperChosenRepairSet G D hCan hmax w

noncomputable def paper11K3RightVertices (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) : Finset V := by
  classical
  exact (BPart G D).filter fun u =>
    (paper11K3IncidentSupports G D hCan hmax u).Nonempty

noncomputable def paper11K3Edges (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) : Finset (V × V) := by
  classical
  exact (paper11K3Supports G D).biUnion fun w =>
    (paperChosenRepairSet G D hCan hmax w).image fun u => (w, u)

noncomputable def paper11K3Compensation (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (u : V) : Finset V := by
  classical
  exact (paper11K3IncidentSupports G D hCan hmax u).biUnion fun w =>
    sharedCompensation G D (supportX G D w) u

theorem mem_paper11K3Supports {D : Finset V} {w : V}
    (hw : w ∈ paper11K3Supports G D) :
    w ∈ SPart G D ∧ externalCharge G D w < 0 ∧ kCharge G D w = 3 := by
  simp only [paper11K3Supports, paper11NegativeSupports, Finset.mem_filter] at hw
  exact ⟨hw.1.1, hw.1.2, hw.2⟩

theorem mem_paper11K4Supports {D : Finset V} {w : V}
    (hw : w ∈ paper11K4Supports G D) :
    w ∈ SPart G D ∧ externalCharge G D w < 0 ∧ kCharge G D w = 4 := by
  simp only [paper11K4Supports, paper11NegativeSupports, Finset.mem_filter] at hw
  exact ⟨hw.1.1, hw.1.2, hw.2⟩

theorem paper11K3_edge_mem {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w u : V} :
    (w, u) ∈ paper11K3Edges G D hCan hmax ↔
      w ∈ paper11K3Supports G D ∧
        u ∈ paperChosenRepairSet G D hCan hmax w := by
  classical
  simp [paper11K3Edges]

theorem paper11_chosen_profile {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w : V}
    (hw : w ∈ SPart G D) (ha : externalCharge G D w < 0) :
    ((kCharge G D w = 3 ∧ betaCharge G D w = 2 ∧
        (paperChosenRepairSet G D hCan hmax w).card = 2) ∨
      (kCharge G D w = 3 ∧ betaCharge G D w = 3 ∧
        (paperChosenRepairSet G D hCan hmax w).card = 1) ∨
      (kCharge G D w = 4 ∧ betaCharge G D w = 2 ∧
        (paperChosenRepairSet G D hCan hmax w).card = 2)) := by
  classical
  have hcond : w ∈ SPart G D ∧ externalCharge G D w < 0 := ⟨hw, ha⟩
  simp only [paperChosenRepairSet, dif_pos hcond]
  exact (Classical.choose_spec
    (paper8_chosen_repair_witness G hCan hmax hw ha)).2

theorem paper11K3Edges_subset_product {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    paper11K3Edges G D hCan hmax ⊆
      (paper11K3Supports G D).product
        (paper11K3RightVertices G D hCan hmax) := by
  classical
  intro e he
  obtain ⟨w, hw, u, hu, heq⟩ := by
    simpa [paper11K3Edges] using Finset.mem_biUnion.mp he
  subst e
  have hwInfo := mem_paper11K3Supports G hw
  have hlegal := paperChosenRepairSet_legal G hCan hmax hwInfo.1 hwInfo.2.1 u hu
  have hInc : w ∈ paper11K3IncidentSupports G D hCan hmax u := by
    simp [paper11K3IncidentSupports, hw, hu]
  have huR : u ∈ paper11K3RightVertices G D hCan hmax := by
    rw [paper11K3RightVertices]
    simp only [Finset.mem_filter]
    exact ⟨hlegal.1, ⟨w, hInc⟩⟩
  exact Finset.mem_product.mpr ⟨hw, huR⟩

theorem paper11K3_left_degree_eq_chosen_card {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w : V}
    (hw : w ∈ paper11K3Supports G D) :
    paper11LeftDegree (paper11K3Edges G D hCan hmax)
      (paper11K3RightVertices G D hCan hmax) w =
        (paperChosenRepairSet G D hCan hmax w).card := by
  classical
  let R := paperChosenRepairSet G D hCan hmax w
  have hImage :
      (paper11K3Edges G D hCan hmax).filter (fun e => e.1 = w) =
        R.image (fun u : V => (w, u)) := by
    ext e
    rcases e with ⟨a, b⟩
    simp only [Finset.mem_filter]
    rw [paper11K3_edge_mem G hCan hmax]
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨⟨ha, hb⟩, hab⟩
      have hEq : a = w := hab
      subst a
      exact ⟨b, hb, rfl⟩
    · rintro ⟨u, hu, heq⟩
      cases heq
      exact ⟨⟨hw, hu⟩, rfl⟩
  rw [paper11LeftDegree, hImage]
  have hinj : Function.Injective (fun u : V => (w, u)) := by
    intro a b hab
    exact congrArg Prod.snd hab
  simpa [R] using (Finset.card_image_of_injective R hinj)

theorem paper11K3_right_degree_eq_incident_card {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V} :
    paper11RightDegree (paper11K3Edges G D hCan hmax)
      (paper11K3Supports G D) u =
        (paper11K3IncidentSupports G D hCan hmax u).card := by
  classical
  let T := paper11K3IncidentSupports G D hCan hmax u
  have hImage :
      (paper11K3Edges G D hCan hmax).filter (fun e => e.2 = u) =
        T.image (fun w : V => (w, u)) := by
    ext e
    rcases e with ⟨a, b⟩
    simp only [Finset.mem_filter]
    rw [paper11K3_edge_mem G hCan hmax]
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨⟨ha, hb⟩, hbu⟩
      subst b
      exact ⟨a, Finset.mem_filter.mpr ⟨ha, hb⟩, rfl⟩
    · rintro ⟨w, hw, heq⟩
      cases heq
      have hw' : a ∈ paper11K3IncidentSupports G D hCan hmax u := by
        simpa [T] using hw
      simp only [paper11K3IncidentSupports, Finset.mem_filter] at hw'
      exact ⟨⟨hw'.1, hw'.2⟩, rfl⟩
  rw [paper11RightDegree, hImage]
  have hinj : Function.Injective (fun w : V => (w, u)) := by
    intro a b hab
    exact congrArg Prod.fst hab
  simpa [T] using (Finset.card_image_of_injective T hinj)

theorem paper11K3_left_degree_profile {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w : V}
    (hw : w ∈ paper11K3Supports G D) :
    paper11LeftDegree (paper11K3Edges G D hCan hmax)
      (paper11K3RightVertices G D hCan hmax) w = 1 ∨
    paper11LeftDegree (paper11K3Edges G D hCan hmax)
      (paper11K3RightVertices G D hCan hmax) w = 2 := by
  rw [paper11K3_left_degree_eq_chosen_card G hCan hmax hw]
  have hinfo := mem_paper11K3Supports G hw
  have hprofile := paper11_chosen_profile G hCan hmax hinfo.1 hinfo.2.1
  rcases hprofile with ⟨_, hβ, hcard⟩ | ⟨_, hβ, hcard⟩ | hbad
  · omega
  · omega
  · omega

theorem paper11K3_left_debt_bound {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w : V}
    (hw : w ∈ paper11K3Supports G D) :
    -externalCharge G D w ≤
      if paper11LeftDegree (paper11K3Edges G D hCan hmax)
          (paper11K3RightVertices G D hCan hmax) w = 1 then 4 else 7 := by
  have hinfo := mem_paper11K3Supports G hw
  have hvalues := lemma_7_2_charge_values G hCan hmax hinfo.1 hinfo.2.1
  have hprofile := paper11_chosen_profile G hCan hmax hinfo.1 hinfo.2.1
  rcases hprofile with ⟨_, hβ2, hcard2⟩ | ⟨_, hβ3, hcard1⟩ | hbad
  · have hdeg : paper11LeftDegree (paper11K3Edges G D hCan hmax)
        (paper11K3RightVertices G D hCan hmax) w = 2 := by
      rw [paper11K3_left_degree_eq_chosen_card G hCan hmax hw]
      exact hcard2
    rcases hvalues with hval | hval | hval <;> omega
  · have hdeg : paper11LeftDegree (paper11K3Edges G D hCan hmax)
        (paper11K3RightVertices G D hCan hmax) w = 1 := by
      rw [paper11K3_left_degree_eq_chosen_card G hCan hmax hw]
      exact hcard1
    rcases hvalues with hval | hval | hval <;> omega
  · omega

/-- The type-indexed form of the left interface: `(3,3)` supports have one
chosen edge and debt at most four, while `(3,2)` supports have two chosen
edges and debt at most seven.
-/
theorem paper11K3_left_type_interface {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w : V}
    (hw : w ∈ paper11K3Supports G D) :
    (kCharge G D w = 3 ∧ betaCharge G D w = 3 ∧
      paper11LeftDegree (paper11K3Edges G D hCan hmax)
        (paper11K3RightVertices G D hCan hmax) w = 1 ∧
      -externalCharge G D w ≤ 4) ∨
    (kCharge G D w = 3 ∧ betaCharge G D w = 2 ∧
      paper11LeftDegree (paper11K3Edges G D hCan hmax)
        (paper11K3RightVertices G D hCan hmax) w = 2 ∧
      -externalCharge G D w ≤ 7) := by
  have hinfo := mem_paper11K3Supports G hw
  have hprofile := paper11_chosen_profile G hCan hmax hinfo.1 hinfo.2.1
  have hvalues := lemma_7_2_charge_values G hCan hmax hinfo.1 hinfo.2.1
  rcases hprofile with hβ2 | hβ3 | h4
  · rcases hβ2 with ⟨hk, hβ, hcard⟩
    have hdeg : paper11LeftDegree (paper11K3Edges G D hCan hmax)
        (paper11K3RightVertices G D hCan hmax) w = 2 := by
      rw [paper11K3_left_degree_eq_chosen_card G hCan hmax hw]
      exact hcard
    rcases hvalues with hval | hval | hval
    · exact Or.inr ⟨hk, hβ, hdeg, by omega⟩
    · omega
    · omega
  · rcases hβ3 with ⟨hk, hβ, hcard⟩
    have hdeg : paper11LeftDegree (paper11K3Edges G D hCan hmax)
        (paper11K3RightVertices G D hCan hmax) w = 1 := by
      rw [paper11K3_left_degree_eq_chosen_card G hCan hmax hw]
      exact hcard
    rcases hvalues with hval | hval | hval
    · omega
    · exact Or.inl ⟨hk, hβ, hdeg, by omega⟩
    · omega
  · omega

theorem paper11K3_right_degree_profile {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V}
    (hu : u ∈ paper11K3RightVertices G D hCan hmax) :
    paper11RightDegree (paper11K3Edges G D hCan hmax)
        (paper11K3Supports G D) u = 1 ∨
    paper11RightDegree (paper11K3Edges G D hCan hmax)
        (paper11K3Supports G D) u = 2 := by
  rw [paper11K3_right_degree_eq_incident_card G hCan hmax]
  have hU : u ∈ BPart G D := (Finset.mem_filter.mp hu).1
  have hInc := (Finset.mem_filter.mp hu).2
  have hne : (paper11K3IncidentSupports G D hCan hmax u).Nonempty := hInc
  have hsub : paper11K3IncidentSupports G D hCan hmax u ⊆ SPart G D := by
    intro w hw
    exact (mem_paper11K3Supports G (Finset.mem_filter.mp hw).1).1
  have hnegative : ∀ w ∈ paper11K3IncidentSupports G D hCan hmax u,
      externalCharge G D w < 0 := by
    intro w hw
    exact (mem_paper11K3Supports G (Finset.mem_filter.mp hw).1).2.1
  have hrepair : ∀ w ∈ paper11K3IncidentSupports G D hCan hmax u,
      u ∈ paperChosenRepairSet G D hCan hmax w := by
    intro w hw
    exact (Finset.mem_filter.mp hw).2
  have hle := paper9_repair_degree_le_two G hCan hmax hU _ hsub hnegative hrepair
  have hpos : 0 < (paper11K3IncidentSupports G D hCan hmax u).card :=
    Finset.card_pos.mpr hne
  omega

theorem paper11K3_right_degree_one_resource {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V}
    (hu : u ∈ paper11K3RightVertices G D hCan hmax)
    (hdeg : paper11RightDegree (paper11K3Edges G D hCan hmax)
      (paper11K3Supports G D) u = 1) :
    4 ≤ vertexCharge G D u +
      ∑ q ∈ paper11K3Compensation G D hCan hmax u, externalCharge G D q := by
  classical
  have hcard := paper11K3_right_degree_eq_incident_card G hCan hmax (u := u)
  rw [hcard] at hdeg
  have hTne : (paper11K3IncidentSupports G D hCan hmax u).Nonempty :=
    (Finset.mem_filter.mp hu).2
  obtain ⟨w, hw⟩ := hTne
  have hTcard : (paper11K3IncidentSupports G D hCan hmax u).card = 1 := hdeg
  obtain ⟨v, hTv⟩ := Finset.card_eq_one.mp hTcard
  have hvw : v = w := by
    have hwv : w ∈ ({v} : Finset V) := by simpa [hTv] using hw
    exact (Finset.mem_singleton.mp hwv).symm
  have hTsing : paper11K3IncidentSupports G D hCan hmax u = {w} := by
    simpa [hvw] using hTv
  have hwInfo := mem_paper11K3Supports G (Finset.mem_filter.mp hw).1
  have hlegal := paperChosenRepairSet_legal G hCan hmax hwInfo.1 hwInfo.2.1 u
    (Finset.mem_filter.mp hw).2
  have hChosen : ChosenRepairRelation G D w
      (paperChosenRepairSet G D hCan hmax w) u :=
    ⟨(Finset.mem_filter.mp hw).2, hlegal⟩
  obtain h3 | h4 := paper9_single_repair_resource_bound G hCan hmax hlegal.1
      hwInfo.1 hwInfo.2.1 hChosen (Or.inl hwInfo.2.2)
  · have hUnion : paper11K3Compensation G D hCan hmax u =
        sharedCompensation G D (supportX G D w) u := by
      simp [paper11K3Compensation, hTsing]
    rw [hUnion]
    exact h3.2
  · omega

/-- A compensation point has a unique selected `B`-neighbor. This proof
uses the exact `D`-restricted neighborhood recorded by `sharedCompensation`.
-/
theorem paper11_compensation_unique_B_owner {D X Y : Finset V} {u v q : V}
    (hX : X ⊆ Z0Part G D) (hY : Y ⊆ Z0Part G D)
    (huB : u ∈ BPart G D) (hvB : v ∈ BPart G D)
    (hqU : q ∈ sharedCompensation G D X u)
    (hqV : q ∈ sharedCompensation G D Y v) : u = v := by
  classical
  obtain ⟨_, ⟨z, hzX, hNz⟩⟩ := (mem_sharedCompensation G D X u q).mp hqU
  obtain ⟨_, ⟨z', hzY, hNz'⟩⟩ := (mem_sharedCompensation G D Y v q).mp hqV
  have hvD := (mem_BPart G D v).mp hvB |>.1
  have hvN : v ∈ neighborhoodIn G D q := by
    rw [hNz']
    simp
  have hvPair : v ∈ ({u, z} : Finset V) := by
    rw [← hNz]
    exact hvN
  simp only [Finset.mem_insert, Finset.mem_singleton] at hvPair
  rcases hvPair with hvu | hvz
  · exact hvu.symm
  · subst v
    have hz0 : z ∈ Z0Part G D := hX hzX
    exact False.elim ((Finset.disjoint_left.mp (Z0_disjoint_B G) hz0 hvB).elim)

theorem paper11_card_two_distinct_members {T : Finset V} (hT : T.card = 2) :
    ∃ a b, a ≠ b ∧ a ∈ T ∧ b ∈ T := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by rw [hT]; omega)
  have herase : (T.erase a).card = 1 := by
    calc
      (T.erase a).card = T.card - 1 := Finset.card_erase_of_mem ha
      _ = 1 := by rw [hT]
  obtain ⟨b, hbEq⟩ := Finset.card_eq_one.mp herase
  have hbErase : b ∈ T.erase a := by rw [hbEq]; simp
  exact ⟨a, b, (Finset.mem_erase.mp hbErase).1.symm, ha,
    (Finset.mem_erase.mp hbErase).2⟩

/-- Compensation regions assigned to distinct selected vertices are
disjoint, as a consequence of the unique-owner lemma rather than an
assumption about the charge accounting.
-/
theorem paper11K3_compensation_disjoint {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u v : V}
    (hu : u ∈ BPart G D) (hv : v ∈ BPart G D) (hne : u ≠ v) :
    Disjoint (paper11K3Compensation G D hCan hmax u)
      (paper11K3Compensation G D hCan hmax v) := by
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
  have huv := paper11_compensation_unique_B_owner G hX hY hu hv hqU hqV
  exact hne huv

/-- The `k=4` negative supports are accounted for separately. Each one has
two distinct chosen repair neighbors; Lemma 9.1 gives chosen degree one at
each neighbor, and Lemma 9.3 gives the two independent `8`-unit edge bounds.
-/
theorem paper11_k4_separate_support {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w : V}
    (hw : w ∈ paper11K4Supports G D) :
    ∃ u v, u ≠ v ∧
      u ∈ paperChosenRepairSet G D hCan hmax w ∧
      v ∈ paperChosenRepairSet G D hCan hmax w ∧
      (paper11NegativeIncidentSupports G D hCan hmax u).card = 1 ∧
      (paper11NegativeIncidentSupports G D hCan hmax v).card = 1 ∧
      8 ≤ vertexCharge G D u +
        ∑ q ∈ sharedCompensation G D (supportX G D w) u,
          externalCharge G D q ∧
      8 ≤ vertexCharge G D v +
        ∑ q ∈ sharedCompensation G D (supportX G D w) v,
          externalCharge G D q := by
  classical
  have hwInfo := mem_paper11K4Supports G hw
  have hprofile := paper11_chosen_profile G hCan hmax hwInfo.1 hwInfo.2.1
  have hcard : (paperChosenRepairSet G D hCan hmax w).card = 2 := by
    rcases hprofile with h | h | h
    · omega
    · omega
    · exact h.2.2
  let R := paperChosenRepairSet G D hCan hmax w
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (by rw [hcard]; omega)
  have hEraseCard : (R.erase u).card = 1 := by
    calc
      (R.erase u).card = R.card - 1 := Finset.card_erase_of_mem hu
      _ = 1 := by dsimp [R]; rw [hcard]
  obtain ⟨v, hvEraseEq⟩ := Finset.card_eq_one.mp hEraseCard
  have hvErase : v ∈ R.erase u := by rw [hvEraseEq]; simp
  have hvR := (Finset.mem_erase.mp hvErase).2
  have hne : u ≠ v := (Finset.mem_erase.mp hvErase).1.symm
  have huChosen : u ∈ paperChosenRepairSet G D hCan hmax w := hu
  have hvChosen : v ∈ paperChosenRepairSet G D hCan hmax w := hvR
  have huLegal := paperChosenRepairSet_legal G hCan hmax hwInfo.1 hwInfo.2.1 u huChosen
  have hvLegal := paperChosenRepairSet_legal G hCan hmax hwInfo.1 hwInfo.2.1 v hvChosen
  let T_u := paper11NegativeIncidentSupports G D hCan hmax u
  let T_v := paper11NegativeIncidentSupports G D hCan hmax v
  have hwTu : w ∈ T_u := by
    simp [T_u, paper11NegativeIncidentSupports, paper11NegativeSupports,
      hwInfo.1, hwInfo.2.1, huChosen]
  have hwTv : w ∈ T_v := by
    simp [T_v, paper11NegativeIncidentSupports, paper11NegativeSupports,
      hwInfo.1, hwInfo.2.1, hvChosen]
  have hTuSub : T_u ⊆ SPart G D := by
    intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  have hTvSub : T_v ⊆ SPart G D := by
    intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  have hTuNeg : ∀ x ∈ T_u, externalCharge G D x < 0 := by
    intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
  have hTvNeg : ∀ x ∈ T_v, externalCharge G D x < 0 := by
    intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
  have hTuChosen : ∀ x ∈ T_u, u ∈ paperChosenRepairSet G D hCan hmax x := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hTvChosen : ∀ x ∈ T_v, v ∈ paperChosenRepairSet G D hCan hmax x := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hTuCard := paper9_repair_degree_eq_one_at_k4 G hCan hmax huLegal.1
    T_u hTuSub hTuNeg hTuChosen hwTu hwInfo.2.2
  have hTvCard := paper9_repair_degree_eq_one_at_k4 G hCan hmax hvLegal.1
    T_v hTvSub hTvNeg hTvChosen hwTv hwInfo.2.2
  have hChosenU : ChosenRepairRelation G D w
      (paperChosenRepairSet G D hCan hmax w) u := ⟨huChosen, huLegal⟩
  have hChosenV : ChosenRepairRelation G D w
      (paperChosenRepairSet G D hCan hmax w) v := ⟨hvChosen, hvLegal⟩
  have hBoundU := paper9_single_repair_resource_bound G hCan hmax huLegal.1
    hwInfo.1 hwInfo.2.1 hChosenU (Or.inr hwInfo.2.2)
  have hBoundV := paper9_single_repair_resource_bound G hCan hmax hvLegal.1
    hwInfo.1 hwInfo.2.1 hChosenV (Or.inr hwInfo.2.2)
  have h8U : 8 ≤ vertexCharge G D u +
      ∑ q ∈ sharedCompensation G D (supportX G D w) u,
        externalCharge G D q := by
    rcases hBoundU with h3 | h4
    · omega
    · exact h4.2
  have h8V : 8 ≤ vertexCharge G D v +
      ∑ q ∈ sharedCompensation G D (supportX G D w) v,
        externalCharge G D q := by
    rcases hBoundV with h3 | h4
    · omega
    · exact h4.2
  exact ⟨u, v, hne, huChosen, hvChosen, by simpa [T_u] using hTuCard,
    by simpa [T_v] using hTvCard, h8U, h8V⟩

theorem paper11_k4_support_total_resource_ge_14 {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w : V}
    (hw : w ∈ paper11K4Supports G D) :
    ∃ u v, u ≠ v ∧
      16 ≤
        (vertexCharge G D u +
          ∑ q ∈ sharedCompensation G D (supportX G D w) u,
            externalCharge G D q) +
        (vertexCharge G D v +
          ∑ q ∈ sharedCompensation G D (supportX G D w) v,
            externalCharge G D q) ∧
      14 ≤
        (vertexCharge G D u +
          ∑ q ∈ sharedCompensation G D (supportX G D w) u,
            externalCharge G D q) +
        (vertexCharge G D v +
          ∑ q ∈ sharedCompensation G D (supportX G D w) v,
            externalCharge G D q) := by
  obtain ⟨u, v, hne, _, _, _, _, h8u, h8v⟩ :=
    paper11_k4_separate_support G hCan hmax hw
  refine ⟨u, v, hne, ?_, ?_⟩ <;> omega

/-! The degree-two `k=3` case of Lemma 9.2 is normalized as one union of
compensation points. In its `x=0` branch that union is the single shared
point, which is promoted to an actual `Q*` witness from Section 10.
-/
theorem paper11K3_degree_two_compensation_cases {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V}
    (hu : u ∈ paper11K3RightVertices G D hCan hmax)
    (hdeg : paper11RightDegree (paper11K3Edges G D hCan hmax)
      (paper11K3Supports G D) u = 2) :
    (xCharge G D u = 1 ∧ vertexCharge G D u = 11 ∧
      paper11K3Compensation G D hCan hmax u = ∅) ∨
    (xCharge G D u = 0 ∧ vertexCharge G D u = 0 ∧
      ∃ q, paper11K3Compensation G D hCan hmax u = {q} ∧
        externalCharge G D q = 4 ∧
        q ∈ paper10SpecialQSet G hCan hmax ∧
        ∃ data : Paper10SpecialWitness G hCan hmax q, data.u = u) := by
  classical
  have hTcard : (paper11K3IncidentSupports G D hCan hmax u).card = 2 := by
    have := paper11K3_right_degree_eq_incident_card G hCan hmax (u := u)
    rw [this] at hdeg
    exact hdeg
  let T := paper11K3IncidentSupports G D hCan hmax u
  have huB : u ∈ BPart G D := (Finset.mem_filter.mp hu).1
  have hTsub : T ⊆ SPart G D := by
    intro w hw
    exact (mem_paper11K3Supports G (Finset.mem_filter.mp hw).1).1
  have hTnegative : ∀ w ∈ T, externalCharge G D w < 0 := by
    intro w hw
    exact (mem_paper11K3Supports G (Finset.mem_filter.mp hw).1).2.1
  have hTrepair : ∀ w ∈ T, u ∈ paperChosenRepairSet G D hCan hmax w := by
    intro w hw
    exact (Finset.mem_filter.mp hw).2
  have h9 := paper9_lemma_9_2 G hCan hmax huB T hTsub hTnegative
    hTrepair hTcard
  rcases h9.2 with hcase | hcase
  · rcases hcase with ⟨hx, hs, hcharge, hempty⟩
    have hUnion : paper11K3Compensation G D hCan hmax u = ∅ := by
      ext q
      simp only [paper11K3Compensation, Finset.mem_biUnion]
      constructor
      · rintro ⟨w, hw, hq⟩
        rw [hempty w hw] at hq
        simp at hq
      · intro hq
        simp at hq
    exact Or.inl ⟨hx, hcharge, hUnion⟩
  · rcases hcase with ⟨hx, hs, hcharge, q, z, hcomp, hqS, hqβ,
      hqk, hqCharge, hz0, hqN, hzAll⟩
    obtain ⟨w₁, w₂, hne, hw₁, hw₂⟩ :=
      paper11_card_two_distinct_members hTcard
    have hUnion : paper11K3Compensation G D hCan hmax u = {q} := by
      ext r
      simp only [paper11K3Compensation, Finset.mem_biUnion]
      constructor
      · rintro ⟨w, hw, hr⟩
        rw [hcomp w hw] at hr
        exact hr
      · intro hr
        have hrq : r = q := Finset.mem_singleton.mp hr
        subst r
        refine ⟨w₁, hw₁, ?_⟩
        rw [hcomp w₁ hw₁]
        simp
    have hw₁Info := mem_paper11K3Supports G (Finset.mem_filter.mp hw₁).1
    have hw₂Info := mem_paper11K3Supports G (Finset.mem_filter.mp hw₂).1
    let hdata : Paper10SpecialWitness G hCan hmax q := {
      u := u
      w₁ := w₁
      w₂ := w₂
      z := z
      w_ne := hne
      w₁S := hw₁Info.1
      w₂S := hw₂Info.1
      w₁negative := hw₁Info.2.1
      w₂negative := hw₂Info.2.1
      uB := huB
      repair₁ := (Finset.mem_filter.mp hw₁).2
      repair₂ := (Finset.mem_filter.mp hw₂).2
      qShared₁ := by rw [hcomp w₁ hw₁]; simp
      qShared₂ := by rw [hcomp w₂ hw₂]; simp
      zSupport₁ := hzAll w₁ hw₁
      zSupport₂ := hzAll w₂ hw₂
      qNeighborhood := hqN
    }
    have hqQ : q ∈ paper10SpecialQSet G hCan hmax :=
      (mem_paper10SpecialQSet G hCan hmax q).mpr ⟨hdata⟩
    exact Or.inr ⟨hx, hcharge, q, hUnion, hqCharge, hqQ, hdata, by rfl⟩

/-- Any two Section 10 witnesses for the same special compensation point
name the same selected `B`-owner. -/
theorem paper11_special_witness_owner_unique {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {q : V}
    (d₁ d₂ : Paper10SpecialWitness G hCan hmax q) : d₁.u = d₂.u := by
  have hX₁ : supportX G D d₁.w₁ ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D d₁.w₁ z).mp hz |>.1
  have hX₂ : supportX G D d₂.w₁ ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D d₂.w₁ z).mp hz |>.1
  exact paper11_compensation_unique_B_owner G hX₁ hX₂ d₁.uB d₂.uB
    d₁.qShared₁ d₂.qShared₁

theorem paper11_special_witness_owner_unique_of_eq {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {q₁ q₂ : V}
    (hq : q₁ = q₂)
    (d₁ : Paper10SpecialWitness G hCan hmax q₁)
    (d₂ : Paper10SpecialWitness G hCan hmax q₂) : d₁.u = d₂.u := by
  subst q₂
  exact paper11_special_witness_owner_unique G hCan hmax d₁ d₂

noncomputable def paper11K3SpecialBudgetVertices (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) : Finset V := by
  classical
  exact (paper11K3RightVertices G D hCan hmax).filter fun u =>
    xCharge G D u = 0 ∧
      paper11RightDegree (paper11K3Edges G D hCan hmax)
        (paper11K3Supports G D) u = 2

theorem paper11_special_witness_for_budget_vertex {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V}
    (hu : u ∈ paper11K3SpecialBudgetVertices G D hCan hmax) :
    ∃ q, q ∈ paper10SpecialQSet G hCan hmax ∧
      ∃ data : Paper10SpecialWitness G hCan hmax q, data.u = u := by
  have huR : u ∈ paper11K3RightVertices G D hCan hmax :=
    (Finset.mem_filter.mp hu).1
  have hx : xCharge G D u = 0 := (Finset.mem_filter.mp hu).2.1
  have hdeg : paper11RightDegree (paper11K3Edges G D hCan hmax)
      (paper11K3Supports G D) u = 2 := (Finset.mem_filter.mp hu).2.2
  rcases paper11K3_degree_two_compensation_cases G hCan hmax huR hdeg with
    hcase | hcase
  · omega
  · obtain ⟨hxcase, _, q, _, _, hqQ, data, howner⟩ := hcase
    exact ⟨q, hqQ, data, howner⟩

theorem paper11K3SpecialBudget_card_le_Qstar {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (paper11K3SpecialBudgetVertices G D hCan hmax).card ≤
      (paper10SpecialQSet G hCan hmax).card := by
  classical
  let P := paper11K3SpecialBudgetVertices G D hCan hmax
  let Q := paper10SpecialQSet G hCan hmax
  let f : {u : V // u ∈ P} → {q : V // q ∈ Q} := fun x => by
    let hspec := paper11_special_witness_for_budget_vertex G hCan hmax
      (u := x.1) x.2
    exact ⟨Classical.choose hspec, (Classical.choose_spec hspec).1⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hspecA := paper11_special_witness_for_budget_vertex G hCan hmax
      (u := a.1) a.2
    have hspecB := paper11_special_witness_for_budget_vertex G hCan hmax
      (u := b.1) b.2
    obtain ⟨da, hda⟩ := (Classical.choose_spec hspecA).2
    obtain ⟨db, hdb⟩ := (Classical.choose_spec hspecB).2
    have hq : Classical.choose hspecA = Classical.choose hspecB := by
      change (f a).1 = (f b).1
      exact congrArg Subtype.val hab
    have howner := paper11_special_witness_owner_unique_of_eq G hCan hmax
      hq da db
    rw [hda, hdb] at howner
    exact Subtype.ext howner
  have hcard := Finset.card_le_card_of_injective hinj
  simpa [P, Q] using hcard

theorem paper11_Qstar_special_cost_bound {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    (hNoIso : HasNoIsolatedVertices G) :
    7 * ((paper10SpecialQSet G hCan hmax).card : ℤ) ≤
      7 * ((incidenceTotal G D - (Z0Part G D).card : ℕ) : ℤ) := by
  have h10 := paper10_lemma_10_1 G hCan hmax hNoIso
  have hcast : ((paper10SpecialQSet G hCan hmax).card : ℤ) ≤
      ((incidenceTotal G D - (Z0Part G D).card : ℕ) : ℤ) := by
    exact_mod_cast h10
  nlinarith

theorem paper11K3SpecialBudget_cost_bound {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    (hNoIso : HasNoIsolatedVertices G) :
    7 * ((paper11K3SpecialBudgetVertices G D hCan hmax).card : ℤ) ≤
      7 * ((incidenceTotal G D - (Z0Part G D).card : ℕ) : ℤ) := by
  have hP := paper11K3SpecialBudget_card_le_Qstar G hCan hmax
  have hPc : ((paper11K3SpecialBudgetVertices G D hCan hmax).card : ℤ) ≤
      ((paper10SpecialQSet G hCan hmax).card : ℤ) := by exact_mod_cast hP
  have hQ := paper11_Qstar_special_cost_bound G hCan hmax hNoIso
  nlinarith

noncomputable def paper11K3AvailableResource (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (u : V) : ℤ := by
  classical
  exact vertexCharge G D u +
    (∑ q ∈ paper11K3Compensation G D hCan hmax u, externalCharge G D q) +
      if u ∈ paper11K3SpecialBudgetVertices G D hCan hmax then 7 else 0

theorem paper11K3SpecialBudget_bonus_sum {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ u ∈ paper11K3RightVertices G D hCan hmax,
      if u ∈ paper11K3SpecialBudgetVertices G D hCan hmax then (7 : ℤ)
      else 0) =
      7 * ((paper11K3SpecialBudgetVertices G D hCan hmax).card : ℤ) := by
  classical
  let R := paper11K3RightVertices G D hCan hmax
  let P := paper11K3SpecialBudgetVertices G D hCan hmax
  have hfilter : R.filter (fun u => u ∈ P) = P := by
    ext u
    simp [P, paper11K3SpecialBudgetVertices, R]
  calc
    (∑ u ∈ R, if u ∈ P then (7 : ℤ) else 0) =
        ∑ u ∈ R.filter (fun u => u ∈ P), (7 : ℤ) := by
          rw [Finset.sum_filter]
    _ = ∑ u ∈ P, (7 : ℤ) := by rw [hfilter]
    _ = 7 * (P.card : ℤ) := by simp <;> ring

theorem paper11K3AvailableResource_sum_decomposition {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ u ∈ paper11K3RightVertices G D hCan hmax,
      paper11K3AvailableResource G D hCan hmax u) =
      (∑ u ∈ paper11K3RightVertices G D hCan hmax,
        (vertexCharge G D u +
          ∑ q ∈ paper11K3Compensation G D hCan hmax u,
            externalCharge G D q)) +
      7 * ((paper11K3SpecialBudgetVertices G D hCan hmax).card : ℤ) := by
  classical
  simp only [paper11K3AvailableResource, Finset.sum_add_distrib]
  rw [paper11K3SpecialBudget_bonus_sum G hCan hmax]

theorem paper11K3_right_resource_bound {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V}
    (hu : u ∈ paper11K3RightVertices G D hCan hmax) :
    (if paper11RightDegree (paper11K3Edges G D hCan hmax)
        (paper11K3Supports G D) u = 1 then 4 else 11) ≤
      paper11K3AvailableResource G D hCan hmax u := by
  classical
  rcases paper11K3_right_degree_profile G hCan hmax hu with h1 | h2
  · have hbase := paper11K3_right_degree_one_resource G hCan hmax hu h1
    unfold paper11K3AvailableResource
    split <;> simp_all <;> omega
  · rcases paper11K3_degree_two_compensation_cases G hCan hmax hu h2 with
      hcase | hcase
    · rcases hcase with ⟨hx, hcharge, hcomp⟩
      unfold paper11K3AvailableResource
      rw [hcharge, hcomp]
      simp
      split <;> omega
    · rcases hcase with ⟨hx, hcharge, q, hcomp, hqcharge, hqQ,
        hdata, howner⟩
      have hbudget : u ∈ paper11K3SpecialBudgetVertices G D hCan hmax := by
        simp [paper11K3SpecialBudgetVertices, hu, hx, h2]
      unfold paper11K3AvailableResource
      rw [hcharge, hcomp]
      simp [hbudget, hqcharge, h2]

/-- Actual degree table adapter for Lemma 11.1 on the fixed chosen relation.
The `k=4` part has already been removed by `paper11_k4_separate_support`.
-/
theorem paper11_chosen_k3_charge_balance {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ w ∈ paper11K3Supports G D, -externalCharge G D w) ≤
      ∑ u ∈ paper11K3RightVertices G D hCan hmax,
        paper11K3AvailableResource G D hCan hmax u := by
  classical
  apply paper11_pure_k3_charge_balance
    (paper11K3Supports G D) (paper11K3RightVertices G D hCan hmax)
    (paper11K3Edges G D hCan hmax)
    (paper11K3Edges_subset_product G hCan hmax)
    (fun w => -externalCharge G D w)
    (paper11K3AvailableResource G D hCan hmax)
  · intro w hw
    exact paper11K3_left_degree_profile G hCan hmax hw
  · intro u hu
    exact paper11K3_right_degree_profile G hCan hmax hu
  · intro w hw
    exact paper11K3_left_debt_bound G hCan hmax hw
  · intro u hu
    exact paper11K3_right_resource_bound G hCan hmax hu

end C6BipartiteDomination

