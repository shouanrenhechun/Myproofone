/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import C6BipartiteDomination.PaperSection9

/-! # Paper section 10: repeated incidence resources -/

namespace C6BipartiteDomination

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

/-- The exact data witnessed by a special compensation vertex from case (b)
of Lemma 9.2. In particular, the two high-support vertices are distinct,
and each is related to `u` by the globally chosen repair relation. -/
structure Paper10SpecialWitness
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (q : V) where
  u : V
  w₁ : V
  w₂ : V
  z : V
  w_ne : w₁ ≠ w₂
  w₁S : w₁ ∈ SPart G D
  w₂S : w₂ ∈ SPart G D
  w₁negative : externalCharge G D w₁ < 0
  w₂negative : externalCharge G D w₂ < 0
  uB : u ∈ BPart G D
  repair₁ : u ∈ paperChosenRepairSet G D hCan hmax w₁
  repair₂ : u ∈ paperChosenRepairSet G D hCan hmax w₂
  qShared₁ : q ∈ sharedCompensation G D (supportX G D w₁) u
  qShared₂ : q ∈ sharedCompensation G D (supportX G D w₂) u
  zSupport₁ : z ∈ supportX G D w₁
  zSupport₂ : z ∈ supportX G D w₂
  qNeighborhood : neighborhoodIn G D q = {u, z}

/-- A vertex satisfying the special incidence pattern of Lemma 9.2(b). -/
def IsPaper10SpecialQ
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (q : V) : Prop :=
  Nonempty (Paper10SpecialWitness G hCan hmax q)

/-- The paper's `Q*`: all special compensation vertices from double repair
vertices in the chosen repair graph. -/
noncomputable def paper10SpecialQSet
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) : Finset V := by
  classical
  exact Finset.univ.filter (IsPaper10SpecialQ G hCan hmax)

theorem mem_paper10SpecialQSet
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (q : V) :
    q ∈ paper10SpecialQSet G hCan hmax ↔ IsPaper10SpecialQ G hCan hmax q := by
  classical
  simp [paper10SpecialQSet]

/-- The selected endpoint, encoded as an option so the definition is total
also for vertices outside `Q*`. -/
noncomputable def paper10SpecialEndpoint
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (q : V) : Option V := by
  classical
  exact if h : IsPaper10SpecialQ G hCan hmax q then
    some (Classical.choice h).z else none

theorem paper10SpecialEndpoint_mem
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {q : V}
    (hq : IsPaper10SpecialQ G hCan hmax q) :
    ∃ z ∈ Z0Part G D, paper10SpecialEndpoint G hCan hmax q = some z := by
  let data := Classical.choice hq
  have hz0 : data.z ∈ Z0Part G D :=
    (mem_supportX G D data.w₁ data.z).mp data.zSupport₁ |>.1
  refine ⟨data.z, hz0, ?_⟩
  simp [paper10SpecialEndpoint, hq, data]

/-- Every `Z₀` vertex has an `S`-neighbor, provided the ambient graph has no
isolated vertices. The fact that it has no selected neighbors follows from
its membership in `Z`; a `W₀` neighbor is excluded by the definition of `Z₀`;
and a private `P`-neighbor would force the vertex into `B`. -/
theorem paper10_z0_has_S_neighbor
    {D : Finset V} (hNoIso : HasNoIsolatedVertices G) {z : V}
    (hz : z ∈ Z0Part G D) :
    ∃ q ∈ SPart G D, G.Adj z q := by
  classical
  obtain ⟨q, hqAdj⟩ := hNoIso z
  have hzInfo := (mem_Z0Part G D z).mp hz
  have hzPart := (mem_ZPart G D z).mp hzInfo.1
  have hqNotD : q ∉ D := by
    intro hqD
    exact hzPart.2 q hqD hqAdj
  have hqNotW0 : q ∉ W0Part G D := by
    intro hqW0
    exact hzInfo.2 q hqW0 hqAdj
  have hqWB : q ∈ WBPart G D := (mem_WBPart G D q).mpr ⟨hqNotD, hqNotW0⟩
  have hqNotP : q ∉ PPart G D := by
    intro hqP
    obtain ⟨b, hbB, hqPriv⟩ := (mem_PPart G D q).mp hqP
    have hzEqB : z = b :=
      ((mem_privateExternalNeighbors G D b q).mp hqPriv).2 z hzPart.1 |>.mp hqAdj
    subst b
    exact (Finset.disjoint_left.mp (Z0_disjoint_B G (D := D)) hz hbB).elim
  exact ⟨q, (mem_SPart G D q).mpr ⟨hqWB, hqNotP⟩, hqAdj⟩

/-- Special vertices assigned to a fixed `z`. -/
noncomputable def paper10SpecialFiber
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (Q : Finset V)
    (hQ : ∀ q ∈ Q, IsPaper10SpecialQ G hCan hmax q) (z : V) : Finset V := by
  classical
  exact Q.filter (fun q => paper10SpecialEndpoint G hCan hmax q = some z)

/-- For every `z ∈ Z₀`, its special vertices together with one additional
`S`-neighbor fit in the `S`-neighborhood of `z`. -/
theorem paper10_fiber_plus_one_le_degree
    {D Q : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    (hNoIso : HasNoIsolatedVertices G)
    (hQ : ∀ q ∈ Q, IsPaper10SpecialQ G hCan hmax q) {z : V}
    (hz : z ∈ Z0Part G D) :
    (paper10SpecialFiber G hCan hmax Q hQ z).card + 1 ≤ degreeTo G (SPart G D) z := by
  classical
  let F := paper10SpecialFiber G hCan hmax Q hQ z
  by_cases hF : F = ∅
  · obtain ⟨r, hrS, hrAdj⟩ := paper10_z0_has_S_neighbor G hNoIso hz
    have hdeg : r ∈ (SPart G D).filter (fun v => G.Adj z v) :=
      Finset.mem_filter.mpr ⟨hrS, hrAdj⟩
    have hpos : 1 ≤ ((SPart G D).filter (fun v => G.Adj z v)).card := by
      have := Finset.card_pos.mpr ⟨r, hdeg⟩
      omega
    simpa [degreeTo, F, hF] using hpos
  · obtain ⟨q, hqF⟩ := Finset.nonempty_iff_ne_empty.mpr hF
    have hqQ : q ∈ Q := (Finset.mem_filter.mp hqF).1
    have hqSpecial := hQ q hqQ
    let data := Classical.choice hqSpecial
    have hqZopt : paper10SpecialEndpoint G hCan hmax q = some z :=
      (Finset.mem_filter.mp hqF).2
    have hqZ : data.z = z := by
      change (Classical.choice hqSpecial).z = z
      simpa [paper10SpecialEndpoint, hqSpecial] using hqZopt
    have hExtraS : data.w₁ ∈ SPart G D := data.w₁S
    have hzExtra : G.Adj z data.w₁ := by
      rw [← hqZ]
      have := (mem_supportX G D data.w₁ data.z).mp data.zSupport₁
      exact this.2.symm
    have hqNeExtra : q ≠ data.w₁ := by
      intro hEq
      have hnegQ : externalCharge G D q < 0 := by
        rw [hEq]
        exact data.w₁negative
      have hqCharge := paper9_shared_external_charge_eq_four G
        (fun x hx => (mem_supportX G D data.w₁ x).mp hx |>.1)
        (q := q) data.uB data.qShared₁
      omega
    have hExtraNotF : data.w₁ ∉ F := by
      intro hwF
      have hwQ : data.w₁ ∈ Q := (Finset.mem_filter.mp hwF).1
      have hwSpecial := hQ data.w₁ hwQ
      have hNeg := data.w₁negative
      have hwZopt : paper10SpecialEndpoint G hCan hmax data.w₁ = some z :=
        (Finset.mem_filter.mp hwF).2
      let hwData := Classical.choice hwSpecial
      have hX : supportX G D hwData.w₁ ⊆ Z0Part G D := by
        intro x hx
        exact (mem_supportX G D hwData.w₁ x).mp hx |>.1
      have hCharge := paper9_shared_external_charge_eq_four G hX
        (q := data.w₁) hwData.uB hwData.qShared₁
      omega
    have hFiberSub : F ⊆ (SPart G D).filter (fun v => G.Adj z v) := by
      intro r hrF
      have hrQ : r ∈ Q := (Finset.mem_filter.mp hrF).1
      have hrSpecial := hQ r hrQ
      let hrData := Classical.choice hrSpecial
      have hrZopt : paper10SpecialEndpoint G hCan hmax r = some z :=
        (Finset.mem_filter.mp hrF).2
      have hrEq : hrData.z = z := by
        have heq : (Classical.choice hrSpecial).z = z := by
          simpa [paper10SpecialEndpoint, hrSpecial] using hrZopt
        simpa [hrData] using heq
      have hrX : supportX G D hrData.w₁ ⊆ Z0Part G D := by
        intro x hx
        exact (mem_supportX G D hrData.w₁ x).mp hx |>.1
      have hrProfile := paper9_shared_compensation_profile G hrX hrData.uB hrData.qShared₁
      have hrNeU : hrData.z ≠ hrData.u := by
        intro hEq
        have hz0 : hrData.z ∈ Z0Part G D :=
          (mem_supportX G D hrData.w₁ hrData.z).mp hrData.zSupport₁ |>.1
        rw [hEq] at hz0
        exact (Finset.disjoint_left.mp (Z0_disjoint_B G (D := D)) hz0 hrData.uB).elim
      have hrAdjZ : G.Adj z r := by
        have hzIn : z ∈ neighborhoodIn G D r := by
          rw [hrData.qNeighborhood]
          simp [hrEq]
        exact (mem_neighborhoodIn G D r z).mp hzIn |>.2.symm
      exact Finset.mem_filter.mpr ⟨hrProfile.1, hrAdjZ⟩
    have hUnionSub : F ∪ {data.w₁} ⊆ (SPart G D).filter (fun v => G.Adj z v) := by
      intro r hr
      rcases Finset.mem_union.mp hr with hrF | hrExtra
      · exact hFiberSub hrF
      · have hrEq : r = data.w₁ := Finset.mem_singleton.mp hrExtra
        subst r
        exact Finset.mem_filter.mpr ⟨hExtraS, hzExtra⟩
    have hdisj : Disjoint F {data.w₁} := by
      rw [Finset.disjoint_singleton_right]
      exact hExtraNotF
    have hcard := Finset.card_le_card hUnionSub
    rw [Finset.card_union_of_disjoint hdisj] at hcard
    simpa [degreeTo, F] using hcard

/-- Lemma 10.1: the special vertices inject into the repeated-incidence
budget `m - |Z₀|`. -/
theorem paper10_lemma_10_1
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    (hNoIso : HasNoIsolatedVertices G) :
    (paper10SpecialQSet G hCan hmax).card ≤
      incidenceTotal G D - (Z0Part G D).card := by
  classical
  let Q := paper10SpecialQSet G hCan hmax
  have hQ : ∀ q ∈ Q, IsPaper10SpecialQ G hCan hmax q := by
    intro q hq
    exact (mem_paper10SpecialQSet G hCan hmax q).mp hq
  by_cases hQempty : Q = ∅
  · have hlocal : ∀ z ∈ Z0Part G D, 1 ≤ degreeTo G (SPart G D) z := by
      intro z hz
      obtain ⟨q, hqS, hqAdj⟩ := paper10_z0_has_S_neighbor G hNoIso hz
      unfold degreeTo
      have hmem : q ∈ (SPart G D).filter (fun v => G.Adj z v) :=
        Finset.mem_filter.mpr ⟨hqS, hqAdj⟩
      have := Finset.card_pos.mpr ⟨q, hmem⟩
      omega
    have hsum := Finset.sum_le_sum hlocal
    have hinc := sum_degreeTo_symm G (Z0Part G D) (SPart G D)
    have hinc' : (∑ z ∈ Z0Part G D, degreeTo G (SPart G D) z) =
        incidenceTotal G D := by
      rw [hinc]
      simp [incidenceTotal, kCharge]
    have hzbound : (Z0Part G D).card ≤ incidenceTotal G D := by
      calc
        (Z0Part G D).card = ∑ z ∈ Z0Part G D, (1 : ℕ) := by simp
        _ ≤ ∑ z ∈ Z0Part G D, degreeTo G (SPart G D) z := hsum
        _ = incidenceTotal G D := hinc'
    simp only [Q, hQempty, Finset.card_empty]
    omega
  · obtain ⟨q₀, hq₀⟩ := Finset.nonempty_iff_ne_empty.mpr hQempty
    let zOf := fun q : V => (paper10SpecialEndpoint G hCan hmax q).getD q₀
    have hmap : ∀ q ∈ Q, zOf q ∈ Z0Part G D := by
      intro q hq
      obtain ⟨z, hz, he⟩ := paper10SpecialEndpoint_mem G hCan hmax (hQ q hq)
      change (paper10SpecialEndpoint G hCan hmax q).getD q₀ ∈ Z0Part G D
      rw [he]
      simpa using hz
    have hmapSet : (Q : Set V).MapsTo zOf (Z0Part G D : Set V) := by
      intro q hq
      exact hmap q hq
    let fiber := fun z => Q.filter (fun q => zOf q = z)
    have hget : ∀ q ∈ Q, ∀ z,
        (zOf q = z ↔ paper10SpecialEndpoint G hCan hmax q = some z) := by
      intro q hq z
      obtain ⟨z', hz', he'⟩ := paper10SpecialEndpoint_mem G hCan hmax (hQ q hq)
      change (paper10SpecialEndpoint G hCan hmax q).getD q₀ = z ↔
        paper10SpecialEndpoint G hCan hmax q = some z
      rw [he']
      simp
    have hfiber : ∀ z, fiber z = paper10SpecialFiber G hCan hmax Q hQ z := by
      intro z
      ext q
      simp only [fiber, paper10SpecialFiber, Finset.mem_filter]
      constructor
      · rintro ⟨hqQ, hqz⟩
        exact ⟨hqQ, (hget q hqQ z).mp hqz⟩
      · rintro ⟨hqQ, he⟩
        exact ⟨hqQ, (hget q hqQ z).mpr he⟩
    have hcard := Finset.card_eq_sum_card_fiberwise (s := Q)
      (t := Z0Part G D) (f := zOf) hmapSet
    have hsumLocal :
        (∑ z ∈ Z0Part G D, ((fiber z).card + 1)) ≤
          ∑ z ∈ Z0Part G D, degreeTo G (SPart G D) z := by
      apply Finset.sum_le_sum
      intro z hz
      rw [hfiber z]
      exact paper10_fiber_plus_one_le_degree G hCan hmax hNoIso hQ hz
    have hinc := sum_degreeTo_symm G (Z0Part G D) (SPart G D)
    have hinc' : (∑ z ∈ Z0Part G D, degreeTo G (SPart G D) z) =
        incidenceTotal G D := by
      rw [hinc]
      simp [incidenceTotal, kCharge]
    have hbound : Q.card + (Z0Part G D).card ≤ incidenceTotal G D := by
      calc
        Q.card + (Z0Part G D).card =
            (∑ z ∈ Z0Part G D, (fiber z).card) + (Z0Part G D).card := by rw [hcard]
        _ = ∑ z ∈ Z0Part G D, ((fiber z).card + 1) := by simp [Finset.sum_add_distrib]
        _ ≤ ∑ z ∈ Z0Part G D, degreeTo G (SPart G D) z := hsumLocal
        _ = incidenceTotal G D := hinc'
    change Q.card ≤ incidenceTotal G D - (Z0Part G D).card
    omega

end C6BipartiteDomination

