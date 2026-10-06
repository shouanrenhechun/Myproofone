/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import C6BipartiteDomination.A5

/-! # A6: exact charge identity -/

namespace C6BipartiteDomination

open Finset BigOperators
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

/-- Open degree from `v` into a specified finite vertex set. -/
noncomputable def degreeTo (A : Finset V) (v : V) : ℕ := by
  classical
  exact (A.filter fun u => G.Adj v u).card

open Classical in
theorem degreeTo_as_sum (A : Finset V) (v : V) :
    degreeTo G A v = ∑ u ∈ A, if G.Adj v u then 1 else 0 := by
  classical
  unfold degreeTo
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

open Classical in
theorem mem_degreeTo (A : Finset V) (v u : V) :
    u ∈ A.filter (fun x => G.Adj v x) ↔ u ∈ A ∧ G.Adj v u := by
  simp

/-- Vertices in `W` with at least one `B`-neighbor. -/
noncomputable def WBPart (D : Finset V) : Finset V :=
  (Finset.univ \ D) \ W0Part G D

/-- The union of all private external neighborhoods of selected non-isolated
vertices. -/
noncomputable def PPart (D : Finset V) : Finset V := by
  classical
  exact (BPart G D).biUnion (fun b => privateExternalNeighbors G D b)

/-- Non-private vertices of `W_B`. -/
noncomputable def SPart (D : Finset V) : Finset V := WBPart G D \ PPart G D

theorem mem_WBPart (D : Finset V) (w : V) :
    w ∈ WBPart G D ↔ w ∉ D ∧ w ∉ W0Part G D := by
  simp [WBPart, Finset.mem_sdiff]

theorem mem_PPart (D : Finset V) (w : V) :
    w ∈ PPart G D ↔ ∃ b ∈ BPart G D, w ∈ privateExternalNeighbors G D b := by
  classical
  simp [PPart]

theorem mem_SPart (D : Finset V) (w : V) :
    w ∈ SPart G D ↔ w ∈ WBPart G D ∧ w ∉ PPart G D := by
  simp [SPart, Finset.mem_sdiff]

theorem privateExternal_pairwiseDisjoint (D : Finset V) :
    (BPart G D : Set V).PairwiseDisjoint (privateExternalNeighbors G D) := by
  classical
  rw [Finset.pairwiseDisjoint_iff]
  intro b hb c hc hne
  have hbInfo := (mem_BPart G D b).mp hb
  have hcInfo := (mem_BPart G D c).mp hc
  rcases hne with ⟨w, hw⟩
  have hwBC := Finset.mem_inter.mp hw
  have hwB : w ∈ privateExternalNeighbors G D b := hwBC.1
  have hwC : w ∈ privateExternalNeighbors G D c := hwBC.2
  have hbPriv := (mem_privateExternalNeighbors G D b w).mp hwB |>.2
  have hcPriv := (mem_privateExternalNeighbors G D c w).mp hwC |>.2
  have hadjB : G.Adj b w := (hbPriv b hbInfo.1).mpr rfl
  exact (hcPriv b hbInfo.1).mp hadjB

theorem PPart_subset_WBPart (D : Finset V) : PPart G D ⊆ WBPart G D := by
  classical
  intro w hw
  rcases (mem_PPart G D w).mp hw with ⟨b, hb, hbw⟩
  have hbD := (mem_BPart G D b).mp hb |>.1
  have hp := (mem_privateExternalNeighbors G D b w).mp hbw
  rw [mem_WBPart]
  refine ⟨hp.1, ?_⟩
  intro hw0
  have hw0info := (mem_W0Part G D w).mp hw0
  exact hw0info.2 b hb (hp.2 b hbD |>.mpr rfl)

theorem card_PPart (D : Finset V) :
    (PPart G D).card = ∑ b ∈ BPart G D, (privateExternalNeighbors G D b).card := by
  classical
  unfold PPart
  exact Finset.card_biUnion (privateExternal_pairwiseDisjoint G D)

/-- The per-vertex surplus in the private-neighbor count. -/
noncomputable def xCharge (D : Finset V) (b : V) : ℕ :=
  (privateExternalNeighbors G D b).card - 2

noncomputable def sCharge (D : Finset V) (b : V) : ℕ :=
  degreeTo G (SPart G D) b

noncomputable def betaCharge (D : Finset V) (w : V) : ℕ :=
  degreeTo G (BPart G D) w

noncomputable def kCharge (D : Finset V) (w : V) : ℕ :=
  degreeTo G (Z0Part G D) w

noncomputable def vertexCharge (D : Finset V) (b : V) : ℤ :=
  9 + 8 * (xCharge G D b : ℤ) - 3 * (sCharge G D b : ℤ)

noncomputable def externalCharge (D : Finset V) (w : V) : ℤ :=
  8 + 3 * (betaCharge G D w : ℤ) - 7 * (kCharge G D w : ℤ)

noncomputable def incidenceTotal (D : Finset V) : ℕ :=
  ∑ w ∈ SPart G D, kCharge G D w

theorem nonisolated_of_mem_BPart {D : Finset V} {b : V}
    (hb : b ∈ BPart G D) : NonisolatedIn G D b := by
  classical
  have hbInfo := (mem_BPart G D b).mp hb
  refine ⟨hbInfo.1, ?_⟩
  by_contra h
  apply hbInfo.2
  rw [mem_ZPart]
  exact ⟨hbInfo.1, by
    intro u hu hadj
    exact h ⟨u, hu, hadj⟩⟩

theorem private_card_eq_two_add_x {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D) {b : V}
    (hb : b ∈ BPart G D) :
    (privateExternalNeighbors G D b).card = 2 + xCharge G D b := by
  have htwo := lemma_3_1_private_neighbors G hCan
    (nonisolated_of_mem_BPart G hb)
  unfold xCharge
  omega

theorem wb_card_eq (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D) :
    (WBPart G D).card =
      2 * (BPart G D).card +
        (∑ b ∈ BPart G D, xCharge G D b) + (SPart G D).card := by
  classical
  have hPsub : PPart G D ⊆ WBPart G D := PPart_subset_WBPart G D
  have hUnion : PPart G D ∪ SPart G D = WBPart G D := by
    ext w
    simp only [Finset.mem_union, mem_SPart]
    constructor
    · rintro (hP | ⟨hWB, _⟩)
      · exact hPsub hP
      · exact hWB
    · intro hWB
      by_cases hP : w ∈ PPart G D
      · exact Or.inl hP
      · exact Or.inr ⟨hWB, hP⟩
  have hdisj : Disjoint (PPart G D) (SPart G D) := by
    rw [Finset.disjoint_left]
    intro w hwP hwS
    exact (mem_SPart G D w).mp hwS |>.2 hwP
  have hPcard := card_PPart G D
  have hsum :
      (∑ b ∈ BPart G D, (privateExternalNeighbors G D b).card) =
        2 * (BPart G D).card + ∑ b ∈ BPart G D, xCharge G D b := by
    calc
      _ = ∑ b ∈ BPart G D, (2 + xCharge G D b) := by
        apply Finset.sum_congr rfl
        intro b hb
        exact private_card_eq_two_add_x G hCan hb
      _ = 2 * (BPart G D).card + ∑ b ∈ BPart G D, xCharge G D b := by
        simp [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        ring
  rw [← hUnion, Finset.card_union_of_disjoint hdisj, hPcard, hsum]

/-! Double counting `B`--`S` and `Z₀`--`S` incidences. -/
theorem sum_degreeTo_symm (A B : Finset V) :
    (∑ a ∈ A, degreeTo G B a) = ∑ b ∈ B, degreeTo G A b := by
  classical
  simp_rw [degreeTo_as_sum]
  rw [Finset.sum_comm]
  simp_rw [G.adj_comm]

theorem sum_beta_eq_sum_s (D : Finset V) :
    (∑ w ∈ SPart G D, betaCharge G D w) =
      ∑ b ∈ BPart G D, sCharge G D b := by
  exact sum_degreeTo_symm G (SPart G D) (BPart G D)

/-- Algebraic core of Lemma 6.1.  The two displayed hypotheses are the exact
partition and incidence equalities established by the structural lemmas of
this appendix; no graph-theoretic premise is folded into the arithmetic. -/
theorem lemma_6_1_charge_identity_of_counts
    (D : Finset V)
    (hWB : (WBPart G D).card =
      2 * (BPart G D).card +
        (∑ b ∈ BPart G D, xCharge G D b) + (SPart G D).card)
    (hInc : (∑ w ∈ SPart G D, betaCharge G D w) =
      ∑ b ∈ BPart G D, sCharge G D b) :
    8 * (WBPart G D).card - 7 * ((BPart G D).card + (Z0Part G D).card) =
      (∑ b ∈ BPart G D, vertexCharge G D b) +
        (∑ w ∈ SPart G D, externalCharge G D w) +
        7 * (incidenceTotal G D - (Z0Part G D).card) := by
  classical
  unfold vertexCharge externalCharge incidenceTotal
  have hIncZ := congrArg (fun n : ℕ => (n : ℤ)) hInc
  have hWBZ := congrArg (fun n : ℕ => (n : ℤ)) hWB
  push_cast at hIncZ hWBZ ⊢
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul] at *
  simp_rw [← Finset.mul_sum] at *
  linarith [hWBZ, hIncZ]

/-- Lemma 6.1 in the paper: exact charge identity.  Its proof uses the
pairwise-disjoint private neighborhoods (from the secondary optimum), the
partition `W_B = P ⊔ S`, and double counting of `B`--`S` incidences. -/
theorem lemma_6_1_charge_identity
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D) :
    8 * (WBPart G D).card - 7 * ((BPart G D).card + (Z0Part G D).card) =
      (∑ b ∈ BPart G D, vertexCharge G D b) +
        (∑ w ∈ SPart G D, externalCharge G D w) +
        7 * (incidenceTotal G D - (Z0Part G D).card) := by
  apply lemma_6_1_charge_identity_of_counts G D (wb_card_eq G D hCan)
  exact sum_beta_eq_sum_s G D

end
end C6BipartiteDomination


