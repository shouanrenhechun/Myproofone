/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Tactic

/-!
# Bipartite domination in finite simple graphs

Formalization of the definitions and initial exchange principle used in
`c6_bipartite_domination_proof.pdf`.
-/

namespace C6BipartiteDomination

open Finset

variable {V : Type*} [DecidableEq V]
variable (G : SimpleGraph V)

/-- A 2-colouring of the selected vertices certifies that their induced graph
is bipartite. -/
def IsBipartiteOn (D : Finset V) : Prop :=
  ∃ colour : V → Bool,
    ∀ ⦃u v⦄, u ∈ D → v ∈ D → G.Adj u v → colour u ≠ colour v

/-- A set dominates every vertex outside the set. -/
def Dominates (D : Finset V) : Prop :=
  ∀ ⦃v⦄, v ∉ D → ∃ u ∈ D, G.Adj u v

/-- A bipartite dominating set, with the paper's convention that selected
vertices need not dominate one another. -/
def IsBipartiteDominatingSet (D : Finset V) : Prop :=
  Dominates G D ∧ IsBipartiteOn G D

/-- Vertices whose domination might be lost when `X` is removed from `D`. -/
def Responsible (D X : Finset V) (v : V) : Prop :=
  v ∉ D \ X ∧ ∀ u ∈ D \ X, ¬ G.Adj u v

/-- The paper's collective replacement lemma (Lemma 2.2), stated with its
responsibility region as a predicate to avoid coercion noise. -/
theorem collective_exchange
    {D X Y : Finset V}
    (hcover : ∀ ⦃v⦄, Responsible G D X v → v ∈ Y ∨ ∃ y ∈ Y, G.Adj y v)
    (hbip : IsBipartiteOn G ((D \ X) ∪ Y)) :
    IsBipartiteDominatingSet G ((D \ X) ∪ Y) := by
  refine ⟨?_, hbip⟩
  intro v hv
  by_cases hresp : Responsible G D X v
  · rcases hcover hresp with hy | ⟨y, hy, hadj⟩
    · exact (hv (Finset.mem_union_right (D \ X) hy)).elim
    · exact ⟨y, Finset.mem_union_right _ hy, hadj⟩
  · by_cases hret : v ∈ D \ X
    · exact (hv (Finset.mem_union_left Y hret)).elim
    · have hnot : ¬ ∀ u ∈ D \ X, ¬ G.Adj u v := by
        intro h
        exact hresp ⟨hret, h⟩
      push Not at hnot
      obtain ⟨u, hu, hadj⟩ := hnot
      exact ⟨u, Finset.mem_union_left Y hu, hadj⟩

/-- The responsibility region can be expressed directly through absence of
neighbors in the retained set. -/
theorem responsible_iff
    (D X : Finset V) (v : V) :
    Responsible G D X v ↔ v ∉ D \ X ∧ ∀ u ∈ D \ X, ¬ G.Adj u v := Iff.rfl

/-- The final numerical step of the paper: a complement of size at least
`7/8` of the selected set yields the `8/15` vertex bound. -/
theorem ratio_from_complement_bound {d w : ℕ}
    (h : 8 * w ≥ 7 * d) : 15 * d ≤ 8 * (d + w) := by
  omega

end C6BipartiteDomination

