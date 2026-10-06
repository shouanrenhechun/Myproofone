/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import C6BipartiteDomination.Basic
import Mathlib.Tactic.FinCases

/-!
The finite extremal example `cor(K₅, 2)` from Section 13 of the source paper.
This file first checks its advertised eight-vertex bipartite dominating set.
-/

namespace C6BipartiteDomination

abbrev CoronaVertex := Fin 5 ⊕ (Fin 5 × Fin 2)

def coronaAdj : CoronaVertex → CoronaVertex → Prop
  | .inl i, .inl j => i ≠ j
  | .inl i, .inr (j, _) => i = j
  | .inr (i, _), .inl j => i = j
  | .inr _, .inr _ => False

instance : DecidableRel coronaAdj := by
  intro u v
  cases u <;> cases v <;> simp [coronaAdj] <;> infer_instance

instance : DecidableEq CoronaVertex := inferInstance

def coronaGraph : SimpleGraph CoronaVertex where
  Adj := coronaAdj
  symm := by
    constructor
    intro u v h
    cases u with
    | inl i => cases v with
      | inl j => exact (ne_comm.mp h)
      | inr p => exact h.symm
    | inr p => cases v with
      | inl j => exact h.symm
      | inr q => exact h.elim
  loopless := by
    constructor
    intro u h
    cases u with
    | inl i => simp [coronaAdj] at h
    | inr p => simp [coronaAdj] at h

def coronaWitness : Finset CoronaVertex :=
  {Sum.inl 0, Sum.inl 1,
   Sum.inr (2, 0), Sum.inr (2, 1),
   Sum.inr (3, 0), Sum.inr (3, 1),
   Sum.inr (4, 0), Sum.inr (4, 1)}

theorem coronaWitness_card : coronaWitness.card = 8 := by
  decide

theorem coronaWitness_dominates : Dominates coronaGraph coronaWitness := by
  intro v hv
  fin_cases v <;>
    simp_all [coronaWitness, coronaGraph, coronaAdj]

-- Finite case splitting checks all selected vertex pairs in this 15-vertex graph.
set_option maxHeartbeats 1000000 in
theorem coronaWitness_bipartite : IsBipartiteOn coronaGraph coronaWitness := by
  refine ⟨fun v => if v = Sum.inl 0 then true else false, ?_⟩
  intro u v hu hv hadj
  fin_cases u <;> fin_cases v <;>
    simp_all [coronaWitness, coronaGraph, coronaAdj]

theorem coronaWitness_isBipartiteDominating :
    IsBipartiteDominatingSet coronaGraph coronaWitness :=
  ⟨coronaWitness_dominates, coronaWitness_bipartite⟩

end C6BipartiteDomination

