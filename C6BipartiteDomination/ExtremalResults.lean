/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import C6BipartiteDomination.MainResults
import C6BipartiteDomination.Corona

/-! # The extremal example and the sharp constant -/

namespace C6BipartiteDomination

open Finset
open Classical

theorem corona_core_neighbor_finset (i : Fin 5) :
    Finset.univ.filter (fun u => coronaGraph.Adj (Sum.inl i) u) =
      (Finset.univ.erase i).image (fun j : Fin 5 => (Sum.inl j : CoronaVertex)) ∪
        ({Sum.inr (i, 0), Sum.inr (i, 1)} : Finset CoronaVertex) := by
  classical
  ext v
  cases v with
  | inl j =>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp [coronaGraph, coronaAdj, Finset.mem_filter, Finset.mem_union,
        Finset.mem_image, eq_comm]
  | inr p =>
      rcases p with ⟨j, q⟩
      fin_cases q <;>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] <;>
        simp [coronaGraph, coronaAdj, Finset.mem_union, Finset.mem_image, eq_comm]

theorem corona_leaf_neighbor_finset (i : Fin 5) (p : Fin 2) :
    Finset.univ.filter (fun u => coronaGraph.Adj (Sum.inr (i, p)) u) =
      {Sum.inl i} := by
  classical
  ext v
  cases v with
  | inl j =>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp [coronaGraph, coronaAdj, eq_comm]
  | inr q =>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp [coronaGraph, coronaAdj]

theorem corona_core_degree (i : Fin 5) :
    degreeTo coronaGraph Finset.univ (Sum.inl i) = 6 := by
  classical
  unfold degreeTo
  rw [corona_core_neighbor_finset]
  have hdisj : Disjoint
      ((Finset.univ.erase i).image (fun j : Fin 5 => (Sum.inl j : CoronaVertex)))
      ({Sum.inr (i, 0), Sum.inr (i, 1)} : Finset CoronaVertex) := by
    rw [Finset.disjoint_left]
    intro v hvC hvL
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hvC
    simp at hvL
  rw [Finset.card_union_of_disjoint hdisj]
  have hcore :
      ((Finset.univ.erase i).image (fun j : Fin 5 => (Sum.inl j : CoronaVertex))).card = 4 := by
    rw [Finset.card_image_of_injective _ (by
      intro a b hab
      exact Sum.inl.inj hab)]
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  rw [hcore]
  simp

theorem corona_leaf_degree (i : Fin 5) (p : Fin 2) :
    degreeTo coronaGraph Finset.univ (Sum.inr (i, p)) = 1 := by
  classical
  unfold degreeTo
  rw [corona_leaf_neighbor_finset]
  simp

theorem corona_has_no_isolates : HasNoIsolatedVertices coronaGraph := by
  intro v
  have hpos : 0 < degreeTo coronaGraph Finset.univ v := by
    cases v with
    | inl i => rw [corona_core_degree]; omega
    | inr p => rw [corona_leaf_degree]; omega
  have hne : (Finset.univ.filter (fun u => coronaGraph.Adj v u)).Nonempty := by
    apply Finset.card_pos.mp
    simpa [degreeTo] using hpos
  obtain ⟨u, hu⟩ := hne
  exact ⟨u, (Finset.mem_filter.mp hu).2⟩

theorem corona_degree_at_most_six :
    ∀ v, degreeTo coronaGraph Finset.univ v ≤ 6 := by
  intro v
  cases v with
  | inl i => rw [corona_core_degree i]
  | inr p => rw [corona_leaf_degree p.1 p.2]; norm_num

theorem corona_degree_six :
    ∃ v, degreeTo coronaGraph Finset.univ v = 6 := by
  refine ⟨Sum.inl 0, ?_⟩
  exact corona_core_degree 0

theorem corona_max_degree_exactly_six :
    (∀ v, degreeTo coronaGraph Finset.univ v ≤ 6) ∧
      (∃ v, degreeTo coronaGraph Finset.univ v = 6) :=
  ⟨corona_degree_at_most_six, corona_degree_six⟩

theorem corona_vertex_card : Fintype.card CoronaVertex = 15 := by
  simp [CoronaVertex]

noncomputable def coronaSelectedCore (D : Finset CoronaVertex) : Finset (Fin 5) :=
  Finset.univ.filter fun i => Sum.inl i ∈ D

noncomputable def coronaUnselectedCore (D : Finset CoronaVertex) : Finset (Fin 5) :=
  Finset.univ \ coronaSelectedCore D

noncomputable def coronaSelectedCoreVertices
    (D : Finset CoronaVertex) : Finset CoronaVertex :=
  (coronaSelectedCore D).image Sum.inl

noncomputable def coronaForcedLeaves
    (D : Finset CoronaVertex) : Finset CoronaVertex :=
  ((coronaUnselectedCore D).product Finset.univ).image
    (fun p : Fin 5 × Fin 2 => Sum.inr p)

theorem corona_selected_core_card_le_two {D : Finset CoronaVertex}
    (hD : IsBipartiteDominatingSet coronaGraph D) :
    (coronaSelectedCore D).card ≤ 2 := by
  classical
  obtain ⟨colour, hcolour⟩ := hD.2
  let C := coronaSelectedCore D
  let f : {i // i ∈ C} → Bool := fun i => colour (Sum.inl i.1)
  have hinj : Function.Injective f := by
    intro i j hEq
    by_contra hne
    have hiD : Sum.inl i.1 ∈ D := by
      simpa [C, coronaSelectedCore] using i.2
    have hjD : Sum.inl j.1 ∈ D := by
      simpa [C, coronaSelectedCore] using j.2
    have hij : i.1 ≠ j.1 := by
      intro h
      exact hne (Subtype.ext h)
    have hadj : coronaGraph.Adj (Sum.inl i.1) (Sum.inl j.1) := by
      simpa [coronaGraph, coronaAdj] using hij
    exact (hcolour hiD hjD hadj) hEq
  have hcard : Fintype.card {i // i ∈ C} ≤ Fintype.card Bool :=
    Fintype.card_le_of_injective f hinj
  have hcard' : Fintype.card {i // i ∈ C} ≤ 2 := by simpa using hcard
  have hsubCard : Fintype.card {i // i ∈ C} = C.card := by
    simpa using Finset.card_attach C
  rw [hsubCard] at hcard'
  exact hcard'

theorem corona_leaf_forced {D : Finset CoronaVertex}
    (hD : IsBipartiteDominatingSet coronaGraph D)
    {i : Fin 5} (hi : i ∉ coronaSelectedCore D) (p : Fin 2) :
    Sum.inr (i, p) ∈ D := by
  classical
  have hiCore : Sum.inl i ∉ D := by
    intro h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  by_contra hleaf
  obtain ⟨y, hyD, hyAdj⟩ := hD.1 hleaf
  cases y with
  | inl j =>
      have hji : j = i := by
        simpa [coronaGraph, coronaAdj] using hyAdj
      subst j
      exact hiCore hyD
  | inr q =>
      simp [coronaGraph, coronaAdj] at hyAdj

theorem corona_core_unselected_card {D : Finset CoronaVertex} :
    (coronaSelectedCore D).card + (coronaUnselectedCore D).card = 5 := by
  classical
  have h := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (coronaSelectedCore D))
  have h' : (coronaUnselectedCore D).card +
      (coronaSelectedCore D).card = 5 := by
    simpa [coronaUnselectedCore] using h
  omega

theorem corona_selected_core_vertices_card (D : Finset CoronaVertex) :
    (coronaSelectedCoreVertices D).card = (coronaSelectedCore D).card := by
  classical
  unfold coronaSelectedCoreVertices
  apply Finset.card_image_of_injective
  intro i j h
  exact Sum.inl.inj h

theorem corona_forced_leaves_card (D : Finset CoronaVertex) :
    (coronaForcedLeaves D).card =
      (coronaUnselectedCore D).card * 2 := by
  classical
  unfold coronaForcedLeaves
  rw [Finset.card_image_of_injective]
  · simp [Finset.card_product]
  · intro p q h
    exact Sum.inr.inj h

theorem corona_core_leaves_disjoint (D : Finset CoronaVertex) :
    Disjoint (coronaSelectedCoreVertices D) (coronaForcedLeaves D) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvC hvL
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hvC
  obtain ⟨p, hp, hEq⟩ := Finset.mem_image.mp hvL
  cases hEq

theorem corona_core_vertices_subset {D : Finset CoronaVertex} :
    coronaSelectedCoreVertices D ⊆ D := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
  exact (Finset.mem_filter.mp hi).2

theorem corona_forced_leaves_subset {D : Finset CoronaVertex}
    (hD : IsBipartiteDominatingSet coronaGraph D) :
    coronaForcedLeaves D ⊆ D := by
  classical
  intro v hv
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
  exact corona_leaf_forced hD
    ((Finset.mem_sdiff.mp (Finset.mem_product.mp hp |>.1)).2) p.2

theorem corona_every_bipartite_dominating_set_card_ge_eight
    {D : Finset CoronaVertex} (hD : IsBipartiteDominatingSet coronaGraph D) :
    8 ≤ D.card := by
  classical
  let C := coronaSelectedCore D
  let U := coronaUnselectedCore D
  let K := coronaSelectedCoreVertices D
  let L := coronaForcedLeaves D
  have hKsub : K ⊆ D := corona_core_vertices_subset
  have hLsub : L ⊆ D := corona_forced_leaves_subset hD
  have hdisj : Disjoint K L := corona_core_leaves_disjoint D
  have hUnionSub : K ∪ L ⊆ D := Finset.union_subset hKsub hLsub
  have hLower : C.card + U.card * 2 ≤ D.card := by
    have hCardUnion : (K ∪ L).card = K.card + L.card :=
      Finset.card_union_of_disjoint hdisj
    have hCardLe : (K ∪ L).card ≤ D.card := Finset.card_le_card hUnionSub
    rw [hCardUnion, corona_selected_core_vertices_card, corona_forced_leaves_card] at hCardLe
    exact hCardLe
  have hC : C.card ≤ 2 := corona_selected_core_card_le_two hD
  have hCU : C.card + U.card = 5 := corona_core_unselected_card
  omega

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_bipartite_dominating_set (G : SimpleGraph V) :
    ∃ D : Finset V, IsBipartiteDominatingSet G D := by
  classical
  obtain ⟨I, hIuniv, hIind, hIdom⟩ :=
    exists_maximal_independent_subset G Finset.univ
  refine ⟨I, ?_⟩
  constructor
  · intro v hv
    obtain ⟨u, hu, hadj⟩ := hIdom (Finset.mem_univ v) hv
    exact ⟨u, hu, hadj⟩
  · refine ⟨fun _ => false, ?_⟩
    intro u v hu hv hadj
    exact (hIind hu hv hadj).elim

theorem exists_bipartite_dominating_card (G : SimpleGraph V) :
    ∃ n : ℕ, ∃ D : Finset V,
      IsBipartiteDominatingSet G D ∧ D.card = n := by
  obtain ⟨D, hD⟩ := exists_bipartite_dominating_set G
  exact ⟨D.card, D, hD, rfl⟩

noncomputable def gammaBip (G : SimpleGraph V) : ℕ :=
  Nat.find (exists_bipartite_dominating_card G)

theorem gammaBip_spec (G : SimpleGraph V) :
    ∃ D : Finset V,
      IsBipartiteDominatingSet G D ∧ D.card = gammaBip G := by
  rcases Nat.find_spec (exists_bipartite_dominating_card G) with
    ⟨D, hD, hcard⟩
  exact ⟨D, hD, by simpa [gammaBip] using hcard⟩

theorem gammaBip_le_card (G : SimpleGraph V) {D : Finset V}
    (hD : IsBipartiteDominatingSet G D) :
    gammaBip G ≤ D.card := by
  apply Nat.find_min' (exists_bipartite_dominating_card G)
  exact ⟨D, hD, rfl⟩

theorem gammaBip_minimum_exists (G : SimpleGraph V) :
    ∃ D : Finset V,
      MinimumBipartiteDominatingSet G D ∧ D.card = gammaBip G := by
  obtain ⟨D, hD, hcard⟩ := gammaBip_spec G
  refine ⟨D, ⟨hD, ?_⟩, hcard⟩
  intro E hE
  have hgamma := gammaBip_le_card G hE
  omega

theorem main_upper_bound_gamma {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hNoIso : HasNoIsolatedVertices G)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    15 * gammaBip G ≤ 8 * Fintype.card V := by
  obtain ⟨D, hmin, hcard⟩ := gammaBip_minimum_exists G
  have h := main_upper_bound_minimum G hNoIso hmax D hmin
  simpa [hcard] using h

theorem corona_gamma_eq_eight : gammaBip coronaGraph = 8 := by
  have hUpper : gammaBip coronaGraph ≤ 8 := by
    calc
      gammaBip coronaGraph ≤ coronaWitness.card :=
        gammaBip_le_card coronaGraph coronaWitness_isBipartiteDominating
      _ = 8 := coronaWitness_card
  obtain ⟨D, hD, hcard⟩ := gammaBip_spec coronaGraph
  have hLower : 8 ≤ gammaBip coronaGraph := by
    rw [← hcard]
    exact corona_every_bipartite_dominating_set_card_ge_eight hD
  omega

/-- A finite simple graph together with its concrete finite vertex type. -/
structure FiniteSimpleGraphData where
  Vertex : Type
  finiteVertex : Fintype Vertex
  decidableVertex : DecidableEq Vertex
  graph : SimpleGraph Vertex

def C6Admissible (H : FiniteSimpleGraphData) : Prop := by
  letI := H.finiteVertex
  letI := H.decidableVertex
  exact HasNoIsolatedVertices H.graph ∧
    0 < Fintype.card H.Vertex ∧
    ∀ v, degreeTo H.graph Finset.univ v ≤ 6

noncomputable def finiteGraphDensity (H : FiniteSimpleGraphData) : ℝ := by
  letI := H.finiteVertex
  letI := H.decidableVertex
  exact (gammaBip H.graph : ℝ) / (Fintype.card H.Vertex : ℝ)

/-- The paper's `c₆` candidate set: ratios over all finite simple graphs with
no isolated vertices and maximum degree at most six. -/
def C6DensitySet : Set ℝ :=
  {r | ∃ H : FiniteSimpleGraphData, C6Admissible H ∧ r = finiteGraphDensity H}

noncomputable def c6 : ℝ := sSup C6DensitySet

theorem finite_graph_density_le_eight_fifteenths {H : FiniteSimpleGraphData}
    (hH : C6Admissible H) : finiteGraphDensity H ≤ (8 : ℝ) / 15 := by
  letI : Fintype H.Vertex := H.finiteVertex
  letI : DecidableEq H.Vertex := H.decidableVertex
  obtain ⟨hNoIso, hcardPos, hmax⟩ := hH
  have hmain := main_upper_bound_gamma H.graph hNoIso hmax
  have hpos : 0 < (Fintype.card H.Vertex : ℝ) := by exact_mod_cast hcardPos
  have hmainR :
      (15 : ℝ) * (gammaBip H.graph : ℝ) ≤
        (8 : ℝ) * (Fintype.card H.Vertex : ℝ) := by
    exact_mod_cast hmain
  unfold finiteGraphDensity
  rw [div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 15)]
  nlinarith

theorem corona_density_mem_C6 :
    (8 : ℝ) / 15 ∈ C6DensitySet := by
  let H : FiniteSimpleGraphData :=
    ⟨CoronaVertex, inferInstance, inferInstance, coronaGraph⟩
  refine ⟨H, ?_, ?_⟩
  · refine ⟨corona_has_no_isolates, ?_, corona_degree_at_most_six⟩
    change 0 < Fintype.card CoronaVertex
    rw [corona_vertex_card]
    norm_num
  · simp [H, finiteGraphDensity, corona_gamma_eq_eight]

theorem c6_eq_eight_fifteenths : c6 = (8 : ℝ) / 15 := by
  have hupper : ∀ r ∈ C6DensitySet, r ≤ (8 : ℝ) / 15 := by
    intro r hr
    obtain ⟨H, hH, rfl⟩ := hr
    exact finite_graph_density_le_eight_fifteenths hH
  have hbdd : BddAbove C6DensitySet := ⟨(8 : ℝ) / 15, hupper⟩
  have hne : C6DensitySet.Nonempty := ⟨(8 : ℝ) / 15, corona_density_mem_C6⟩
  apply le_antisymm
  · change sSup C6DensitySet ≤ (8 : ℝ) / 15
    exact csSup_le hne hupper
  · change (8 : ℝ) / 15 ≤ sSup C6DensitySet
    exact le_csSup hbdd corona_density_mem_C6

end C6BipartiteDomination

