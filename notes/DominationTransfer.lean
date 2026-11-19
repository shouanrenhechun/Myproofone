import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset BigOperators

namespace DominationTransfer

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
## 第1节：定义与基本性质
-/

/-- 集合 D 支配图 G：每个 D 外的顶点在 D 中都有邻点 -/
def IsDominating (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v ∉ D, ∃ u ∈ D, G.Adj u v

/-- 诱导子图性质 P（以顶点子集谓词表示）满足 P-支配集 -/
def IsPDominating (G : SimpleGraph V) (P : Finset V → Prop) (D : Finset V) : Prop :=
  IsDominating G D ∧ P D

/-- 性质 P 对添加孤立顶点封闭：
    空集满足 P；若 A 满足 P，且 J 内部独立、J 与 A 之间无边，则 A ∪ J 满足 P -/
def ClosedUnderIsolated (G : SimpleGraph V) (P : Finset V → Prop) : Prop :=
  P ∅ ∧ ∀ (A J : Finset V), P A → Disjoint A J →
    (∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y) →
    (∀ x ∈ A, ∀ y ∈ J, ¬ G.Adj x y) →
    P (A ∪ J)

/-- 公式 (3) 中的局部候选比例函数 f_{Δ, k}(a) -/
noncomputable def f_cand (Δ k a : ℝ) : ℝ :=
  (k + 1 + a * (Δ - a - k)) / ((Δ - a + 1) * (a + 1))

/-!
## 第2节：匹配支配核心与唯一分配结构
-/

/-- 引理 2.1 导出的核心与唯一外部顶点分配结构 (公式 4, 5) -/
structure CoreAllocation (G : SimpleGraph V) (Δ : ℕ) where
  C : Finset V
  Q : Finset V
  P_alloc : V → Finset V
  disj_CQ : Disjoint C Q
  union_CQ : C ∪ Q = univ
  a_ge_one : ∀ v ∈ C, 1 ≤ (P_alloc v).card
  alloc_sub_Q : ∀ v ∈ C, P_alloc v ⊆ Q
  alloc_adj : ∀ v ∈ C, ∀ u ∈ P_alloc v, G.Adj v u
  alloc_pairwise_disj : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → Disjoint (P_alloc u) (P_alloc v)
  Q_card_eq : Q.card = ∑ v ∈ C, (P_alloc v).card
  V_card_eq : (univ : Finset V).card = ∑ v ∈ C, ((P_alloc v).card + 1)

/-!
## 第3节：Ownership-Selection-Completion 转移原理 (定理 3.1)
-/

theorem transfer_completion_valid
    (G : SimpleGraph V) (P : Finset V → Prop) (hP : ClosedUnderIsolated G P)
    (C Q A R J : Finset V)
    (h_union : C ∪ Q = univ)
    (h_disj_CQ : Disjoint C Q)
    (h_AC : A ⊆ C)
    (h_RQ : R ⊆ Q)
    (h_PA : P A)
    (h_A_dom_C : ∀ c ∈ C, c ∉ A → ∃ a ∈ A, G.Adj a c)
    (h_R_def : ∀ q ∈ Q, q ∉ R → ∃ a ∈ A, G.Adj a q)
    (h_R_no_adj : ∀ a ∈ A, ∀ r ∈ R, ¬ G.Adj a r)
    (h_JR : J ⊆ R)
    (h_J_indep : ∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y)
    (h_J_dom_R : ∀ r ∈ R, r ∉ J → ∃ j ∈ J, G.Adj j r) :
    IsPDominating G P (A ∪ J) := by
  constructor
  · intro v hv
    rw [mem_union, not_or] at hv
    have hv_univ : v ∈ C ∪ Q := by rw [h_union]; exact mem_univ v
    rcases mem_union.mp hv_univ with hvC | hvQ
    · obtain ⟨a, haA, hadj⟩ := h_A_dom_C v hvC hv.1
      exact ⟨a, mem_union_left J haA, hadj⟩
    · by_cases hvR : v ∈ R
      · obtain ⟨j, hjJ, hadj⟩ := h_J_dom_R v hvR hv.2
        exact ⟨j, mem_union_right A hjJ, hadj⟩
      · obtain ⟨a, haA, hadj⟩ := h_R_def v hvQ hvR
        exact ⟨a, mem_union_left J haA, hadj⟩
  · apply hP.2 A J h_PA
    · exact Disjoint.mono h_AC (Subset.trans h_JR h_RQ) h_disj_CQ
    · exact h_J_indep
    · intro x hx y hy
      exact h_R_no_adj x hx y (h_JR hy)

theorem transfer_cardinality_bound
    (C Q A R J : Finset V) (a : V → ℕ)
    (h_AC : A ⊆ C)
    (h_JR : J ⊆ R)
    (h_Q_eq : Q.card = ∑ v ∈ C, a v)
    (h_R_cov : R.card + ∑ v ∈ A, a v ≤ Q.card) :
    ((A ∪ J).card : ℝ) ≤ (∑ v ∈ C, (a v : ℝ)) - ∑ v ∈ A, ((a v : ℝ) - 1) := by
  have h1 : (A ∪ J).card ≤ A.card + J.card := card_union_le A J
  have h2 : J.card ≤ R.card := card_le_card h_JR
  have h3 : (A ∪ J).card + ∑ v ∈ A, a v ≤ A.card + Q.card := by omega
  have h_cast : ((A ∪ J).card : ℝ) + ∑ v ∈ A, (a v : ℝ) ≤ (A.card : ℝ) + (Q.card : ℝ) := by
    exact_mod_cast h3
  have h_Q_cast : (Q.card : ℝ) = ∑ v ∈ C, (a v : ℝ) := by exact_mod_cast h_Q_eq
  have h_A_cast : (A.card : ℝ) = ∑ _v ∈ A, (1 : ℝ) := by simp
  have h_diff : (∑ v ∈ A, ((a v : ℝ) - 1)) = (∑ v ∈ A, (a v : ℝ)) - (A.card : ℝ) := by
    rw [sum_sub_distrib, h_A_cast]
  linarith

/-!
## 第4节：加权 k-退化选择与精确上界 (引理 4.1 与 公式 12-13)
-/

lemma local_budget_branch1 (Δ k a p : ℝ)
    (hk : 0 ≤ k)
    (ha : 1 ≤ a)
    (hm : k + 2 ≤ Δ - a + 1)
    (hp : (k + 1) / (Δ - a + 1) ≤ p) :
    a - p * (a - 1) ≤ f_cand Δ k a * (a + 1) := by
  have hm_pos : 0 < Δ - a + 1 := by linarith
  have ha_pos : 0 < a + 1 := by linarith
  have ha_nonneg : 0 ≤ a - 1 := by linarith
  have h_mul : (k + 1) / (Δ - a + 1) * (a - 1) ≤ p * (a - 1) :=
    mul_le_mul_of_nonneg_right hp ha_nonneg
  have h_ne1 : Δ - a + 1 ≠ 0 := ne_of_gt hm_pos
  have h_ne2 : a + 1 ≠ 0 := ne_of_gt ha_pos
  -- 先消去 (a + 1)，再消去 (Δ - a + 1)，全称使用纯乘法与 ring
  have h_step1 : f_cand Δ k a * (a + 1) = (k + 1 + a * (Δ - a - k)) / (Δ - a + 1) := by
    unfold f_cand
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ h_ne2]
  have h_step2 : a - (k + 1) / (Δ - a + 1) * (a - 1) = (k + 1 + a * (Δ - a - k)) / (Δ - a + 1) := by
    rw [div_mul_eq_mul_div, sub_eq_iff_eq_add, ← add_div, eq_div_iff h_ne1]
    ring
  linarith

lemma local_budget_branch2 (C_val a : ℝ)
    (ha : 1 ≤ a) (hC : (1 : ℝ) / 2 ≤ C_val) :
    a - 1 * (a - 1) ≤ C_val * (a + 1) := by
  have : (2 : ℝ) ≤ a + 1 := by linarith
  have h_prod : (1 : ℝ) / 2 * 2 ≤ C_val * (a + 1) := by nlinarith
  linarith

theorem global_upper_bound
    (C : Finset V) (a p : V → ℝ) (γ C_const V_card : ℝ)
    (h_V : V_card = ∑ v ∈ C, (a v + 1))
    (h_transfer : γ ≤ ∑ v ∈ C, (a v - p v * (a v - 1)))
    (h_local : ∀ v ∈ C, a v - p v * (a v - 1) ≤ C_const * (a v + 1)) :
    γ ≤ C_const * V_card := by
  calc γ ≤ ∑ v ∈ C, (a v - p v * (a v - 1)) := h_transfer
    _ ≤ ∑ v ∈ C, C_const * (a v + 1) := sum_le_sum h_local
    _ = C_const * ∑ v ∈ C, (a v + 1) := (mul_sum C (fun v => a v + 1) C_const).symm
    _ = C_const * V_card := by rw [← h_V]

/-!
## 第5节 & 第6节：叶冠图下界 (命题 5.1) 与性质夹逼定理 (定理 6.1)
-/

theorem corona_lower_bound (m k a j D_card : ℤ)
    (ha : 1 ≤ a)
    (hj_le : j ≤ k + 1)
    (hD_ge : j + a * (m - j) ≤ D_card) :
    k + 1 + a * (m - k - 1) ≤ D_card := by
  have h_mono : k + 1 + a * (m - k - 1) ≤ j + a * (m - j) := by
    have h_diff : (j + a * (m - j)) - (k + 1 + a * (m - k - 1)) = (a - 1) * (k + 1 - j) := by ring
    have h_nonneg : 0 ≤ (a - 1) * (k + 1 - j) := mul_nonneg (by linarith) (by linarith)
    linarith
  linarith

theorem property_squeeze_theorem (c_P c_Dk C_val : ℝ)
    (h_le_Dk : c_P ≤ c_Dk)
    (h_Dk_upper : c_Dk ≤ C_val)
    (h_corona_lower : C_val ≤ c_P) :
    c_P = C_val ∧ c_Dk = C_val := by
  constructor <;> linarith

/-!
## 第7节：半数阈值与显式代数优化 (公式 18-20, 推论 7.1)
-/

def N_denom (Δ a : ℝ) : ℝ := (Δ - a + 1) * (a + 1)

theorem eq_18_identity (Δ k a : ℝ) (hN : N_denom Δ a ≠ 0) :
    f_cand Δ k a = 1 - (Δ - k + k * a) / N_denom Δ a ∧
    N_denom Δ a = -a^2 + Δ * a + Δ + 1 := by
  constructor
  · unfold f_cand
    change (k + 1 + a * (Δ - a - k)) / N_denom Δ a = 1 - (Δ - k + k * a) / N_denom Δ a
    rw [div_eq_iff hN, sub_mul, one_mul, div_mul_cancel₀ _ hN]
    unfold N_denom
    ring
  · unfold N_denom
    ring

theorem eq_19_half_diff (Δ k a : ℝ) (hN : N_denom Δ a ≠ 0) :
    f_cand Δ k a - 1 / 2 = (a - 1) * (Δ - 2 * k - 1 - a) / (2 * N_denom Δ a) := by
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  have h2N : 2 * N_denom Δ a ≠ 0 := mul_ne_zero h2 hN
  unfold f_cand
  change (k + 1 + a * (Δ - a - k)) / N_denom Δ a - 1 / 2 =
    (a - 1) * (Δ - 2 * k - 1 - a) / (2 * N_denom Δ a)
  rw [div_sub_div _ _ hN h2, div_eq_div_iff (mul_ne_zero hN h2) h2N]
  unfold N_denom
  ring

theorem threshold_le_half (Δ k a : ℤ)
    (hΔ : Δ ≤ 2 * k + 3)
    (ha : 1 ≤ a)
    (hN_pos : 0 < (Δ - a + 1) * (a + 1)) :
    f_cand (Δ : ℝ) (k : ℝ) (a : ℝ) ≤ 1 / 2 := by
  have hN_real : 0 < N_denom (Δ : ℝ) (a : ℝ) := by
    unfold N_denom
    exact_mod_cast hN_pos
  have h_id := eq_19_half_diff (Δ : ℝ) (k : ℝ) (a : ℝ) (ne_of_gt hN_real)
  have h_num_nonpos : ((a : ℝ) - 1) * ((Δ : ℝ) - 2 * (k : ℝ) - 1 - (a : ℝ)) ≤ 0 := by
    by_cases ha1 : a = 1
    · subst ha1; norm_num
    · have ha2 : 2 ≤ a := by omega
      have h_f1 : (0 : ℝ) ≤ (a : ℝ) - 1 := by exact_mod_cast (by omega : 0 ≤ a - 1)
      have h_f2 : (Δ : ℝ) - 2 * (k : ℝ) - 1 - (a : ℝ) ≤ 0 := by
        exact_mod_cast (by omega : Δ - 2 * k - 1 - a ≤ 0)
      exact mul_nonpos_of_nonneg_of_nonpos h_f1 h_f2
  have h_div_nonpos :
      ((a : ℝ) - 1) * ((Δ : ℝ) - 2 * (k : ℝ) - 1 - (a : ℝ)) / (2 * N_denom (Δ : ℝ) (a : ℝ)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg h_num_nonpos (by linarith)
  linarith

theorem threshold_gt_half (Δ k : ℤ)
    (hΔ : 2 * k + 4 ≤ Δ)
    (hk : 0 ≤ k) :
    1 / 2 < f_cand (Δ : ℝ) (k : ℝ) 2 := by
  have hN_pos : 0 < N_denom (Δ : ℝ) 2 := by
    unfold N_denom
    have : (4 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast (by omega : 4 ≤ Δ)
    linarith
  have h_id := eq_19_half_diff (Δ : ℝ) (k : ℝ) 2 (ne_of_gt hN_pos)
  have h_num_pos : 0 < ((2 : ℝ) - 1) * ((Δ : ℝ) - 2 * (k : ℝ) - 1 - 2) := by
    have : (0 : ℝ) < (Δ : ℝ) - 2 * (k : ℝ) - 3 := by
      exact_mod_cast (by omega : 0 < Δ - 2 * k - 3)
    linarith
  have h_div_pos : 0 < ((2 : ℝ) - 1) * ((Δ : ℝ) - 2 * (k : ℝ) - 1 - 2) / (2 * N_denom (Δ : ℝ) 2) :=
    div_pos h_num_pos (by linarith)
  linarith

def q_poly (Δ k a : ℝ) : ℝ :=
  k * a^2 + (2 * Δ - k) * a - Δ^2 + (2 * k + 1) * Δ

theorem eq_20_adjacent_diff (Δ k a : ℝ)
    (hNa : N_denom Δ a ≠ 0) (hNa1 : N_denom Δ (a + 1) ≠ 0) :
    f_cand Δ k (a + 1) - f_cand Δ k a =
      - q_poly Δ k a / (N_denom Δ a * N_denom Δ (a + 1)) := by
  have h_prod : N_denom Δ a * N_denom Δ (a + 1) ≠ 0 := mul_ne_zero hNa hNa1
  unfold f_cand
  change (k + 1 + (a + 1) * (Δ - (a + 1) - k)) / N_denom Δ (a + 1) -
         (k + 1 + a * (Δ - a - k)) / N_denom Δ a =
         - q_poly Δ k a / (N_denom Δ a * N_denom Δ (a + 1))
  rw [div_sub_div _ _ hNa1 hNa, div_eq_div_iff (mul_ne_zero hNa1 hNa) h_prod]
  unfold q_poly N_denom
  ring

/-!
## 第8节 & 第9节：孤立顶点修正与稀疏图转移接口 (公式 29-30)
-/

theorem sparse_transfer_bound (Q_card C_card β ρ : ℝ)
    (h_beta : ρ * (Q_card - C_card) ≤ β) :
    Q_card - β ≤ (1 - ρ) * Q_card + ρ * C_card := by
  linarith

theorem sparse_max_degree_bound (V_card C_card Q_card Δ ρ : ℝ)
    (h_ρ : ρ ≤ 1 / 2)
    (h_Δ : 0 < Δ + 1)
    (h_Q : Q_card = V_card - C_card)
    (h_C : V_card / (Δ + 1) ≤ C_card) :
    (1 - ρ) * Q_card + ρ * C_card ≤ (1 - ρ - (1 - 2 * ρ) / (Δ + 1)) * V_card := by
  have h_rearrange :
      (1 - ρ) * Q_card + ρ * C_card = (1 - ρ) * V_card - (1 - 2 * ρ) * C_card := by
    rw [h_Q]; ring
  have h_nonneg : 0 ≤ 1 - 2 * ρ := by linarith
  have h_mul : (1 - 2 * ρ) * (V_card / (Δ + 1)) ≤ (1 - 2 * ρ) * C_card :=
    mul_le_mul_of_nonneg_left h_C h_nonneg
  linarith [show (1 - ρ) * V_card - (1 - 2 * ρ) * (V_card / (Δ + 1)) =
    (1 - ρ - (1 - 2 * ρ) / (Δ + 1)) * V_card by ring]

end DominationTransfer