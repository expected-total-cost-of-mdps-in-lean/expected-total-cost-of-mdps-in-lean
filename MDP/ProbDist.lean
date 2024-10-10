import MDP.Paths.Sets

-- TODO: remove this
set_option linter.unusedSectionVars false

namespace MDP

variable {State : Type*} {Act : Type*}
variable [DecidableEq State] [DecidableEq Act]
variable [ActNonempty : Nonempty Act]
variable (M : MDP State Act)

variable [M.FiniteBranching]

theorem Paths_n₀_Disjoint_succs (s : State) (n : ℕ) : (M.Paths_n₀ s n).toSet.PairwiseDisjoint Path.succs_univ₀ := by
  intro a _ b _ a_ne_b
  intro S hSa hSb
  intro x hx
  absurd a_ne_b
  rw [←a.succs_univ₀_is_prev x (hSa hx), ←b.succs_univ₀_is_prev x (hSb hx)]

theorem prepend_Prob (𝒮 : M.Scheduler) (π : M.Path) (s : State) {hs : π.first ∈ M.succs_univ s} : (π.prepend s hs).Prob 𝒮 = M.P s (𝒮 s) π.first * π.Prob 𝒮 := by
  simp only [Path.Prob, Fin.getElem_fin, Nat.succ_eq_add_one, Fin.val_succ]
  rw [←Fin.prod_ofFn, ←Fin.prod_ofFn]
  rw [List.prod_step _]
  · simp_all only [Path.prepend_length, add_tsub_cancel_right, Fin.cast_eq_self,
    Nat.add_one_sub_one, Path.length_pos, List.ofFn_head, Path.prepend_get_zero, id_eq,
    Int.Nat.cast_ofNat_Int, zero_add, Path.prepend_second, List.ofFn_tail]
    rw [Path.prepend_get_zero]
    simp only [Path.first, List.head_eq_get]
    congr
  · simp only [Path.prepend_states_length, add_tsub_cancel_right, Fin.cast_eq_self,
    Nat.add_succ_sub_one, Nat.add_zero, ne_eq, List.ofFn_eq_nil_iff, List.length_eq_zero,
    π.nonempty, not_false_eq_true]

theorem Path.prepend_states (π : M.Path) (s : State) {hs : π.first ∈ M.succs_univ s} : (π.prepend s hs).states = s :: π.states := by
  simp [prepend]

theorem Path.prepend_Cost (cost : M.Costs) (π : M.Path) (s : State) {hs : π.first ∈ M.succs_univ s} : (π.prepend s hs).Cost cost = cost s + π.Cost cost := by
  simp only [Path.Cost, Fin.getElem_fin, Nat.succ_eq_add_one, Fin.val_succ]
  simp [prepend_states]

theorem Fin.prod_univ_castPred {n : ℕ} (h : 0 < n) (f : Fin n → ENNReal) :
  ∏ (i : Fin n), f i = (∏ (i : Fin (n - 1)), f ⟨i, by have := i.prop ; omega⟩) * f ⟨n - 1, by omega⟩
:= by
  have ⟨m, hm⟩ : ∃m, n=m+1 := Nat.exists_eq_add_one.mpr h
  subst_eqs
  simp
  exact Fin.prod_univ_castSucc f

theorem Fin.prod_univ_pred {n : ℕ} (h : 0 < n) (f : Fin n → ENNReal) :
  ∏ (i : Fin n), f i = f ⟨0, by omega⟩ * ∏ (i : Fin (n - 1)), f ⟨i.succ, by have := i.prop ; omega⟩
:= by
  have ⟨m, hm⟩ : ∃m, n=m+1 := Nat.exists_eq_add_one.mpr h
  subst_eqs
  simp
  exact Fin.prod_univ_succ f

theorem Fin.prod_congr {n m : ℕ} {f : Fin n → ENNReal} {g : Fin m → ENNReal} (h₁ : n = m) (h₂ : ∀ i : Fin n, f i = g ⟨i, by omega⟩) :
  ∏ (i : Fin n), f i = ∏ (j : Fin m), g j
:= by
  apply Finset.prod_bij (fun a _ ↦ ⟨a, by have := a.prop ; omega⟩)
  · simp
  · simp_all only [Finset.mem_univ, Fin.mk.injEq, true_implies]
    exact fun a₁ a₂ a ↦ Fin.eq_of_val_eq a
  · simp_all only [Finset.mem_univ, exists_const, true_implies]
    intro i
    use ⟨i, by omega⟩
  · simp_all

theorem extend_Prob' (𝒮 : M.Scheduler') (π : M.Path) (s : State) {hs : s ∈ M.succs_univ π.last} : (π.extend s hs).Prob' 𝒮 = π.Prob' 𝒮 * M.P π.last (𝒮 π) s := by
  have := π.extend_Prob' s hs 𝒮
  simp [Path.Prob']
  rw [Fin.prod_univ_castPred (by simp)]
  congr! 1
  · rw [Fin.prod_congr]
    · simp
    · intro ⟨i, h⟩
      simp at h ⊢
      rw [List.getElem_append, List.getElem_append]
      simp
      suffices (π.extend s hs).take i = π.take i by
        congr! 7 <;> split_ifs <;> try omega
        · simp_all
        · simp_all
      simp [Path.take]
      apply List.take_append_of_le_length
      omega
  · simp [Path.last_eq_get, Path.getElem_eq_states_getElem']
    congr! 2
    · simp [List.getElem_append, Path.last_eq_states_get]
    · congr! 5 <;> simp

theorem extend_Prob (𝒮 : M.Scheduler) (π : M.Path) (s : State) {hs : s ∈ M.succs_univ π.last} : (π.extend s hs).Prob 𝒮 = π.Prob 𝒮 * M.P π.last (𝒮 π.last) s := by
  simp [Path.Prob]
  rw [Fin.prod_univ_castPred (by simp)]
  rw [List.getElem_append]
  congr! 1
  · rw [Fin.prod_congr]
    · simp
    · intro ⟨i, h⟩
      simp at h ⊢
      rw [List.getElem_append, List.getElem_append]
      congr! 4
      · simp_all [Path.extend_states]
        split_ifs <;> try omega
        rfl
      · simp_all [Path.extend_states]
        congr! 2
        apply List.getElem_append_left
      · simp_all
        apply List.getElem_append_left
      · simp_all
        split_ifs
        · rfl
        · omega
  · simp only [Path.extend_states, List.length_append, List.length_cons, List.length_nil, zero_add,
    add_tsub_cancel_right, tsub_lt_self_iff, Path.length_pos, zero_lt_one, and_self, ↓reduceDIte,
    Int.Nat.cast_ofNat_Int, id_eq, Int.reduceNeg, Int.reduceAdd, Nat.reduceAdd, Nat.add_one_sub_one,
    Path.length_pred_add, List.getElem_concat_length, Path.last_eq_get,
    Path.getElem_eq_states_getElem']
    congr! 4
    · simp [List.getElem_append, Path.last_eq_states_get]
    · simp only [Path.extend_states, List.length_append, List.length_cons, List.length_nil,
      zero_add, add_tsub_cancel_right, Path.last_eq_states_get, List.get_eq_getElem]
      apply List.getElem_append_left

theorem succs_univ₀_sum_eq_succs_sum' (𝒮 : M.Scheduler') (π : M.Path) : ∑ π' ∈ π.succs_univ₀, π'.Prob' 𝒮 = ∑ π' ∈ (π.succs (𝒮 π) : Finset M.Path), π'.Prob' 𝒮 := by
  apply Finset.sum_bij_ne_zero (fun π' _ _ ↦ π')
  · simp
    simp only [Path.succs_univ₀, Path.succs, Finset.mem_biUnion, Finset.mem_map,
    Function.Embedding.coeFn_mk, Subtype.exists, Finset.mem_val, Finsupp.mem_support_iff, ne_eq,
    forall_exists_index, and_imp]
    intro π' α _ s' hs' _ hπ' hπ'_Prob
    rw [←hπ', extend_Prob'] at hπ'_Prob
    use s'
    simp_all only [Finset.mem_attach, mul_eq_zero, not_or, and_self, exists_prop, and_true]
    simp [succs]
    exact hπ'_Prob.right
  · simp only [ne_eq, imp_self, implies_true]
  · simp only [ne_eq, exists_prop, Path.succs_univ₀, Finset.mem_biUnion, exists_and_left,
    exists_eq_right_right]
    intro π' hπ' _
    simp_all only [not_false_eq_true, and_true]
    use 𝒮 π
    simp_all only [and_true]
    have := (𝒮 π).prop
    simp only [act₀_mem_iff_act_mem, Path.Scheduler'_act_mem_act]
  · simp only [ne_eq, implies_true]

theorem succs_univ₀_sum_eq_succs_sum (𝒮 : M.Scheduler) (π : M.Path) : ∑ π' ∈ π.succs_univ₀, π'.Prob 𝒮 = ∑ π' ∈ (π.succs (𝒮 π.last) : Finset M.Path), π'.Prob 𝒮 := by
  apply Finset.sum_bij_ne_zero (fun π' _ _ ↦ π')
  · simp only [Path.succs_univ₀, Path.succs, Finset.mem_biUnion, Finset.mem_map,
    Function.Embedding.coeFn_mk, Subtype.exists, Finset.mem_val, Finsupp.mem_support_iff, ne_eq,
    forall_exists_index, and_imp]
    intro π' α _ s' hs' _ hπ' hπ'_Prob
    rw [←hπ', extend_Prob] at hπ'_Prob
    use s'
    simp_all only [Finset.mem_attach, mul_eq_zero, not_or, and_self, exists_prop, and_true]
    simp [succs]
    exact hπ'_Prob.right
  · simp only [ne_eq, imp_self, implies_true]
  · simp only [ne_eq, exists_prop, Path.succs_univ₀, Finset.mem_biUnion, exists_and_left,
    exists_eq_right_right]
    intro π' hπ' _
    simp_all only [not_false_eq_true, and_true]
    use 𝒮 π.last
    simp_all only [and_true]
    have := (𝒮 π.last).prop
    simp only [act₀_mem_iff_act_mem, Subtype.coe_prop]
  · simp only [ne_eq, implies_true]

@[simp]
theorem Path.succs_Prob' {M : MDP State Act} (𝒮 : M.Scheduler') (π : M.Path) : ∑ π' ∈ π.succs (↑(𝒮 π)), π'.Prob' 𝒮 = π.Prob' 𝒮 := by
  simp only [Path.succs, Finset.sum_map, Function.Embedding.coeFn_mk, Path.extend_Prob']
  rw [←Finset.sum_mul]
  conv => right ; rw [←one_mul (π.Prob' 𝒮)]
  congr
  rw [←M.P_sum_support_one_iff π.last (𝒮 π) |>.mpr (by simp only [MDP.Path.Scheduler'_act_mem_act])]
  exact Finset.sum_attach _ _

@[simp]
theorem Path.succs_Prob {M : MDP State Act} (𝒮 : M.Scheduler) (π : M.Path) : ∑ π' ∈ π.succs (↑(𝒮 π.last)), π'.Prob 𝒮 = π.Prob 𝒮 := by
  simp only [Path.succs, Finset.sum_map, Function.Embedding.coeFn_mk, Path.extend_Prob]
  rw [←Finset.sum_mul]
  conv => right ; rw [←one_mul (π.Prob 𝒮)]
  congr
  rw [←M.P_sum_support_one_iff π.last (𝒮 π.last) |>.mpr (by simp only [MDP.Path.Scheduler_act_mem_act])]
  exact Finset.sum_attach _ _

@[simp]
theorem Path.succs_univ₀_Prob' {M : MDP State Act} [M.FiniteBranching] (𝒮 : M.Scheduler') (π : M.Path) : ∑ π' ∈ π.succs_univ₀, π'.Prob' 𝒮 = π.Prob' 𝒮 := by
  rw [succs_univ₀_sum_eq_succs_sum']
  exact π.succs_Prob' 𝒮

@[simp]
theorem Path.succs_univ₀_Prob {M : MDP State Act} [M.FiniteBranching] (𝒮 : M.Scheduler) (π : M.Path) : ∑ π' ∈ π.succs_univ₀, π'.Prob 𝒮 = π.Prob 𝒮 := by
  rw [succs_univ₀_sum_eq_succs_sum]
  exact π.succs_Prob 𝒮

theorem succs_univ_sum_eq_succs_sum (𝒮 : M.Scheduler') (s : State) : ∑ s' ∈ M.succs_univ₀ s, M.P s (𝒮 {s}) s' = ∑ s' ∈ M.succs (𝒮 {s}) s, M.P s (𝒮 {s}) s' := by
  apply Finset.sum_bij_ne_zero (fun a _ _ ↦ a)
  · intro s' _ hP
    simp only [succs, Finsupp.mem_support_iff, ne_eq]
    exact hP
  · simp only [ne_eq, imp_self, implies_true]
  · intro s' hs' hp
    simp_all only [ne_eq, exists_prop, succs_univ₀, Finset.mem_biUnion, exists_eq_right_right,
      not_false_eq_true]
    simp only [and_true]
    use 𝒮 {s}
    simp_all only [act₀_mem_iff_act_mem, Subtype.coe_prop, and_self]
  · simp only [ne_eq, implies_true]

@[simp]
theorem succs_P (𝒮 : M.Scheduler') (s : State) : ∑ x ∈ M.succs (↑(𝒮 {s})) s, (M.P s ↑(𝒮 {s})) x = 1 := by
  simp only [succs, P_sum_one_iff_Scheduler]

theorem succs_univ_P (𝒮 : M.Scheduler') (s : State) : ∑ s' ∈ M.succs_univ₀ s, (M.P s ↑(𝒮 {s})) s' = 1 := by
  simp only [succs_univ_sum_eq_succs_sum, succs_P]

theorem Paths_n₀_Prob' (𝒮 : M.Scheduler') (n : ℕ) : ∑ π ∈ M.Paths_n₀ s n, π.Prob' 𝒮 = 1 := by
  induction n with
  | zero =>
    simp [Paths_n₀]
  | succ n ih =>
    simp [Paths_n₀]
    rw [Finset.sum_biUnion]
    · simp [Path.succs_univ₀_Prob']
      exact ih
    · exact M.Paths_n₀_Disjoint_succs s n

theorem Paths_n₀_Prob (𝒮 : M.Scheduler) (n : ℕ) : ∑ π ∈ M.Paths_n₀ s n, π.Prob 𝒮 = 1 := by
  induction n with
  | zero =>
    simp [Paths_n₀]
  | succ n ih =>
    simp [Paths_n₀]
    rw [Finset.sum_biUnion]
    · simp [Path.succs_univ₀_Prob]
      exact ih
    · exact M.Paths_n₀_Disjoint_succs s n

theorem sum_succs_eq_sum_succs_univ_mul (α : Act) (s : State) (f : State → ENNReal) : ∑ s' ∈ M.succs α s, M.P s α s' * f s' = ∑ s' ∈ M.succs_univ₀ s, M.P s α s' * f s' := by
  simp [succs, succs_univ₀, act₀_mem_iff_act_mem]
  apply Finset.sum_bij_ne_zero (fun a _ _ ↦ a)
  · intro s' hs' hs''
    simp_all [Fintype.complete]
    use α
    simp_all only [act₀_mem_iff_act_mem, not_false_eq_true, and_true]
    exact (P_ne_zero_sum_eq_one hs').symm
  · simp only [Finsupp.mem_support_iff, ne_eq, imp_self, implies_true]
  · simp_all only [Finset.mem_biUnion, Finset.mem_filter, Finsupp.mem_support_iff, ne_eq,
    mul_eq_zero, not_or, exists_prop, exists_and_left, exists_eq_right_right, not_false_eq_true,
    and_self, and_imp, implies_true]
  · simp only [Finsupp.mem_support_iff, ne_eq, implies_true]

theorem sum_succs_eq_sum_succs_univ (α : Act) (s : State) : ∑ s' ∈ M.succs α s, M.P s α s' = ∑ s' ∈ M.succs_univ₀ s, M.P s α s' := by
  convert M.sum_succs_eq_sum_succs_univ_mul α s (fun _ ↦ 1)
  all_goals rw [mul_one]

theorem succs_univ_P_act₀ (s : State) (a : M.act₀ s) : ∑ s' ∈ M.succs_univ₀ s, M.P s a s' = 1 := by
  simp only [← sum_succs_eq_sum_succs_univ, succs, M.P_sum_support_one_iff s a]
  exact (act₀_mem_iff_act_mem M s ↑a).mp a.prop
