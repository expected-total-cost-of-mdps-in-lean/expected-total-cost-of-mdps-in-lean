import MDP.Scheduler

namespace MDP

namespace Path

variable {State : Type*} {Act : Type*}
variable [DecidableEq State] [DecidableEq Act]
variable {M : MDP State Act} (π π' : M.Path)

noncomputable def Prob (𝒮 : M.Scheduler) : ENNReal :=
  ∏ (i : Fin (∎|π| - 1)), M.P π[i] (𝒮 π[i]) π[i.succ]

noncomputable def Prob' (𝒮 : M.Scheduler') : ENNReal :=
  ∏ (i : Fin (∎|π| - 1)), M.P π[i] (𝒮 (π.take i)) π[i.succ]

noncomputable def Prob_i (𝒮 : M.Scheduler) (i : Fin (∎|π| - 1)) := M.P π[i] (𝒮 π[i]) π[i.succ]

theorem Prob_alt (𝒮 : M.Scheduler) : π.Prob 𝒮 = (List.ofFn <| π.Prob_i 𝒮).prod := by
  simp only [Prob, Fin.getElem_fin, Nat.succ_eq_add_one, Fin.val_succ, ← List.prod_ofFn]
  congr

@[simp]
theorem mk_single_Prob (x : State) (𝒮 : M.Scheduler) : (mk_single M x).Prob 𝒮 = 1 := by
  unfold Prob
  simp only [mk_single, List.length_singleton, Nat.reduceSub, Finset.univ_eq_empty, Nat.reduceAdd,
    Fin.getElem_fin, Finset.prod_empty]

@[simp]
theorem mk_single_Prob' (x : State) (𝒮 : M.Scheduler') : (mk_single M x).Prob' 𝒮 = 1 := by
  unfold Prob'
  simp only [mk_single, List.length_singleton, Nat.reduceSub, Finset.univ_eq_empty, Nat.reduceAdd,
    Fin.getElem_fin, Finset.prod_empty]

@[simp]
theorem Prob_le_one (𝒮 : M.Scheduler') : π.Prob' 𝒮 ≤ 1 := by
  simp only [Prob', Fin.getElem_fin, Nat.succ_eq_add_one, Fin.val_succ]
  apply Finset.prod_le_one
  · simp only [Finset.mem_univ, zero_le, imp_self, implies_true]
  · intro n _
    apply M.P_le_one

@[simp]
theorem Prob_ne_top (𝒮 : M.Scheduler') : π.Prob' 𝒮 ≠ ⊤ := by
  exact π.Prob_le_one 𝒮 |>.trans_lt ENNReal.one_lt_top |>.ne

@[simp]
theorem Scheduler'_act_mem_act (𝒮 : M.Scheduler') : ↑(𝒮 π) ∈ M.act π.last := by
  convert (𝒮 π).prop

@[simp]
theorem Scheduler_act_mem_act (𝒮 : M.Scheduler) : ↑(𝒮 π.last) ∈ M.act π.last := by
  convert (𝒮 π.last).prop

theorem extend_Prob' (s : State) (h : s ∈ M.succs_univ π.last) (𝒮 : M.Scheduler') : (π.extend s h).Prob' 𝒮 = M.P π.last (𝒮 π) s * π.Prob' 𝒮 := by
  unfold Prob'
  let ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero π.length_ne_zero
  rw [←Fin.prod_congr' _ (by simp ; omega : n + 1 = ∎|π.extend s h| - 1)]
  rw [←Fin.prod_congr' _ (by omega : n = ∎|π| - 1)]
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.getElem_fin, Nat.succ_eq_add_one, Fin.val_succ]
  rw [mul_comm]
  have hn' : n = ∎|π| - 1 := by omega
  simp only [Fin.coe_cast, Fin.val_last, hn', extend_get_length_pred, Nat.add_succ_sub_one,
    Nat.add_zero, id_eq, Int.reduceNeg, Int.Nat.cast_ofNat_Int, eq_mpr_eq_cast, length_pred_add,
    extend_get_length, Fin.coe_castSucc]
  congr
  · simp only [hn', extend_take_length_pred]
  · simp only [hn', extend_take_length_pred]
  · ext i
    congr! 1
    · congr! 1
      · simp only [getElem, extend]
        simp only [List.get_eq_getElem]
        apply List.getElem_append_left
      · congr! 2
        · rw [extend_take]
          omega
        · rw [extend_take]
          omega
    · simp only [getElem, extend]
      simp only [List.get_eq_getElem]
      apply List.getElem_append_left

theorem extend_Prob (s : State) (h : s ∈ M.succs_univ π.last) (𝒮 : M.Scheduler) : (π.extend s h).Prob 𝒮 = M.P π.last (𝒮 π.last) s * π.Prob 𝒮 := by
  unfold Prob
  let ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero π.length_ne_zero
  rw [←Fin.prod_congr' _ (by simp ; omega : n + 1 = ∎|π.extend s h| - 1)]
  rw [←Fin.prod_congr' _ (by omega : n = ∎|π| - 1)]
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.getElem_fin, Nat.succ_eq_add_one, Fin.val_succ]
  rw [mul_comm]
  have hn' : n = ∎|π| - 1 := by omega
  simp only [Fin.coe_cast, Fin.val_last, hn', extend_get_length_pred, Nat.add_one_sub_one, id_eq,
    Int.reduceNeg, Int.Nat.cast_ofNat_Int, eq_mpr_eq_cast, length_pred_add, extend_get_length,
    Fin.coe_castSucc]
  congr
  · simp only [hn', extend_get_length_pred]
  · simp only [hn', extend_get_length_pred]
  · ext i
    congr! 1
    · congr! 1
      · simp only [extend, getElem_eq_states_getElem']
        apply List.getElem_append_left
      · congr! 2
        · rw [extend_get]
          simp
          split_ifs <;> simp_all only [Nat.succ_eq_add_one, add_tsub_cancel_right]
          omega
        · rw [extend_get]
          split_ifs <;> simp_all only [Nat.succ_eq_add_one, add_tsub_cancel_right, extend_length]
          omega
    · simp only [extend, getElem_eq_states_getElem']
      apply List.getElem_append_left

theorem tail_Prob_i (𝒮 : M.Scheduler) (i : Fin (∎|π.tail| - 1)) : π.tail.Prob_i 𝒮 i = π.Prob_i 𝒮 ⟨i.val + 1, by have := i.isLt ; simp at this ; omega⟩ := by
  simp [Prob_i]
  have iLt := i.isLt
  simp at iLt
  have h : 1 < ∎|π| := by
    by_contra q
    absurd iLt
    omega
  congr! 1
  · congr! 1
    all_goals
      rw [ ←π.tail_getElem_of_nonempty h i.val (by omega)]
      simp only [getElem]
  · rw [←π.tail_getElem_of_nonempty h (i.val + 1) (by omega)]
    simp only [getElem_eq_states_getElem']
