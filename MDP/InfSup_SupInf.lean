import Init.Data.List.Lemmas
import MDP.Bellman
import MDP.OptEC

-- TODO: remove this
set_option linter.unusedSectionVars false

namespace Finset

variable {α β : Type*}
variable (f : α → β) (S : Finset α) (hS : S.Nonempty)
variable [LinearOrder β] [OrderTop β]

noncomputable def argmin : α := (S.exists_mem_eq_inf' hS f).choose
noncomputable def argmin_spec : S.argmin f hS ∈ S ∧ S.inf' hS f = f (S.argmin f hS) := (S.exists_mem_eq_inf' hS f).choose_spec

theorem argmin_le (a : α) (ha : a ∈ S) : f (S.argmin f hS) ≤ f a := by
  rw [←(S.argmin_spec f hS).right, inf'_le_iff]
  use a

theorem argmin_mem : S.argmin f hS ∈ S := (S.argmin_spec f hS).left

end Finset

open OmegaCompletePartialOrder

namespace MDP

variable {State : Type*} {Act : Type*}
variable (M : MDP State Act)
variable [DecidableEq State] [DecidableEq Act]
variable [M.FiniteBranching] [Nonempty Act]

noncomputable def 𝒮' (cost : M.Costs) : M.Scheduler :=
  fun s ↦ ⟨(M.act₀ s).argmin (M.Φf s · (M.lfp_Φ cost)) (M.act₀_nonempty s), by rw [←M.act₀_mem_iff_act_mem] ; apply Finset.argmin_mem⟩
noncomputable def 𝒮'_spec (cost : M.Costs) (s : State) :
  (M.act₀ s).inf' (M.act₀_nonempty s) (M.Φf s · (M.lfp_Φ cost)) = (M.Φf s · (M.lfp_Φ cost)) (M.𝒮' cost s)
:= Finset.argmin_spec (M.Φf s · (M.lfp_Φ cost)) (M.act₀ s) (act₀_nonempty M s) |>.right

theorem EC'_ext_eq_EC (cost : M.Costs) (𝒮 : M.Scheduler) : M.EC' cost n s 𝒮.ext = M.EC cost n s 𝒮 := by
  simp [EC', EC]
  congr with π
  simp [Path.Prob', Path.Prob]
  congr with i
  simp [Scheduler.ext]
  rw [Path.take_last_eq_get']
  simp

noncomputable def sup_Φ𝒮 (cost : M.Costs) (𝒮 : M.Scheduler) : State → ENNReal := ⨆ n, (M.Φ𝒮 cost 𝒮)^[n] ⊥
noncomputable def sup'_Φ𝒮 (cost : M.Costs) (𝒮 : M.Scheduler) : State → ENNReal := ⨆ n, (M.Φ𝒮 cost 𝒮)^[n+1] ⊥

theorem lfp_Φ𝒮_eq_sup_Φ𝒮 (cost : M.Costs) (𝒮 : M.Scheduler) : M.lfp_Φ𝒮 cost 𝒮 = M.sup_Φ𝒮 cost 𝒮 := by
  simp [lfp_Φ𝒮, sup_Φ𝒮]
  apply KleeneFixedPoint.Pi.iSup _ <| Φ𝒮.continuous' M cost 𝒮
theorem sup_Φ𝒮_eq_sup'_Φ𝒮 (cost : M.Costs) (𝒮 : M.Scheduler) : M.sup_Φ𝒮 cost 𝒮 = M.sup'_Φ𝒮 cost 𝒮 := by
  ext s
  simp [sup_Φ𝒮, sup'_Φ𝒮]
  apply le_antisymm
  · simp
    intro n
    apply le_iSup_iff.mpr
    intro e h
    rcases n with n | n
    · simp_all
    · simp_all
  · simp
    intro n
    refine le_iSup_iff.mpr ?h.h.a.a
    intro e h
    have := h (n + 1)
    simp_all

theorem Φ𝒮_step_EC (cost : M.Costs) (𝒮 : M.Scheduler) : M.EC cost (n + 1) s 𝒮 = M.Φ𝒮 cost 𝒮 (M.EC cost n · 𝒮) s := by
  simp [EC]
  rw [M.Paths_n₀_succ n s]
  simp [succs_Paths_n₀]
  rw [Finset.sum_biUnion]
  · simp []
    simp [Φ𝒮, Φf]
    rw [sum_succs_eq_sum_succs_univ_mul]
    simp [prepend_Prob, Path.prepend_Cost]
    simp [mul_add]
    simp [Finset.sum_add_distrib]
    congr! 1
    · simp [←Finset.sum_mul]
      conv => right ; rw [←one_mul (cost s)]
      congr
      calc
        ∑ s' ∈ (M.succs_univ₀ s).attach, ∑ π ∈ (M.Paths_n₀ s' n).attach, M.P s (𝒮 s) π.val.first * π.val.Prob 𝒮
          = ∑ s' ∈ M.succs_univ₀ s, ∑ π ∈ (M.Paths_n₀ s' n).attach, M.P s (𝒮 s) π.val.first * π.val.Prob 𝒮 := by
            apply Finset.sum_of_injOn (·.val)
            · intro _ _ _ _ h ; exact SetCoe.ext h
            · intro _ _ ; simp
            · intro s' hs' hs'' ; simp_all
            · simp
        _ = ∑ s' ∈ M.succs_univ₀ s, ∑ π ∈ M.Paths_n₀ s' n, M.P s (𝒮 s) π.first * π.Prob 𝒮 := by
          congr with s'
          apply Finset.sum_of_injOn (·.val)
          · intro _ _ _ _ h ; exact SetCoe.ext h
          · intro _ _ ; simp
          · intro s' hs' hs'' ; simp_all
          · simp
        _ = ∑ s' ∈ M.succs_univ₀ s, ∑ π ∈ M.Paths_n₀ s' n, M.P s (𝒮 s) s' * π.Prob 𝒮 := by
          congr! 2 with s' _ π hπ
          rw [M.Paths_n₀_first_eq_first s' n π hπ]
        _ = ∑ s' ∈ M.succs_univ₀ s, M.P s (𝒮 s) s' * ∑ π ∈ M.Paths_n₀ s' n, π.Prob 𝒮 := by simp [Finset.mul_sum]
        _ = ∑ s' ∈ M.succs_univ₀ s, M.P s (𝒮 s) s' * 1 := by
          congr! 2 with s' _
          exact M.Paths_n₀_Prob 𝒮 n
        _ = 1 := by
          simp
          exact M.succs_univ_P_act₀ s ⟨𝒮 s, (M.act₀_mem_iff_act_mem s (𝒮 s)).mpr (𝒮 s).prop⟩
    · apply Finset.sum_of_injOn (fun s ↦ s.val)
      · intro _ _ _ _ h
        exact SetCoe.ext h
      · intro _ _ ; simp
      · intro s' hs' hs''
        simp_all
      · intro s' _
        rw [Finset.mul_sum]
        apply Finset.sum_of_injOn (fun s ↦ s.val)
        · intro _ _ _ _ h
          exact SetCoe.ext h
        · intro _ _ ; simp
        · intro π hπ hπ'
          simp_all
          absurd hπ'
          simp only [not_forall, Decidable.not_not]
          refine Exists.intro hπ ?h.e'_6.h.h'.h
          apply Finset.mem_attach
        · intro π _
          simp [mul_assoc]
          congr
          apply M.Paths_n₀_first_eq_first s' n
          exact Finset.coe_mem π
  · intro s₁ _ s₂ _ h S h₁ h₂ π hπ
    simp_all
    have hπ₁ := h₁ hπ
    have hπ₂ := h₂ hπ
    simp_all
    obtain ⟨π₁, hπ₁, _, hπ₁'⟩ := hπ₁
    obtain ⟨π₂, hπ₂, _, hπ₂'⟩ := hπ₂
    have : π₁ = π₂ := by
      rw [←hπ₂'] at hπ₁'
      exact π₁.preprend_injective π₂ s hπ₁'
    have hf₁ : π₁.first = s₁ := M.Paths_n₀_first_eq_first s₁ n π₁ hπ₁
    have hf₂ : π₂.first = s₂ := M.Paths_n₀_first_eq_first s₂ n π₂ hπ₂
    absurd h
    apply SetCoe.ext
    simp_all

theorem sup_EC_eq_lfp_Φ𝒮 (cost : M.Costs) (𝒮 : M.Scheduler) : ⨆ n, M.EC cost n s 𝒮 = M.lfp_Φ𝒮 cost 𝒮 s := by
  rw [lfp_Φ𝒮_eq_sup_Φ𝒮, sup_Φ𝒮_eq_sup'_Φ𝒮]
  simp only [sup'_Φ𝒮, iSup_apply]
  congr with n
  induction n generalizing s with
  | zero => simp [EC, Paths_n₀, Φ𝒮, Φf, Path.Cost]
  | succ n ih =>
    simp only [M.Φ𝒮_step_EC cost 𝒮, ih]
    conv => right ; rw [Φ𝒮_iterate_succ]
    simp [Φ𝒮]

theorem lfp_Φ𝒮_𝒮'_eq_lfp_Φ (cost : M.Costs) : M.lfp_Φ𝒮 cost (M.𝒮' cost) = M.lfp_Φ cost := by
  apply le_antisymm
  · apply OrderHom.lfp_le
    intro s
    rw [lfp_Φ_step_Φf]
    simp [Φ𝒮, M.𝒮'_spec cost s]
  · suffices M.Φ𝒮 cost (M.𝒮' cost) (M.lfp_Φ cost) ≤ M.lfp_Φ cost by
      apply OrderHom.lfp_le
      conv => right ; rw [← lfp_Φ𝒮_step]
      apply Φ_le_Φ𝒮
    intro s
    rw [lfp_Φ_step_Φf]
    simp only [Φ𝒮, OrderHom.coe_mk, ← M.𝒮'_spec cost s, le_refl]

theorem sup_inf_EC'_eq_inf_sup_EC' (cost : M.Costs) (s : State) : ⨆ n, ⨅ 𝒮, M.EC' cost n s 𝒮 = ⨅ 𝒮, ⨆ n, M.EC' cost n s 𝒮 := by
  apply le_antisymm
  · apply iSup_iInf_le_iInf_iSup
  · suffices ∃ (𝒮' : M.Scheduler), ⨆ n, M.EC' cost n s 𝒮'.ext = ⨆ n, ⨅ 𝒮, M.EC' cost n s 𝒮 by
      obtain ⟨𝒮', h⟩ := this
      simp [← h, iInf_le']
    use M.𝒮' cost
    simp [M.EC'_ext_eq_EC, sup_EC_eq_lfp_Φ𝒮]
    have : ⨆ n, ⨅ (𝒮 : M.Scheduler'), M.EC' cost n s 𝒮 = ⨆ n, ⨅ (𝒮 : M.Scheduler'), M.EC₀' cost n s 𝒮.constrain := by
      congr! 4 with n 𝒮
      exact (sum_Paths_n₀_RProb'_Cost_eq_Prob'_Cost cost s n 𝒮).symm
    rw [this]
    simp [M.Scheduler'_constrain_inf]
    rw [M.sup_inf_EC₀'_eq_lfp_Φ cost s]
    simp [M.lfp_Φ𝒮_𝒮'_eq_lfp_Φ]

theorem inf_sup_EC_eq_inf_sup_EC' (cost : M.Costs) (s : State) : ⨅ 𝒮, ⨆ n, M.EC cost n s 𝒮 = ⨅ 𝒮, ⨆ n, M.EC' cost n s 𝒮 := by
  rw [←M.sup_inf_EC'_eq_inf_sup_EC' cost s, M.sup_inf_EC'_eq_sup_inf_EC₀' cost s, M.sup_inf_EC₀'_eq_lfp_Φ cost s]
  simp [sup_EC_eq_lfp_Φ𝒮]
  apply le_antisymm
  · rw [← M.lfp_Φ𝒮_𝒮'_eq_lfp_Φ cost]
    apply iInf_le'
  · simp
    intro 𝒮
    suffices M.lfp_Φ cost ≤ M.lfp_Φ𝒮 cost 𝒮 by exact this s
    apply OrderHom.lfp_le
    conv => right ; rw [←lfp_Φ𝒮_step]
    apply Φ_le_Φ𝒮

theorem sup_inf_EC'_le_sup_inf_EC (cost : M.Costs) (s : State) : ⨆ n, ⨅ 𝒮, M.EC' cost n s 𝒮 ≤ ⨆ n, ⨅ 𝒮, M.EC cost n s 𝒮 := by
  gcongr with n
  simp
  intro 𝒮
  apply iInf_le_of_le 𝒮.ext
  simp [EC', EC, Path.Prob, Path.Prob', Scheduler.ext]
  congr! 6 with π _ i
  all_goals
    have : (π.take ↑i).last = π.states[↑i] := by simp [Path.take, Path.last_eq_get] ; congr ; omega
    congr! 3

theorem sup_inf_EC'_eq_inf_sup_EC (cost : M.Costs) (s : State) : ⨆ n, ⨅ 𝒮, M.EC' cost n s 𝒮 = ⨅ 𝒮, ⨆ n, M.EC cost n s 𝒮 := by
  rw [sup_inf_EC'_eq_inf_sup_EC']
  exact Eq.symm (inf_sup_EC_eq_inf_sup_EC' M cost s)

theorem sup_inf_EC_eq_inf_sup_EC (cost : M.Costs) (s : State) : ⨆ n, ⨅ 𝒮, M.EC cost n s 𝒮 = ⨅ 𝒮, ⨆ n, M.EC cost n s 𝒮 := by
  apply le_antisymm
  · apply iSup_iInf_le_iInf_iSup
  · apply le_trans _ (M.sup_inf_EC'_le_sup_inf_EC cost s)
    rw [inf_sup_EC_eq_inf_sup_EC']
    rw [sup_inf_EC'_eq_inf_sup_EC']

theorem sup_inf_EC'_eq_sup_inf_EC (cost : M.Costs) (s : State) : ⨆ n, ⨅ 𝒮, M.EC' cost n s 𝒮 = ⨆ n, ⨅ 𝒮, M.EC cost n s 𝒮 := by rw [sup_inf_EC'_eq_inf_sup_EC, sup_inf_EC_eq_inf_sup_EC]

theorem sup_inf_EC_eq_inf_sup_EC' (cost : M.Costs) (s : State) : ⨆ n, ⨅ 𝒮, M.EC cost n s 𝒮 = ⨅ 𝒮, ⨆ n, M.EC' cost n s 𝒮 := by rw [sup_inf_EC_eq_inf_sup_EC, inf_sup_EC_eq_inf_sup_EC']

theorem inf_sup_EC'_eq_lfp_Φ (cost : M.Costs) (s : State) : ⨅ 𝒮, ⨆ n, M.EC' cost n s 𝒮 = M.lfp_Φ cost s := by
  simp only [← sup_inf_EC₀'_eq_lfp_Φ, ← sup_inf_EC'_eq_sup_inf_EC₀', M.sup_inf_EC'_eq_inf_sup_EC' cost s]

theorem Complete (cost : M.Costs) (s : State) :
  let S: Set ENNReal := {
    ⨆ n, ⨅ 𝒮, M.EC' cost n s 𝒮,
    ⨆ n, ⨅ 𝒮, M.EC cost n s 𝒮,
    ⨅ 𝒮, ⨆ n, M.EC cost n s 𝒮,
    ⨅ 𝒮, ⨆ n, M.EC' cost n s 𝒮,
    M.lfp_Φ cost s
  }
  ∀ v₁ v₂ : S, v₁ = v₂
:= by
  simp only [Subtype.forall, M.sup_inf_EC'_eq_inf_sup_EC' cost s, ←
    M.sup_inf_EC'_eq_sup_inf_EC cost s, ← M.sup_inf_EC'_eq_inf_sup_EC cost s, ← sup_inf_EC₀'_eq_lfp_Φ,
    ← sup_inf_EC'_eq_sup_inf_EC₀', Set.mem_singleton_iff, Set.insert_eq_of_mem, Subtype.mk.injEq,
    forall_eq, imp_self, implies_true]
