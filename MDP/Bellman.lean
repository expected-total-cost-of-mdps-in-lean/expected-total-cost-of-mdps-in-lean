import MDP.Paths.Sets
import MDP.ProbDist
import MDP.OmegaCompletePartialOrder
import MDP.KleeneFixedPoint

-- TODO: remove this
set_option linter.unusedSectionVars false

theorem Finset.sum_singleton_attach {α : Type*} (y : α) (f : { x // x ∈ ({y} : Finset α) } → ENNReal) : ∑ x ∈ ({y} : Finset α).attach, f x = f ⟨y, by simp⟩ := by
  refine Finset.sum_unique_nonempty ({y} : Finset α).attach f ?h
  simp

open OmegaCompletePartialOrder

namespace MDP

variable {State : Type*} {Act : Type*}
variable (M : MDP State Act)
variable [DecidableEq State] [DecidableEq Act]
variable [M.FiniteBranching] [Nonempty Act]

noncomputable def Φf (s : State) (a : Act) : (State → ENNReal) →𝒄 ENNReal :=
  ⟨⟨fun v ↦ (M.succs a s).sum fun s' ↦ M.P s a s' * v s', by
    intro v v' v_le_v'
    simp
    apply Finset.sum_le_sum
    exact fun i _ ↦ mul_le_mul_left' (v_le_v' i) (M.P s a i)
  ⟩, by
    apply Continuous'.to_bundled
    apply Finset_sum_continuous'
    intros
    apply mul_continuous'
    · exact const_continuous' _
    · exact Continuous.of_bundled _ _ (congrFun rfl)⟩

noncomputable def Φ𝒮 (cost : M.Costs) (𝒮 : M.Scheduler) : (State → ENNReal) →o (State → ENNReal) :=
  ⟨fun v s ↦ cost s + M.Φf s (𝒮 s) v, by
    intro v v' h s
    simp only
    gcongr
    exact (M.Φf s (𝒮 s)).mono h⟩

noncomputable def Φ (cost : M.Costs) : (State → ENNReal) →o (State → ENNReal) :=
  ⟨fun v s ↦ cost s + ((M.act₀ s).inf' (M.act₀_nonempty s) (M.Φf s · v)), by
    intro v v' h s
    simp only
    gcongr
    simp only [Finset.le_inf'_iff, Finset.inf'_le_iff]
    intro a a_in ; use a, a_in, (M.Φf s a).mono h⟩

theorem Φ.monotone' : Monotone (fun (cost : State → ENNReal) ↦ M.Φ cost) := by
    intro v v' h s
    simp_all only [Φ]
    apply add_le_add <;> try rfl
    simp_all only [Finset.le_inf'_iff, Finset.inf'_le_iff]

theorem Φ.continuous' (cost : M.Costs) : Continuous' <| M.Φ cost := by
  unfold Φ
  apply flip₂_continuous'
  intro s
  apply add_continuous' _ _ (const_continuous' _)
  apply Continuous.of_bundled
  apply Finset_inf'
  exact fun a ↦ (M.Φf s a).map_ωSup'

theorem Φ𝒮.continuous' (cost : M.Costs) (𝒮 : M.Scheduler) : Continuous' <| M.Φ𝒮 cost 𝒮 := by
  unfold Φ𝒮
  apply flip₂_continuous'
  intro s
  apply add_continuous' _ _ (const_continuous' _)
  apply Continuous.of_bundled
  exact (M.Φf s (𝒮 s)).map_ωSup'

theorem Φ_le_Φ𝒮 (cost : M.Costs) : M.Φ cost ≤ M.Φ𝒮 cost 𝒮 := by
  intro f s
  simp [Φ, Φ𝒮]
  gcongr
  simp
  use 𝒮 s, (M.act₀_mem_iff_act_mem _ _).mpr (𝒮 s).prop

noncomputable def lfp_Φ (cost : M.Costs) : State → ENNReal := OrderHom.lfp (M.Φ cost)

noncomputable def iSup_Φ (cost : M.Costs) : State → ENNReal := ⨆ (n : ℕ), (M.Φ cost)^[n.succ] ⊥
noncomputable def iSup'_Φ (cost : M.Costs) : State → ENNReal := ⨆ (n : ℕ), (M.Φ cost)^[n] ⊥

theorem iSup_Φ_eq_iSup'_Φ : M.iSup_Φ = M.iSup'_Φ := by
  ext cost s
  simp [iSup_Φ, iSup'_Φ]
  apply le_antisymm
  · simp
    intro n
    refine le_iSup_iff.mpr ?h.h.a.a
    intro e h
    have := h (n + 1)
    simp_all
  · simp
    intro n
    apply le_iSup_iff.mpr
    intro e h
    rcases n with n | n
    · simp_all
    · simp_all

theorem lfp_Φ_eq_iSup_Φ : M.lfp_Φ = M.iSup_Φ := by
  funext cost
  unfold lfp_Φ iSup_Φ
  rw [KleeneFixedPoint.Pi.succ'_iSup]
  exact Φ.continuous' M cost

theorem lfp_Φ_eq_iSup'_Φ : M.lfp_Φ = M.iSup'_Φ := M.lfp_Φ_eq_iSup_Φ.trans M.iSup_Φ_eq_iSup'_Φ

theorem Φ_iterate_succ (cost : M.Costs) (s : State) :
    (M.Φ cost)^[i + 1] ⊥ s
  = cost s + (M.act₀ s).inf' (M.act₀_nonempty s) fun x ↦ (M.Φf s x) ((M.Φ cost)^[i] ⊥)
:= by
  simp only [Function.iterate_succ', Function.comp_apply, Φ]
  simp
theorem Φ𝒮_iterate_succ (cost : M.Costs) (𝒮 : M.Scheduler) (s : State) :
    (M.Φ𝒮 cost 𝒮)^[i + 1] ⊥ s
  = cost s + (M.Φf s (𝒮 s)) ((M.Φ𝒮 cost 𝒮)^[i] ⊥)
:= by
  simp only [Function.iterate_succ', Function.comp_apply, Φ𝒮]
  simp

theorem lfp_Φ_step (cost : M.Costs) : M.Φ cost (M.lfp_Φ cost) = M.lfp_Φ cost :=
  OrderHom.map_lfp (M.Φ cost)

theorem lfp_Φ_step' (cost : M.Costs) (s : State) :
    M.lfp_Φ cost s
  = cost s + ((M.act₀ s).inf' (M.act₀_nonempty s) (fun a ↦ (M.succs a s).sum fun s' ↦ M.P s a s' * M.lfp_Φ cost s'))
:= by
  conv => left ; rw [←lfp_Φ_step]
  simp [Φ]
  rfl

theorem lfp_Φ_step_Φf (cost : M.Costs) (s : State) :
    M.lfp_Φ cost s
  = cost s + ((M.act₀ s).inf' (M.act₀_nonempty s) (fun a ↦ M.Φf s a (M.lfp_Φ cost)))
:= by
  conv => left ; rw [←lfp_Φ_step]
  simp [Φ]

noncomputable def lfp_Φ𝒮 (cost : M.Costs) (𝒮 : M.Scheduler) : State → ENNReal := OrderHom.lfp (M.Φ𝒮 cost 𝒮)

theorem lfp_Φ𝒮_step (cost : M.Costs) (𝒮 : M.Scheduler) : M.Φ𝒮 cost 𝒮 (M.lfp_Φ𝒮 cost 𝒮) = M.lfp_Φ𝒮 cost 𝒮 :=
  OrderHom.map_lfp (M.Φ𝒮 cost 𝒮)

theorem lfp_Φ𝒮_step_Φf (cost : M.Costs) (𝒮 : M.Scheduler) (s : State) :
    M.lfp_Φ𝒮 cost 𝒮 s
  = cost s + M.Φf s (𝒮 s) (M.lfp_Φ𝒮 cost 𝒮)
:= by
  conv => left ; rw [←lfp_Φ𝒮_step]
  simp [Φ𝒮]

theorem iSup_Φ_step (cost : M.Costs) : M.Φ cost (M.iSup_Φ cost) = M.iSup_Φ cost := by
  rw [←lfp_Φ_eq_iSup_Φ]
  exact M.lfp_Φ_step cost

theorem iSup_Φ_step' (cost : M.Costs) (s : State) :
    M.iSup_Φ cost s
  = cost s + ((M.act₀ s).inf' (M.act₀_nonempty s) (fun a ↦ (M.succs a s).sum fun s' ↦ M.P s a s' * M.iSup_Φ cost s'))
:= by
  rw [←lfp_Φ_eq_iSup_Φ]
  exact M.lfp_Φ_step' cost s

theorem lfp_Φ.mono (s : State) : Monotone (fun (cost : State → ENNReal) ↦ M.lfp_Φ cost s) := by
  rw [lfp_Φ_eq_iSup'_Φ]
  intro r₁ r₂ h
  simp only [iSup'_Φ, iSup_apply]
  have Φ_mono := MDP.Φ.monotone' M h
  simp at Φ_mono
  apply iSup_mono
  intro i
  induction i generalizing s with
  | zero => simp
  | succ i ih =>
    simp_all only [Function.iterate_succ']
    simp
    simp [Φ, Φf]
    gcongr
    · exact h s
    · simp
      intro α hα
      use α, hα
      gcongr
      apply ih
