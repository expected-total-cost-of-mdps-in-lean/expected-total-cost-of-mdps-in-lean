import MDP.Paths

namespace MDP

variable {State : Type*} {Act : Type*}

def Scheduler (M : MDP State Act) := (l : State) → {a // a ∈ M.act l}
def Scheduler' (M : MDP State Act) := (l : M.Path) → {a // a ∈ M.act l.last}

noncomputable instance (M : MDP State Act) : Inhabited M.Scheduler' :=
  ⟨fun l ↦ ⟨(M.progress_act l.last).choose, (M.progress_act l.last).choose_spec⟩⟩

noncomputable instance (M : MDP State Act) : Inhabited M.Scheduler :=
  ⟨fun l ↦ ⟨(M.progress_act l).choose, (M.progress_act l).choose_spec⟩⟩

@[simp]
theorem P_sum_one_iff_Scheduler (M : MDP State Act) (𝒮 : M.Scheduler') (s : State) : ∑ (s' ∈ (M.P s (𝒮 {s})).support), M.P s (𝒮 {s}) s' = 1 := by
  rw [P_sum_support_one_iff]
  exact Subtype.coe_prop (𝒮 {s})

@[simp]
theorem P_tsum_one_iff_Scheduler (M : MDP State Act) (𝒮 : M.Scheduler') (s : State) : ∑' (s' : (M.P s (𝒮 {s})).support), M.P s (𝒮 {s}) s' = 1 := by
  simp only [Finset.tsum_subtype, P_sum_one_iff_Scheduler]
