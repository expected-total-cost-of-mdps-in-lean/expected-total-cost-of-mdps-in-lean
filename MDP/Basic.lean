import Mathlib.Control.Fix
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Real.EReal
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Use
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Topology.Instances.Rat
import MDP.ZeroOne

abbrev PReal := { p : ENNReal // 0 < p ∧ p ≤ 1 }

structure MDP (State : Type*) (Act : Type*) where
  P : State → Act → State →₀ ENNReal
  sum_P_zero_or_one s a : is₀₁ (∑' s', P s a s')
  progress s : ∃ (a : Act) (s' : State), 0 < P s a s'

namespace MDP

variable {State : Type*} {Act : Type*}

theorem progress' (M : MDP State Act) (s : State) : ∃ (a : Act), (M.P s a).support.Nonempty := by
  obtain ⟨a, s', h⟩ := M.progress s
  use a, s'
  simp only [Finsupp.mem_support_iff, ne_eq]
  exact pos_iff_ne_zero.mp h

theorem sum_P_zero_or_one' (M : MDP State Act) (s : State) (a : Act) : is₀₁ ((M.P s a).support.sum (M.P s a)) := by
  rcases M.sum_P_zero_or_one s a with h | h
  · left
    rw [←h, tsum_eq_sum]
    exact fun _  ↦ Finsupp.not_mem_support_iff.mp
  · right
    rw [←h, tsum_eq_sum]
    exact fun _  ↦ Finsupp.not_mem_support_iff.mp

theorem if_and_eq_if_if {α : Type*} (a b : Prop) [Decidable a] [Decidable b] (x y : α) : (if a ∧ b then x else y) = if a then if b then x else y else y := by
  by_cases h : a ∧ b
  · simp only [h, and_self, ↓reduceIte]
  · simp_all only [not_and, ite_false, ite_self, ite_eq_right_iff, isEmpty_Prop, not_false_eq_true,
    implies_true, IsEmpty.forall_iff]

theorem tsum_finsum_if_eq_finsum {α β γ : Type*} [DecidableEq α] [AddCommMonoid β] [TopologicalSpace β] [DecidableEq γ]
  (S : Finset α) (i : α → γ) (f : α → β)
:
  (tsum   fun x ↦ S.sum fun s ↦ if i s = x then f s else 0)         = S.sum f := by
  have : (fun x ↦ S.sum fun s ↦ if i s = x then f s else 0).support ⊆ S.image i := by
    simp only [Finset.coe_image, Function.support_subset_iff, ne_eq, Set.mem_image, Finset.mem_coe]
    intro x h
    obtain ⟨y, h₁, h₂⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    rw [ne_eq, ite_eq_right_iff, not_forall, exists_prop] at h₂
    use y
    rw [h₂.left]
    exact ⟨h₁, rfl⟩
  rw [tsum_eq_sum' this, Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_image]
  rw [Finset.sum_congr] <;> try rfl
  simp only [ite_eq_left_iff, not_exists, not_and]
  exact fun x x' h ↦ (h x x' rfl).elim

lemma P_le_sum_P (M : MDP State Act) (s : State) (a : Act) (s' : State) : M.P s a s' ≤ ∑' (s'' : State), M.P s a s'' :=
  ENNReal.le_tsum s'

lemma P_le_one (M : MDP State Act) (s : State) (a : Act) (s' : State) : M.P s a s' ≤ 1 :=
  Preorder.le_trans _ _ _ (P_le_sum_P M s a s') (is₀₁_le_one (M.sum_P_zero_or_one s a))

lemma P_ne_top (M : MDP State Act) (s : State) (a : Act) (s' : State) : M.P s a s' ≠ ⊤ :=
  M.P_le_one s a s' |>.trans_lt ENNReal.one_lt_top |>.ne

lemma P_ne_zero_sum_eq_one {M : MDP State Act} {s : State} {a : Act} {s' : State} (h : M.P s a s' ≠ 0) : ∑' s'', M.P s a s'' = 1 := by
  cases M.sum_P_zero_or_one s a with
  | inl h' => rw [tsum_eq_sum (fun _ ↦ Finsupp.not_mem_support_iff.mp), Finset.sum_eq_zero_iff] at h'
              exact (h (h' _ (Finsupp.mem_support_iff.mpr h))).elim
  | _ => assumption

theorem P_pos_iff_sum_eq_one {M : MDP State Act} {s : State} {a : Act} : (M.P s a).support.Nonempty ↔ 1 = ∑' s', M.P s a s' := by
  constructor <;> intro h
  · obtain ⟨s', h⟩ := h
    simp [P_ne_zero_sum_eq_one (Finsupp.mem_support_iff.mp h)]
  · by_contra q
    simp at q
    rw [tsum_eq_sum (α := ENNReal) (s := (M.P s a).support)] at h
    · simp_all only [Finsupp.support_zero, Finsupp.coe_zero, Pi.zero_apply, Finset.sum_const_zero,
      one_ne_zero]
    · simp

-- def act_discrete   (M : MDP State Act) (s : State) : Set Act := {a | ∃s', M.P s a s' ≠ 0}
-- def act_continouos (M : MDP State Act) (s : State) : Set Act := {a | (∑' s', M.P s a s') = 1}
def act (M : MDP State Act) (s : State) : Set Act := {a | 1 = ∑' s', M.P s a s'}
def act' (M : MDP State Act) (s : State) : Set Act := {a | 1 = (M.P s a).support.sum (M.P s a)}

theorem act_eq_act' (M : MDP State Act) : M.act = M.act' := by
  ext s α
  simp only [act, Finsupp.fun_support_eq, Finset.finite_toSet, tsum_eq_finsum, finsum_eq_sum,
    Set.toFinite_toFinset, Finset.toFinset_coe, Set.mem_setOf_eq, act']

def PMF (M : MDP State Act) (s : State) {a : Act} (h : a ∈ M.act s) : PMF State := ⟨M.P s a, by
  simp_all only [act, Set.mem_setOf_eq]
  exact (Summable.hasSum_iff ENNReal.summable).mpr rfl⟩

class FiniteBranching (M : MDP State Act) where
  act₀ : State → Finset Act
  act₀_eq_act : ∀ (s : State), act₀ s = M.act s

noncomputable instance (M : MDP State Act) [Fintype Act] (s : State) : Fintype ↑(M.act s) := Fintype.ofFinite ↑(M.act s)
noncomputable instance (M : MDP State Act) (s : State) : Nonempty ↑(M.act s) := by
  simp only [act, ← P_pos_iff_sum_eq_one, Set.coe_setOf, nonempty_subtype]
  exact M.progress' s

noncomputable instance (M : MDP State Act) [Fintype Act] : M.FiniteBranching where
  act₀ s := (M.act s).toFinset
  act₀_eq_act _ := Set.coe_toFinset _

def act₀ (M : MDP State Act) [i : M.FiniteBranching] (s : State) : Finset Act := i.act₀ s
theorem act₀_iff_act (M : MDP State Act) [i : M.FiniteBranching] (s : State) : M.act₀ s = M.act s := i.act₀_eq_act s

theorem act₀_mem_iff_act_mem (M : MDP State Act) [M.FiniteBranching] (s : State) (a : Act) : a ∈ M.act₀ s ↔ a ∈ M.act s := by
  simp only [← act₀_iff_act, Finset.mem_coe]
noncomputable def act₀_prop (M : MDP State Act) [i : FiniteBranching M] (s : State) (a : Act) (h : a ∈ M.act₀ s) : 1 = ∑' s', M.P s a s' := by
  simp_all [act₀_mem_iff_act_mem]
  simp [act] at h
  exact h

noncomputable instance (M : MDP State Act) [M.FiniteBranching] (s : State) : Nonempty ↑(M.act₀ s) := by
  simp only [act₀_mem_iff_act_mem, act, ← P_pos_iff_sum_eq_one, Set.coe_setOf, nonempty_subtype]
  exact M.progress' s

theorem P_nonempty_iff_act (M : MDP State Act) (s : State) (a : Act) : (M.P s a).support.Nonempty ↔ a ∈ M.act s := by
  simp only [act, Finset.mem_filter, Fintype.complete, true_and]
  exact M.P_pos_iff_sum_eq_one

theorem P_nonempty_iff_act₀ (M : MDP State Act) [M.FiniteBranching] (s : State) (a : Act) : (M.P s a).support.Nonempty ↔ a ∈ M.act₀ s := by
  simp [act₀_mem_iff_act_mem, Finset.mem_filter, Fintype.complete, true_and]
  exact M.P_pos_iff_sum_eq_one

noncomputable def act_nonempty [Nonempty Act] (M : MDP State Act) (s : State) : (M.act s).Nonempty := by
  simp [act]
  obtain ⟨a, h⟩ := M.progress' s
  have : a ∈ M.act s := (MDP.P_nonempty_iff_act M s a).mp h
  use a, this

noncomputable def act_default [Nonempty Act] (M : MDP State Act) [inst : M.FiniteBranching] (s : State) : {α // α ∈ M.act s} :=
  ⟨(M.act₀ s).toList.head (by
    simp_all
    have ⟨α, hα⟩ := M.act_nonempty s
    simp_all [←M.act₀_iff_act s]
    exact Finset.ne_empty_of_mem hα
    ), by
      simp_all only [← M.act₀_iff_act s, Finset.mem_coe, ← Finset.mem_toList]
      apply List.head_mem⟩


noncomputable def act₀_nonempty [Nonempty Act] (M : MDP State Act) [M.FiniteBranching] (s : State) : (M.act₀ s).Nonempty := by
  simp [act₀]
  obtain ⟨a, h⟩ := M.progress' s
  have : a ∈ M.act₀ s := (MDP.P_nonempty_iff_act₀ M s a).mp h
  use a, this

noncomputable def act₀_default [Nonempty Act] (M : MDP State Act) [inst : M.FiniteBranching] (s : State) : {α // α ∈ M.act₀ s} := ⟨M.act_default s, by
  simp_all only [← Finset.mem_toList]
  apply List.head_mem⟩

theorem progress_act (M : MDP State Act) (s : State) : ∃ (a : Act), a ∈ M.act s := by
  obtain ⟨a, s', h⟩ := M.progress' s
  use a
  rw [←M.P_nonempty_iff_act s a]
  use s'

theorem progress_act₀ (M : MDP State Act) [M.FiniteBranching] (s : State) : ∃ (a : Act), a ∈ M.act₀ s := by
  obtain ⟨a, h⟩ := M.progress_act s
  use a
  exact (act₀_mem_iff_act_mem M s a).mpr h

theorem P_sum_one_iff (M : MDP State Act) (s : State) (a : Act) : ∑' s', M.P s a s' = 1 ↔ a ∈ M.act s := by
  simp only [act, Set.mem_setOf_eq]
  constructor <;> (intros h ; symm ; exact h)

theorem P_sum_support_one_iff (M : MDP State Act) (s : State) (a : Act) : ∑ (s' ∈ (M.P s a).support), M.P s a s' = 1 ↔ a ∈ M.act s := by
  simp only [Finset.univ_eq_attach, ← P_sum_one_iff]
  symm
  apply Eq.congr _ rfl
  apply tsum_eq_sum fun _ a_1 ↦ Finsupp.not_mem_support_iff.mp a_1

theorem P_tsum_support_one_iff (M : MDP State Act) (s : State) (a : Act) : ∑' (s' : (M.P s a).support), M.P s a s' = 1 ↔ a ∈ M.act s := by
  simp only [Finset.tsum_subtype, P_sum_support_one_iff]

def Post (M : MDP State Act) (s : State) (a : Act) : Set State := {s' | M.P s a s' > 0}
def Pre (M : MDP State Act) (s' : State) : Set (State × Act) := {(s, a) | M.P s a s' > 0}

section mk

variable [DecidableEq State] [DecidableEq Act]

noncomputable def mk_from_succs
  (succs : State → Act → Finset (State × PReal))
  (h : ∀ (s : State) (a : Act), is₀₁ (succs s a |>.sum (·.2.val)))
  (progress : ∀ (s : State), ∃ (a : Act) (s' : State) (p : PReal), (s', p) ∈ succs s a)
  : MDP State Act
:=
  let P s a := Finsupp.onFinset
    (succs s a |>.filter (fun (_, p) ↦ 0 < p.val) |>.image (fun (s', _) ↦ s'))
    (fun s' ↦ succs s a |>.filter (fun (s'', _) ↦ s'' = s') |>.sum (·.2.val))
    (fun s'' h => by
      simp_all only [Subtype.exists, ne_eq, Finset.sum_eq_zero_iff, Finset.mem_filter, and_imp,
        Prod.forall, Subtype.forall, not_forall, Classical.not_imp, exists_and_right,
        Finset.mem_image, Prod.exists, and_true, exists_eq_right]
      obtain ⟨_, p', p_le_one, _, _⟩ := h
      use p'
      simp_all only [exists_prop, exists_true_left, ne_eq, not_false_eq_true, and_self, and_true]
      )
  have h := by
    simp only [Finset.sum_filter, Finsupp.onFinset_apply, tsum_finsum_if_eq_finsum, P]
    exact h
  let progress := by
    intro s
    obtain ⟨a, s', p, h⟩ := progress s
    use a, s'
    simp only [Finset.sum_filter, Finsupp.onFinset_apply, P]
    by_contra q
    simp only [not_lt, nonpos_iff_eq_zero] at q
    absurd Finset.sum_eq_zero_iff.mp q (s', p) h
    simp only [↓reduceIte]
    exact pos_iff_ne_zero.mp p.property.1
  ⟨P, h, progress⟩

noncomputable def mk_from_op
  (op : State → Finset (Act × State × PReal))
  (h : ∀ (s : State) (a : Act), is₀₁ (op s |>.filter (·.1 = a) |>.sum (·.2.2.val)))
  (progress : ∀ (s : State), ∃ (a : Act) (s' : State) (p : PReal), (a, s', p) ∈ op s)
  : MDP State Act
:= mk_from_succs (fun s a ↦ op s |>.filter (·.1 = a) |>.image (·.2))
  (by
    intro s a
    simp_all only [Finset.sum_filter, Finset.mem_filter, and_imp, Prod.forall, Subtype.forall,
      implies_true, Finset.sum_image])
  (by
    intro s
    obtain ⟨a, s', p, h⟩ := progress s
    use a, s', p
    simp only [Finset.mem_image, Finset.mem_filter, Prod.exists, exists_eq_right]
    exact h)

end mk

theorem Finset.biUnion_ite_eq {α β : Type*} [DecidableEq α] [DecidableEq β] (s : Finset α) (a : α) (f : α → Finset β) : (s.biUnion fun i ↦ if i = a then f i else ∅) = if a ∈ s then f a else ∅ := by
  apply subset_antisymm <;> by_cases h : a ∈ s
  · simp_all
    intro x _
    by_cases h' : x = a
    · simp [h']
    · simp [h']
  · simp_all
    intro x hx
    have : x ≠ a := by
      intro q
      simp_all only
    simp_all
  · simp_all
    intro x hx
    simp_all
    use a, h
    simp [hx]
  · simp_all

section Succs

variable (M : MDP State Act)

def succs (M : MDP State Act) (α : Act) (s : State) : Finset State := (M.P s α).support

def succs_univ (s : State) : Set State := ⋃ α ∈ M.act s, M.succs α s

variable [DecidableEq State] [M.FiniteBranching]

def succs_univ₀ (s : State) : Finset State := Finset.biUnion (M.act₀ s) (M.succs · s)
noncomputable def succs_univ₀_subtype (s : State) : Finset (Subtype (fun s' ↦ s' ∈ M.succs_univ₀ s)) := (M.succs_univ₀ s).attach
theorem succs_univ₀_spec (s s' : State) : s' ∈ M.succs_univ₀ s → ∃α, 0 < M.P s α s' := by
  intro h
  simp [succs_univ₀] at h
  obtain ⟨α, _, hα⟩ := h
  use α
  simp [succs] at hα
  exact pos_iff_ne_zero.mpr hα

@[simp]
theorem succs_univ_eq_succs_univ₀ (s : State) :
  M.succs_univ s = M.succs_univ₀ s
:= by simp [succs_univ, succs_univ₀, act₀_mem_iff_act_mem]

end Succs

end MDP
