import Mathlib.Data.List.Indexes
import MDP.ListExt
import MDP.Basic

-- TODO: remove this
set_option linter.unusedSectionVars false

namespace MDP

structure Path (M : MDP State Act) where
  states : List State
  nonempty : states ≠ []
  property : ∀ (i : Fin (states.length - 1)),
    states.get ⟨i.succ, by have := List.length_pos.mpr nonempty ; omega⟩ ∈ M.succs_univ (states.get ⟨i, by omega⟩)
deriving DecidableEq

namespace Path

variable {State : Type*} {Act : Type*}
variable [DecidableEq State] [DecidableEq Act]
variable {M : MDP State Act} (π π' : M.Path)

def first := π.states.head π.nonempty
def last := π.states.getLast π.nonempty
notation "∎|" a "|" => List.length (Path.states a)

@[simp]
theorem last_in_states : π.last ∈ π.states := List.getLast_mem π.nonempty

@[simp]
theorem length_pos : 0 < ∎|π| := List.length_pos.mpr π.nonempty

@[simp]
theorem length_ne_zero : ∎|π| ≠ 0 := Nat.not_eq_zero_of_lt π.length_pos

@[simp]
theorem length_pred_succ : (∎|π| - 1).succ = ∎|π| :=
  Nat.succ_pred (Nat.not_eq_zero_of_lt (List.length_pos.mpr π.nonempty))
@[simp]
theorem length_pred_add : ∎|π| - 1 + 1 = ∎|π| :=
  Nat.succ_pred (Nat.not_eq_zero_of_lt (List.length_pos.mpr π.nonempty))

instance instGetElem : GetElem M.Path ℕ State fun π i ↦ i < ∎|π| where
  getElem π i h := π.states[i]

theorem property' (i : Fin (∎|π| - 1)) : ∃ (α : Act),  0 < M.P π[i] α π[i.succ] := by
  have := π.property ⟨i, by omega⟩
  simp [succs_univ] at this
  obtain ⟨α, _, h⟩ := this
  use α
  simp_all [succs]
  exact pos_iff_ne_zero.mpr h

theorem property_first (h : 1 < ∎|π|) : ∃ (α : Act), (0 : ENNReal) < M.P π.first α π[1] := by
  convert π.property' ⟨0, by omega⟩
  simp only [first, List.head_eq_get, List.get_eq_getElem, Fin.getElem_fin]
  rfl

theorem states_get_eq_getElem (i : Fin ∎|π|) : π.states.get i = π[i] := by
  rfl

@[simp]
theorem getElem_eq_states_getElem (i : Fin ∎|π|) : π[i] = π.states[i] := by
  rfl

@[simp]
theorem getElem_eq_states_getElem' (i : ℕ) (h : i < ∎|π|) : π[i] = π.states[i] := by
  rfl

theorem states_getElem_eq_getElem (i : Fin ∎|π|) : π.states[i] = π[i] := by
  rfl

theorem first_eq_states_getElem_zero : π.first = π.states[0] := by
  simp only [first, List.head_eq_get, List.get_eq_getElem]

theorem first_eq_getElem_zero : π.first = π[0] := by
  rw [first_eq_states_getElem_zero]
  rfl

@[simp]
theorem getElem_mem_states (i : Fin ∎|π|) : π[i] ∈ π.states := by
  simp only [Fin.getElem_fin, getElem_eq_states_getElem', List.getElem_mem]

@[simp]
theorem getElem_mem_states' (i : Fin (∎|π| - 1)) : π[i] ∈ π.states := by
  simp only [getElem]
  simp only [List.get_eq_getElem, List.getElem_mem]

theorem last_eq_get : π.last = π[∎|π| - 1] := by
  exact List.getLast_eq_getElem π.states π.nonempty

theorem last_eq_states_get : π.last = π.states.get ⟨∎|π| - 1, by simp⟩ := by
  rw [last_eq_get]
  unfold instGetElem
  simp only [get, Fin.getElem_fin, List.get_eq_getElem]

abbrev mk_single (M : MDP State Act) (s : State) : M.Path := ⟨[s], List.cons_ne_nil s _,  fun i ↦ False.elim (not_lt_zero' i.isLt)⟩

instance instSingleton : Singleton State M.Path := ⟨mk_single M⟩

attribute [reducible] instSingleton

instance [i : Inhabited State] : Inhabited M.Path where
  default := mk_single M i.default

@[simp]
theorem mk_single_length (M : MDP State Act) (s : State) : ∎|mk_single M s| = 1 := by
  simp only [mk_single, List.length_cons, List.length_nil, zero_add]

@[simp]
theorem mk_single_get_zero (M : MDP State Act) (s : State) : (mk_single M s)[0] = s := by
  simp only [mk_single]
  rfl

@[simp]
theorem mk_single_get (M : MDP State Act) (s : State) (i : Fin 1) : (mk_single M s)[i] = s := by
  simp only [Fin.getElem_fin, Fin.val_eq_zero, getElem_eq_states_getElem', List.getElem_cons_zero]

@[simp]
theorem mk_single_first (M : MDP State Act) (s : State) : (mk_single M s).first = s := by
  unfold first
  simp only [mk_single, List.head_cons]

@[simp]
theorem mk_single_last (M : MDP State Act) (s : State) : (mk_single M s).last = s := by
  unfold last
  simp only [mk_single, List.getLast_singleton]

@[simp]
theorem mk_single_states (M : MDP State Act) (s : State) : (mk_single M s).states = [s] := by
  simp only [mk_single]

theorem eq_iff_right (π π' : M.Path)
  (h₁ : ∎|π| = ∎|π'|)
  (h₂ : ∀ (i : ℕ), (h : i < ∎|π|) → π[i] = π'[i])
: π = π' := by
  cases π  with | mk s₁ nonempty₁ prop₁ =>
  cases π'  with | mk s₂ nonempty₂ prop₂ =>
  simp_all only [length_pred_succ, P, get, Nat.succ_eq_add_one, Fin.succ_mk, mk.injEq]
  apply List.ext_get_iff.mpr ; constructor
  · have := Nat.succ_inj.mpr h₁
    simp only [Nat.succ_eq_add_one, add_left_inj] at this
    exact this
  · intro i h₁' h₂'
    by_cases h : i < s₂.length
    · have : s₁.get ⟨i, by omega⟩ = s₂.get ⟨i, by omega⟩ := by exact h₂ i (by omega)
      exact this
    · contradiction

theorem eq_states (π π' : M.Path) (h : π.states = π'.states) : π = π' := by
  apply eq_iff_right
  · intros
    simp [h]
  · exact congrArg List.length h

theorem mk_single_iff_length_zero : π = mk_single M π.first ↔ ∎|π| = 1 := by
  dsimp only [Nat.succ_eq_add_one, mk_single]
  constructor
  · intro h
    rw [h]
    simp only [List.length_cons, List.length_nil, zero_add]
  · intro h
    apply eq_iff_right
    · simp_all
      intros i hi
      unfold first
      apply List.get_mk_zero
    · simp_all only [List.length_cons, List.length_nil, zero_add]

-- @[simp]
-- def mk' (M : MDP State Act) (π : Paths.Path State) (h : ∀ (i : ℕ), (h : i < ∎|π|) → ∃ (α : Act), π.P ⟨i, h⟩ = M.P (π.get i) α (π.get i.succ)) : M.Path := ⟨π, by
--   intro i
--   obtain ⟨a, h⟩ := h i i.isLt
--   use a
--   simp [Nat.lt_add_right 1, h, Fin.coe_eq_castSucc, Fin.eta, Nat.cast_succ, Fin.coeSucc_eq_succ, implies_true]
-- ⟩

def prev : M.Path := if h : 0 < ∎|π| - 1 then ⟨List.dropLast π.states,
  by
    simp_all [tsub_pos_iff_lt, ne_eq]
    rw [←List.length_eq_zero, List.length_dropLast]
    omega,
  by
    simp_all
    intro i
    apply π.property ⟨i, _⟩
    have := i.isLt
    simp_all only [tsub_pos_iff_lt, List.length_dropLast, gt_iff_lt]
    omega
    ⟩ else π

theorem prev_states_eq_dropLast (h : 1 < ∎|π|) : π.prev.states = π.states.dropLast := by
  simp [prev, states]
  split_ifs
  · simp_all
  · simp_all

@[simp]
theorem prev_first_eq_first : π.prev.first = π.first := by
  simp only [first, prev, tsub_pos_iff_lt]
  split_ifs with h
  · simp_all only
    unfold List.dropLast
    simp only [List.head, ne_eq]
    split
    simp_all only [ne_eq, not_false_eq_true, heq_eq_eq]
    rename_i x _ h
    split at h
    · exact False.elim (x (id (Eq.symm h)))
    · exact False.elim (x (id (Eq.symm h)))
    · split
      simp_all only [List.length_cons, Nat.succ_eq_add_one, lt_add_iff_pos_left, List.length_pos,
        ne_eq, not_false_eq_true, false_implies, List.cons.injEq, heq_eq_eq]
  · rfl

theorem prev_last_eq_get : π.prev.last = π[∎|π| - 2] := by
  unfold prev
  simp only [last, tsub_pos_iff_lt, getElem_eq_states_getElem']
  split_ifs with h
  · simp only [List.getLast_eq_getElem, List.length_dropLast, List.get_eq_getElem,
    List.getElem_dropLast, Fin.getElem_fin]
    congr! 1
  · have : ∎|π| = 1 := by have := π.length_pos ; omega
    simp_all only [List.getLast_eq_getElem, le_refl, tsub_eq_zero_of_le, List.get_eq_getElem,
      Nat.one_le_ofNat, Fin.getElem_fin]

@[simp]
theorem prev_length_eq_pred : ∎|π.prev| = max 1 (∎|π| - 1) := by
  simp only [prev]
  split_ifs with h
  · simp only [tsub_pos_iff_lt, List.length_dropLast] at h ⊢
    omega
  · have := π.length_pos
    simp only [tsub_pos_iff_lt, not_lt] at h ⊢
    omega

def take (i : ℕ) : M.Path := ⟨π.states.take (i + 1),
  by
    simp_all only [ne_eq, List.take_eq_nil_iff, π.nonempty, add_eq_zero, one_ne_zero, and_false,
      or_self, not_false_eq_true],
  by
    intro j
    simp only [List.get_eq_getElem, List.getElem_take, Fin.val_succ]
    apply π.property ⟨j, _⟩
    have := j.isLt
    simp_all only [not_lt, List.length_take]
    omega⟩

theorem take_states (i : ℕ) :
  (π.take i).states = π.states.take (i + 1)
:= rfl

@[simp]
theorem Fin_PathFin_length_succ_le_length (i : Fin ∎|π|) : i.val + 1 ≤ ∎|π| := by
  have := i.isLt
  omega

@[simp]
theorem Fin_PathFin_length_succ_le_length' (i : Fin ∎|π|) : i.val + 1 ≤ π.states.length :=
  π.Fin_PathFin_length_succ_le_length i

@[simp]
theorem take_last_eq_get (i : Fin ∎|π|) : (π.take i).last = π[i] := by
  have := i.isLt
  simp only [last, take, Fin.getElem_fin, getElem_eq_states_getElem']
  simp only [List.getLast_eq_getElem, List.length_take, Fin_PathFin_length_succ_le_length',
    min_eq_left, add_tsub_cancel_right, List.getElem_take, getElem_eq_states_getElem']

@[simp]
theorem take_last_eq_get' (i : Fin (∎|π| - 1)) : (π.take i).last = π[i] := by
  rw [π.take_last_eq_get ⟨i, by omega⟩]
  simp

theorem states_last_eq_last : π.states.getLast π.nonempty = π.last := by
  simp only [last]

theorem take_states_last_eq_get (i : Fin ∎|π|) : (π.take i).states.getLast (π.take ↑i).nonempty = π[i] := by
  convert π.take_last_eq_get i

theorem take_states_last_eq_get' (i : ℕ) (hi : i < ∎|π|) : (π.take i).states.getLast (π.take i).nonempty = π[i] := by
  convert π.take_last_eq_get ⟨i, hi⟩

theorem take_eq_prev : π.take (∎|π| - 2) = π.prev := by
  simp only [take, prev, tsub_pos_iff_lt]
  split_ifs with h
  · simp_all only [mk.injEq]
    rw [List.dropLast_eq_take]
    congr
    omega
  · simp_all only [not_lt, ge_iff_le, tsub_eq_zero_of_le, zero_le, zero_add]
    congr
    apply List.take_of_length_le
    omega

@[simp]
theorem take_length_pred_eq : π.take (∎|π| - 1) = π := by
  simp only [take, length_pred_add, List.take_length]

@[simp]
theorem take_length_eq : π.take ∎|π| = π := by
  simp only [take]
  congr
  apply List.take_of_length_le
  simp only [le_add_iff_nonneg_right, zero_le]

@[simp]
theorem take_states_length (i : ℕ) : (π.take i).states.length = min (i + 1) π.states.length := by
  simp only [take, List.length_take]

@[simp]
theorem take_length (i : ℕ) : ∎|π.take i| = min (i + 1) ∎|π| := by
  simp only [take, List.length_take, Nat.min_def]

@[simp]
theorem take_first_eq_first (i : ℕ) : (π.take i).first = π.first := by
  simp only [first, take, List.take_head π.nonempty]

noncomputable def act (i : Fin (∎|π| - 1)) : Act := by
  let x := (π.property i)
  simp [succs_univ] at x
  exact x.choose
theorem act_spec (i : Fin (∎|π| - 1)) : π[i.succ] ∈ M.succs (π.act i) π[i] :=  by
  let x := (π.property i)
  simp [succs_univ] at x
  exact x.choose_spec.right

-- theorem act_spec (i : Fin (∎|π| - 1)) : 0 < M.P (π[i]) (π.act i) π[i.succ] := (π.property i).choose_spec

def extend (s : State) (h : s ∈ M.succs_univ π.last) : M.Path :=
  ⟨π.states ++ [s], by simp_all only [ne_eq, List.append_eq_nil, List.cons_ne_self, and_false, not_false_eq_true],
    by
      intro ⟨i, hi⟩
      simp only [List.length_append, List.length_cons, List.length_nil, zero_add,
        add_tsub_cancel_right, List.get_eq_getElem, Nat.succ_eq_add_one, Fin.succ_mk] at hi ⊢
      simp_all only [List.getElem_append]
      by_cases hi : i = ∎|π| - 1
      · simp only [↓reduceDIte, hi, length_pred_add, lt_self_iff_false, le_refl,
        tsub_eq_zero_of_le, List.getElem_cons_zero]
        convert h
        simp only [last]
        exact Eq.symm (List.getLast_eq_getElem π.states π.nonempty)
      · have : i + 1 < π.states.length := by
          apply Nat.lt_of_le_of_ne (by omega)
          omega
        simp_all only [List.getElem_singleton, dite_true]
        exact π.property ⟨i, by omega⟩
    ⟩

def extend' (s : M.succs_univ π.last) : M.Path := π.extend s.val s.prop

theorem extend'_eq_extend (s : State) (h : s ∈ M.succs_univ π.last) : π.extend' ⟨s, h⟩ = π.extend s h := rfl

theorem extend_inj' (π₁ π₂ : M.Path) (s₁ s₂ : State) (h₁ : s₁ ∈ M.succs_univ π₁.last) (h₂ : s₂ ∈ M.succs_univ π₂.last) (h : π₁.extend s₁ h₁ = π₂.extend s₂ h₂) : π₁ = π₂ ∧ s₁ = s₂ := by
  simp only [extend] at h
  simp_all only [mk.injEq]
  constructor
  · have : π₁.states = π₂.states := by exact List.append_inj_left' h rfl
    exact eq_states π₁ π₂ this
  · have : [s₁] = [s₂] := by exact List.append_inj_right' h rfl
    simp_all

theorem extend_inj (s₁ s₂ : State) (h₁ : s₁ ∈ M.succs_univ π.last) (h₂ : s₂ ∈ M.succs_univ π.last) (h : π.extend s₁ h₁ = π.extend s₂ h₂) : s₁ = s₂ := by
  simp only [extend] at h
  simp_all only [mk.injEq, List.append_cancel_left_eq, List.cons.injEq, and_true]

theorem extend'_inj : Function.Injective π.extend' := by
  intro ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ h
  simp only [Subtype.mk.injEq]
  apply π.extend_inj s₁ s₂ h₁ h₂
  exact h

theorem List.head_append_of_ne_nul {α : Type*} (l₁ : List α) {l₂ : List α} (h : l₁ ≠ []) : (l₁ ++ l₂).head (List.append_ne_nil_of_left_ne_nil h l₂) = l₁.head h := by
  induction l₁
  · absurd h ; rfl
  · simp_all only [ne_eq, List.cons_append, List.head_cons]

@[simp]
theorem extend_last (s : State) (h : s ∈ M.succs_univ π.last) : (π.extend s h).last = s := by
  simp [extend, last]

@[simp]
theorem extend_first_eq_first (s : State) (h : s ∈ M.succs_univ π.last) : (π.extend s h).first = π.first := by
  simp [first, extend, tsub_pos_iff_lt, List.head_append_of_ne_nul _ π.nonempty]

@[simp]
theorem extend_length (s : State) (h : s ∈ M.succs_univ π.last) : ∎|π.extend s h| = ∎|π| + 1 := by
  simp only [extend, List.length_append, List.length_singleton, add_tsub_cancel_right,
    length_pred_add]

theorem extend_get (s : State) (h : s ∈ M.succs_univ π.last) (i : ℕ) (hi : i < ∎|π.extend s h|) : (π.extend s h)[i] = if hi' : i = ∎|π.extend s h| - 1 then s else π[i]'(by simp at hi hi' ; omega) := by
  simp only [extend, getElem_eq_states_getElem', List.length_append, List.length_singleton,
    add_tsub_cancel_right]
  split_ifs with hf
  · simp_all only [getElem_eq_states_getElem', List.getElem_concat_length]
  · rw [List.getElem_append]
    simp_all
    split_ifs
    · rfl
    · simp at hi
      omega

theorem extend_take (s : State) (h : s ∈ M.succs_univ π.last) (i : ℕ) (hi : i < ∎|π|) : (π.extend s h).take i = π.take i := by
  simp only [take, extend, mk.injEq]
  apply List.take_append_of_le_length
  omega

@[simp]
theorem extend_take_length_pred (s : State) (h : s ∈ M.succs_univ π.last) : (π.extend s h).take (∎|π| - 1) = π := by
  simp only [take, length_pred_add, extend, List.take_left]

@[simp]
theorem extend_get_length_pred (s : State) (h : s ∈ M.succs_univ π.last) : (π.extend s h)[∎|π| - 1] = π.last := by
  simp only [extend, getElem_eq_states_getElem']
  rw [List.getElem_append, last_eq_states_get]
  simp [List.get_eq_getElem]

@[simp]
theorem extend_get_length (s : State) (h : s ∈ M.succs_univ π.last) : (π.extend s h)[∎|π|] = s := by
  simp only [extend, getElem_eq_states_getElem', List.getElem_concat_length]

@[simp]
theorem extend_get_states_length (s : State) (h : s ∈ M.succs_univ π.last) : (π.extend s h)[π.states.length]'(by simp only [extend_length] ; simp only [lt_add_iff_pos_right, zero_lt_one]) = s :=
  π.extend_get_length s h

theorem Fin.prod_rfl_iff_ty_eq {α : Type*} [CommMonoid α] (n m : ℕ) (h : n = m) (f : Fin m → α) : ∏ x : Fin n, f ⟨x, by omega⟩ = ∏ x : Fin m, f x := by
  apply Fin.prod_congr' _ h

@[simp]
theorem extend_states (s : State) (h : s ∈ M.succs_univ π.last) : (π.extend s h).states = π.states ++ [s] := by
  simp only [extend]

@[simp]
theorem extend_states_subset (s : State) (h : s ∈ M.succs_univ π.last) : π.states ⊆ (π.extend s h).states := by
  simp only [extend, List.subset_append_left]

@[simp]
theorem extend_states_mem (s : State) (h : s ∈ M.succs_univ π.last) (s' : State) (hs' : s' ∈ π.states) : s' ∈ (π.extend s h).states :=
  π.extend_states_subset s h hs'

theorem List.get_append' {α : Type u_1} {l₁ : List α} {l₂ : List α} (n : Nat) (h₁ : l₁.length ≤ n) (h₂ : n < l₁.length + l₂.length) :
  (l₁ ++ l₂).get ⟨n, by rw [List.length_append] ; exact h₂⟩ = l₂.get ⟨n - l₁.length, by omega⟩
:= by
  induction l₁ generalizing n with
  | nil => simp only [List.nil_append, List.length_nil, tsub_zero]
  | cons l₁ t₁ ih =>
    simp_all only [List.get_eq_get?, List.cons_append, List.length_cons, Nat.succ_eq_add_one]
    have : n ≠ 0 := Nat.not_eq_zero_of_lt h₁
    conv =>
      left ; congr ; arg 2 ; rw [←Nat.succ_pred this]
    simp only [Nat.pred_eq_sub_one, Nat.succ_eq_add_one, List.get?_cons_succ]
    have := ih (n - 1) (by simp_all only [List.length_cons, Nat.succ_eq_add_one, ne_eq] ; omega)
    rw [this]
    · congr! 1
      rw [Nat.sub_right_comm]
      rfl
    · simp only [List.length_cons, Nat.succ_eq_add_one] at h₁ h₂
      omega

theorem List.get_succ_eq_tail {α : Type*} (l : List α) (n : ℕ) (h : n + 1 < l.length) : l.get ⟨n + 1, by omega⟩ = l.tail.get ⟨n, by rw [List.length_tail] ; omega⟩ := by
  induction l with
  | nil => simp only [List.get_eq_get?, List.get?_nil, List.tail_nil]
  | cons => simp_all only [List.length_cons, Nat.succ_eq_add_one, List.get_cons_succ, List.tail_cons]

theorem List.get?_cons_pred {α : Type*} (l : List α) (x : α) (i : ℕ) (h₁ : 0 < i) : (x :: l).get? i = l.get? (i - 1) := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le' h₁
  simp_rw [hj]
  simp only [Nat.succ_eq_add_one, zero_add, List.get?_cons_succ, add_tsub_cancel_right]
theorem List.get_cons_pred {α : Type*} (l : List α) (x : α) (i : ℕ) (h₁ : 0 < i) (h₂ : i < (x :: l).length) : (x :: l).get ⟨i, by omega⟩ = l.get ⟨i - 1, by simp_all only [List.length_cons, Nat.succ_eq_add_one] ; apply Nat.sub_lt_right_of_lt_add <;> omega⟩ := by
  simp_rw [List.get_eq_get?]
  have := List.get?_cons_pred l x i h₁
  simp_all only [List.get?_eq_getElem?]

def prepend (s : State) (hs : π.first ∈ M.succs_univ s) : M.Path := ⟨s :: π.states, List.cons_ne_nil _ _, by
  intro i
  by_cases hi : i.val = 0
  · simp only [List.length_cons, Nat.add_one_sub_one, hi, Fin.zero_eta, List.get_eq_getElem,
    Fin.val_zero, List.getElem_cons_zero, Nat.succ_eq_add_one, Fin.val_succ, zero_add,
    List.getElem_cons_succ]
    convert hs
    exact π.first_eq_states_getElem_zero.symm
  · simp only [List.length_cons, Nat.add_one_sub_one, List.get_eq_getElem, List.getElem_cons, hi,
    ↓reduceDIte, Nat.succ_eq_add_one, Fin.val_succ, List.getElem_cons_succ]
    convert π.property ⟨i - 1, Nat.pred_lt_pred hi i.isLt⟩
    simp only [AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, ↓reduceDIte,
      Nat.succ_eq_add_one, List.length_cons, Nat.add_one_sub_one, Fin.succ_mk, List.get_eq_getElem]
    congr
    omega⟩

theorem preprend_injective (π₁ π₂ : M.Path) (s : State) {hs₁ : π₁.first ∈ M.succs_univ s} {hs₂ : π₂.first ∈ M.succs_univ s} (h : π₁.prepend s hs₁ = π₂.prepend s hs₂) : π₁ = π₂ := by
  simp only [prepend, mk.injEq, List.cons.injEq, true_and] at h
  apply eq_states _ _ h

@[simp]
theorem prepend_first (s : State) {hs : π.first ∈ M.succs_univ s} : (π.prepend s hs).first = s := by
  simp only [first, prepend, List.head_cons]

@[simp]
theorem prepend_last (s : State) {hs : π.first ∈ M.succs_univ s} : (π.prepend s hs).last = π.last := by
  simp only [last, prepend, List.getLast_cons π.nonempty]

@[simp]
theorem prepend_length (s : State) (hs : π.first ∈ M.succs_univ s) : ∎|π.prepend s hs| = ∎|π| + 1 := by
  simp only [prepend, List.length_cons, Nat.succ_eq_add_one, add_tsub_cancel_right,
    length_pred_add]

@[simp]
theorem prepend_states_second (s : State) {hs : π.first ∈ M.succs_univ s} : ((π.prepend s hs).states[1]'(by simp)) = π.first := by
  simp only [prepend, List.getElem_cons_succ, first, List.head_eq_get, List.get_eq_getElem]

@[simp]
theorem prepend_second (s : State) {hs : π.first ∈ M.succs_univ s} : ((π.prepend s hs)[1]'(by simp)) = π.first := by
  simp only [getElem_eq_states_getElem', prepend_states_second]

@[simp]
theorem prepend_states_length (s : State) (hs : π.first ∈ M.succs_univ s) : (π.prepend s hs).states.length = π.states.length + 1 := by
  simp only [prepend, List.length_cons]

@[simp]
theorem prepend_get_zero (s : State) (hs : π.first ∈ M.succs_univ s) : (π.prepend s hs)[0] = s := by
  simp [prepend]

@[simp]
theorem prepend_get_one (s : State) (hs : π.first ∈ M.succs_univ s) : (π.prepend s hs)[1] = π.first := by
  simp [prepend, first, List.getElem_zero]

@[simp]
theorem prepend_get_succ' (s : State) (hs : π.first ∈ M.succs_univ s) (i : Fin ∎|π|) : (π.prepend s hs)[(⟨i + 1, by
  simp only [prepend_length, add_lt_add_iff_right, Fin.is_lt]
⟩ : Fin ∎|π.prepend s hs|)] = π[i] := by
  simp [prepend]

theorem prepend_get (s : State) (hs : π.first ∈ M.succs_univ s) (i : Fin ∎|π.prepend s hs|) : (π.prepend s hs)[i] = if h : i = ⟨0, by
  simp only [prepend_length, length_pred_add]
  omega⟩ then s else π[i.val - 1]'(by
    have := i.isLt
    simp [prepend_length, length_pred_add, gt_iff_lt] at this ⊢
    have := Nat.zero_lt_of_ne_zero <| Fin.ext_iff.not.mp h
    omega) := by
  simp [ prepend, List.length_cons, Nat.succ_eq_add_one, dite_eq_ite]
  split_ifs with h
  · simp_all
  · rcases i with ⟨i, hi⟩
    simp_all only
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero <| Fin.ext_iff.not.mp h
    simp only [Nat.succ_eq_add_one] at hj
    simp only [instGetElem, hj, add_tsub_cancel_right]
    simp only [getElem]
    simp only [List.length_cons, List.get_eq_getElem, List.getElem_cons_succ]

theorem prepend_get_nat (s : State) (hs : π.first ∈ M.succs_univ s) (i : ℕ) (hi : i < ∎|π.prepend s hs|) : (π.prepend s hs)[i] = if i = 0 then s else π[i - 1]'(by have := π.length_pos ; simp only [prepend_length, gt_iff_lt] at hi ⊢ ; omega) := by
  simp only [getElem, get, prepend, List.length_cons, Nat.succ_eq_add_one]
  split_ifs with h
  · simp_all only [Fin.zero_eta, List.get_cons_zero]
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero h
    simp_all only [Nat.succ_eq_add_one, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
      not_false_eq_true, List.get_eq_getElem, List.getElem_cons_succ]
    simp [List.get_eq_getElem, add_tsub_cancel_right]

theorem prepend_take_last (s : State) (hs : π.first ∈ M.succs_univ s) (i : ℕ) (hi : i < ∎|π.prepend s hs| - 1) : ((π.prepend s hs).take (i + 1)).states.getLast ((π.prepend s hs).take (i + 1)).nonempty = (π.take i).states.getLast (π.take i).nonempty := by
  simp only [prepend_length, length_pred_add] at hi
  have hi' : i % π.states.length = i := Nat.mod_eq_of_lt hi
  rw [(π.prepend s hs).take_states_last_eq_get ⟨i + 1, by simp ; omega⟩]
  rw [π.take_states_last_eq_get ⟨i, by exact hi⟩]
  simp only [Fin.getElem_fin]
  rw [Path.prepend_get_nat]
  simp only [add_eq_zero, one_ne_zero, and_false, ↓reduceIte, getElem]
  simp only [add_tsub_cancel_right, List.get_eq_getElem]

theorem prepend_take_zero (s : State) (hs : π.first ∈ M.succs_univ s) : (π.prepend s hs).take 0 = Path.mk_single M s := by
  simp only [take, zero_add, prepend, List.take_succ_cons, List.take_zero]

theorem eq_extend_prev (s : State) (h : s ∈ M.succs_univ π.last) : (π.extend s h).prev = π := by
  unfold prev extend
  simp_all only [List.length_append, List.length_singleton, add_tsub_cancel_right,
    List.length_pos, ne_eq, π.nonempty, not_false_eq_true, List.dropLast_concat, dite_true]

def last_transition (h : 1 < ∎|π|) : Fin (∎|π| - 1) := ⟨∎|π| - 2, by omega⟩

def eq_prev_extend (h : 1 < ∎|π|) : π = π.prev.extend π.last (by
  rw [prev_last_eq_get, last_eq_get]
  convert π.property ⟨∎|π| - 2, by omega⟩
  congr
  simp only [Fin.succ_mk, Nat.succ_eq_add_one, Nat.pred_eq_succ_iff]
  omega
) := by
  have : 1 < ∎|π| := by simp_all only [tsub_pos_iff_lt]
  simp only [extend, prev, tsub_pos_iff_lt, this, ↓reduceDIte, last, List.dropLast_append_getLast]

@[deprecated extend]
def append (s : State) (hs : s ∈ M.succs_univ π.last) : M.Path := ⟨π.states ++ [s], by simp, by
  simp
  intro ⟨i, hi⟩
  simp at hi
  simp_all
  by_cases h : i + 1 = ∎|π|
  · simp_all
    rw [List.getElem_append_left]
    · simp_all [last, List.getLast_eq_getElem]
      convert hs
      omega
    · omega
  · rw [List.getElem_append_left, List.getElem_append_left]
    · have := π.property ⟨i, by omega⟩
      simp_all
    · omega
    · omega⟩

def join (h : π.last = π'.first) : M.Path :=
  ⟨π.states ++ π'.states.tail, by simp [π.nonempty], by
    simp_all only [List.get_eq_getElem, Fin.val_succ]
    intro ⟨i, hi⟩
    simp only [List.length_append, List.length_tail] at hi
    simp_all only
    by_cases h_split : i + 1 < ∎|π|
    · rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega)]
      exact π.property ⟨i, by omega⟩
    · have tail₁ := List.tail_getElem π'.states ⟨i - ∎|π|, by omega⟩
      have tail₂ := List.tail_getElem π'.states ⟨(i + 1) - ∎|π|, by simp_all ; omega⟩
      simp at tail₁ tail₂
      have : (π.states ++ π'.states.tail)[i] = (π'.states)[(i + 1) - ∎|π|] := by
        by_cases hi' : i = ∎|π| - 1
        · simp [hi'] at *
          have : (π.states ++ π'.states.tail)[∎|π| - 1] = π'.states[0] := by
            rw [List.getElem_append_left (by simp)]
            simp [first, last, List.head_eq_get, List.getLast_eq_getElem] at h
            exact h
          rw [this]
        · rw [List.getElem_append_right]
          · simp [tail₁]
            congr
            omega
          · omega
      simp [this]
      rw [List.getElem_append_right]
      · simp [tail₂]
        exact π'.property ⟨(i + 1) - ∎|π|, by omega⟩
      · omega
  ⟩

@[simp]
theorem join_first (h : π.last = π'.first) : (π.join π' h).first = π.first := by
  simp [join, first, List.head_eq_get, List.getElem_append]

@[simp]
theorem join_last (h : π.last = π'.first) : (π.join π' h).last = π'.last := by
  simp [join, last, List.getLast_eq_getElem]
  by_cases h' : ∎|π'| = 1
  · simp_all
    rw [List.getElem_append_left]
    simp [first, last, List.head_eq_get, List.getLast_eq_getElem] at h
    exact h
  · have : ∎|π| + (∎|π'| - 1) - 1 - ∎|π| = ∎|π'| - 2 := by
      have := π'.length_pos
      have := π.length_pos
      omega
    have := π'.length_pos
    rw [List.getElem_append_right]
    · simp_all
      congr
      omega
    · omega

@[simp]
theorem join_length (h : π.last = π'.first) : ∎|π.join π' h| = ∎|π| + ∎|π'| - 1 := by
  simp [join]
  have := π'.length_pos
  omega

theorem join_states_helper (h : π.last = π'.first) : (π.join π' h).states = π.states.dropLast ++ [π.last] ++ π'.states.tail := by
  simp only [join, last, List.dropLast_append_getLast]

theorem join_states (h : π.last = π'.first) : (π.join π' h).states = π.states.dropLast ++ π'.states := by
  rw [join_states_helper]
  simp [h, first]

def tail : M.Path := if h : 1 < ∎|π| then ⟨π.states.tail, by
    simp_all only [ne_eq]
    rw [←List.length_eq_zero, π.states.length_tail]
    omega,
  by
    intro i
    have iLt := i.isLt
    simp_all only [π.states.length_tail, Nat.succ_eq_add_one, Fin.val_succ]
    rw [←List.get_succ_eq_tail, ←List.get_succ_eq_tail]
    · apply π.property ⟨i + 1, by omega⟩
    · omega
    · omega⟩ else π

@[simp]
theorem tail_first_eq_get_one (h : 1 < ∎|π|) : π.tail.first = π[1] := by
  simp only [first, tail, h, ↓reduceDIte, List.head_eq_get, List.get_eq_getElem,
    getElem_eq_states_getElem']
  conv => left ; simp only [getElem]
  rw [@List.get_tail _ π.states 0 (by simp_all)]
  rfl

@[simp]
theorem tail_length : ∎|π.tail| = max 1 (∎|π| - 1) := by
  simp only [tail, tsub_pos_iff_lt, Nat.max_def]
  split_ifs with h
  · simp_all only [List.length_tail]
  · simp_all only [not_le, Nat.lt_one_iff, List.length_tail, zero_ne_one]
    omega
  · simp_all only [not_lt, tsub_eq_zero_of_le, nonpos_iff_eq_zero, one_ne_zero]
  · simp_all only [not_lt, tsub_eq_zero_of_le, nonpos_iff_eq_zero, one_ne_zero, not_false_eq_true]
    have := π.length_ne_zero
    omega

@[simp]
theorem tail_last : π.tail.last = π.last := by
  simp only [last, tail]
  split_ifs
  · simp [List.tail_getLast]
  · simp

theorem tail_get_nat (i : ℕ) (h : i < ∎|π| - 1) : π.tail[i]'(by simp ; omega) = π[i + 1]'(by omega) := by
  simp only [tail, getElem_eq_states_getElem']
  split_ifs with h'
  · simp only [← List.tail_getElem (L := π.states) (i := ⟨i, by simp_all⟩), Fin.getElem_fin]
  · omega

theorem prepend_tail (h : 1 < ∎|π|) : π.tail.prepend π.first (by
  rw [π.tail_first_eq_get_one h]
  simp only [first, List.head_eq_get, List.get_eq_getElem, get, Fin.getElem_fin]
  exact π.property ⟨0, by omega⟩) = π := by
  simp_all only [first, prepend, tail, dite_true, List.head_cons_tail]

@[simp]
theorem tail_prepend (h : π.first ∈ M.succs_univ s) : (π.prepend s h).tail = π := by
  simp [tail]
  congr

theorem tail_states_of_nonempty {M : MDP State Act} (π : M.Path) (h : 1 < ∎|π|) : π.tail.states = π.states.tail := by
  simp [tail, h]

theorem tail_get_of_nonempty {M : MDP State Act} (π : M.Path) (h : 1 < ∎|π|) (i : ℕ) (hi : i < ∎|π| - 1) : π.tail[i]'(by simp ; omega) = π.states.get ⟨i + 1, by omega⟩ := by
  simp [tail, h, get, h]


theorem tail_getElem_of_nonempty {M : MDP State Act} (π : M.Path) (h : 1 < ∎|π|) (i : ℕ) (hi : i < ∎|π| - 1) : (π.tail[i]'(by simp ; omega)) = π.states[i + 1]'(by omega) := by
  simp [tail, h, get, h]

def drop (i : Fin ∎|π|) : M.Path := ⟨π.states.drop i, by simp, by
  simp only [List.get_eq_getElem, List.getElem_drop, Nat.succ_eq_add_one, Fin.val_succ]
  intro ⟨i', hi'⟩
  simp only [List.length_drop] at hi'
  have ⟨a, ha⟩ := π.property ⟨i + i', by omega⟩
  use a
  simp only [id_eq, Int.Nat.cast_ofNat_Int, Int.reduceNeg, eq_mpr_eq_cast, Set.mem_range]
  convert ha⟩

def infixes := List.join <| List.ofFn fun (start : Fin ∎|π|) ↦ (List.ofFn fun (e : Fin (∎|π| - start)) ↦ π.drop ⟨start, by omega⟩ |>.take e)

theorem List.take_drop_IsInfix {α : Type*} (l : List α) (n m : ℕ) : (l.take n).drop m <:+: l := by
  simp [List.IsInfix]
  have a := List.take_append_drop m (l.take n)
  have b := List.take_append_drop n l
  rw [←a] at b
  use List.take m (List.take n l)
  use List.drop n l
  conv => right ; rw [←b]
  rw [List.append_assoc]

theorem List.drop_take_IsInfix {α : Type*} (l : List α) (n m : ℕ) : (l.drop n).take m <:+: l := by
  simp [List.IsInfix]
  have a := List.take_append_drop m (l.drop n)
  have b := List.take_append_drop n l
  rw [←a] at b
  use List.take n l
  use List.drop m (List.drop n l)

theorem infixes_IsInfix (h : π' ∈ π.infixes) : List.IsInfix π'.states π.states := by
  simp [infixes, drop, take, List.mem_ofFn] at h
  obtain ⟨s, e, h⟩ := h
  rw [←h]
  simp [List.drop_take_IsInfix]

theorem infixes_univ (h : π'.states <:+: π.states) : π' ∈ π.infixes := by
  simp [List.IsInfix] at h
  obtain ⟨s, t, h⟩ := h
  simp [infixes, drop, take, List.mem_ofFn]
  use ⟨s.length, by rw [←h] ; simp⟩
  use ⟨∎|π'| - 1, by simp [←h, π'.length_pos] ; have := π'.length_pos ; omega⟩
  apply eq_states
  simp
  rw [←h]
  simp

theorem infixes_iff : π' ∈ π.infixes ↔ π'.states <:+: π.states :=
  ⟨π.infixes_IsInfix π', π.infixes_univ π'⟩

@[simp]
theorem infixes_mem_self : π ∈ π.infixes := by simp [infixes_iff]

theorem infixes_subset_iff : π.infixes ⊆ π'.infixes ↔ π ∈ π'.infixes := by
  simp [infixes_iff]
  constructor
  · intro h
    have : π ∈ π.infixes := by simp
    have := h this
    simp_all [infixes_iff]
  · intro h
    intro π''
    simp [infixes_iff]
    intro h'
    exact List.IsInfix.trans h' h

theorem join_infixes_left (h : π.last = π'.first) : π.infixes ⊆ (π.join π' h).infixes := by
  simp [infixes_subset_iff]
  simp [infixes_iff]
  simp [join]
  simp [List.IsInfix]
  use [], π'.states.tail
  simp

theorem join_infixes_right (h : π.last = π'.first) : π'.infixes ⊆ (π.join π' h).infixes := by
  simp only [infixes_subset_iff, infixes_iff, List.IsInfix, List.append_assoc, join_states]
  use π.states.dropLast, []
  simp only [List.append_nil]

theorem take_infixes : (π.take n).infixes ⊆ π.infixes := by
  simp only [take, infixes_subset_iff, infixes_iff, List.IsInfix, List.append_assoc]
  use [], π.states.drop (n + 1)
  simp only [List.take_append_drop, List.nil_append]

@[simp]
theorem take_mem_infixes : π.take n ∈ π.infixes := by
  simp only [take, infixes_subset_iff, infixes_iff, List.IsInfix, List.append_assoc]
  use [], π.states.drop (n + 1)
  simp only [List.take_append_drop, List.nil_append]

@[simp]
theorem prepend_not_mem_infixes (h : π.first ∈ M.succs_univ s) : π.prepend s h ∉ π.infixes := by
  simp only [prepend, infixes_iff, List.IsInfix, List.append_assoc, List.cons_append, not_exists]
  intro _ _ a
  have := congrArg List.length a
  simp at this
  omega

@[simp]
theorem prepend_mem_infixes (s : State) (h : π.first ∈ M.succs_univ s) : π ∈ (π.prepend s h).infixes := by
  simp only [prepend, infixes_iff, List.IsInfix, List.append_assoc]
  use [s], []
  simp

def prefixes_list : List M.Path := List.ofFn (fun (i : Fin ∎|π|) ↦ π.take i)
def prefixes : Finset M.Path := π.prefixes_list.toFinset

theorem prefixes_list_Nodup : π.prefixes_list.Nodup := by
  simp [prefixes_list]
  refine List.nodup_ofFn_ofInjective ?hf
  intro a b c
  simp_all [take]
  omega

theorem prefixes_toList_mem_iff : π' ∈ π.prefixes.toList ↔ π' ∈ π.prefixes_list := by
  simp [prefixes, prefixes_list]
theorem prefixes_mem_iff : π' ∈ π.prefixes ↔ π' ∈ π.prefixes_list := by
  simp [prefixes, prefixes_list]

def isPrefixOf := π.states.isPrefixOf π'.states

theorem prefixes_are_isPrefixOf : ∀ π' ∈ π.prefixes, π'.isPrefixOf π := by
  simp only [prefixes_mem_iff, prefixes_list, take, isPrefixOf, List.isPrefixOf_iff_prefix,
    List.forall_mem_ofFn_iff]
  intros
  apply List.take_prefix

theorem isPrefixOf_mem_prefixes (h : π'.isPrefixOf π) : π' ∈ π.prefixes := by
  simp_all only [isPrefixOf, List.isPrefixOf_iff_prefix, prefixes_mem_iff, prefixes_list, take]
  apply (List.mem_ofFn _ _).mpr
  simp only [Set.mem_range]
  use ⟨∎|π'| - 1, by have := List.IsPrefix.length_le h ; have := π'.length_pos ; omega⟩
  simp only [length_pred_add]
  apply eq_states
  conv => right ; rw [List.prefix_iff_eq_take.mp h]

theorem prefixes_iff_isPrefixOf : π' ∈ π.prefixes ↔ π'.isPrefixOf π :=
  ⟨π.prefixes_are_isPrefixOf π', π.isPrefixOf_mem_prefixes π'⟩

theorem prefixes_length_le : ∀ π' ∈ π.prefixes, ∎|π'| ≤ ∎|π| := by
  simp [prefixes_mem_iff, prefixes_list, take, isPrefixOf]

theorem prefixes_first : ∀ π' ∈ π.prefixes, π'.first = π.first := by
  simp [prefixes_mem_iff, prefixes_list, take, first, List.head_eq_get]

end Path
