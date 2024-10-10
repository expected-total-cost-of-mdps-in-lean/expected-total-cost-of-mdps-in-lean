import MDP.Basic
import MDP.Paths

-- TODO: remove this
set_option linter.unusedSectionVars false

def DisjointOn {α β : Type*} [DecidableEq β] (f : α → Finset β) := ∀ a b, a ≠ b → Disjoint (f a) (f b)

namespace MDP

variable {State : Type*} {Act : Type*}
variable [DecidableEq State] [DecidableEq Act]
variable [ActNonempty : Nonempty Act]
variable (M : MDP State Act)

theorem succs_univ_if_succs (h : s' ∈ M.succs α s) : s' ∈ M.succs_univ s := by
  simp [succs_univ]
  use α
  constructor
  · simp [succs] at h
    refine (P_nonempty_iff_act M s α).mp ?h.left.a
    use s'
    simp [h]
  · exact h

namespace Path

variable {M : MDP State Act}
variable (π : M.Path)

theorem succs_univ₀_get_1 [M.FiniteBranching] (π : M.Path) (h : 1 < ∎|π|) : π[1] ∈ M.succs_univ₀ π.first := by
  simp only [succs_univ₀, Finset.mem_biUnion]
  obtain ⟨α, hα⟩ := π.property_first h
  use α
  constructor
  · apply (M.P_nonempty_iff_act₀ π.first α).mp
    use π[1]
    simp only [Finsupp.mem_support_iff, ne_eq]
    exact pos_iff_ne_zero.mp hα
  · simp only [succs, Finsupp.mem_support_iff, ne_eq]
    exact pos_iff_ne_zero.mp hα

def succs (α : Act) (π : M.Path) : Finset M.Path :=
  (M.succs α π.last).attach.map
    ⟨fun s' ↦ π.extend s'.val (M.succs_univ_if_succs s'.prop), fun s₁ s₂ ↦ Subtype.eq ∘ π.extend_inj s₁ s₂ _ _⟩

theorem succs_first_eq_first (α : Act) (π : M.Path) : ∀ π' ∈ π.succs α, π.first = π'.first := by
  intro π' h
  simp [Path.succs] at h
  obtain ⟨s', _, h⟩ := h
  rw [←h]
  simp only [Path.extend_first_eq_first]

theorem succs_non_zero (a : Act) (π : M.Path) : ∀π' ∈ π.succs a, 0 < ∎|π'| := by
  intro π' h
  simp only [Path.succs, Path.extend, Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists,
    Finset.mem_val, Finsupp.mem_support_iff, ne_eq] at h
  obtain ⟨s', _, _, h⟩ := h
  rw [←h]
  simp only [List.length_append, List.length_singleton, add_tsub_cancel_right,
    List.length_pos, ne_eq]
  omega

theorem succs_length_eq_succ (a : Act) (π : M.Path) : ∀π' ∈ π.succs a, ∎|π'| = ∎|π|.succ := by
  intro π' h
  simp only [Path.succs, Path.extend, Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists,
    Finset.mem_val, Finsupp.mem_support_iff, ne_eq] at h
  obtain ⟨_, _, _, h₂⟩ := h
  rw [←h₂]
  simp only [List.length_append, List.length_singleton, add_tsub_cancel_right,
    Nat.succ_eq_add_one, Path.length_pred_add]

theorem succs_is_prev (a : Act) (π : M.Path) : ∀π' ∈ π.succs a, π'.prev = π := by
  intro π' h
  simp_all only [succs, extend, Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk, true_and, Subtype.exists]
  obtain ⟨s', s'_in_support, h₂⟩ := h
  rw [←h₂]
  simp [prev]

instance instDecidableEq : DecidableEq M.Path := decEq

noncomputable def succs_univ (π : M.Path) : Set M.Path := Set.iUnion (π.succs ·)
def succs_univ₀ [M.FiniteBranching] (π : M.Path) : Finset M.Path := Finset.biUnion (M.act₀ π.last) π.succs

theorem succs_univ_eq_succs_univ₀
  {M : MDP State Act}
  [M.FiniteBranching]
  (π : M.Path)
: π.succs_univ = π.succs_univ₀ := by
  simp only [succs_univ, succs_univ₀, Finset.coe_biUnion, Finset.mem_coe]
  ext π'
  constructor <;> intro h
  · simp_all only [Set.mem_iUnion, Finset.mem_coe, exists_prop]
    obtain ⟨α, h⟩ := h
    use α
    simp_all only [Path.succs, Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists,
      Finset.mem_val, Finsupp.mem_support_iff, ne_eq, and_true]
    obtain ⟨s, h₁, _⟩ := h
    simp_all only [Finset.mem_attach, true_and, act₀_mem_iff_act_mem, MDP.act, Set.mem_setOf_eq]
    symm
    simp only [MDP.succs, Finsupp.mem_support_iff, ne_eq] at h₁
    apply P_ne_zero_sum_eq_one h₁
  · simp_all only [Set.mem_iUnion, Finset.mem_coe, exists_prop]
    obtain ⟨α, h⟩ := h
    use α
    simp_all only

theorem succs_univ₀_nonempty  [M.FiniteBranching] (π : M.Path) : π.succs_univ₀.Nonempty := by
  have ⟨α, hα⟩ := M.act₀_nonempty π.last
  simp [succs_univ₀]
  use α, hα
  have := M.act₀_prop π.last α hα
  simp [succs]
  exact P_pos_iff_sum_eq_one.mpr this

theorem succs_univ₀_inj [inst : M.FiniteBranching] : Function.Injective (@succs_univ₀ _ _ _ _ _ M inst) := by
  intro π₁ π₂ h
  have h₁ : ∀ π ∈ π₁.succs_univ₀, π.prev = π₁ := by
    intro π hπ
    simp [succs_univ₀] at hπ
    obtain ⟨α, _, hα⟩ := hπ
    exact π₁.succs_is_prev α π hα
  have h₂ : ∀ π ∈ π₂.succs_univ₀, π.prev = π₂ := by
    intro π hπ
    simp [succs_univ₀] at hπ
    obtain ⟨α, _, hα⟩ := hπ
    exact π₂.succs_is_prev α π hα
  have h' : π₁.succs_univ₀.Nonempty := π₁.succs_univ₀_nonempty
  obtain ⟨π, hπ⟩ := h'
  have := h₁ π hπ
  have := h₂ π (by simp_all only)
  simp_all only

@[deprecated succs_univ_eq_succs_univ₀]
theorem succs_univ_iff_succs_univ₀ [M.FiniteBranching] (π : M.Path) : π.succs_univ = π.succs_univ₀ := by
  rw [succs_univ_eq_succs_univ₀]

theorem last_in_succs_univ₀_prev_last [M.FiniteBranching] (π : M.Path) (h : 1 < ∎|π|) : π.last ∈ M.succs_univ₀ π.prev.last := by
  have := π.property ⟨∎|π| - 2, by omega⟩
  simp at this
  convert this
  · simp [prev_last_eq_get]
  · simp [last_eq_get]
    congr
    omega

theorem succs_univ_length_eq_succ (π : M.Path) : ∀π' ∈ π.succs_univ, ∎|π'| = ∎|π|.succ := by
  intro π' h
  simp_all only [succs_univ, Set.mem_iUnion, Finset.mem_coe, Nat.succ_eq_add_one]
  obtain ⟨α, hα⟩ := h
  exact π.succs_length_eq_succ α π' hα

theorem succs_univ_is_prev (π : M.Path) : ∀π' ∈ π.succs_univ, π'.prev = π := by
  intro π' h
  simp_all [succs_univ]
  obtain ⟨a, p⟩ := h
  exact π.succs_is_prev a π' p

theorem succs_univ₀_is_prev [M.FiniteBranching] (π : M.Path) : ∀π' ∈ π.succs_univ₀, π'.prev = π := by
  intro π' h
  simp_all [succs_univ₀]
  obtain ⟨a, p⟩ := h
  exact π.succs_is_prev a π' p.right

theorem succs_univ₀_length_eq_succ [M.FiniteBranching] (π : M.Path) : ∀π' ∈ π.succs_univ₀, ∎|π'| = ∎|π|.succ := by
  intro π' h
  simp_all only [succs_univ₀, Finset.mem_biUnion, Nat.succ_eq_add_one, length_pred_add]
  obtain ⟨α, hα⟩ := h
  exact π.succs_length_eq_succ α π' hα.right

theorem succs_univ₀_frist_eq_first [M.FiniteBranching] (π : M.Path) : ∀π' ∈ π.succs_univ₀, π'.first = π.first := by
  intro π' hπ'
  simp only [succs_univ₀, Finset.mem_biUnion] at hπ'
  obtain ⟨α, _, h₂⟩ := hπ'
  exact π.succs_first_eq_first α π' h₂ |> symm

theorem extend_mem_succs_univ₀ [M.FiniteBranching] (π : M.Path) (s : State) (h : s ∈ M.succs_univ π.last) : π.extend s h ∈ π.succs_univ₀ := by
  simp only [MDP.succs_univ_eq_succs_univ₀, MDP.succs_univ₀, Finset.coe_biUnion, Finset.mem_coe,
    Set.mem_iUnion, exists_prop', nonempty_prop] at h
  simp only [succs_univ₀, Finset.mem_biUnion]
  obtain ⟨α, hα₁, hα₂⟩ := h
  use α, hα₁
  simp only [succs, Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk, true_and,
    Subtype.exists]
  use s, hα₂

theorem succs_contained_in_prev (π : M.Path) (h : 1 < ∎|π|) : π ∈ π.prev.succs (π.act (π.last_transition h)) := by
  unfold succs
  simp only [Finset.mem_map]
  simp_all only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, Finset.mem_val,
    Finsupp.mem_support_iff, ne_eq]
  use π.last
  apply Exists.intro ?h.w ?h.h
  · rw [prev_last_eq_get, last_eq_get]
    convert (π.act_spec ⟨∎|π| - 2, by omega⟩)
    congr
    simp only [Nat.succ_eq_add_one, Fin.succ_mk, Nat.pred_eq_succ_iff]
    omega
  · rw [←eq_prev_extend _ h]
    simp only [Finset.mem_attach, and_self]

theorem succs_univ₀_DisjointOn [inst : M.FiniteBranching] : DisjointOn (@succs_univ₀ _ _ _ _ _ M inst) := by
  intro π₁ π₂ h
  intro S hS₁ hS₂ π h'
  simp_all only [ne_eq, Finset.le_eq_subset, Finset.bot_eq_empty, Finset.not_mem_empty]
  have h₁ : π ∈ π₁.succs_univ₀ := hS₁ h'
  have h₂ : π ∈ π₂.succs_univ₀ := hS₂ h'
  have : π₁.succs_univ₀ = π₂.succs_univ₀ → π₁ = π₂ := fun h ↦ succs_univ₀_inj h
  rw [←π₁.succs_univ₀_is_prev π h₁, ←π₂.succs_univ₀_is_prev π h₂] at h
  exact h rfl

theorem tail_first_mem_succs_univ₀ {M : MDP State Act} [M.FiniteBranching] (π : M.Path) (h : 1 < ∎|π|) : π.tail.first ∈ M.succs_univ₀ π.first := by
  simp_all only [tail_first_eq_get_one]
  exact π.succs_univ₀_get_1 (of_eq_true (eq_true h))

noncomputable def extend_arb [M.FiniteBranching] : M.Path := π.succs_univ₀.toList.head (by simp ; exact Finset.nonempty_iff_ne_empty.mp π.succs_univ₀_nonempty)
noncomputable def extend_arb_n [M.FiniteBranching] (π : M.Path) : ℕ → M.Path
  | 0 => π
  | n+1 => π.extend_arb.extend_arb_n n

@[simp]
theorem extend_arb_length [M.FiniteBranching] : ∎|π.extend_arb| = ∎|π| + 1 := by
  simp [extend_arb, List.head_eq_get]
  apply succs_univ₀_length_eq_succ
  rw [←Finset.mem_toList]
  apply List.getElem_mem

@[simp]
theorem extend_arb_first [M.FiniteBranching] : π.extend_arb.first = π.first := by
  simp [extend_arb, List.head_eq_get]
  apply succs_univ₀_frist_eq_first
  rw [←Finset.mem_toList]
  apply List.getElem_mem

@[simp]
theorem extend_arb_n_length [M.FiniteBranching] (n : ℕ) : ∎|π.extend_arb_n n| = ∎|π| + n := by
  induction n generalizing π with
  | zero => simp [extend_arb_n]
  | succ n ih =>
    simp_all [extend_arb_n]
    omega

@[simp]
theorem extend_arb_n_first [M.FiniteBranching] (n : ℕ) : (π.extend_arb_n n).first = π.first := by
  induction n generalizing π with
  | zero => simp [extend_arb_n]
  | succ n ih => simp_all [extend_arb_n]

noncomputable def set_length [M.FiniteBranching] (π : M.Path) (n : ℕ) (h : 0 < n) : M.Path :=
  if ∎|π| < n then
    -- we extend it arbitrarily
    π.extend_arb_n (n - ∎|π|)
  else
    π.take (n - 1)

@[simp]
theorem set_length_length [M.FiniteBranching] (n : ℕ) (h : 0 < n) : ∎|π.set_length n h| = n := by
  simp [set_length]
  split_ifs
  · simp
    omega
  · simp
    omega

@[simp]
theorem set_length_first [M.FiniteBranching] (n : ℕ) (h : 0 < n) : (π.set_length n h).first = π.first := by
  simp [set_length]
  split_ifs
  · simp
  · simp

end Path

end MDP

namespace MDP

variable {State : Type*} {Act : Type*}
variable [DecidableEq State] [DecidableEq Act]
variable [ActNonempty : Nonempty Act]
variable (succs : State → Act → Finset (State × PReal))
variable (M : MDP State Act)
variable {h_succs₁ : ∀ (s : State) (a : Act), is₀₁ (succs s a |>.sum (·.2.val))}
variable {h_succs₂ : ∀ (s : State), ∃ (a : Act) (s' : State) (p : PReal), (s', p) ∈ succs s a}

theorem succs_eq_succs (hM : M = mk_from_succs succs h_succs₁ h_succs₂) (s : State) (α : Act) :
  M.succs α s = (succs s α).image (·.1)
:= by
  ext s'
  simp [hM, mk_from_succs, MDP.succs]
  constructor <;> intro h
  · obtain ⟨s'', p, ⟨hp, hp'⟩, _⟩ := h
    use p, hp
    simp_all
  · obtain ⟨p, hp, h⟩ := h
    use s', p
    simp_all [pos_iff_ne_zero.mp hp.left]

theorem succs_mem_iff_P_pos (hM : M = mk_from_succs succs h_succs₁ h_succs₂) (s s' : State) (α : Act) :
  (∃p, (s', p) ∈ succs s α) ↔ 0 < M.P s α s'
:= by
  simp [hM, mk_from_succs]
  constructor <;> intro h
  · refine zero_lt_iff.mpr ?mp.a
    simp
    obtain ⟨p, hp, h⟩ := h
    use s', p
    simp_all [hp, pos_iff_ne_zero.mp hp.left]
  · simp [zero_lt_iff] at h
    rcases h with ⟨s', p', ⟨hp, hp'⟩, hs', _⟩
    symm at hs' ; simp_all
    use p', ⟨pos_iff_ne_zero.mpr hp.left, hp.right⟩
