import MDP.Basic
import MDP.Paths
import MDP.Succs
import MDP.Scheduler
import MDP.Paths.Prob

-- TODO: remove this
set_option linter.unusedSectionVars false

namespace MDP

variable {State : Type*} {Act : Type*}
variable [DecidableEq State] [DecidableEq Act]
variable [ActNonempty : Nonempty Act]
variable (M : MDP State Act)

noncomputable def Paths_mono : Set M.Path →o Set M.Path :=
  have : DecidableEq M.Path := Classical.typeDecidableEq M.Path
  OrderHom.mk (fun πs ↦ πs ∪ ⋃ π' ∈ πs, π'.succs_univ) (by
    intro s₁ s₂ h π h'
    simp_all
    cases h' with
    | inl h' =>
      left
      exact Set.mem_of_subset_of_mem h h'
    | inr h' =>
      right
      obtain ⟨π', h'⟩ := h'
      use π'
      exact ⟨Set.mem_of_subset_of_mem h h'.left, h'.right⟩)

noncomputable def Paths_mono_Set : Set M.Path →o Set M.Path :=
  have : DecidableEq M.Path := Classical.typeDecidableEq M.Path
  OrderHom.mk (fun πs ↦ πs ∪ ⋃ π ∈ πs, π.succs_univ) (by
    intro s₁ s₂ h π h'
    simp_all
    cases h' with
    | inl h' =>
      left
      exact h h'
    | inr h' =>
      right
      obtain ⟨π', h'⟩ := h'
      use π'
      exact ⟨h h'.left, h'.right⟩)

noncomputable def Paths_n
  (s : State)
: ℕ → Set M.Path
  | 0 => {MDP.Path.mk_single M s}
  | n+1 =>
    have : DecidableEq M.Path := Classical.typeDecidableEq M.Path
    ⋃ π ∈ Paths_n s n, π.succs_univ

def Paths_n₀
  [M.FiniteBranching]
  (s : State)
: ℕ → Finset M.Path
  | 0 => {MDP.Path.mk_single M s}
  | n+1 => (Paths_n₀ s n).biUnion Path.succs_univ₀

noncomputable def Paths_n_iff_Paths_n₀ [M.FiniteBranching] (s : State) (n : ℕ) : M.Paths_n s n = M.Paths_n₀ s n := by
  induction n with
  | zero => simp [Paths_n, Paths_n₀]
  | succ n ih =>
    simp only [Paths_n, ih, Finset.mem_coe, Path.succs_univ_eq_succs_univ₀, Paths_n₀, Finset.coe_biUnion]

noncomputable def Paths_n₀_subtype [M.FiniteBranching] (s : State) (n : ℕ) := M.Paths_n₀ s n |>.attach

theorem Paths_n₀_first_eq_first [M.FiniteBranching] (s : State) (n : ℕ) : ∀ π ∈ M.Paths_n₀ s n, π.first = s := by
  intro π h
  induction n generalizing π with
  | zero =>
    simp only [Paths_n₀, Set.mem_iUnion] at h
    simp_all only [Finset.mem_singleton, Path.mk_single_first]
  | succ n ih =>
    simp [Paths_n₀] at h
    obtain ⟨π', h₁, h₂⟩ := h
    suffices π.first = π'.first by
      rw [this]
      exact ih π' h₁
    unfold Path.succs_univ₀ at h₂
    simp at h₂
    obtain ⟨a, _, h'⟩ := h₂
    symm
    exact π'.succs_first_eq_first a π h'

noncomputable def Paths_le_n
  (s : State)
: ℕ → Set M.Path
  | 0 => {MDP.Path.mk_single M s}
  | n+1 =>
    have : DecidableEq M.Path := Classical.typeDecidableEq M.Path
    Paths_le_n s n ∪ ⋃ π ∈ M.Paths_n s n, π.succs_univ

theorem Paths_n_subset_Paths_le_n
  (s : State)
  (n : ℕ)
: M.Paths_n s n ⊆ M.Paths_le_n s n := by
  induction n with
  | zero => simp only [Paths_n, Paths_le_n, Set.subset_singleton_iff, Set.mem_singleton_iff,
    imp_self, implies_true]
  | succ n _ =>
    dsimp only [Paths_n, Paths_le_n]
    have : DecidableEq M.Path := Classical.typeDecidableEq M.Path
    convert Set.subset_union_right

noncomputable def Paths (s : State) : Set M.Path := Set.iUnion (fun l ↦ M.Paths_n s l)

noncomputable def Paths_rec (s : State) : ℕ → Set M.Path
  | 0 => M.Paths_n s 0
  | n+1 => M.Paths_n s (n+1) ∪ Paths_rec s n

theorem Paths_n_first_eq_first (s : State) (n : ℕ) : ∀ π ∈ M.Paths_n s n, π.first = s := by
  intro π h
  induction n generalizing π with
  | zero =>
    simp_all only [Paths_n, Path.mk_single, Set.mem_singleton_iff, Path.first, List.head_cons]
  | succ n ih =>
    simp_all [Paths_n]
    obtain ⟨π', h₁, h₂⟩ := h
    have := ih π' h₁
    rw [←Path.succs_univ_is_prev π' π h₂] at this
    rw [Path.prev_first_eq_first] at this
    assumption

theorem Paths_first_eq_first (s : State) : ∀ π ∈ M.Paths s, π.first = s := by
  intro π h
  simp only [Paths, Set.mem_iUnion] at h
  obtain ⟨n, h⟩ := h
  exact M.Paths_n_first_eq_first s n π h

theorem Paths_rec_first_eq_first (s : State) (n : ℕ) : ∀ π ∈ M.Paths_rec s n, π.first = s := by
  intro π h
  induction n generalizing π with
  | zero =>
    have := M.Paths_n_first_eq_first s 0
    simp_all only [Paths_rec, Path.first]
  | succ n ih =>
    simp_all only [Nat.succ_eq_add_one, Paths_rec, Set.mem_union]
    rcases h with h | h
    · exact M.Paths_n_first_eq_first s (n + 1) π h
    · exact ih π h

theorem Paths_n_contains_prev
  (s : State)
  (n : ℕ)
: ∀ π ∈ M.Paths_n s n.succ, π.prev ∈ M.Paths_n s n := by
  intro π h
  simp_all only [Paths_n, Path.succs_univ, Path.succs, Finset.coe_map, Function.Embedding.coeFn_mk,
    Set.mem_iUnion, Set.mem_image, Finset.mem_coe, Subtype.exists, Finset.mem_val,
    Finsupp.mem_support_iff, ne_eq, exists_prop]
  obtain ⟨π', π'_h, a, s', h₁, _, h₃⟩ := h
  convert π'_h
  simp only [Path.extend, Nat.succ_eq_add_one] at h₃
  simp only [Path.prev, ← h₃, List.length_append, List.length_cons,
    List.length_nil, zero_add, tsub_pos_iff_lt, lt_add_iff_pos_left, List.length_pos, ne_eq,
    π'.nonempty, not_false_eq_true, ↓reduceDIte, List.cons_ne_self, List.dropLast_append_of_ne_nil,
    List.dropLast_single, List.append_nil]

theorem Paths_n₀_contains_prev
  [M.FiniteBranching]
  (s : State)
  (n : ℕ)
: ∀ π ∈ M.Paths_n₀ s n.succ, π.prev ∈ M.Paths_n₀ s n := by
  intro π h
  have := M.Paths_n_contains_prev s n π (by simp [Paths_n_iff_Paths_n₀, h])
  simp only [Paths_n_iff_Paths_n₀, Finset.mem_coe] at this
  exact this

theorem Paths_n_mem
  (π : M.Path)
: π ∈ M.Paths_n π.first (∎|π| - 1) := by
  generalize h' : (∎|π| - 1) = n
  induction n generalizing π with
  | zero =>
    simp only [Paths_n, Set.mem_singleton_iff]
    apply π.mk_single_iff_length_zero.mpr
    have := π.length_pos ; omega
  | succ n ih =>
    simp [Paths_n, Finset.mem_union]
    use π.prev
    have : ∎|π.prev| - 1 = n := by simp ; omega
    have := @ih π.prev this
    rw [Path.prev_first_eq_first] at this
    simp [this]
    simp [Path.succs_univ]
    apply Exists.intro _
    exact π.succs_contained_in_prev (by simp_all)

theorem Paths_n_eq_Paths_n₀
  [M.FiniteBranching]
  (s : State)
  (n : ℕ)
: M.Paths_n s n = M.Paths_n₀ s n := by
  induction n with
  | zero => simp_all [Paths_n, Paths_n₀]
  | succ n ih =>
    simp_all [Paths_n, Paths_n₀]
    ext π
    simp_all
    constructor <;> intro h
    · obtain ⟨π', h⟩ := h
      use π'
      simp_all [Path.succs_univ_eq_succs_univ₀]
    · obtain ⟨π', h⟩ := h
      use π'
      simp_all [Path.succs_univ_eq_succs_univ₀]

theorem Paths_n₀_mem
  [M.FiniteBranching]
  (π : M.Path)
: π ∈ M.Paths_n₀ π.first (∎|π| - 1) := by
  have := M.Paths_n_mem π
  rw [Paths_n_eq_Paths_n₀] at this
  exact this

theorem Paths_n₀_Nonempty
  [M.FiniteBranching]
  (s : State)
  (n : ℕ)
: (M.Paths_n₀ s n).Nonempty := by
  induction n with
  | zero => simp [Paths_n₀]
  | succ n ih =>
    obtain ⟨π, hπ⟩ := ih
    simp [Paths_n₀]
    use π, hπ
    exact π.succs_univ₀_nonempty

theorem Paths_n₀_nonempty
  [M.FiniteBranching]
  (s : State)
  (n : ℕ)
: M.Paths_n₀ s n ≠ ∅ := Finset.nonempty_iff_ne_empty.mp <| M.Paths_n₀_Nonempty s n

theorem Paths_n₀_length
  [M.FiniteBranching]
  {s₀ : State}
  {n : ℕ}
  {π : M.Path}
  (h : π ∈ M.Paths_n₀ s₀ n)
: (∎|π| - 1) = n := by
  induction n generalizing π with
  | zero => simp_all [Paths_n₀]
  | succ n ih =>
    simp_all [Paths_n₀]
    obtain ⟨π', h, h'⟩ := h
    have := π'.length_pos
    have := ih h
    have := Path.succs_univ₀_length_eq_succ _ _ h'
    omega

theorem Paths_n₀_iff
  [M.FiniteBranching]
  {s₀ : State}
  {n : ℕ}
  {π : M.Path}
: π ∈ M.Paths_n₀ s₀ n ↔ π.first = s₀ ∧ (∎|π| - 1) = n := by
  constructor
  · intro h
    have := M.Paths_n₀_first_eq_first s₀ n
    have := M.Paths_n₀_length h
    simp_all
  · intro ⟨h, h'⟩
    convert M.Paths_n₀_mem π
    · simp_all
    · omega

theorem Paths_le_n_mem (π : M.Path) : π ∈ M.Paths_le_n π.first (∎|π| - 1) :=
  (M.Paths_n_subset_Paths_le_n π.first (∎|π| - 1)) (M.Paths_n_mem π)

theorem Paths_n_length_eq_n
  (s : State)
  (n : ℕ)
: ∀ π ∈ M.Paths_n s n, ∎|π| = n + 1 := by
  intro π h
  induction n generalizing π with
  | zero =>
    simp only [Paths_n, Set.mem_singleton_iff] at h
    simp_all only [Path.mk_single, List.length_singleton, ge_iff_le, le_refl,
      tsub_eq_zero_of_le]
  | succ n ih =>
    simp [Paths_n] at h
    obtain ⟨π', h₁, h₂⟩ := h
    rw [Path.succs_univ_length_eq_succ π' _ h₂]
    rw [ih π' h₁]

theorem Paths_n₀_length_eq_n
  [M.FiniteBranching]
  (s : State)
  (n : ℕ)
: ∀ π ∈ M.Paths_n₀ s n, ∎|π| = n + 1 := by
  intro π h
  induction n generalizing π with
  | zero =>
    simp only [Paths_n₀, Finset.mem_singleton] at h
    simp_all only [Path.mk_single, List.length_singleton, ge_iff_le, le_refl,
      tsub_eq_zero_of_le]
  | succ n ih =>
    simp [Paths_n₀] at h
    obtain ⟨π', h₁, h₂⟩ := h
    rw [Path.succs_univ₀_length_eq_succ π' _ h₂]
    rw [ih π' h₁]

theorem Paths_le_n_length_le_n
  (s : State)
  (n : ℕ)
: ∀ π ∈ M.Paths_le_n s n, ∎|π| ≤ n + 1 := by
  intro π h
  induction n generalizing π with
  | zero =>
    simp only [Paths_le_n, Set.mem_singleton_iff] at h
    simp_all only [Path.mk_single, List.length_singleton, ge_iff_le, le_refl,
      tsub_eq_zero_of_le]
  | succ n ih =>
    simp [Paths_le_n] at h
    rcases h with h | h
    · exact Nat.le_succ_of_le (ih π h)
    · obtain ⟨π', h₁, h₂⟩ := h
      rw [Path.succs_univ_length_eq_succ π' _ h₂]
      exact Nat.le_of_eq (congrArg Nat.succ <| M.Paths_n_length_eq_n s n π' h₁)

theorem Paths_mem
  (π : M.Path)
: π ∈ M.Paths π.first := by
  simp only [Paths, Set.mem_iUnion, Finset.mem_coe]
  use ∎|π| - 1
  exact M.Paths_n_mem π

theorem Paths_eq_univ (s : State) : M.Paths s = { π | π.first = s } := by
  ext π
  have p₁ := M.Paths_mem π
  have p₂ := M.Paths_first_eq_first s
  constructor <;> intro h
  · exact p₂ π h
  · simp_all only [Nat.succ_eq_add_one, Set.mem_setOf_eq]

theorem Paths_eq_Paths_rec (s : State) : M.Paths s = ⨆n, M.Paths_rec s n := by
  rw [Paths_eq_univ]
  ext π
  simp_all [Paths_rec, Paths]
  generalize h' : ∎|π| - 1 = n
  constructor
  · intro h
    use n
    induction n generalizing π with
    | zero =>
      simp [Paths_rec, Paths_n]
      have := π.mk_single_iff_length_zero.mpr (by have := π.length_pos ; omega)
      rw [h] at this
      exact this
    | succ n ih =>
      left
      have := π.succs_contained_in_prev (by omega)
      have := ih π.prev (by rw [π.prev_length_eq_pred] ; omega)
      have := M.Paths_n_mem π
      simp_all [Paths_rec, Paths_n]
  · intro h
    obtain ⟨i, h⟩ := h
    exact M.Paths_rec_first_eq_first s i π h

def Pathsable_eq [M.FiniteBranching] (n : ℕ) (s : State) : Finset State :=
  match n with
  | 0 => {s}
  | n+1 => Pathsable_eq n s |>.biUnion M.succs_univ₀

def Pathsable_le [M.FiniteBranching] (n : ℕ) (s : State) : Finset State :=
  match n with
  | 0 => {s}
  | n+1 => Pathsable_le n s ∪ M.Pathsable_eq (n + 1) s

def Pathsable_le' [M.FiniteBranching] (n : ℕ) (s : State) : Finset (Fin (n + 1) × State) :=
  match n with
  | 0 => {(0, s)}
  | n+1 => (Pathsable_le' n s).image (fun (i, s') ↦ (i, s')) ∪ (M.Pathsable_eq (n + 1) s).image (fun s' ↦ (n + 1, s'))

@[simp]
theorem Pathsable_eq_zero [M.FiniteBranching] (s : State) : M.Pathsable_eq 0 s = {s} := by rfl
@[simp]
theorem Pathsable_le_zero [M.FiniteBranching] (s : State) : M.Pathsable_le 0 s = {s} := by rfl
@[simp]
theorem Pathsable_le'_zero [M.FiniteBranching] (s : State) : M.Pathsable_le' 0 s = {(0, s)} := by rfl

@[simp]
theorem Pathsable_le_s_mem [M.FiniteBranching] (n : ℕ) (s : State) : s ∈ M.Pathsable_le n s := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [Pathsable_le]
    left
    exact ih

theorem succs_univ₀_eq_Pathsable_eq_1 [M.FiniteBranching] : M.succs_univ₀ = M.Pathsable_eq 1 := by simp [Pathsable_eq]

theorem Pathsable_eq_succ [M.FiniteBranching] (n : ℕ) (s : State) : M.Pathsable_eq (n + 1) s = (M.succs_univ₀ s).biUnion (M.Pathsable_eq n) := by
  induction n with
  | zero => simp only [Pathsable_eq, Finset.singleton_biUnion, Finset.biUnion_singleton_eq_self]
  | succ n ih =>
    conv => right ; simp only [Pathsable_eq] ; rw [←Finset.biUnion_biUnion]
    rw [←ih]
    simp only [Pathsable_eq]

theorem Pathsable_eq_subset_le_n [M.FiniteBranching] (n : ℕ) (s : State) : M.Pathsable_eq n s ⊆ M.Pathsable_le n s := by
  cases n <;> simp only [Pathsable_eq, Pathsable_le, subset_refl, Finset.subset_union_right]

theorem Pathsable_eq_n_m [M.FiniteBranching] (n m : ℕ) (s : State) : M.Pathsable_eq (n + m) s = (M.Pathsable_eq n s).biUnion (M.Pathsable_eq m) := by
  induction m generalizing s with
  | zero => simp only [add_zero, Pathsable_eq, Finset.biUnion_singleton_eq_self]
  | succ m ih =>
    rw [←add_assoc, Pathsable_eq_succ]
    have h : ∀ a b, M.Pathsable_eq (a + b) = fun s ↦ M.Pathsable_eq (a + b) s := fun _ _ ↦ rfl
    rw [h n m, h m 1]
    simp only [ih, ← Finset.biUnion_biUnion, M.Pathsable_eq_succ m]
    rw [← M.Pathsable_eq_succ]
    rfl

theorem Pathsable_le_exists [M.FiniteBranching] {s s' : State} {n : ℕ} (h : s' ∈ M.Pathsable_le n s) : ∃ m, s' ∈ M.Pathsable_eq m s ∧ m ≤ n := by
  induction n
  · use 0 ; use h
  · rename_i n ih
    unfold Pathsable_le at h
    simp at h
    rcases h with h | h
    · have ⟨m, hm₁, hm₂⟩ := ih h
      use m
      simp only [hm₁, true_and]
      omega
    · use n + 1

theorem Pathsable_le_if_le [M.FiniteBranching] {s₁ s₂ : State} {n m : ℕ} (h : n ≤ m) (h' : s₂ ∈ M.Pathsable_eq n s₁) : s₂ ∈ M.Pathsable_le m s₁ := by
  induction m with
  | zero => simp_all only [nonpos_iff_eq_zero, Pathsable_le_zero, Finset.mem_singleton,
    Pathsable_eq_zero]
  | succ m ih =>
    simp only [Pathsable_le, Finset.mem_union]
    cases h
    · simp_all only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, false_implies,
      or_true]
    · simp_all only [Nat.le_eq, true_or]

theorem Pathsable_eq_trans [M.FiniteBranching] {n m : ℕ} {s₁ s₂ s₃ : State} (h₁ : s₂ ∈ M.Pathsable_eq n s₁) (h₂ : s₃ ∈ M.Pathsable_eq m s₂) : s₃ ∈ M.Pathsable_eq (n + m) s₁ := by
  simp [Pathsable_eq_n_m]
  exact Filter.frequently_principal.mp fun a ↦ a h₁ h₂

theorem Pathsable_le_trans [M.FiniteBranching] {n m : ℕ} {s₁ s₂ s₃ : State} (h₁ : s₂ ∈ M.Pathsable_le n s₁) (h₂ : s₃ ∈ M.Pathsable_le m s₂) : s₃ ∈ M.Pathsable_le (n + m) s₁ := by
  let ⟨i₁, hi₁, _⟩ := M.Pathsable_le_exists h₁
  let ⟨i₂, hi₂, _⟩ := M.Pathsable_le_exists h₂
  exact M.Pathsable_le_if_le (by omega) (M.Pathsable_eq_trans hi₁ hi₂)

theorem le_add_exists_le_exists_le_eq_add (n m i : ℕ) (h : i ≤ n + m) : ∃ a ≤ n, ∃ b ≤ m, i = a + b := by
  induction i generalizing n m with
  | zero => use 0 ; simp
  | succ i ih =>
    have : 0 < n ∨ 0 < m := by omega
    cases this
    · have ⟨a, ha, b, hab⟩ := ih (n - 1) m (by omega)
      use a + 1
      constructor
      · omega
      · use b
        omega
    · have ⟨a, ha, b, hab⟩ := ih n (m - 1) (by omega)
      use a
      constructor
      · omega
      · use b + 1
        omega

theorem Pathsable_le_n_m [M.FiniteBranching] (n m : ℕ) (s : State) : M.Pathsable_le (n + m) s = (M.Pathsable_le n s).biUnion (M.Pathsable_le m) := by
  ext s'
  simp
  constructor
  · intro h
    have ⟨i, hi, hi'⟩ := M.Pathsable_le_exists h
    have ⟨a, ha, b, hb, hab⟩ := le_add_exists_le_exists_le_eq_add n m i hi'
    have ⟨x, hx⟩ := (Finset.ext_iff.mp (M.Pathsable_eq_n_m a b s) s').mp (by simp_all) |> Finset.mem_biUnion.mp
    use x
    exact ⟨M.Pathsable_le_if_le ha hx.left, M.Pathsable_le_if_le hb hx.right⟩
  · simp_all
    intro _
    exact M.Pathsable_le_trans

theorem Pathsable_le_subset_succ [M.FiniteBranching] (n : ℕ) (s : State) : M.Pathsable_le n s ⊆ M.Pathsable_le (n + 1) s := by
  intro s' h
  have ⟨i, hi, hi'⟩ := M.Pathsable_le_exists h
  rcases i with i | i
  · simp_all
  · apply M.Pathsable_le_if_le _ hi
    omega

theorem Pathsable_le_subset_le [M.FiniteBranching] {n m : ℕ} (h : n ≤ m) (s : State) : M.Pathsable_le n s ⊆ M.Pathsable_le m s := by
  have ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  simp_all
  induction k generalizing n m with
  | zero => simp
  | succ k ih =>
    rw [←add_comm 1 k, ←add_assoc]
    exact (M.Pathsable_le_subset_succ n s).trans <| @ih (n + 1) m (by omega)

theorem succs_univ₀_imp_Pathsable_le [M.FiniteBranching] (n : ℕ) {s s' : State} (h : s' ∈ M.succs_univ₀ s) : s' ∈ M.Pathsable_le (n + 1) s := by
  unfold Pathsable_le
  simp
  induction n with
  | zero => simp_all [Pathsable_eq]
  | succ n ih =>
    rcases ih with ih | ih
    · left
      exact M.Pathsable_le_subset_succ n s ih
    · left
      exact M.Pathsable_eq_subset_le_n (n + 1) s ih

theorem Pathsable_le_succ [M.FiniteBranching] (n : ℕ) (s : State) : M.Pathsable_le (n + 1) s = {s} ∪ (M.succs_univ₀ s).biUnion (M.Pathsable_le n) := by
  have : {s} ∪ (M.succs_univ₀ s).biUnion (M.Pathsable_le n) = (M.Pathsable_le 1 s).biUnion (M.Pathsable_le n) := by
    ext s'
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
    constructor <;> intro h
    · rcases h with h | ⟨x, hx, h⟩
      · use s
        simp [h]
      · use x
        simp only [succs_univ₀_imp_Pathsable_le, and_self, hx, h]
    · simp only [Pathsable_le, Pathsable_eq, Finset.singleton_biUnion, Finset.mem_union,
      Finset.mem_singleton, exists_eq_or_imp] at h
      rcases h with h | ⟨x, hx, h⟩
      · have ⟨i, hi, hi'⟩ := M.Pathsable_le_exists h
        rcases i with _ | i
        · simp_all
        · right
          simp only [Pathsable_eq_succ, Finset.mem_biUnion] at hi
          have ⟨x, hx₁, hx₂⟩ := hi
          use x, hx₁
          apply M.Pathsable_le_if_le _ hx₂
          omega
      · right
        use x
  rw [add_comm, this]
  exact M.Pathsable_le_n_m 1 n s

theorem Pathsable_le_n_m_subset [M.FiniteBranching] (n m : ℕ) (s s' : State) (h : s' ∈ M.Pathsable_le n s) : M.Pathsable_le m s' ⊆ M.Pathsable_le (n + m) s := by
  intro s'' h'
  simp only [Pathsable_le_n_m, Finset.mem_biUnion]
  use s', h, h'

theorem Fin.succ_eq_val_succ (n : ℕ) : ((⟨n, by omega⟩ : Fin (n + 1 + 1)) + 1).val = n + 1 := by
  apply Fin.val_add_one_of_lt
  exact Set.Ici_subset_Ioi.mp fun ⦃a⦄ a ↦ a

theorem Pathsable_le'_eq_Reacable_eq [M.FiniteBranching] (n : ℕ) (s : State) (i : Fin (n + 1)) (s' : State) : (i, s') ∈ M.Pathsable_le' n s ↔ s' ∈ M.Pathsable_eq i s := by
  induction n with
  | zero =>
    have := i.isLt
    simp
    omega
  | succ n ih =>
    simp_all [Pathsable_le', Pathsable_eq]
    constructor
    · intro h
      rcases h with ⟨⟨i', hi'⟩, h₂⟩ | ⟨⟨s'', h₁, h₂⟩, h₃⟩
      · simp_all
        rw [←h₂.right]
        exact h₂.left
      · have : i.val = n + 1 := by
          rw [←h₃] at *
          convert Fin.succ_eq_val_succ n
          simp
          omega
        simp_all
        simp [Pathsable_eq]
        use s''
    · intro s''
      by_cases hi : ↑i < n + 1
      · left
        use i
        simp
        constructor
        · convert s''
          simp
          have := i.isLt
          omega
        · refine Fin.eq_of_val_eq ?h.right.a
          simp
          omega
      · right
        simp_all
        have hn : n + 1 = i := by omega
        simp_all
        symm at hn
        simp_all
        simp [Pathsable_eq] at s''
        use s''
        symm at hn
        obtain ⟨i, hi⟩ := i
        simp_all
        simp [←hn]
        refine Fin.eq_mk_iff_val_eq.mpr ?right.mk.a
        convert Fin.succ_eq_val_succ n
        simp
        omega

theorem Paths_n₀_Pathsable [M.FiniteBranching] (s : State) (n : ℕ) (π : M.Paths_n₀ s n) (h : s' ∈ π.val.states) : s' ∈ M.Pathsable_le n s := by
  obtain ⟨π, hπ⟩ := π
  induction n generalizing π s' with
  | zero =>
    simp only [Paths_n₀, Finset.mem_singleton] at hπ
    simp_all only [Path.mk_single_states, List.mem_singleton, Pathsable_le_zero,
      Finset.mem_singleton]
  | succ n ih =>
    have ih' : π.prev ∈ M.Paths_n₀ s n := M.Paths_n₀_contains_prev s n π hπ
    by_cases h' : s' ∈ π.prev.states
    · have := ih π.prev ih' h'
      exact M.Pathsable_le_subset_succ n s this
    · simp_all
      simp [Pathsable_le_n_m]
      use π.prev.last
      use ih π.prev ih' π.prev.last_in_states
      simp [Pathsable_le, Pathsable_eq]
      right
      have π_nonempty : 1 < ∎|π| := by
        have := M.Paths_n₀_length_eq_n s (n + 1) π hπ
        omega
      simp_all [π.prev_states_eq_dropLast π_nonempty]
      have : s' = π.last := List.mem_not_mem_dropLast s' π.states h h'
      simp_all
      exact π.last_in_succs_univ₀_prev_last π_nonempty

theorem Paths_n₀_Pathsable_le [M.FiniteBranching] (s : State) (n m : ℕ) (hnm : n ≤ m) (π : M.Paths_n₀ s n) (h : s' ∈ π.val.states) : s' ∈ M.Pathsable_le m s :=
  M.Pathsable_le_subset_le hnm s <| M.Paths_n₀_Pathsable s n π h

def RScheduler [M.FiniteBranching] (n : ℕ) (s : State) := (s' : M.Pathsable_le n s) → M.act₀ s'

namespace RScheduler

variable {M : MDP State Act}
variable [M.FiniteBranching]

instance instNonempty (n : ℕ) (s : State) : Nonempty (M.RScheduler n s) := Nonempty.intro (fun x ↦ M.act₀_default x)
instance instFinite (n : ℕ) (s : State) : Finite (M.RScheduler n s) := Pi.finite
instance instFintype (n : ℕ) (s : State) : Fintype (M.RScheduler n s) := Pi.fintype

def elems (n : ℕ) (s : State) : Finset (M.RScheduler n s) := (instFintype n s).elems
def elems_nonempty (n : ℕ) (s : State) : (elems (M:=M) n s).Nonempty := by
  have 𝒮 := instNonempty (M:=M) n s
  use 𝒮.some, (instFintype n s).complete 𝒮.some

def inf {γ : Type*} [SemilatticeInf γ] {n : ℕ} {s : State} (f : M.RScheduler n s → γ) := Finset.inf' (RScheduler.elems n s) (RScheduler.elems_nonempty n s) f

noncomputable def inf_choose {n : ℕ} {s : State} (f : M.RScheduler n s → ENNReal) : M.RScheduler n s :=
  (Finset.exists_mem_eq_inf' (elems_nonempty n s) f).choose

noncomputable def inf_choose_spec {n : ℕ} {s : State} (f : M.RScheduler n s → ENNReal) : (inf_choose f) ∈ elems n s ∧ (elems n s).inf' (elems_nonempty n s) f = f (inf_choose f) :=
  (Finset.exists_mem_eq_inf' (elems_nonempty n s) f).choose_spec

theorem inf_const_add {n : ℕ} {s : State} (f : M.RScheduler n s → ENNReal) (x : ENNReal) : RScheduler.inf (fun 𝒮 ↦ x + f 𝒮) = x + RScheduler.inf f := by
  simp [inf, elems]
  simp [Finset.inf'_eq_inf, Finset.inf_eq_iInf]
  conv => left ; arg 1 ; ext 𝒮 ; rw [add_comm x]
  simp [←ENNReal.iInf_add]
  rw [add_comm x]

theorem inf_const_mul {n : ℕ} {s : State} (f : M.RScheduler n s → ENNReal) (x : ENNReal) : RScheduler.inf (fun 𝒮 ↦ x * f 𝒮) = x * RScheduler.inf f := by
  simp [inf, elems]
  by_cases hx : x ≠ ⊤
  · simp [Finset.inf'_eq_inf, Finset.inf_eq_iInf, Fintype.complete]
    conv => left ; arg 1 ; ext 𝒮 ; rw [mul_comm x]
    rw [mul_comm x]
    symm
    apply ENNReal.iInf_mul
    simp_all
  · simp at hx
    simp only [hx]
    by_cases h0 : (Fintype.elems : Finset (M.RScheduler n s)).inf' (elems_nonempty n s) f = 0
    · simp [h0]
      have ⟨x0, hx0⟩ : ∃ x ∈ (Fintype.elems : Finset (M.RScheduler n s)), f x = 0 := by
        refine Finset.inf_eq_bot_iff.mp ?_
        simp [Finset.inf'_eq_inf] at h0
        exact h0
      apply le_antisymm
      · apply Finset.inf'_le_of_le (fun x ↦ ⊤ * f x) hx0.left
        simp only [mul_zero, le_refl, hx0]
      · simp
    · simp [h0]
      have : ∀ x ∈ (Fintype.elems : Finset (M.RScheduler n s)), f x ≠ 0 := by
        simp [Finset.inf'_eq_inf] at h0
        simp [Fintype.complete]
        have := (@Finset.inf_eq_bot_iff _ _ _ _ _ (Fintype.elems : Finset (M.RScheduler n s)) f).not.mp
        simp [Fintype.complete] at this
        exact this h0
      simp_all only [ne_eq, not_false_eq_true, ENNReal.top_mul, Finset.inf'_const]

def cast_n {n : ℕ} {s : State} (𝒮 : M.RScheduler n s) (m : ℕ) (h : m ≤ n) : M.RScheduler m s :=
  fun ⟨s', hs'⟩ ↦ 𝒮 ⟨s', M.Pathsable_le_subset_le h s hs'⟩

def cast_s {n : ℕ} {s₀ : State} (m : ℕ) (𝒮 : M.RScheduler (n + m) s₀) (s₀' : State) (h : s₀' ∈ M.Pathsable_le n s₀) : M.RScheduler m s₀' :=
  fun ⟨s', h'⟩ ↦ 𝒮 ⟨s', M.Pathsable_le_n_m_subset n m s₀ s₀' h h'⟩

def cast_s' {n : ℕ} {s₀ : State} (m : ℕ) (𝒮 : M.RScheduler (n + m) s₀) (s₀' : State) (h : s₀' ∈ M.Pathsable_le m s₀) : M.RScheduler n s₀' :=
  fun ⟨s', h'⟩ ↦ 𝒮 ⟨s', by
    rw [add_comm]
    exact M.Pathsable_le_n_m_subset m n s₀ s₀' h h'⟩

def cast_s_succ {n : ℕ} {s₀ : State} (𝒮 : M.RScheduler (n + 1) s₀) (s₀' : State) (h : s₀' ∈ M.succs_univ₀ s₀) : M.RScheduler n s₀' :=
  𝒮.cast_s' 1 s₀' (M.succs_univ₀_imp_Pathsable_le 0 h)

noncomputable def cast_s_succ' {n : ℕ} {s₀ : State} (𝒮 : M.RScheduler n s₀) (s₀' : State) : M.RScheduler (n + 1) s₀' :=
  fun ⟨s, hs⟩ ↦
    if h : s ∈ M.Pathsable_le n s₀ then
      ⟨𝒮 ⟨s, h⟩, by
        have := (𝒮 ⟨s, h⟩).prop
        simp_all⟩
    else
      M.act₀_default s

noncomputable def cast_arb {n : ℕ} {s : State} (𝒮 : M.RScheduler n s) (m : ℕ) (s' : State) : M.RScheduler m s' :=
  fun ⟨sx, _⟩ ↦
    if h' : sx ∈ M.Pathsable_le n s then
      𝒮 ⟨sx, h'⟩
    else
      M.act₀_default sx

end RScheduler

namespace Path

variable {M : MDP State Act}
variable [M.FiniteBranching]

variable (π : M.Path) (n : ℕ) (s : State)

def reachable_from := ∎|π| = n + 1 ∧ π.first = s
def reachable_in := ∎|π| ≤ n + 1 ∧ π.first = s

theorem reachable_from_first {n : ℕ} {s : State} (h : π.reachable_from n s) : π.first = s := h.right

theorem reachable_from_length {n : ℕ} {s : State} (h : π.reachable_from n s) : ∎|π| = n + 1 := h.left

theorem Paths_n₀_imp_reachable_from (hπ : π ∈ M.Paths_n₀ s n) : π.reachable_from n s := by
  constructor
  · exact M.Paths_n₀_length_eq_n s n π hπ
  · exact M.Paths_n₀_first_eq_first s n π hπ

theorem reachable_from_imp_Paths_n₀ (hπ : π.reachable_from n s) : π ∈ M.Paths_n₀ s n := by
  convert M.Paths_n₀_mem π
  · symm
    exact hπ.right
  · obtain ⟨h₁, _⟩ := hπ
    omega

theorem Paths_n₀_iff_reachable_from {n : ℕ} {s : State} : π ∈ M.Paths_n₀ s n ↔ π.reachable_from n s :=
  ⟨π.Paths_n₀_imp_reachable_from n s, π.reachable_from_imp_Paths_n₀ n s⟩

theorem reachable_from_univ : π.reachable_from (∎|π| - 1) π.first := by
  simp [←Paths_n₀_iff_reachable_from]
  exact M.Paths_n₀_mem π

theorem reachable_from_iff {n : ℕ} {s : State} : ∎|π| - 1 = n ∧ π.first = s ↔ π.reachable_from n s := by
  have := π.length_pos
  simp [reachable_from]
  omega

theorem reachable_from_succ_eq_prev (h : π.reachable_from (n + 1) s) : π.prev.reachable_from n s := by
  obtain ⟨h₁, h₂⟩ := h

  constructor
  · simp [prev_length_eq_pred]
    omega
  · exact π.prev_first_eq_first.trans h₂

theorem reachable_from_imp_Paths_n₀''' (h : π ∈ M.Paths_n₀ s (n + 1)) : π.prev ∈ M.Paths_n₀ s n := by
  simp_all [Paths_n₀_iff_reachable_from]
  exact π.reachable_from_succ_eq_prev n s h

theorem reachable_from_tail_first (h : π.reachable_from (n + 1) s) : π.tail.reachable_from n (π[1]'(by have := π.reachable_from_length h ; omega)) := by
  obtain ⟨h₁, h₂⟩ := h
  convert π.tail.reachable_from_univ
  · simp_all only [Prod.forall, tail_length, add_tsub_cancel_right, le_add_iff_nonneg_left,
    zero_le, max_eq_right]
  · simp_all only [getElem, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true,
    tail_first_eq_get_one]

theorem reachable_from_succ_left (h : π.reachable_from (n + 1) s) : ∃ s' ∈ M.succs_univ₀ s, π.tail.reachable_from n s' := by
  have := π.reachable_from_length h
  use π[1]
  simp only [← π.reachable_from_first h, π.reachable_from_tail_first n s h, and_true]
  exact π.succs_univ₀_get_1 (by omega)

theorem reachable_from_succ_right (h : ∃ s' ∈ M.succs_univ₀ s, π.reachable_from n s') :
  (π.prepend s (by obtain ⟨s', h₁, h₂⟩ := h ; rw [π.reachable_from_first h₂] ; simp [h₁])).reachable_from (n + 1) s
:= by
  obtain ⟨s', h₁, h₂⟩ := h
  have h_len' : n = ∎|π| - 1 := by
    have := π.reachable_from_length h₂
    simp at this
    omega
  simp only [h_len', length_pred_add]
  apply reachable_from_univ

theorem reachable_from_mem (h : π.reachable_from n s) (i : Fin π.states.length) : π[i] ∈ M.Pathsable_le n s := by
  simp only [← Paths_n₀_iff_reachable_from] at h
  apply M.Paths_n₀_Pathsable_le s n n (by omega) ⟨π, h⟩
  simp [List.getElem_mem]

theorem asdf (π : M.Path) (s' : State) (hπ : π ∈ M.Paths_n₀ s' n) (hs' : s' ∈ M.succs_univ₀ s₀) : π.first ∈ M.succs_univ s₀ := by
  simp [M.Paths_n₀_first_eq_first s' n π hπ, hs']

theorem reachable_from_imp_reachable_in {n : ℕ} {s : State} (h : π.reachable_from n s) : π.reachable_in n s := by
  have := π.reachable_from_length h
  simp [reachable_in, this] at h ⊢
  exact π.reachable_from_first h

theorem reachable_from_imp_prev_reachable_in {n : ℕ} {s : State} (h : π.reachable_from n s) : π.prev.reachable_in n s := by
  have := π.reachable_from_length h
  simp [reachable_in, this] at h ⊢
  simp [π.reachable_from_first h]

noncomputable def RProb {n : ℕ} {s : State} (𝒮 : M.RScheduler n s) (π : M.Path) (h : π.reachable_from n s) : ENNReal :=
  ∏ (i : Fin (∎|π| - 1)), M.P π[i] (𝒮 ⟨π[i], π.reachable_from_mem n s h ⟨i, by omega⟩⟩) π[i.succ]

noncomputable def Cost (cost : State → ENNReal) : ENNReal := π.states.map cost |>.sum

theorem Cost_eq_Cost_tail (cost : State → ENNReal) (h : 1 < ∎|π|) : π.Cost cost = cost π.first + π.tail.Cost cost := by
  simp [Path.Cost, Path.tail, h, tail_length]
  have : π.states ≠ [] := π.nonempty
  rw [←List.headI_add_tail_sum_of_ne_nil _ (by simp [this])]
  simp [List.headI, this]
  split
  · simp_all
  · simp_all only [ne_eq, List.tail_cons]
    rename_i heq
    congr
    let ⟨s, L, h₁, h₂, _⟩ := List.map_eq_cons_iff.mp heq
    subst_eqs
    have : π.first = s := by simp [first_eq_states_getElem_zero, h₁]
    simp [this]

def cyl (π : M.Path) (n : ℕ) : Finset M.Path := Finset.range n |>.biUnion (fun i ↦ M.Paths_n₀ π.first i |>.filter (fun π' ↦ π.isPrefixOf π'))

theorem cyl_take {π₀ : M.Path} {n : ℕ} (h : π ∈ π₀.cyl n) (i : ℕ) (hi : ∎|π₀| ≤ i) : π.take i ∈ π₀.cyl n := by
  simp_all [cyl, Paths_n₀_iff, and_assoc]
  obtain ⟨a, h₁, h₂, h₃, h₄⟩ := h
  use ∎|π.take i| - 1
  simp_all
  have := π.prefixes_length_le π₀ (by simp_all [Path.prefixes_iff_isPrefixOf])
  have := π.length_pos
  have : ∎|π| = a + 1 := by omega
  have : min (i + 1) (a + 1) - 1 = min i a := by omega
  simp_all [isPrefixOf]
  simp [take]
  apply List.prefix_take_iff.mpr
  simp_all
  omega

instance reachable_from.DecidablePred [M.FiniteBranching] (n : ℕ) (s : State) : DecidablePred fun (π : M.Path) ↦ π.reachable_from n s :=
  fun _ ↦ instDecidableAnd

instance reachable_from.Fintype [M.FiniteBranching] (n : ℕ) (s : State) : Fintype {π : M.Path // π.reachable_from n s} where
  elems := M.Paths_n₀ s n |>.subtype _
  complete := by simp [Path.Paths_n₀_iff_reachable_from]

end Path

def Pathsable_list [M.FiniteBranching] (n : ℕ) (s : State) := {π : M.Path // π.first = s ∧ ∎|π| ≤ n + 1}
theorem Pathsable_list_eq [M.FiniteBranching] (n : ℕ) (s : State) : M.Pathsable_list n s = (Finset.range (n + 1)).biUnion (M.Paths_n₀ s) := by
  simp [Pathsable_list, Paths_n₀_iff]
  congr with π
  have := π.length_pos
  constructor
  · intro ⟨h₁, h₂⟩
    simp_all only [and_true, gt_iff_lt]
    omega
  · intro ⟨h₁, h₂⟩
    simp_all only [true_and, ge_iff_le]
    omega

instance Pathsable_list.instFintype [M.FiniteBranching] (n : ℕ) (s : State) : Fintype (M.Pathsable_list n s) := by
  simp [Pathsable_list_eq]
  apply Fintype.ofFinset ((Finset.range (n + 1)).biUnion (M.Paths_n₀ s ·))
  simp
  intro π
  rfl

def Pathsable_list.cast_eq [M.FiniteBranching] {n : ℕ} {s₀ : State} (l : M.Pathsable_list n s₀) (m : ℕ) (s₀' : State) (h₁ : s₀ = s₀') (h₂ : n = m) : M.Pathsable_list m s₀' :=
  ⟨l.val, by have := l.prop ; simp_all⟩

def Pathsable_list.extended {M : MDP State Act} [M.FiniteBranching] {n : ℕ} {s₀ : State} (l : M.Pathsable_list n s₀) (m : ℕ) (h : n ≤ m) : M.Pathsable_list m s₀ := by
  use l.val
  have := l.prop
  simp_all
  omega

def Pathsable_list.take {M : MDP State Act} [M.FiniteBranching] {n : ℕ} {s₀ : State} (l : M.Pathsable_list n s₀) (m : ℕ) : M.Pathsable_list n s₀ := by
  use l.val.take m
  have := l.prop
  simp_all

def RScheduler' [M.FiniteBranching] (n : ℕ) (s : State) := (π : M.Pathsable_list n s) → M.act₀ π.val.last

namespace RScheduler'

variable {M : MDP State Act}
variable [M.FiniteBranching]

instance instNonempty (n : ℕ) (s : State) : Nonempty (M.RScheduler' n s) := Nonempty.intro (fun x ↦ M.act₀_default x.val.last)
instance instFinite (n : ℕ) (s : State) : Finite (M.RScheduler' n s) :=
  Pi.finite
instance instFintype (n : ℕ) (s : State) : Fintype (M.RScheduler' n s) := by
  simp [RScheduler']
  have : DecidableEq (M.Pathsable_list n s) := Subtype.instDecidableEq
  exact Pi.fintype

def elems (n : ℕ) (s : State) : Finset (M.RScheduler' n s) := (instFintype n s).elems
def elems_nonempty (n : ℕ) (s : State) : (elems (M:=M) n s).Nonempty := by
  have 𝒮 := instNonempty (M:=M) n s
  use 𝒮.some, (instFintype n s).complete 𝒮.some

def inf {γ : Type*} [SemilatticeInf γ] {n : ℕ} {s : State} (f : M.RScheduler' n s → γ) := Finset.inf' (RScheduler'.elems n s) (RScheduler'.elems_nonempty n s) f

noncomputable def inf_choose {n : ℕ} {s : State} (f : M.RScheduler' n s → ENNReal) : M.RScheduler' n s :=
  (Finset.exists_mem_eq_inf' (elems_nonempty n s) f).choose

noncomputable def inf_choose_spec {n : ℕ} {s : State} (f : M.RScheduler' n s → ENNReal) : (inf_choose f) ∈ elems n s ∧ (elems n s).inf' (elems_nonempty n s) f = f (inf_choose f) :=
  (Finset.exists_mem_eq_inf' (elems_nonempty n s) f).choose_spec

theorem inf_eq_iInf {γ : Type*} [CompleteLattice γ] {n : ℕ} {s : State} (f : M.RScheduler' n s → γ) : ⨅ 𝒮, f 𝒮 = inf f := by
  simp only [inf, elems, Finset.inf'_eq_inf, Finset.inf_eq_iInf, Fintype.complete, iInf_pos]

theorem inf_const_add {n : ℕ} {s : State} (f : M.RScheduler' n s → ENNReal) (x : ENNReal) : inf (fun 𝒮 ↦ x + f 𝒮) = x + inf f := by
  simp [inf, elems]
  simp [Finset.inf'_eq_inf, Finset.inf_eq_iInf]
  conv => left ; arg 1 ; ext 𝒮 ; rw [add_comm x]
  simp [←ENNReal.iInf_add]
  rw [add_comm x]

theorem inf_const_mul {n : ℕ} {s : State} (f : M.RScheduler' n s → ENNReal) (x : ENNReal) : inf (fun 𝒮 ↦ x * f 𝒮) = x * inf f := by
  simp [inf, elems]
  by_cases hx : x ≠ ⊤
  · simp [Finset.inf'_eq_inf, Finset.inf_eq_iInf, Fintype.complete]
    conv => left ; arg 1 ; ext 𝒮 ; rw [mul_comm x]
    rw [mul_comm x]
    symm
    apply ENNReal.iInf_mul
    simp_all
  · simp at hx
    simp only [hx]
    by_cases h0 : (Fintype.elems : Finset (M.RScheduler' n s)).inf' (elems_nonempty n s) f = 0
    · simp [h0]
      have ⟨x0, hx0⟩ : ∃ x ∈ (Fintype.elems : Finset (M.RScheduler' n s)), f x = 0 := by
        refine Finset.inf_eq_bot_iff.mp ?_
        simp [Finset.inf'_eq_inf] at h0
        exact h0
      apply le_antisymm
      · apply Finset.inf'_le_of_le (fun x ↦ ⊤ * f x) hx0.left
        simp only [mul_zero, le_refl, hx0]
      · simp
    · simp [h0]
      have : ∀ x ∈ (Fintype.elems : Finset (M.RScheduler' n s)), f x ≠ 0 := by
        simp [Finset.inf'_eq_inf] at h0
        simp [Fintype.complete]
        have := (Finset.inf_eq_bot_iff (s:=(Fintype.elems : Finset (M.RScheduler' n s))) (f:=f)).not.mp
        simp [Fintype.complete] at this
        exact this h0
      simp_all only [ne_eq, not_false_eq_true, ENNReal.top_mul, Finset.inf'_const]

noncomputable def Path_between (s s' : State) (n : ℕ) (h : s' ∈ M.Pathsable_eq n s) : M.Path :=
  (M.Paths_n₀ s n).toList.find? (fun π ↦ π.last = s') |>.get (by
    apply List.find?_if_mem
    simp only [Finset.mem_toList, decide_eq_true_eq]
    induction n generalizing s' with
    | zero => simp_all [Paths_n₀]
    | succ n ih =>
      simp_all only [Pathsable_eq, Finset.mem_biUnion, Paths_n₀]
      obtain ⟨s'', hs''₁, hs''₂⟩ := h
      let ⟨π, hπ⟩ := ih s'' hs''₁
      use π.extend s' (by simp_all)
      simp only [Path.extend_last, and_true]
      use π
      simp_all [Path.extend_mem_succs_univ₀])

@[simp]
theorem Path_between_length {s s' : State} {n : ℕ} {hs : s' ∈ M.Pathsable_eq n s} : ∎|Path_between s s' n hs| = n + 1 := by
  set π := Path_between s s' n hs with h
  simp [Path_between] at h
  have : List.find? (fun π ↦ decide (π.last = s')) (M.Paths_n₀ s n).toList = some π := by
    simp_all only [Option.some_get]
  have := List.mem_of_find?_eq_some this
  simp at this
  exact M.Paths_n₀_length_eq_n s n π this

@[simp]
theorem Path_between_first {s s' : State} {n : ℕ} {hs : s' ∈ M.Pathsable_eq n s} : (Path_between s s' n hs).first = s := by
  set π := Path_between s s' n hs with h
  simp [Path_between] at h
  have : List.find? (fun π ↦ decide (π.last = s')) (M.Paths_n₀ s n).toList = some π := by
    simp_all only [Option.some_get]
  have := List.mem_of_find?_eq_some this
  simp at this
  exact M.Paths_n₀_first_eq_first s n π this

@[simp]
theorem Path_between_last {s s' : State} {n : ℕ} {hs : s' ∈ M.Pathsable_eq n s} : (Path_between s s' n hs).last = s' := by
  set π := Path_between s s' n hs with h
  simp [Path_between] at h
  have : List.find? (fun π ↦ decide (π.last = s')) (M.Paths_n₀ s n).toList = some π := by
    simp_all only [Option.some_get]
  have := List.find?_some this
  simp at this
  exact this

theorem Path_between_imp {s s' : State} {n : ℕ} {hs : s' ∈ M.Pathsable_eq n s} : ∎|Path_between s s' n hs| = n + 1 ∧ (Path_between s s' n hs).first = s ∧ (Path_between s s' n hs).last = s' := by
  simp only [Path_between_length, Path_between_first, Path_between_last, and_self]

/-- extends the domain of the scheduler one step backwards, where the first state is ignored during scheduling -/
noncomputable def cast_s_succ' {n : ℕ} {s₀ : State} (𝒮 : M.RScheduler' n s₀) (s₀' : State) : M.RScheduler' (n + 1) s₀' :=
  fun ⟨π, hπ⟩ ↦
    if h : π.tail.first = s₀ then
      ⟨𝒮 ⟨π.tail, by simp_all⟩, by
        have := (𝒮 ⟨π.tail, by simp_all⟩).prop
        simp_all⟩
    else
      M.act₀_default π.last

end RScheduler'

section Paths_n₀

variable {M : MDP State Act}
variable [M.FiniteBranching]

noncomputable def succs_Paths_n₀ (n : ℕ) (s₀ : State) :=
  (M.succs_univ₀ s₀).attach.biUnion (fun ⟨s', hs'⟩ ↦ (M.Paths_n₀ s' n).attach.map ⟨fun ⟨π, hπ⟩ ↦ π.prepend s₀ (π.asdf n s' hπ hs'), fun _ _ ↦ SetCoe.ext ∘ Path.preprend_injective _ _ s₀⟩)

theorem Path.succs_Paths_n₀_imp_rechable_from (π : M.Path) (n : ℕ) (s : State) (hπ : π ∈ M.succs_Paths_n₀ n s) : π.reachable_from (n + 1) s := by
  apply π.reachable_from_iff.mp
  simp [succs_Paths_n₀] at hπ
  have ⟨s', hs', π', hπ'₁, _, hπ'₃⟩ := hπ
  rw [←hπ'₃]
  simp
  exact M.Paths_n₀_length_eq_n s' n π' hπ'₁

theorem Paths_n₀_succ (n : ℕ) (s₀ : State) : M.Paths_n₀ s₀ (n + 1) = succs_Paths_n₀ n s₀
:= by
  ext π
  constructor <;> intro h
  · simp only [succs_Paths_n₀, Finset.mem_biUnion, Finset.mem_attach, Finset.mem_map,
    Function.Embedding.coeFn_mk, Subtype.exists, Set.mem_def, Finset.mem_val, true_and]
    simp only [Path.Paths_n₀_iff_reachable_from] at h
    have ⟨s', hs', hs''⟩ := π.reachable_from_succ_left _ _ h
    use s', hs', π.tail
    apply Exists.intro (π.tail.reachable_from_imp_Paths_n₀ n s' hs'')
    constructor
    · apply Finset.mem_attach
    · obtain ⟨h₁, h₂⟩ := h
      simp only [← h₂]
      rw [Path.prepend_tail]
      omega
  · exact π.reachable_from_imp_Paths_n₀ (n + 1) s₀ <| π.succs_Paths_n₀_imp_rechable_from _ _ h

end Paths_n₀

def Costs (_M : MDP State Act) := State → ENNReal

section ER

variable {M : MDP State Act}
variable [M.FiniteBranching]

def Path.states_reachable (π : M.Path) : M.Pathsable_list (∎|π| - 1) π.first := ⟨π, by simp only [length_pred_add, le_refl, and_self]⟩

noncomputable def Path.RProb' {n : ℕ} {s : State} (𝒮 : M.RScheduler' n s) (π : M.Path) (h : π.reachable_from n s) : ENNReal :=
  ∏ (i : Fin (∎|π| - 1)), M.P π[i] (𝒮 <| (π.states_reachable.take i).cast_eq _ _ _ (π.reachable_from_first h) (by have := π.reachable_from_length h ; omega)) π[i.succ]

noncomputable def RScheduler'.ext {M : MDP State Act} [M.FiniteBranching] (𝒮 : M.RScheduler' n s₀) : M.Scheduler' := fun π' ↦
  if h₁ : ∃ m ≤ n, ∃ π ∈ M.Paths_n₀ s₀ m, π' = π then
    have h' : π'.first = s₀ ∧ π'.states.length ≤ n + 1 := by
      obtain ⟨m, hm, ⟨π, hπ, hπ'⟩⟩ := h₁
      simp only [Paths_n₀_iff] at hπ
      simp_all only [true_and]
      omega
    ⟨𝒮 ⟨π', h'⟩, by
      obtain ⟨m, _, ⟨π, hπ, hπ'⟩⟩ := h₁
      simp only [Paths_n₀_iff] at hπ
      have := (𝒮 ⟨π', h'⟩).prop
      simp_all only [Path.last, M.act₀_mem_iff_act_mem]⟩
  else
    M.act_default π'.last

theorem RScheduler'.mem_act₀ (𝒮 : M.RScheduler' n s₀) (l : M.Pathsable_list n s₀) : (𝒮 l).val ∈ M.act₀ l.val.last := by
  simp

theorem RScheduler'.mem_act₀_if_last_eq (𝒮 : M.RScheduler' n s₀) (l : M.Pathsable_list n s₀) (s' : State) (h : l.val.last = s') : (𝒮 l).val ∈ M.act₀ s' := by
  rw [←h]
  exact mem_act₀ 𝒮 l

theorem RScheduler'.ext_eq (𝒮 : M.RScheduler' n s₀) : ∀ l, 𝒮 l = ⟨𝒮.ext l.val, by
  have := (𝒮.ext l.val).prop
  simp [←M.act₀_iff_act] at this
  exact this⟩
:= by
  intro l
  unfold ext
  split_ifs with h
  · simp_all only
    refine SetCoe.ext ?_
    simp [ne_eq, Path.states]
    exact rfl
  · absurd h
    simp_all only [exists_eq_right', not_exists, not_and]
    have := l.prop
    use ∎|l.val| - 1, (by omega)
    simp_all [Paths_n₀_iff]

theorem RScheduler'.ext_eq' (𝒮 : M.RScheduler' n s₀) : ∀ l, (𝒮 l).val = (𝒮.ext l.val).val
:= by
  intro s
  have := 𝒮.ext_eq s
  simp [this]

def Scheduler.ext {M : MDP State Act} (𝒮 : M.Scheduler) : M.Scheduler' := fun s ↦ 𝒮 s.last

def Scheduler.ext_eq {M : MDP State Act} (𝒮 : M.Scheduler) (π : M.Path) : π.Prob 𝒮 = π.Prob' 𝒮.ext := by
  unfold ext
  simp [Path.Prob', Path.Prob]
  congr
  ext i
  have : π[↑i] = (List.take (↑i + 1) π.states).getLast (by simp [π.nonempty]) := by
    simp [@List.take_getLast _ π.states π.nonempty ⟨i.val + 1, by have := i.isLt ; omega⟩ (by simp)]
  congr
  ext α
  exact Eq.to_iff (congrFun (congrArg Membership.mem (congrArg M.act this)) α)

noncomputable def RScheduler.ext {M : MDP State Act} [M.FiniteBranching] (𝒮 : M.RScheduler n s₀) : M.Scheduler := fun s ↦
  if h₁ : s ∈ M.Pathsable_le n s₀ then
    ⟨𝒮 ⟨s, h₁⟩, by exact (M.act₀_mem_iff_act_mem s _).mp (𝒮 ⟨s, h₁⟩).prop⟩
  else
    M.act_default s

theorem RScheduler.ext_eq (𝒮 : M.RScheduler n s₀) : ∀ s, 𝒮 s = ⟨𝒮.ext s, by
  have := (𝒮.ext s).prop
  simp [←M.act₀_iff_act] at this
  exact this⟩
:= by
  intro s
  unfold ext
  split_ifs with h
  · simp_all only
  · absurd h
    simp_all only [Finset.coe_mem, not_true_eq_false]

theorem RScheduler.ext_eq' (𝒮 : M.RScheduler n s₀) : ∀ s, (𝒮 s).val = (𝒮.ext s).val
:= by
  intro s
  have := 𝒮.ext_eq s
  simp [this]

theorem Pathsable_list_eq_val {n : ℕ} {s₀ : State} (l : M.Pathsable_list n s₀) (π : M.Path) (h : l.val.states = π.states) : l.val = π := by
  exact Path.eq_states l.val π h

@[simp]
theorem Path.getElem_succ_mem_succs_univ₀ (π : M.Path) (i : ℕ) (h : i + 1 < ∎|π|) : π[i + 1] ∈ M.succs_univ₀ π[i] := by
  have := π.property ⟨i, by omega⟩
  simp_all only [List.get_eq_getElem, MDP.succs_univ_eq_succs_univ₀, Nat.succ_eq_add_one,
    Fin.succ_mk, Finset.mem_coe]
  exact this

@[simp]
theorem Path.getElem_1_mem_succs_univ₀ (π : M.Path) (h : 1 < ∎|π|) : π[1] ∈ M.succs_univ₀ π.first := by
  have := π.getElem_succ_mem_succs_univ₀ 0 (by omega)
  simp_all [first_eq_getElem_zero]

@[simp]
theorem Path.states_getElem_1_mem_succs_univ₀ (π : M.Path) (h : 1 < ∎|π|) : π.states[1] ∈ M.succs_univ₀ π.first := by
  have := π.getElem_succ_mem_succs_univ₀ 0 (by omega)
  simp_all [first_eq_getElem_zero]


theorem Path.RProb'_succ {n : ℕ} {s : State} (𝒮 : M.RScheduler' (n + 1) s) (π : M.Path) (h : π.reachable_from (n + 1) s) (h' : 0 < n) :
  π.RProb' 𝒮 h =
    have := π.reachable_from_length h
    ∏ (i : Fin ((∎|π| - 2) + 1)), M.P (π[i.val]'(by omega)) (𝒮 <| (π.states_reachable.take i).cast_eq _ _ _ (π.reachable_from_first h) (by have := π.reachable_from_length h ; omega)) π[i.succ]
:= by
  have := π.reachable_from_length h
  have : 1 < ∎|π| := by
    simp_all
  have : 2 < ∎|π| := by
    simp_all
  simp
  simp [RProb']
  congr
  · simp_all
  · simp_all
  · simp_all
  · simp_all
    refine (Fin.heq_fun_iff ?h.e_5.h).mpr ?h.e_5.a
    · simp_all
    · simp_all

def RScheduler'.specialize {M : MDP State Act} [M.FiniteBranching] {n : ℕ} {s₀ : State} (𝒮 : M.RScheduler' (n + 1) s₀) (s₀' : M.succs_univ₀ s₀) : M.RScheduler' n s₀' :=
  fun ⟨π, hπ⟩ ↦ ⟨𝒮 ⟨π.prepend s₀ (by simp_all), by simp ; omega⟩, by
    simp
    have := (𝒮 ⟨π.prepend s₀ (by simp_all), by simp ; omega⟩).prop
    simp_all⟩

theorem Path.RProb'_succ_tail {n : ℕ} {s : State} (𝒮 : M.RScheduler' (n + 1) s) (π : M.Path) (h : π.reachable_from (n + 1) s) :
  π.RProb' 𝒮 h =
    have := π.reachable_from_length h
    M.P
      π[0]
      (𝒮 <| (π.states_reachable.take 0).cast_eq _ _ _ (π.reachable_from_first h) (by omega))
      π[1]
    * π.tail.RProb' (𝒮.specialize ⟨π[1], by simp [←π.reachable_from_first h]⟩) (π.reachable_from_tail_first _ _ h)
:= by
  by_cases h' : 0 < n
  · simp [Path.RProb'_succ _ _ _ h']
    simp [←Fin.prod_ofFn]
    simp [RProb', ←Fin.prod_ofFn]
    congr! 1
    congr! 1
    have len_pos : 1 < π.states.length := by have := π.reachable_from_length h ; omega
    have π_tail₁ : ∀ x : Fin (max 1 (π.states.length - 1) - 1), π.tail[x.val]'(by simp_all ; omega) = (π[x.val + 1]'(by omega)) := by
      intro i
      simp only [getElem, get, tail]
      simp [len_pos]
    have π_tail₂ : ∀ x : Fin (max 1 (π.states.length - 1) - 1), π.tail[x.val + 1]'(by simp_all ; omega) = (π[x.val + 1 + 1]'(by omega)) := by
      intro i
      simp only [getElem, get, tail]
      simp [len_pos]
    simp_all
    simp [Pathsable_list.cast_eq]
    simp [Path.states_reachable, Pathsable_list.take]
    simp [RScheduler'.specialize]
    have := (π.reachable_from_first h).symm
    have : ∀ (i : Fin (max 1 (π.states.length - 1) - 1)), (π.tail.take ↑i).prepend s (by
      simp only [this, π.first_eq_getElem_zero, getElem, MDP.succs_univ_eq_succs_univ₀,
        take_first_eq_first, π.tail_first_eq_get_one (by omega), Finset.mem_coe]
      have := π.property ⟨0, by omega⟩
      simp at this
      exact this
      ) = π.take (i + 1)
    := by
      intro i
      simp [this]
      apply eq_states
      simp [take, prepend, tail, first, List.head_eq_get, len_pos]
      apply List.ext_getElem
      · have := π.reachable_from_length h
        simp
        omega
      · simp
        intro i' h₁ h₂
        rcases i' with i' | i'
        · simp
        · simp
    simp [RScheduler'.ext_eq]
    conv =>
      right
      arg 1
      ext i
      rw [this i]
    congr! 1
    · omega
    · have : (π.states.length - 2) = (max 1 (π.states.length - 1) - 1) := by omega
      apply (Fin.heq_fun_iff this).mpr
      simp
  · have : n = 0 := by omega
    have : ∎|π| = 2 := by
      have := π.reachable_from_length h
      simp_all
    have : ∎|π.tail| = 1 := by simp_all
    simp_all
    simp [RProb']
    simp [RScheduler'.ext_eq]
    simp [Pathsable_list.cast_eq]
    simp [Path.states_reachable, Pathsable_list.take]
    rw [Finset.prod_eq_single ⟨0, by omega⟩]
    · simp
      conv =>
        left
        rw [←mul_one (M.P _ _ _)]
      congr
      refine Eq.symm (Finset.prod_eq_one ?_)
      simp_all
      intro ⟨x, hx⟩
      absurd hx
      simp_all
    · intro ⟨b, hb_lt⟩ _ hb'
      simp_all
      absurd hb'
      omega
    · simp_all

theorem Path.RProb'_eq (𝒮 : M.RScheduler' n s₀) (π : M.Path) (h : π.reachable_from n s₀) : π.RProb' 𝒮 h = π.Prob' 𝒮.ext := by
  simp [RProb', Prob, RScheduler'.ext_eq']
  congr

def Scheduler'.constrain (𝒮 : M.Scheduler') {n : ℕ} {s : State} : M.RScheduler' n s := fun xs ↦ ⟨𝒮 xs.val, by simp [MDP.act₀_mem_iff_act_mem]⟩

theorem RScheduler'.ext_constrain {n : ℕ} {s : State} (𝒮 : M.RScheduler' n s) : 𝒮.ext.constrain = 𝒮 := by
  funext l
  simp [ext, Scheduler'.constrain]
  split_ifs with h
  · simp_all
    congr
  · simp at h
    absurd h (∎|l.val| - 1) (by have := l.prop ; omega)
    simp [MDP.Paths_n₀_iff]
    have ⟨h₁, _⟩ := l.prop
    simp_all

theorem Path.RProb'_eq' (𝒮 : M.Scheduler') (π : M.Path) (h : π.reachable_from n s₀) : π.Prob' 𝒮 = π.RProb' 𝒮.constrain h := by
  simp [RProb', Prob, RScheduler'.ext_eq', Scheduler'.constrain]
  congr

def Scheduler.constrain (𝒮 : M.Scheduler) {n : ℕ} {s : State} : M.RScheduler n s := fun s' ↦ ⟨𝒮 s', by simp [MDP.act₀_mem_iff_act_mem]⟩

theorem RScheduler.ext_constrain {n : ℕ} {s : State} (𝒮 : M.RScheduler n s) : 𝒮.ext.constrain = 𝒮 := by
  funext l
  simp [ext, Scheduler.constrain]

theorem Path.RProb_eq (𝒮 : M.RScheduler n s₀) (π : M.Path) (h : π.reachable_from n s₀) : π.RProb 𝒮 h = π.Prob 𝒮.ext := by
  simp [RProb, Prob, RScheduler.ext_eq]

theorem Path.RProb_eq' (𝒮 : M.Scheduler) (π : M.Path) (h : π.reachable_from n s₀) : π.Prob 𝒮 = π.RProb 𝒮.constrain h := by
  simp [RProb, Prob, RScheduler.ext_eq, Scheduler.constrain]

noncomputable def EC₀ (cost : M.Costs) (n : ℕ) (s : State) (𝒮 : M.RScheduler n s) :=
  ∑ π ∈ (M.Paths_n₀ s n).attach, π.val.RProb 𝒮 (π.val.Paths_n₀_iff_reachable_from.mp π.prop) * π.val.Cost cost

noncomputable def EC₀' (cost : M.Costs) (n : ℕ) (s : State) (𝒮 : M.RScheduler' n s) :=
  ∑ π ∈ (M.Paths_n₀ s n).attach, π.val.RProb' 𝒮 (π.val.Paths_n₀_iff_reachable_from.mp π.prop) * π.val.Cost cost

noncomputable def EC (cost : M.Costs) (n : ℕ) (s : State) (𝒮 : M.Scheduler) :=
  ∑ π ∈ M.Paths_n₀ s n, π.Prob 𝒮 * π.Cost cost

noncomputable def EC' (cost : M.Costs) (n : ℕ) (s : State) (𝒮 : M.Scheduler') :=
  ∑ π ∈ M.Paths_n₀ s n, π.Prob' 𝒮 * π.Cost cost

theorem sum_Paths_n₀_RProb_Cost_eq_Prob_Cost (cost : M.Costs) (s : State) (n : ℕ) (𝒮 : M.Scheduler) :
    ∑ π ∈ (M.Paths_n₀ s n).attach, π.val.RProb 𝒮.constrain (π.val.Paths_n₀_imp_reachable_from n s π.prop) * π.val.Cost cost
  = ∑ π ∈ M.Paths_n₀ s n, π.Prob 𝒮 * π.Cost cost
:= by
  conv => right ; rw [←Finset.sum_attach]
  congr

theorem sum_Paths_n₀_RProb'_Cost_eq_Prob'_Cost (cost : M.Costs) (s : State) (n : ℕ) (𝒮 : M.Scheduler') :
    ∑ π ∈ (M.Paths_n₀ s n).attach, π.val.RProb' 𝒮.constrain (π.val.Paths_n₀_imp_reachable_from n s π.prop) * π.val.Cost cost
  = ∑ π ∈ M.Paths_n₀ s n, π.Prob' 𝒮 * π.Cost cost
:= by
  conv => right ; rw [←Finset.sum_attach]
  congr

theorem Scheduler'_constrain_inf {n : ℕ} {s : State} (f : M.RScheduler' n s → ENNReal) :
  ⨅ (𝒮 : M.Scheduler'), f 𝒮.constrain = RScheduler'.inf f
:= by
  simp only [RScheduler'.inf, RScheduler'.elems, Finset.inf'_eq_inf, Finset.inf_eq_iInf,
    Fintype.complete, iInf_pos]
  refine Function.Surjective.iInf_comp ?hf f
  intro 𝒮
  simp
  use 𝒮.ext
  simp [RScheduler'.ext_constrain]

theorem Scheduler_constrain_inf {n : ℕ} {s : State} (f : M.RScheduler n s → ENNReal) :
  ⨅ (𝒮 : M.Scheduler), f 𝒮.constrain = RScheduler.inf f
:= by
  simp only [RScheduler.inf, RScheduler.elems, Finset.inf'_eq_inf, Finset.inf_eq_iInf,
    Fintype.complete, iInf_pos]
  refine Function.Surjective.iInf_comp ?hf f
  intro 𝒮
  simp
  use 𝒮.ext
  simp [RScheduler.ext_constrain]

theorem sup_inf_EC'_eq_sup_inf_EC₀' (cost : M.Costs) (s : State) : ⨆ n, ⨅ 𝒮, M.EC' cost n s 𝒮 = ⨆ n, RScheduler'.inf (M.EC₀' cost n s) := by
  simp only [EC', ← sum_Paths_n₀_RProb'_Cost_eq_Prob'_Cost]
  unfold EC₀'
  congr with n
  rw [M.Scheduler'_constrain_inf (fun 𝒮 ↦ ∑ π ∈ (M.Paths_n₀ s n).attach, π.val.RProb' 𝒮 (π.val.Paths_n₀_imp_reachable_from n s π.prop) * π.val.Cost cost)]

theorem sup_inf_EC_eq_sup_inf_EC₀ (cost : M.Costs) : ⨆ n, ⨅ 𝒮, M.EC cost n s 𝒮 = ⨆ n, RScheduler.inf (M.EC₀ cost n s) := by
  simp only [EC, ← sum_Paths_n₀_RProb_Cost_eq_Prob_Cost]
  unfold EC₀
  congr with n
  rw [M.Scheduler_constrain_inf (fun 𝒮 ↦ ∑ π ∈ (M.Paths_n₀ s n).attach, π.val.RProb 𝒮 (π.val.Paths_n₀_imp_reachable_from n s π.prop) * π.val.Cost cost)]

-- NOTE: Alternative more general definitions. Might be useful later

-- def Sch (M : MDP State Act) := (π : M.Path) → M.act π.last

-- class Sch.Memoryless (𝒮 : M.Sch) where
--   prop : ∀ π, 𝒮 π = 𝒮 {π.last}

-- abbrev Sch' (M : MDP State Act) := { 𝒮 : M.Sch // ∃ _ : 𝒮.Memoryless, True }

-- @[simp]
-- theorem Sch.Memoryless_take_last (𝒮 : M.Sch) [inst : 𝒮.Memoryless] (π : M.Path) (i : Fin (∎|π| - 1)) : 𝒮 (π.take i) = ⟨𝒮 {π[i]}, by simp [Path.take_last_eq_get']⟩ := by
--   rw [inst.prop (π.take i)]
--   apply SetCoe.ext
--   simp only [Fin.getElem_fin, Path.getElem_eq_states_getElem']
--   congr! 6 <;> simp [Path.take_last_eq_get']

-- noncomputable def Path.P (π : M.Path) (𝒮 : M.Sch) : ENNReal := ∏ (i : Fin (∎|π| - 1)), M.P π[i] (𝒮 (π.take i)) π[i.succ]

-- theorem Path.P_Memoryless (π : M.Path) (𝒮 : M.Sch) [𝒮.Memoryless] : π.P 𝒮 = ∏ (i : Fin (∎|π| - 1)), M.P π[i] (𝒮 {π[i]}) π[i.succ] := by
--   simp [P]

-- theorem Path.P'_Memoryless (π : M.Path) (𝒮 : M.Sch) [𝒮.Memoryless] : ∏ (i : Fin (∎|π| - 1)), M.P π[i] (𝒮 (π.take i)) π[i.succ] = ∏ (i : Fin (∎|π| - 1)), M.P π[i] (𝒮 {π[i]}) π[i.succ] := by
--   simp

-- noncomputable def Sch.EC (cost : M.Costs) (n : ℕ) (s : State) (𝒮 : M.Sch) :=
--   ∑ π ∈ M.Paths_n₀ s n, π.P 𝒮 * π.Cost cost

-- example (cost : M.Costs) (n : ℕ) (s : State) (𝒮 : M.Sch) : 𝒮.EC cost n s = 0 :=
--   sorry
