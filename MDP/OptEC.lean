import Init.Data.List.Lemmas
import MDP.Bellman
import MDP.Paths.Sets

-- TODO: remove this
set_option linter.unusedSectionVars false

theorem Finset.sum_biUnion_attach {α β : Type*} [DecidableEq β] {S : Finset α} {f : S → Finset β} (hf' : DisjointOn f) (g : { x : β // ∃ a : S, x ∈ f a } → ENNReal) : ∑ x ∈ (S.attach.biUnion f).attach, g ⟨x, by
  have := x.prop
  simp only [Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists] at this
  apply SetCoe.exists.mpr this
  ⟩ = ∑ x ∈ S.attach, ∑ y ∈ (f x).attach, g ⟨y, by
  use x, Finset.coe_mem y⟩
:= by
  have := Finset.sum_biUnion (s:=S.attach) (f:=g) (t:=fun x ↦
    (f x).attach.map ⟨fun y ↦ (⟨y.val, by use x, Finset.coe_mem y⟩ : { x // ∃ a : S, x ∈ f a }), by
      intro _ _ h
      simp at h
      exact SetCoe.ext h⟩)
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk] at this
  rw [←this]
  · symm
    fapply Finset.sum_nbij (fun ⟨x, hx⟩ ↦ ⟨x, by simp ; exact Subtype.exists'.mpr hx⟩)
    · simp_all
    · simp_all only [Finset.coe_biUnion, Finset.mem_coe, Finset.mem_attach, Finset.coe_map,
      Function.Embedding.coeFn_mk, Set.iUnion_true]
      intro ⟨x, hx⟩ _
      simp_all
    · simp_all only [Finset.coe_biUnion, Finset.mem_coe, Finset.mem_attach, Finset.coe_map,
      Function.Embedding.coeFn_mk, Set.iUnion_true]
      intro ⟨x, hx⟩ _
      simp_all only [Finset.mem_coe, Finset.mem_attach, Set.mem_image, Set.mem_iUnion, true_and,
        Subtype.exists, Subtype.mk.injEq, exists_prop, exists_eq_right, exists_and_left,
        and_self_left]
      simp only [Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists] at hx
      exact hx
    · simp_all
  · intro x₁ _ x₂ _ h
    have f_disjoint := hf' x₁ x₂ h
    intro S hS₁ hS₂ y h'
    simp_all only [Finset.mem_coe, Finset.mem_attach, ne_eq, Finset.le_eq_subset, Finset.bot_eq_empty, Finset.not_mem_empty]
    have h'₁ := hS₁ h'
    have h'₂ := hS₂ h'
    simp at h'₁ h'₂
    obtain ⟨a₁, b₁, h'₁⟩ := h'₁
    obtain ⟨a₂, b₂, h'₂⟩ := h'₂
    absurd Disjoint.forall_ne_finset f_disjoint b₁ b₂
    rw [←h'₂] at h'₁
    simp at h'₁
    assumption

open OmegaCompletePartialOrder

namespace MDP

variable {State : Type*} {Act : Type*}
variable (M : MDP State Act)
variable [DecidableEq State] [DecidableEq Act]
variable [M.FiniteBranching] [Nonempty Act]

theorem sum_Paths_n₀_eq_sum_succs_Paths_n₀ (cost : M.Costs) :
  ∑ π ∈ (M.Paths_n₀ s₀ (n + 1)).attach, π.val.RProb' 𝒮 (π.val.Paths_n₀_imp_reachable_from (n + 1) s₀ π.prop) * π.val.Cost cost
= ∑ π ∈ (M.succs_Paths_n₀ n s₀).attach, π.val.RProb' 𝒮 (π.val.succs_Paths_n₀_imp_rechable_from n s₀ π.prop)  * π.val.Cost cost := by
  congr <;> try rw [M.Paths_n₀_succ n s₀]
  apply Function.hfunext
  · simp only [Paths_n₀_succ]
  · simp only [heq_eq_eq, Subtype.forall, ← Paths_n₀_succ]
    intro π₁ h₁ π₂ h₂ h
    have : π₁ = π₂ := by
      apply (Subtype.heq_iff_coe_eq _).mp h
      simp [Paths_n₀_succ]
    simp [this]

noncomputable def Paths_n₀_by (n : ℕ) (s₀ : State) (s' : M.succs_univ₀ s₀ ) : Finset M.Path :=
  (M.Paths_n₀ s' n).attach.map ⟨
    fun π ↦ π.val.prepend s₀ (by simp only [succs_univ_eq_succs_univ₀, M.Paths_n₀_first_eq_first s' n π π.prop, Subtype.coe_prop]),
    fun _ _ ↦ SetCoe.ext ∘ Path.preprend_injective _ _ s₀⟩

theorem Paths_n₀_by_Paths_n₀ : M.Paths_n₀_by n s₀ s' = ((M.Paths_n₀ s₀ (n + 1)).filter (fun π ↦ (h : 1 < π.states.length) → π[1] = s'.val)) := by
  symm
  simp
  simp [Paths_n₀_by, Paths_n₀_iff]
  ext π
  simp
  simp_all [Paths_n₀_by, Paths_n₀_iff]
  constructor
  · simp_all [Paths_n₀_by, Paths_n₀_iff]
    intro ⟨_, _⟩ _
    subst_eqs
    use π.tail
    have : π.tail ∈ M.Paths_n₀ s' n := by simp_all [Paths_n₀_iff]
    apply Exists.intro this
    constructor
    · apply Finset.mem_attach
    · rw [Path.prepend_tail]
      omega
  · simp_all [Paths_n₀_by, Paths_n₀_iff]
    intros π' h _ _
    subst_eqs
    simp_all
    have : π' ∈ M.Paths_n₀ s' n := h
    simp_all [Paths_n₀_by, Paths_n₀_iff]
    have := π'.length_pos
    omega

theorem Paths_n₀_by_length {n : ℕ} {s₀ : State} {s' : M.succs_univ₀ s₀ } {π : M.Path} (h : π ∈ M.Paths_n₀_by n s₀ s') : ∎|π| = n + 2 := by
  simp only [Paths_n₀_by, Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk, true_and,
    Subtype.exists, Finset.mem_val] at h
  have ⟨π', h₁, _, h₂⟩ := h
  rw [←h₂]
  have := M.Paths_n₀_length_eq_n s' n π' h₁
  simp only [Path.prepend_length, this]

theorem Paths_n₀_by_first {n : ℕ} {s₀ : State} {s' : M.succs_univ₀ s₀ } {π : M.Path} (h : π ∈ M.Paths_n₀_by n s₀ s') : π.first = s₀ := by
  simp only [Paths_n₀_by, Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk, true_and,
    Subtype.exists, Finset.mem_val] at h
  have ⟨π', h₁, _, h₂⟩ := h
  rw [←h₂]
  simp

theorem Paths_n₀_by_second {n : ℕ} {s₀ : State} {s' : M.succs_univ₀ s₀ } {π : M.Path} (h : π ∈ M.Paths_n₀_by n s₀ s') : (π.states[1]'(by have := M.Paths_n₀_by_length h ; omega)) = s' := by
  simp only [Paths_n₀_by, Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk, true_and,
    Subtype.exists, Finset.mem_val] at h
  have ⟨π', h₁, _, h₂⟩ := h
  simp [←h₂]
  exact M.Paths_n₀_first_eq_first s' n π' h₁

theorem Paths_n₀_by_tail_first {n : ℕ} {s₀ : State} {s' : M.succs_univ₀ s₀ } {π : M.Path} (h : π ∈ M.Paths_n₀_by n s₀ s') : π.tail.first = s' := by
  convert M.Paths_n₀_by_second h
  rw [Path.tail_first_eq_get_one _ (by have := M.Paths_n₀_by_length h ; omega)]
  simp

theorem Paths_n₀_by_reachable {n : ℕ} {s₀ : State} {s' : M.succs_univ₀ s₀ } {π : M.Path} (h : π ∈ M.Paths_n₀_by n s₀ s') : π.reachable_from (n + 1) s₀ := by
  apply π.reachable_from_iff.mp
  have := M.Paths_n₀_by_length h
  have := M.Paths_n₀_by_first h
  simp_all

theorem Paths_n₀_by_DisjointOn (n : ℕ) (s₀ : State) : DisjointOn (M.Paths_n₀_by n s₀) := by
  intro s₁ s₂ h
  intro S hS₁ hS₂ π hπ
  simp_all [Paths_n₀_by_Paths_n₀, Paths_n₀_iff]
  have hπ₁ := hS₁ hπ
  have hπ₂ := hS₂ hπ
  simp_all [Paths_n₀_by_Paths_n₀, Paths_n₀_iff]
  absurd hπ₂
  exact Subtype.coe_ne_coe.mpr h

theorem Paths_n₀_by_Prob' {n : ℕ} {s₀ : State} {s' : M.succs_univ₀ s₀ } (𝒮 : M.Scheduler') : ∑ π ∈ M.Paths_n₀_by n s₀ s', π.tail.Prob' 𝒮 = 1 := by
  simp [Paths_n₀_by]
  suffices ∑ π ∈ M.Paths_n₀ s' n, π.Prob' 𝒮 = 1 by
    convert this
    exact Finset.sum_attach (M.Paths_n₀ s' n) (fun π ↦ π.Prob' 𝒮)
  exact M.Paths_n₀_Prob' 𝒮 n

theorem Paths_n₀_by_Prob {n : ℕ} {s₀ : State} {s' : M.succs_univ₀ s₀ } (𝒮 : M.Scheduler) : ∑ π ∈ M.Paths_n₀_by n s₀ s', π.tail.Prob 𝒮 = 1 := by
  simp [Paths_n₀_by]
  suffices ∑ π ∈ M.Paths_n₀ s' n, π.Prob 𝒮 = 1 by
    convert this
    exact Finset.sum_attach (M.Paths_n₀ s' n) (fun π ↦ π.Prob 𝒮)
  exact M.Paths_n₀_Prob 𝒮 n

theorem Fin.zero_mul_prod (n : ℕ) (f : Fin (n + 1) → ENNReal) : ∏ i : Fin (n + 1), f i = f 0 * ∏ i : Fin n, f ⟨i.val + 1, by omega⟩ := by
  simp only [← Fin.prod_ofFn, List.ofFn_succ, Fin.coe_eq_castSucc,
    Fin.coeSucc_eq_succ]
  exact List.prod_cons

theorem Path.take_0_eq_mk_single (π : M.Path) : π.take 0 = {π.first} := by
  simp only [take, zero_add, instSingleton, first, List.head_eq_get, List.get_eq_getElem, mk_single,
    mk.injEq]
  unfold List.take
  split
  · simp_all
  · simp_all [π.nonempty]
  · simp_all [π.nonempty]

theorem RScheduler'.ext_eq'' (s₀ : State) (𝒮 : M.RScheduler' (n + 1) s₀) (s' : M.succs_univ₀ s₀) (π : M.Paths_n₀_by n s₀ s') : (𝒮.ext (Path.mk_single M (π.val.states.head π.val.nonempty))).val = (𝒮.ext ({s₀})) := by
  simp only [RScheduler'.ext]
  have : π.val.states.head (π.val.nonempty) = s₀ := by
    have := M.Paths_n₀_by_first π.prop
    simp_all [Path.first]
  split_ifs with h h'
  · simp_all [Path.instSingleton]
    congr
    simp_all
  · simp_all [Path.instSingleton]
    absurd h' 0 (by omega)
    simp_all [Paths_n₀_iff]
  · simp_all
    absurd h 0 (by omega)
    simp_all [Paths_n₀_iff]
  · simp_all [Path.instSingleton]
    congr
    simp_all

theorem Path.RProb'_Cost_eq_tail (cost : M.Costs) (n : ℕ) (s₀ : State) (𝒮 : M.RScheduler' (n + 1) s₀) (s' : M.succs_univ₀ s₀) (π : M.Paths_n₀_by n s₀ s') :
    π.val.RProb' 𝒮 (by
      have := π.prop
      simp only [Paths_n₀_by, Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists] at this
      obtain ⟨π', hπ, _, hπ'⟩ := this
      symm at hπ'
      simp_all [Path.reachable_from]
      have := M.Paths_n₀_length hπ
      have := π'.length_pos
      omega)
      * π.val.Cost cost
  = M.P s₀ (𝒮 ⟨{s₀}, by simp [Path.instSingleton]⟩) s'.val * π.val.tail.RProb' (𝒮.specialize s') (by
    convert π.val.reachable_from_tail_first _ _ (M.Paths_n₀_by_reachable π.prop)
    rw [←M.Paths_n₀_by_tail_first π.prop]
    have := π.val.tail_first_eq_get_one (by simp_all [M.Paths_n₀_by_length π.prop])
    simp [this])
      * (cost s₀ + π.val.tail.Cost cost)
:= by
  rw [Path.RProb'_succ_tail]
  simp
  congr! 1
  · simp [RScheduler'.ext_eq, Pathsable_list.cast_eq, Path.states_reachable, Pathsable_list.take]
    rw [π.val.take_0_eq_mk_single]
    simp [Path.first, List.head_eq_get]
    congr! 1
    congr! 1
    · congr! 1
      · simp [←M.Paths_n₀_by_first π.prop]
        exact π.val.first_eq_states_getElem_zero.symm
      · apply RScheduler'.ext_eq''
    · simp [←M.Paths_n₀_by_second π.prop]
  · rw [Path.Cost_eq_Cost_tail]
    · congr
      simp [←M.Paths_n₀_by_first π.prop]
    · have := M.Paths_n₀_by_length π.prop
      omega

theorem sum_succs_univ₀_sum_Paths_n₀_by (cost : M.Costs) (n : ℕ) (s₀ : State) (𝒮 : M.RScheduler' (n + 1) s₀) :
    ∑ s' : M.succs_univ₀ s₀, ∑ ⟨π, h⟩ : M.Paths_n₀_by n s₀ s', π.RProb' 𝒮 (M.Paths_n₀_by_reachable h) * π.Cost cost
  = cost s₀ + ∑ s' : M.succs_univ₀ s₀, M.P s₀ (𝒮 ⟨{s₀}, by simp [Path.instSingleton]⟩) s' * ∑ ⟨π, h⟩ : M.Paths_n₀_by n s₀ s', π.tail.RProb' (𝒮.specialize s') (by
    convert π.reachable_from_tail_first _ _ (M.Paths_n₀_by_reachable h)
    simp [M.Paths_n₀_by_second h]) * π.tail.Cost cost
:= by
  simp [Path.RProb'_Cost_eq_tail]
  simp [Path.RProb'_eq]
  conv =>
    left ; arg 2 ; ext s'
    rw [Finset.sum_attach (M.Paths_n₀_by n s₀ s') (fun π ↦ (M.P _ _ _ * π.tail.Prob' _) * (cost s₀ + π.tail.Cost cost))]
  conv =>
    right ; right ; arg 2 ; ext s' ; right
    rw [Finset.sum_attach (M.Paths_n₀_by n s₀ s') (fun π ↦ π.tail.Prob' _ * π.tail.Cost cost)]
  simp [mul_add]
  simp [Finset.sum_add_distrib]
  congr
  · conv =>
      left ; arg 2 ; ext s' ; arg 2 ; ext x
      rw [←mul_comm]
    simp [←Finset.mul_sum]
    conv => right ; rw [←mul_one (cost s₀)]
    congr
    simp [Paths_n₀_by_Prob']
    simp [Finset.sum_attach]
    convert M.succs_univ_P_act₀ s₀ _
  · ext s'
    rw [Finset.mul_sum]
    simp [←mul_assoc]

theorem sum_Paths_n₀_by_tail_eq_sum_Paths_n₀ (cost : M.Costs) (n : ℕ) (s₀ : State) (s' : M.succs_univ₀ s₀) (𝒮 : M.RScheduler' (n + 1) s₀) :
    ∑ ⟨π, h⟩ : M.Paths_n₀_by n s₀ s', π.tail.RProb' (𝒮.specialize s') (by
      simp [Paths_n₀_by] at h
      obtain ⟨π', h, _, h'⟩ := h
      simp [←h']
      exact π'.Paths_n₀_imp_reachable_from n s' h) * π.tail.Cost cost
  = ∑ ⟨π, h⟩ : M.Paths_n₀ s' n, π.RProb' (𝒮.specialize s') (π.Paths_n₀_imp_reachable_from n s' h) * π.Cost cost
:= by
  simp
  simp [Path.RProb'_eq]
  conv =>
    left
    rw [Finset.sum_attach (M.Paths_n₀_by n s₀ s') (fun π ↦ π.tail.Prob' _ * π.tail.Cost cost)]
  simp [Paths_n₀_by]
  congr

@[simp]
theorem RScheduler'.cast_s_succ'_specialize (s₀ : State) (s₀' : M.succs_univ₀ s₀ ) (𝒮' : M.RScheduler' n s₀') :
  (𝒮'.cast_s_succ' s₀).specialize s₀' = 𝒮'
:= by
  funext ⟨π, hπ, _⟩
  simp only [RScheduler'.specialize, cast_s_succ', Path.tail_prepend]
  split_ifs
  simp only ; congr <;> simp only [Path.tail_prepend]

theorem RScheduler'_inf_n_eq_n_succ (cost : M.Costs) (n : ℕ) (s₀ : State) (s₀' : M.succs_univ₀ s₀) :
    RScheduler'.inf (M:=M) (EC₀' cost n s₀')
  = RScheduler'.inf (fun 𝒮 ↦ EC₀' cost n s₀' (𝒮.specialize s₀'))
:= by
  simp [RScheduler'.inf, RScheduler'.elems]
  apply le_antisymm
  · simp [Fintype.complete]
    intro 𝒮
    use 𝒮.specialize ⟨s₀', Finset.coe_mem s₀'⟩
  · simp [Fintype.complete]
    intro 𝒮'
    use 𝒮'.cast_s_succ' s₀
    rw [RScheduler'.cast_s_succ'_specialize]

def RScheduler'.fixed {M : MDP State Act} [M.FiniteBranching] {n : ℕ} {s₀ : State} (𝒮 : M.RScheduler' n s₀) (α : M.act₀ s₀) : M.RScheduler' n s₀ :=
  fun ⟨π, hπ⟩ ↦ if h : π.states = [s₀] then ⟨α.val, by simp_all [Path.last]⟩ else 𝒮 ⟨π, hπ⟩

theorem RScheduler'.fixed_specialize {M : MDP State Act} [M.FiniteBranching] {n : ℕ} {s₀ : State} (𝒮 : M.RScheduler' (n + 1) s₀) (α : M.act₀ s₀) (s₀' : M.succs_univ₀ s₀) :
  (𝒮.fixed α).specialize s₀' = 𝒮.specialize s₀'
:= by
  funext π
  simp only [RScheduler'.specialize, fixed]
  split
  split_ifs with h
  · absurd h ; simp [Path.prepend, Path.nonempty]
  · simp

theorem RScheduler'_consume_act_inf (cost : M.Costs) (n : ℕ) (s₀ : State) :
  (M.act₀ s₀).inf' (M.act₀_nonempty s₀) (fun α ↦
    RScheduler'.inf fun 𝒮 ↦
      ∑ s' ∈ (M.succs_univ₀ s₀).attach, M.P s₀ α s' * EC₀' cost n s' (𝒮.specialize s'))
  = RScheduler'.inf fun 𝒮 ↦
        ∑ s' ∈ (M.succs_univ₀ s₀).attach, M.P s₀ (𝒮 ⟨{s₀}, by simp [Path.instSingleton]⟩) s' * EC₀' cost n s' (𝒮.specialize s')
:= by
  simp [RScheduler'.inf, RScheduler'.elems, Fintype.complete]
  apply le_antisymm
  · simp_all [Fintype.complete]
    intro 𝒮
    use 𝒮 ⟨{s₀}, by simp [Path.instSingleton]⟩
    constructor
    · convert (𝒮 ⟨{s₀}, by simp [Path.instSingleton]⟩).prop
    · simp_all only [Path.instSingleton, List.length_singleton]
      use 𝒮
  · simp_all [Fintype.complete, Path.instSingleton]
    intro α hα 𝒮
    use 𝒮.fixed ⟨α, hα⟩
    simp [RScheduler'.fixed_specialize, RScheduler'.fixed]

theorem RScheduler'_inf_independent_sum (n : ℕ) (s₀ : State) (f : (s' : State) → M.RScheduler' n s' → ENNReal)
  (h : ∀ (𝒮 : M.RScheduler' (n + 1) s₀) (s' : M.succs_univ₀ s₀) (π' : M.Path) (h : π'.first = s'),
    (f (π'.prepend s₀ (by simp_all))[1] fun ⟨π, hπ⟩ ↦ ⟨𝒮 ⟨π.prepend s₀ (by simp_all), by simp_all⟩, by have := (𝒮 ⟨π.prepend s₀ (by simp_all), by simp_all⟩).prop ; simp_all⟩)
  = (f s' fun ⟨π, hπ⟩ ↦ ⟨𝒮 ⟨π.prepend s₀ (by simp_all), by simp_all⟩, by have := (𝒮 ⟨π.prepend s₀ (by simp_all), by simp_all⟩).prop ; simp_all⟩))
:
    ∑ s' : M.succs_univ₀ s₀, RScheduler'.inf (fun 𝒮 ↦ f s' (𝒮.specialize ⟨↑s', by simp⟩))
  = RScheduler'.inf fun 𝒮 ↦  ∑ s' : M.succs_univ₀ s₀, f s' (𝒮.specialize ⟨↑s', by simp⟩)
:= by
  conv => right ; simp [RScheduler'.inf, RScheduler'.elems, Fintype.complete]
  apply le_antisymm
  · simp_all [Fintype.complete]
    intro 𝒮
    gcongr
    simp [RScheduler'.inf, RScheduler'.elems, Fintype.complete]
    use 𝒮
  · simp_all [Fintype.complete]
    use fun ⟨π, hπ⟩ ↦
      if h : 1 < ∎|π| then
        RScheduler'.inf_choose
          (fun 𝒮 ↦ f (π[1]) (𝒮.specialize ⟨π[1], by
            rw [←hπ.left]
            exact Path.getElem_1_mem_succs_univ₀ π h⟩))
          ⟨π, by simp_all⟩
      else
        M.act₀_default π.last
    simp
    gcongr with s'
    have := RScheduler'.inf_choose_spec (fun 𝒮 ↦ f (s') (𝒮.specialize s')) |>.right
    unfold RScheduler'.inf
    rw [this]
    apply le_of_eq
    congr
    unfold RScheduler'.specialize
    simp
    funext π
    simp_all
    split
    rename_i π' _
    simp_all
    congr
    ext 𝒮
    exact h 𝒮 s' s'.prop π' (by simp_all)

theorem RScheduler'_inf_independent_sum' (cost : M.Costs) (n : ℕ) (s₀ : State) (α : Act) :
    ∑ s' ∈ (M.succs_univ₀ s₀).attach, RScheduler'.inf (fun 𝒮 ↦ M.P s₀ α s' * EC₀' cost n s' (𝒮.specialize ⟨↑s', by simp⟩))
  = RScheduler'.inf fun 𝒮 ↦ ∑ s' ∈ (M.succs_univ₀ s₀).attach, M.P s₀ α s' * EC₀' cost n s' (𝒮.specialize ⟨↑s', by simp⟩)
:= by
  apply M.RScheduler'_inf_independent_sum n s₀ fun s' 𝒮 ↦ M.P s₀ α s' * EC₀' cost n s' 𝒮
  intro 𝒮 s' π' hπ'
  simp_all
  congr! 1
  simp [EC₀']
  simp [Path.RProb'_eq]
  have : ∃ α, 0 < M.P s₀ α s' := M.succs_univ₀_spec _ _ s'.prop
  conv => left ; rw [Finset.sum_attach (M.Paths_n₀ (π'.prepend s₀ (by simp_all)).states[1] n) (fun π ↦ π.Prob' _ * π.Cost cost)]
  conv => right ; rw [Finset.sum_attach (M.Paths_n₀ s' n) (fun π ↦ π.Prob' _ * π.Cost cost)]
  simp_all
  congr with π
  congr! 1
  simp [Path.Prob']
  congr with i
  congr! 1
  simp_all [RScheduler'.ext]

theorem RScheduler'.split_inf (cost : M.Costs) (n : ℕ) (s₀ : State) :
  (RScheduler'.inf fun 𝒮 ↦
    ∑ s' ∈ (M.succs_univ₀ s₀).attach, M.P s₀ (𝒮 ⟨{s₀}, by simp [Path.instSingleton]⟩) s' * EC₀' cost n s' (𝒮.specialize s'))
  = (M.act₀ s₀).inf' (M.act₀_nonempty s₀) fun α ↦ ∑ s' ∈ (M.succs_univ₀ s₀).attach, M.P s₀ α s' * (RScheduler'.inf (M.EC₀' cost n s'))
:= by
  simp [RScheduler'_inf_n_eq_n_succ]
  simp [←RScheduler'.inf_const_mul]
  simp [M.RScheduler'_inf_independent_sum' cost n s₀]
  simp [M.RScheduler'_consume_act_inf cost n s₀]

theorem inf_succs_univ₀_Paths_n₀_by_eq_Φ_inf_EC₀' (cost : M.Costs) (n : ℕ) (s₀ : State) :
  (RScheduler'.inf fun 𝒮 ↦
    ∑ s' : M.succs_univ₀ s₀, ∑ ⟨π, h⟩ : M.Paths_n₀_by n s₀ s', π.RProb' 𝒮 (M.Paths_n₀_by_reachable h) * π.Cost cost)
  = M.Φ cost (fun s' ↦ RScheduler'.inf (M.EC₀' cost n s')) s₀
:= by
  simp
  have := fun (𝒮 : M.RScheduler' (n + 1) s₀) ↦ M.sum_succs_univ₀_sum_Paths_n₀_by cost n s₀ 𝒮
  simp at this
  simp [this]
  have := M.sum_Paths_n₀_by_tail_eq_sum_Paths_n₀ cost n s₀
  simp at this
  simp [this]
  have : ∀ (s' : M.succs_univ₀ s₀ ) (𝒮 : M.RScheduler' (n + 1) s₀), M.EC₀' cost n s' (𝒮.specialize s') = M.EC₀' cost n s' (𝒮.specialize s') := fun _ _ ↦ rfl
  conv at this =>
    ext s' 𝒮 ; left ; unfold EC₀'
  conv =>
    left ; congr ; ext 𝒮 ; right ; arg 2 ; ext s' ; right ; rw [this s' 𝒮]
  simp [RScheduler'.inf_const_add]
  simp [Φ, Φf]
  congr
  rw [RScheduler'.split_inf]
  congr
  ext α
  conv =>
    left
    rw [Finset.sum_attach (M.succs_univ₀ s₀) fun s' ↦ M.P s₀ α s' * RScheduler'.inf (EC₀' cost n s')]
  exact M.sum_succs_eq_sum_succs_univ_mul α s₀ _ |>.symm

theorem sup_inf_EC₀'_eq_Φ_sup_inf_EC₀' (cost : M.Costs) (n : ℕ) (s₀ : State) : RScheduler'.inf (M.EC₀' cost (n + 1) s₀) = M.Φ cost (fun s' ↦ RScheduler'.inf (M.EC₀' cost n s')) s₀ := by
  conv => left ; unfold EC₀' ; congr ; ext 𝒮 ; rw [sum_Paths_n₀_eq_sum_succs_Paths_n₀]
  simp [succs_Paths_n₀]
  have := fun (𝒮 : M.RScheduler' (n + 1) s₀) ↦ Finset.sum_biUnion_attach
      (M.Paths_n₀_by_DisjointOn n s₀)
      (fun ⟨π, h⟩ ↦ Path.RProb' 𝒮 π (M.Paths_n₀_by_reachable h.choose_spec) * π.Cost cost)
  unfold Paths_n₀_by at this
  conv => left ; congr ; ext 𝒮 ; rw [this 𝒮]
  exact M.inf_succs_univ₀_Paths_n₀_by_eq_Φ_inf_EC₀' cost n s₀

theorem sup_inf_EC₀'_eq_iSup_Φ (cost : M.Costs) : ⨆ n, RScheduler'.inf (M.EC₀' cost n s₀) = M.iSup_Φ cost s₀ := by
  simp only [iSup_Φ, Nat.succ_eq_add_one, iSup_apply]
  congr! with n
  induction n generalizing s₀ with
  | zero =>
    simp only [RScheduler'.inf, RScheduler'.elems, EC₀', Paths_n₀, Path.mk_single, Path.RProb',
      Fin.getElem_fin, Pathsable_le_zero, Nat.succ_eq_add_one, Fin.val_succ, Path.Cost,
      Finset.sum_singleton_attach, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
      Finset.univ_eq_empty, Finset.prod_empty, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, one_mul, Finset.inf'_const, zero_add, Function.iterate_succ,
      Function.iterate_zero, Function.comp_apply, id_eq, Φ, Φf, ContinuousHom.coe_mk,
      OrderHom.coe_mk, Pi.bot_apply, bot_eq_zero', mul_zero, Finset.sum_const_zero]
  | succ n ih =>
    have ih' : (fun s₀ ↦ RScheduler'.inf (EC₀' cost n s₀)) = (M.Φ cost)^[n + 1] ⊥ := by
      ext s₀ ; exact ih
    rw [Function.iterate_succ', Function.comp_apply, ←ih']
    exact M.sup_inf_EC₀'_eq_Φ_sup_inf_EC₀' cost n s₀

theorem sup_inf_EC₀'_eq_lfp_Φ (cost : M.Costs) (s : State) : ⨆ n, RScheduler'.inf (EC₀' cost n s) = M.lfp_Φ cost s := by
  rw [lfp_Φ_eq_iSup_Φ]
  exact M.sup_inf_EC₀'_eq_iSup_Φ cost
