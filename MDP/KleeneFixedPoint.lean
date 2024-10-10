import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.SetTheory.Ordinal.FixedPointApproximants
import MDP.OmegaCompletePartialOrder

theorem iterate_succ {α : Type*} (f : α → α) (a : α) (n : ℕ) : f (f^[n] a) = f^[n.succ] a :=
  Eq.symm (Function.iterate_succ_apply' f n a)

theorem iterate_succ' {α : Type*} (f : α → α) (a : α) (n : ℕ) : f (f^[n] a) = f^[n] (f a) :=
  iterate_succ f a n

theorem KleeneFixedPoint' {α : Type*} [CompleteLattice α] (f : α →o α) (n : ℕ) : f^[n] ⊥ ≤ f^[n+1] ⊥ := by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq, zero_add, Function.iterate_one, bot_le]
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact f.monotone ih

theorem Monotone.iterate_add {α : Type*} [CompleteLattice α] (f : α →o α) (n m : ℕ) : f^[n] ⊥ ≤ f^[n + m] ⊥ := by
  rw [Function.iterate_add_apply]
  exact Monotone.iterate f.monotone n (OrderBot.bot_le _)

theorem Monotone.iterate_le {α : Type*} [CompleteLattice α] (f : α →o α) {n m : ℕ} (h : n ≤ m) : f^[n] ⊥ ≤ f^[m] ⊥ := by
  obtain ⟨c, hc⟩ := le_iff_exists_add.mp h
  rw [hc]
  exact Monotone.iterate_add f n c

theorem lfp_eq_iff {α : Type*} [CompleteLattice α] (f : α →o α) (a : α) (h : f a = a) (h' : ∀ b, f b ≤ b → a ≤ b) : OrderHom.lfp f = a := by
  have p₁ := OrderHom.lfp_le_fixed f h
  have p₂ : a ≤ OrderHom.lfp f := OrderHom.le_lfp f h'
  exact (p₁.le_iff_eq.mp p₂).symm

theorem KleeneFixedPoint.ScottContinuous {α : Type*} [CompleteLattice α] (f : α →o α) {h : ScottContinuous f} : (OrderHom.lfp f) = (⨆n, f^[n] ⊥) :=
  let M := { f^[n] ⊥ | n : ℕ }
  let m := sSup M
  have : f m = m := by
    have p : IsLUB (f '' M) (f m) := (h (by use ⊥, 0 ; rfl ) (by
        intro a a_in_M b b_in_M
        simp_all [M]
        obtain ⟨n₁, a_in_M⟩ := a_in_M
        obtain ⟨n₂, b_in_M⟩ := b_in_M
        subst_eqs
        by_cases h' : n₁ < n₂
        · have := Monotone.iterate_le f h'.le
          use n₂
        · have := Monotone.iterate_le f (not_lt.mp h')
          use n₁
      ) (isLUB_sSup M))
    have p₁ : sSup (f '' M) = f m := IsLUB.sSup_eq p
    have p₂ : (f '' M) ∪ {⊥} = M := by
      ext a
      simp_all [M]
      constructor
      · intro h'
        cases h' <;> rename_i h'
        · simp_all
          use 0
          simp
        · obtain ⟨n, h'⟩ := h'
          use n.succ
          simp_all [Function.iterate_succ_apply']
      · simp_all
        intro n h'
        induction n with
        | zero => simp_all
        | succ n _ =>
          right
          use n
          simp_all [Function.iterate_succ_apply']
    have p₃ : sSup (f '' M) = sSup M := by
      conv in sSup M => rw [←p₂]
      simp
    exact p₁.symm.trans p₃
  lfp_eq_iff f m this (by
    intro b h'
    simp only [sSup_le_iff, Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff, m, M]
    intro n
    induction n with
    | zero => simp only [Function.iterate_zero, id_eq, bot_le]
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (f.monotone ih).trans h')

theorem KleeneFixedPoint.OmegaCompletePartialOrder.Continuous {α : Type*} [CompleteLattice α] (f : α →𝒄 α) : (OrderHom.lfp f) = (⨆n, f^[n] ⊥) := by
  have f_iterate_mono d : Monotone (fun n ↦ f^[n + d] ⊥) := by
    intro a b a_le_b
    dsimp only
    obtain ⟨c, h⟩ := le_iff_exists_add.mp a_le_b
    rw [add_comm a, add_comm b]
    simp [h, Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply]
    exact Monotone.iterate f.monotone d (Monotone.iterate f.monotone a (OrderBot.bot_le _))
  let M : OmegaCompletePartialOrder.Chain α := ⟨fun n ↦ f^[n] ⊥, f_iterate_mono 0⟩
  have M_eq n : M n = f^[n] ⊥ := rfl
  have M_map_eq n : M.map f n = f (f^[n] ⊥) := rfl
  have M_map : M.map f = ⟨fun n ↦ f^[n.succ] ⊥, f_iterate_mono 1⟩ := by
    dsimp only [OmegaCompletePartialOrder.Chain.map, OrderHom.comp, OrderHomClass.coe_coe,
      OrderHom.coe_mk, Nat.succ_eq_add_one, Function.iterate_succ, Function.comp_apply, M]
    congr
    ext a
    exact iterate_succ' f ⊥ a
  let m := OmegaCompletePartialOrder.ωSup M
  apply lfp_eq_iff f m
  · apply (f.map_ωSup' M).trans
    apply le_antisymm
    · apply OmegaCompletePartialOrder.ωSup_le_ωSup_of_le
      intro n
      use n + 1
      simp_all only [Nat.succ_eq_add_one, Function.iterate_succ, Function.comp_apply,
        OmegaCompletePartialOrder.Chain.map_coe,
        OmegaCompletePartialOrder.ContinuousHom.coe_toOrderHom]
      exact (M_map_eq n).ge
    · apply OmegaCompletePartialOrder.ωSup_le_ωSup_of_le
      intro n
      use n
      simp only [M_eq, OmegaCompletePartialOrder.Chain.map_coe,
        OmegaCompletePartialOrder.ContinuousHom.coe_toOrderHom, Function.comp_apply]
      rw [iterate_succ' f ⊥ n]
      exact Monotone.iterate f.mono n (OrderBot.bot_le _)
  · intro b h'
    simp [m, OmegaCompletePartialOrder.ωSup_le_iff]
    intro n
    rw [M_eq]
    induction n with
    | zero => simp only [Function.iterate_zero, id_eq, bot_le]
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (f.monotone ih).trans h'

lemma f_iterate_mono {α : Type*} [Preorder α] [OrderBot α] (f : α →o α) (d : ℕ) : Monotone (fun n ↦ f^[n + d] ⊥) := by
    intro a b a_le_b
    dsimp only
    obtain ⟨c, h⟩ := le_iff_exists_add.mp a_le_b
    rw [add_comm a, add_comm b]
    simp [h, Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply]
    exact Monotone.iterate f.monotone d (Monotone.iterate f.monotone a (OrderBot.bot_le _))


theorem KleeneFixedPoint.Pi.OmegaCompletePartialOrder.Continuous {α β : Type*} [CompleteLattice β] (f : (α → β) →𝒄 (α → β)) : (OrderHom.lfp f) = OmegaCompletePartialOrder.ωSup ⟨fun n ↦ f^[n] ⊥, f_iterate_mono f 0⟩ := by
  let M : OmegaCompletePartialOrder.Chain (α → β) := ⟨fun n ↦ f^[n] ⊥, f_iterate_mono f 0⟩
  have M_eq n : M n = f^[n] ⊥ := rfl
  have M_map_eq n : M.map f n = f (f^[n] ⊥) := rfl
  have M_map : M.map f = ⟨fun n ↦ f^[n.succ] ⊥, f_iterate_mono f 1⟩ := by
    dsimp only [OmegaCompletePartialOrder.Chain.map, OrderHom.comp, OrderHomClass.coe_coe,
      OrderHom.coe_mk, Nat.succ_eq_add_one, Function.iterate_succ, Function.comp_apply, M]
    congr
    funext a
    simp
    exact iterate_succ' f ⊥ a
  let m := OmegaCompletePartialOrder.ωSup M
  apply lfp_eq_iff f m
  · apply (f.map_ωSup' M).trans
    apply le_antisymm
    · apply OmegaCompletePartialOrder.ωSup_le_ωSup_of_le
      intro n
      use n + 1
      simp_all only [Nat.succ_eq_add_one, Function.iterate_succ, Function.comp_apply,
        OmegaCompletePartialOrder.Chain.map_coe,
        OmegaCompletePartialOrder.ContinuousHom.coe_toOrderHom]
      exact (M_map_eq n).ge
    · apply OmegaCompletePartialOrder.ωSup_le_ωSup_of_le
      intro n
      use n
      simp only [M_eq, OmegaCompletePartialOrder.Chain.map_coe,
        OmegaCompletePartialOrder.ContinuousHom.coe_toOrderHom, Function.comp_apply]
      rw [iterate_succ' f ⊥ n]
      exact Monotone.iterate f.mono n (OrderBot.bot_le _)
  · intro b h'
    simp [m, OmegaCompletePartialOrder.ωSup_le_iff]
    intro n
    rw [M_eq]
    induction n with
    | zero => simp only [Function.iterate_zero, id_eq, bot_le]
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (f.monotone ih).trans h'

theorem KleeneFixedPoint.Pi.Continuous' {α β : Type*} [CompleteLattice β] (f : (α → β) →o (α → β)) (hf : OmegaCompletePartialOrder.Continuous' f) : (OrderHom.lfp f) = OmegaCompletePartialOrder.ωSup ⟨fun n ↦ f^[n] ⊥, f_iterate_mono f 0⟩ := by
  exact KleeneFixedPoint.Pi.OmegaCompletePartialOrder.Continuous ⟨f, OmegaCompletePartialOrder.continuous'_coe.mp hf⟩


theorem KleeneFixedPoint {α : Type*} [CompleteLattice α] (f : α →𝒄 α) : OrderHom.lfp f = ⨆n, f^[n] ⊥ :=
  KleeneFixedPoint.OmegaCompletePartialOrder.Continuous f


theorem KleeneFixedPoint_succ {α : Type*} [CompleteLattice α] (f : α →𝒄 α) : OrderHom.lfp f = ⨆(n : ℕ), f^[n.succ] ⊥ := by
  rw [KleeneFixedPoint f]
  have := sup_iSup_nat_succ (fun n ↦ f^[n] ⊥)
  simp_all only [Function.iterate_zero, id_eq, Function.iterate_succ, Function.comp_apply,
    ge_iff_le, bot_le, sup_of_le_right, Nat.succ_eq_add_one]

theorem KleeneFixedPoint_succ' {α : Type*} [CompleteLattice α] (f : α →o α) (hf : OmegaCompletePartialOrder.Continuous' f) : OrderHom.lfp f = ⨆(n : ℕ), f^[n.succ] ⊥ :=
  KleeneFixedPoint_succ ⟨f, hf.to_bundled⟩

theorem KleeneFixedPoint.Pi.succ {α β : Type*} [CompleteLattice β] (f : (α → β) →𝒄 (α → β)) : OrderHom.lfp f = OmegaCompletePartialOrder.ωSup ⟨fun (n : ℕ) ↦ f^[n.succ] ⊥, f_iterate_mono f 1⟩ := by
  rw [KleeneFixedPoint.Pi.OmegaCompletePartialOrder.Continuous f]
  -- simp
  apply le_antisymm
  · apply OmegaCompletePartialOrder.ωSup_le_ωSup_of_le
    intro n
    use n
    exact Monotone.iterate f.mono n (OrderBot.bot_le _)
  · apply OmegaCompletePartialOrder.ωSup_le_ωSup_of_le
    intro n
    use n + 1
    simp_all only [Nat.succ_eq_add_one, Function.iterate_succ, Function.comp_apply,
      OmegaCompletePartialOrder.Chain.map_coe,
      OmegaCompletePartialOrder.ContinuousHom.coe_toOrderHom]
    apply Preorder.le_refl

  -- have := sup_iSup_nat_succ (fun n ↦ f^[n] ⊥)
  -- simp_all only [Function.iterate_zero, id_eq, Function.iterate_succ, Function.comp_apply,
  --   ge_iff_le, bot_le, sup_of_le_right, Nat.succ_eq_add_one]

theorem KleeneFixedPoint.Pi.succ' {α β : Type*} [CompleteLattice β] (f : (α → β) →o (α → β)) (hf : OmegaCompletePartialOrder.Continuous' f) : OrderHom.lfp f = OmegaCompletePartialOrder.ωSup ⟨fun (n : ℕ) ↦ f^[n.succ] ⊥, f_iterate_mono f 1⟩ :=
  KleeneFixedPoint.Pi.succ ⟨f, hf.to_bundled⟩

theorem KleeneFixedPoint.Pi.succ'_iSup {α β : Type*} [CompleteLattice β] (f : (α → β) →o (α → β)) (hf : OmegaCompletePartialOrder.Continuous' f) : OrderHom.lfp f = iSup (fun (n : ℕ) ↦ f^[n.succ] ⊥) := by
  rw [KleeneFixedPoint.Pi.succ', ←OmegaCompletePartialOrder.Pi.iSup_eq_ωSup]
  simp only [Nat.succ_eq_add_one, Function.iterate_succ, Function.comp_apply, OrderHom.coe_mk]
  exact hf

theorem KleeneFixedPoint.Pi.iSup {α β : Type*} [CompleteLattice β] (f : (α → β) →o (α → β)) (hf : OmegaCompletePartialOrder.Continuous' f) : OrderHom.lfp f = iSup (fun (n : ℕ) ↦ f^[n] ⊥) := by
  rw [KleeneFixedPoint.Pi.Continuous', ←OmegaCompletePartialOrder.Pi.iSup_eq_ωSup]
  simp only [Nat.succ_eq_add_one, Function.iterate_succ, Function.comp_apply, OrderHom.coe_mk]
  exact hf

-- theorem KleeneFixedPoint_succ'' {α β : Type*} [CompleteLattice (α → β)] (f : ((a : α) → β a) →o ((a : α) → β a)) (hf : @OmegaCompletePartialOrder.Continuous' _ _ _ Pi.instCompleteLattice f) : OrderHom.lfp f = ⨆(n : ℕ), f^[n.succ] ⊥ := by
--   -- have : OmegaCompletePartialOrder ((a : α) → β a) := Pi.instOmegaCompletePartialOrderForall
--   have : CompleteLattice ((a : α) → β a) := Pi.instCompleteLattice
--   have := @KleeneFixedPoint ((a : α) → β a) this ⟨f, hf.to_bundled⟩
--   rw [KleeneFixedPoint ⟨f, hf.to⟩]
--   apply KleeneFixedPoint_succ'
--   exact hf
  -- KleeneFixedPoint_succ ⟨f, hf.to_bundled⟩
