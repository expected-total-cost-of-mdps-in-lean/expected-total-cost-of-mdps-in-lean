import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Topology.Instances.ENNReal

-- TODO: remove this
set_option linter.unusedSectionVars false

namespace OmegaCompletePartialOrder

theorem ωSup_eq_top_if_top_exists {α : Type*} [CompleteLattice α] (A : Chain α) (h : ⊤ ∈ A) : ωSup A = ⊤ := by
  obtain ⟨i, h⟩ := h
  exact eq_top_iff.mpr <| h.trans_le <| le_ωSup A i

theorem SupremumOfSubsetOfENNRealsIsArbitrarilyClose (A : Chain ENNReal) (hA : ωSup A ≠ ⊤) (ε : NNReal) (hε : ε > 0) :
  ∃x ∈ A, ωSup A - x < ε := by
  by_contra q
  simp_all
  have h₁ : ∀x ∈ A, x ≤ (ωSup A) - ε := by
    intro x h
    apply ENNReal.le_sub_of_add_le_left (ENNReal.coe_ne_top)
    convert add_le_add (q x h) le_rfl
    apply Eq.symm (tsub_add_cancel_of_le _)
    obtain ⟨i, hi⟩ := h
    exact le_ωSup_of_le i hi.le
  have h₂ : ωSup A ≤ (ωSup A) - ε := ωSup_le A ((ωSup A) - ε) (fun i ↦ h₁ (A i) (by use i))
  absurd h₂
  simp only [not_le]
  apply (ENNReal.sub_lt_self_iff _).mpr
  · simp only [ENNReal.coe_pos, hε, and_true]
    by_contra q'
    simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at q'
    simp only [q', ge_iff_le, zero_le, tsub_eq_zero_of_le, nonpos_iff_eq_zero,
      ENNReal.coe_eq_zero] at q
    exact (q (A 0) (by use 0)).not_gt hε
  · exact hA

theorem top_not_mem_if_ωSup_ne_top {α : Type*} [CompleteLattice α] {A : Chain α} (h : ¬ωSup A = ⊤) : ⊤ ∉ A := by
  intro q
  obtain ⟨i, h'⟩ := q
  exact not_lt_of_le (h'.trans_le <| le_ωSup A i) (Ne.lt_top h)

theorem mem_if_exists {α : Type*} [CompleteLattice α] {A : Chain α} {x : α} (h : ∃i, A i = x) : x ∈ A := by
  obtain ⟨i, h⟩ := h
  use i
  exact h.symm

theorem le_le_not_top_sub_comm {a b c : ENNReal} (hb : b ≤ a) (hc : c ≤ a) (hbt : b ≠ ⊤) (hct : c ≠ ⊤) : a - b < c ↔ a - c < b := by
  constructor <;> intro h
  · apply (ENNReal.sub_lt_iff_lt_right hct hc).mpr
    rw [add_comm]
    exact ENNReal.sub_lt_iff_lt_right hbt hb |>.mp h
  · apply (ENNReal.sub_lt_iff_lt_right hbt hb).mpr
    rw [add_comm]
    exact ENNReal.sub_lt_iff_lt_right hct hc |>.mp h

theorem SupremumOfSubsetOfENNRealsIsArbitrarilyClose' (A : Chain ENNReal) (hA : ωSup A ≠ ⊤) (ε : NNReal) (hε : 0 < ε ∧ ε ≤ ωSup A) :
  ∃x ∈ A, ωSup A - ε < x := by
  obtain ⟨x, hx₁, hx₂⟩ := SupremumOfSubsetOfENNRealsIsArbitrarilyClose A hA ε hε.left
  use x, hx₁
  obtain ⟨i, hx₁⟩ := hx₁
  apply (le_le_not_top_sub_comm _ _ _ _).mp hx₂
  · exact hx₁.trans_le <| le_ωSup_of_le i (Preorder.le_refl _)
  · exact hε.right
  · exact hx₁.trans_ne <| not_exists.mp (top_not_mem_if_ωSup_ne_top hA ∘ mem_if_exists) i
  · exact ENNReal.coe_ne_top

theorem iSup_eq_ωSup {α : Type*} [CompleteLattice α] (f : ℕ →o α) : ⨆ n, f n = ωSup f :=
  le_antisymm
    (iSup_le     <| le_ωSup f)
    (ωSup_le f _ <| le_iSup f)

theorem iSup_eq_ωSup' {α : Type*} [CompleteLattice α] (f : Chain α) : ⨆ n, f n = ωSup f :=
  le_antisymm
    (iSup_le     <| le_ωSup f)
    (ωSup_le f _ <| le_iSup f)

theorem Pi.iSup_eq_ωSup {α β : Type*} [CompleteLattice β] (f : ℕ →o (α → β)) : ⨆ n, f n = ωSup f :=
  le_antisymm
    (iSup_le     <| le_ωSup f)
    (ωSup_le f _ <| le_iSup f)

theorem add_continuous {α : Type u} [OmegaCompletePartialOrder α] (f : α →o ENNReal) (g : α →o ENNReal) (hf : Continuous f) (hg : Continuous g) :
Continuous ⟨fun (x : α) => f x + g x, fun _ _ a_le_b ↦ add_le_add (f.monotone a_le_b) (g.monotone a_le_b)⟩ := by
  intro chain
  rw [OrderHom.coe_mk, hf chain, hg chain]
  simp_rw [←iSup_eq_ωSup]
  exact ENNReal.iSup_add_iSup_of_monotone (fun _ _ h ↦ f.monotone <| chain.mono h) (fun _ _ h ↦ g.monotone <| chain.mono h)

theorem ENNReal.iSup_mul_le {a : ENNReal} {g : ι → ENNReal} {h : ENNReal} (H : ∀ i, g i * h ≤ a) : iSup g * h ≤ a := by
  rw [ENNReal.iSup_mul]
  exact ciSup_le' H

theorem ENNReal.mul_iSup_le {a : ENNReal} {g : ENNReal} {h : ι → ENNReal} (H : ∀ j, g * h j ≤ a) : g * iSup h ≤ a := by
  rw [ENNReal.mul_iSup]
  exact ciSup_le' H

theorem ENNReal.iSup_mul_iSup_le {a : ENNReal} {g h : ι → ENNReal} (H : ∀ i j, g i * h j ≤ a) :
    iSup g * iSup h ≤ a :=
  iSup_mul_le fun _ => ENNReal.mul_iSup_le <| H _

theorem ENNReal.iSup_mul_iSup {ι : Sort*} {f g : ι → ENNReal} (h : ∀ i j, ∃ k, f i * g j ≤ f k * g k) :
    iSup f * iSup g = ⨆ a, f a * g a := by
  cases isEmpty_or_nonempty ι
  · simp [iSup_of_empty, bot_eq_zero, zero_mul]
  · refine le_antisymm ?_ (iSup_le fun a => mul_le_mul' (le_iSup _ _) (le_iSup _ _))
    refine iSup_mul_iSup_le fun i j => ?_
    rcases h i j with ⟨k, hk⟩
    exact le_iSup_of_le k hk

-- NOTE: this is crazy...
-- theorem ENNReal.le_mul_iInf {ι : Sort u_1} [Nonempty ι] {a : ENNReal} {g : ENNReal} {h : ι → ENNReal} (hg : g ≠ ⊤) (H : ∀ j, a ≤ g * h j) : a ≤ g * iInf h := by
--   rw [ENNReal.mul_iInf hg]
--   exact le_ciInf H

-- theorem ENNReal.le_iInf_mul {ι : Sort u_1} [Nonempty ι] {a : ENNReal} {g : ι → ENNReal} {h : ENNReal} (hh : h ≠ ⊤) (H : ∀ i, a ≤ g i * h) : a ≤ iInf g * h := by
--   rw [ENNReal.iInf_mul hh]
--   exact le_ciInf H

-- theorem ENNReal.le_iInf_mul_iInf {ι : Type*} [Nonempty ι] [CompleteLattice ι] {a : ENNReal} {g : ι →o ENNReal} {h : ι → ENNReal} (hg : ∀i, g i ≠ ⊤) (H : ∀ (i j : ι), a ≤ g i * h j) : a ≤ iInf g * iInf h := by
--   by_cases hh : iInf h ≠ ⊤
--   · exact ENNReal.le_iInf_mul hh fun i ↦ le_mul_iInf (hg i) <| H i
--   · simp_all only [ne_eq, not_forall, not_exists, Decidable.not_not, forall_const]
--     simp_all only [iInf_eq_top, forall_const]
--     by_contra q
--     simp_all
--     by_cases hg' : iInf g = 0
--     · simp_all
--       have : 0 ≤ g ⊥ := zero_le (g _)
--       by_contra q
--       simp_all
--     · simp_all only [ne_eq, not_false_eq_true, ENNReal.mul_top, le_top]

theorem mul_continuous {α : Type u} [OmegaCompletePartialOrder α] (f : α →o ENNReal) (g : α →o ENNReal) (hf : Continuous f) (hg : Continuous g) :
  Continuous ⟨fun (x : α) => f x * g x, fun _ _ a_le_b ↦ mul_le_mul' (f.monotone a_le_b) (g.monotone a_le_b)⟩ := by
  intro chain
  rw [OrderHom.coe_mk, hf chain, hg chain, ←iSup_eq_ωSup]
  apply ENNReal.iSup_mul_iSup
  intro i j
  use max i j
  exact mul_le_mul' ((chain.map f).monotone (Nat.le_max_left i j)) ((chain.map g).monotone (Nat.le_max_right i j))

theorem mul_continuous' {α : Type u} [OmegaCompletePartialOrder α] (f : α → ENNReal) (g : α → ENNReal) (hf : Continuous' f) (hg : Continuous' g) :
  Continuous' (f * g) :=
    Continuous.of_bundled
      (f * g)
      (fun _ _ h ↦ mul_le_mul' (hf.to_monotone h) (hg.to_monotone h))
      (mul_continuous ⟨f, hf.to_monotone⟩ ⟨g, hg.to_monotone⟩ (hf.to_bundled f) (hg.to_bundled g))

theorem add_continuous' {α : Type u} [OmegaCompletePartialOrder α] (f : α → ENNReal) (g : α → ENNReal) (hf : Continuous' f) (hg : Continuous' g) :
  Continuous' (f + g) :=
    Continuous.of_bundled
      (f + g)
      (fun _ _ h ↦ add_le_add (hf.to_monotone h) (hg.to_monotone h))
      (add_continuous ⟨f, hf.to_monotone⟩ ⟨g, hg.to_monotone⟩ (hf.to_bundled f) (hg.to_bundled g))

theorem Finset_sum_continuous {α : Type u} {ι : Type w} [OmegaCompletePartialOrder α] [DecidableEq ι] (S : Finset ι) (f : ι → α →o ENNReal) (hf : ∀ a, Continuous (f a)) :
  Continuous ⟨fun i ↦ Finset.sum S (fun a ↦ f a i), fun _ _ h ↦ Finset.sum_le_sum fun s _ ↦ (f s).monotone h⟩ := by
  induction S using Finset.induction_on
  next => apply OmegaCompletePartialOrder.continuous_const
  next i S i_ni_S ih =>
    simp only [Finset.sum_insert i_ni_S]
    exact @add_continuous α _ (f i) ⟨fun x ↦ S.sum fun a ↦ (f a) x,
      fun _ _ h ↦ Finset.sum_le_sum (fun i _ ↦ (f i).monotone h)⟩ (hf i) ih

theorem Finset_sum_continuous' {α : Type u} {ι : Type w} [OmegaCompletePartialOrder α] [DecidableEq ι] (S : Finset ι) (f : ι → α → ENNReal) (hf : ∀ a, Continuous' (f a)) :
  Continuous' fun i ↦ Finset.sum S (fun a ↦ f a i) := by
  apply Continuous.of_bundled
  apply Finset_sum_continuous S (fun a ↦ ⟨f a, (hf a).to_monotone⟩)
  intro a
  exact continuous'_coe.mp (hf a)

theorem Finset_inf' {α : Type u} {ι : Type w} [OmegaCompletePartialOrder α] (S : Finset ι) (S_Nonempty : S.Nonempty) (f : ι → α →o ENNReal) (hf : ∀ a, Continuous (f a)) :
  Continuous ⟨fun i ↦ Finset.inf' S S_Nonempty (fun a ↦ f a i), by
    intro a b a_le_b
    simp only [Finset.le_inf'_iff, Finset.inf'_le_iff]
    intro x x_in
    use x, x_in, (f x).monotone a_le_b
    ⟩ := by
  have : DecidableEq ι := Classical.typeDecidableEq ι
  intro chain
  simp_all [←iSup_eq_ωSup, Chain.map]
  induction S using Finset.induction_on
  next =>
    obtain ⟨x, h⟩ := S_Nonempty
    absurd h
    simp only [Finset.not_mem_empty, not_false_eq_true]
  next x S _ ih =>
    by_cases S'_Nonempty : S.Nonempty
    · simp_all only [forall_true_left, Finset.inf'_insert]
      have := @iSup_inf_of_monotone _ _ _ _ _ (fun n ↦ f x (chain n)) (fun n ↦ S.inf' S'_Nonempty fun a ↦ (f a) (chain n))
        (by
          intro a b a_le_b
          simp
          exact (f x).monotone <| chain.monotone a_le_b)
        (by
          intro a b a_le_b
          simp_all
          intro x hx
          use x, hx
          exact (f x).monotone <| chain.monotone a_le_b)
      rw [this]
      apply congrFun (congrArg Inf.inf (hf x chain)) (⨆ n, S.inf' (Eq.substr (eq_true S'_Nonempty) True.intro) fun a ↦ (f a) (chain n))
    · simp_all only [not_isEmpty_of_nonempty, ciSup_of_empty, bot_eq_zero', IsEmpty.forall_iff,
      Finset.not_nonempty_iff_eq_empty, Finset.insert_empty, Finset.inf'_singleton,
      Finset.not_mem_empty, not_false_eq_true]
      exact hf x chain


theorem Finset.sup'_unapply {α β ι : Type*} [SemilatticeSup β] (s : Finset ι) (h : s.Nonempty) (f : ι → α → β) (v : α) : (s.sup' h fun x ↦ f x v) = (s.sup' h fun x ↦ f x) v := by
  exact Eq.symm (Finset.sup'_apply h (fun x ↦ f x) v)

theorem Finset.sup'_mono' {α β ι : Type*} [SemilatticeSup β] [PartialOrder α] (s : Finset ι) (h : s.Nonempty) (f : α →o ι → β) (v v' : α) (hv : v ≤ v') : s.sup' h (f v) ≤ s.sup' h (f v') :=
  (Finset.sup'_le_iff h _).mpr fun x xh ↦ Finset.le_sup'_of_le (f v') xh (f.mono hv x)

theorem Finset.sup'_mono'' {α β ι : Type*} [SemilatticeSup β] [PartialOrder α] (s : Finset ι) (h : s.Nonempty) (f : ι → α →o β) (v v' : α) (hv : v ≤ v') : s.sup' h f v ≤ s.sup' h f v' := by
  apply OrderHom.apply_mono (@Finset.sup'_le_iff _ _ _ _ h f (s.sup' h f) |>.mpr _) hv
  intro x xh
  exact Finset.le_sup' f xh

theorem Finset_sup' {α : Type u} {ι : Type w} [CompleteLattice α] {S : Finset ι} (S_Nonempty : S.Nonempty) (f : ι → α →o ENNReal) (hf : ∀ a, Continuous (f a)) :
  Continuous ⟨fun i ↦ Finset.sup' S S_Nonempty (fun a ↦ f a i), by
    intro a b a_le_b
    simp only [Finset.sup'_unapply]
    convert Finset.sup'_mono' S S_Nonempty ⟨fun a i ↦ f i a, fun a a' ha i ↦ by simp ; exact (f i).mono ha⟩ a b a_le_b
    · simp
    · simp
    ⟩ := by
  intro chain
  simp_all only [OrderHom.coe_mk, Chain.map, ← iSup_eq_ωSup, OrderHom.comp_coe, Function.comp_apply]
  apply le_antisymm
  · simp only [Finset.sup'_le_iff]
    intro i hi
    have := hf i chain
    simp_all only [← iSup_eq_ωSup, iSup_le_iff]
    intro j
    refine le_iSup_iff.mpr ?_
    simp only [Finset.sup'_le_iff]
    intro b h
    convert h j i hi
  · simp only [Finset.le_sup'_iff, iSup_le_iff, Finset.sup'_le_iff]
    obtain ⟨i, hi₁, hi₂⟩ := Finset.exists_mem_eq_sup' S_Nonempty (fun i ↦ f i (⨆ n, chain n))
    use i, hi₁
    rw [←hi₂]
    simp only [Finset.le_sup'_iff]
    intro n i' hi'
    use i', hi'
    exact (f i').mono (le_ωSup _ _)

theorem Finset_sup'.Pi {α : Type u} {β : Type*} {ι : Type w} [CompleteLattice β] {S : Finset ι} (S_Nonempty : S.Nonempty) (f : ι → (α → β) →o ENNReal) (hf : ∀ a, Continuous (f a)) :
  Continuous ⟨fun i ↦ Finset.sup' S S_Nonempty (fun a ↦ f a i), by
    intro a b a_le_b
    simp only [Finset.sup'_unapply]
    convert Finset.sup'_mono' S S_Nonempty ⟨fun a i ↦ f i a, fun a a' ha i ↦ by simp ; exact (f i).mono ha⟩ a b a_le_b
    · simp
    · simp
    ⟩ := by
  intro chain
  simp_all only [OrderHom.coe_mk, Chain.map, ← iSup_eq_ωSup, OrderHom.comp_coe, Function.comp_apply]
  apply le_antisymm
  · simp only [Finset.sup'_le_iff]
    intro i hi
    have := hf i chain
    simp_all only [← iSup_eq_ωSup, iSup_le_iff]
    intro j
    refine le_iSup_iff.mpr ?_
    simp only [Finset.sup'_le_iff]
    intro b h
    convert h j i hi
  · simp only [Finset.le_sup'_iff, iSup_le_iff, Finset.sup'_le_iff]
    obtain ⟨i, hi₁, hi₂⟩ := Finset.exists_mem_eq_sup' S_Nonempty (fun i ↦ f i (ωSup chain))
    use i, hi₁
    rw [←hi₂]
    simp only [Finset.le_sup'_iff]
    intro n i' hi'
    use i', hi'
    exact (f i').mono (le_ωSup _ _)
