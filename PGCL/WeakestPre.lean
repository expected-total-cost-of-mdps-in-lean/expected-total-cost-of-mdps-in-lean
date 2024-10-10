import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Rat
import Mathlib.Control.Fix
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Tactic.Use
import PGCL.Exp
import PGCL.pGCL

namespace pGCL

variable {ϖ : Type*}
variable [DecidableEq ϖ]

local notation "dwp〚" X "〛" C => pGCL.dwp X C

def lfp {α} [CompleteLattice α] (f : α → α) : α := sInf {a | f a ≤ a}

theorem lfp.monotone {α} [CompleteLattice α] : Monotone (lfp : (α → α) → α) := by
  intro f g h
  unfold lfp
  simp only [le_sInf_iff, Set.mem_setOf_eq]
  intro x gx_le_x
  apply sInf_le
  simp only [Set.mem_setOf_eq]
  exact ge_trans gx_le_x (h x)

@[simp]
theorem lfp.eq_OrderHom.lfp [CompleteLattice α] (f : α → α) (h : Monotone f) : lfp f = OrderHom.lfp (OrderHom.mk f h) := rfl

noncomputable def dwp (C : pGCL ϖ) (X : Exp ϖ) : Exp ϖ := match C with
  | .skip => X
  | .assign x A => X.subst x A
  | .seq C₁ C₂ => C₁.dwp (C₂.dwp X)
  | .prob C₁ p C₂ => p.val * C₁.dwp X + (1 - p.val) * C₂.dwp X
  | .nonDet C₁ C₂ => C₁.dwp X ⊓ C₂.dwp X
  | .ite B C₁ C₂ => B.probOf * C₁.dwp X + B.not.probOf * C₂.dwp X
  | .loop B C' => lfp λY => B.probOf * C'.dwp Y + B.not.probOf * X
  | .tick e => e + X

theorem dwp.monotone (C : pGCL ϖ) : Monotone (C.dwp) := by
  intro X₁ X₂ X₁_le_X₂
  induction C generalizing X₁ X₂ with simp only [dwp]
  | skip => assumption
  | assign x e =>
    intro σ ; exact X₁_le_X₂ _
  | seq _ C₂ ih₁ ih₂ => exact ih₁ (ih₂ X₁_le_X₂)
  | prob C₁ p C₂ ih₁ ih₂ =>
    intro σ
    apply add_le_add <;> apply mul_le_mul_left' <;> apply_assumption <;> assumption
  | nonDet C₁ C₂ ih₁ ih₂ =>
    intro σ
    simp only [Pi.inf_apply, le_inf_iff, inf_le_iff]
    constructor
    · left  ; exact ih₁ X₁_le_X₂ σ
    · right ; exact ih₂ X₁_le_X₂ σ
  | ite B C₁ C₂ ih₁ ih₂ =>
    intro σ
    apply add_le_add <;> apply mul_le_mul_left'
    · apply ih₁ X₁_le_X₂
    · apply ih₂ X₁_le_X₂
  | loop B C' =>
    apply lfp.monotone
    intro Y σ ; simp only [Pi.add_apply, Pi.mul_apply]
    by_cases h : B σ
    · simp only [h, BExpr.true_probOf, one_mul, BExpr.true_not_probOf, zero_mul, add_zero, le_refl]
    · simp only [h, BExpr.false_probOf, zero_mul, BExpr.false_not_probOf, one_mul, zero_add]
      exact X₁_le_X₂ σ
  | tick e =>
    intro σ
    apply add_le_add_left (X₁_le_X₂ σ)

noncomputable def dwp_loop_f (B : BExpr ϖ) (C' : pGCL ϖ) (X : Exp ϖ) : Exp ϖ →o Exp ϖ := ⟨fun Y => B.probOf * C'.dwp Y + B.not.probOf * X, by
  intro _ _ h σ
  simp only [Pi.add_apply, Pi.mul_apply]
  by_cases h' : B σ
  · simp only [h', BExpr.true_probOf, one_mul, BExpr.true_not_probOf, zero_mul, add_zero]
    exact dwp.monotone C' h σ
  · simp_all⟩
noncomputable def dwp_loop_f' (B : BExpr ϖ) (C' : pGCL ϖ) (X : Exp ϖ) : (States ϖ → ENNReal) →o (States ϖ → ENNReal) := ⟨fun (Y : States ϖ → ENNReal) ↦ (dwp_loop_f B C' X) Y, by
  intro _ _ h σ
  exact (dwp_loop_f B C' X).mono h σ⟩
theorem dwp_loop (B : BExpr ϖ) (C' : pGCL ϖ) : (loop B C').dwp = fun X ↦ OrderHom.lfp (C'.dwp_loop_f B X) := by
  ext X
  conv => left ; unfold dwp
  rw [lfp.eq_OrderHom.lfp]
  rfl
