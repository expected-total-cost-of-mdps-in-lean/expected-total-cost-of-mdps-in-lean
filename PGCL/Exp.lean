import Mathlib.Data.ENNReal.Basic

variable {ϖ : Type*}
def States (ϖ : Type*) := ϖ → ENNReal

instance : Nonempty (States ϖ) := ⟨λ_ => Inhabited.default⟩

abbrev Exp (ϖ : Type*) := States ϖ → ENNReal
abbrev BExpr (ϖ : Type*) := States ϖ → Bool
def ProbExp (ϖ : Type*) := { e : Exp ϖ // ∀σ, 0 < e σ ∧ e σ ≤ 1 }

def States.subst [DecidableEq ϖ] (σ : States ϖ) (x : ϖ) (v : ENNReal) : States ϖ := λ α => if x = α then v else σ α

def Exp.subst [DecidableEq ϖ] (e : Exp ϖ) (x : ϖ) (A : Exp ϖ) : Exp ϖ :=
  λs => e (λy => if x = y then A s else s y)

notation σ "[" x " ↦ " v "]" => States.subst σ x v

@[simp]
theorem Exp.subst_lift [DecidableEq ϖ] (e : Exp ϖ) (x : ϖ) (A : Exp ϖ) (σ : States ϖ) : (e.subst x A) σ = e (σ[x ↦ A σ]) := rfl

def BExpr.not (x : BExpr ϖ) : BExpr ϖ := λs => !x s
noncomputable def BExpr.probOf (x : BExpr ϖ) : Exp ϖ := λs => if x s then 1 else 0

@[simp]
theorem BExpr.true_probOf {b : BExpr ϖ} (h : b σ = true) : b.probOf σ = 1 := by simp [probOf, h]
@[simp]
theorem BExpr.false_probOf {b : BExpr ϖ} (h : b σ = false) : b.probOf σ = 0 := by simp [probOf, h]
@[simp]
theorem BExpr.true_not_probOf {b : BExpr ϖ} (h : b σ = true) : b.not.probOf σ = 0 := by simp [probOf, not, h]
@[simp]
theorem BExpr.false_not_probOf {b : BExpr ϖ} (h : b σ = false) : b.not.probOf σ = 1 := by simp [probOf, not, h]
