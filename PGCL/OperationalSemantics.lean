import PGCL.pGCL
import PGCL.WeakestPre
import MDP.OptEC

theorem Finset.filter_pair {α : Type u_1} [DecidableEq α] (p : α → Prop) [DecidablePred p] (a b : α) :
Finset.filter p {a, b} = if p a ∧ p b then {a, b} else if p a then {a} else if p b then {b} else ∅ := by
  simp only [Finset.filter_insert, Finset.filter_singleton]
  by_cases p a
  · simp_all only [ite_true, true_and, ite_false]
    by_cases p b
    · simp_all only [ite_true]
    · simp_all only [ite_false, Finset.insert_empty]
  · simp_all only [ite_false, false_and]

theorem Finset.filterMap_singleton {α β : Type*} {f : α → Option β} {hf : ∀ (a a' : α), ∀ b ∈ f a, b ∈ f a' → a = a'} (a : α) :
  ({a} : Finset α).filterMap f hf = match f a with | some b => {b} | none => {}
:= by
  ext B
  simp
  split
  · simp_all
    exact eq_comm
  · simp_all
theorem Finset.filterMap_pair {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → Option β} {hf : ∀ (a a' : α), ∀ b ∈ f a, b ∈ f a' → a = a'} (a a' : α) :
  ({a, a'} : Finset α).filterMap f hf =
    match (f a, f a') with
    | (some b, some b') => {b, b'}
    | (none, some b')   => {b'}
    | (some b, none)    => {b}
    | (none, none) => {}
:= by
  ext B
  simp only [mem_filterMap, mem_insert, mem_singleton, exists_eq_or_imp, exists_eq_left]
  split
  · simp_all
    apply or_congr eq_comm eq_comm
  · simp_all [eq_comm]
  · simp_all [eq_comm]
  · simp_all

theorem SizeOf.ne_if {α : Sort*} [inst : SizeOf α] {a b : α} (h : @SizeOf.sizeOf α inst a ≠ @SizeOf.sizeOf α inst  b) : a ≠ b := by
  exact fun a_1 ↦ h (congrArg sizeOf a_1)

noncomputable instance : One { p : ENNReal // 0 < p ∧ p ≤ 1 } := ⟨1, by simp⟩

@[simp]
theorem Exp_zero (σ : States ϖ) : (0 : Exp ϖ) σ = 0 := rfl
-- @[simp]
-- theorem Exp_bot (σ : States ϖ) : (⊥ : Exp ϖ) σ = 0 := rfl
@[simp]
theorem Exp_one (σ : States ϖ) : (1 : Exp ϖ) σ = 1 := rfl
@[simp]
theorem Exp_one_mul (σ : States ϖ) (x : Exp ϖ) : (1 : { p : ENNReal // 0 < p ∧ p ≤ 1}) * x σ = x σ := one_mul (x σ)
@[simp]
theorem ENNReal.prod_one_mul (x : ENNReal) : (1 : { p : ENNReal // 0 < p ∧ p ≤ 1}).val * x = x := one_mul x

theorem ENNReal.add_one_minus_eq_one (a : ENNReal) (ha : a ≤ 1) : a + (1 - a) = 1 := by
  induction a
  · absurd ha
    exact of_decide_eq_false rfl
  · simp_all only [ENNReal.some_eq_coe, ENNReal.coe_le_one_iff, ge_iff_le, add_tsub_cancel_of_le]

theorem prob_complete (p : ProbExp ϖ) (x : ENNReal) (σ : States ϖ) : p.val σ * x + (1 - p.val σ) * x = x := by
  rw [mul_comm,
      mul_comm (1 - p.val σ),
      LeftDistribClass.left_distrib x (p.val σ) (1 - p.val σ) |>.symm,
      ENNReal.add_one_minus_eq_one _ (p.prop σ).right]
  exact MulOneClass.mul_one x

namespace pGCL

@[reducible]
def Conf (ϖ : Type*) := Option (Option (pGCL ϖ) × States ϖ)

namespace Conf

variable {ϖ : Type*}
variable [DecidableEq ϖ]

notation:90 "·⟨⇓" ϖ "," rhs "⟩" => some ((none : Option (pGCL ϖ)), rhs)
notation:90 "·⟨" lhs "," rhs "⟩" => some (some lhs, rhs)
notation:90 "·⟨skip," rhs "⟩" => ·⟨pGCL.skip, rhs⟩
notation:90 "·⟨if " B " then " C₁ " else " C₂ "," rhs "⟩" => ·⟨pGCL.ite B C₁ C₂, rhs⟩
notation:90 "·⟨" C₁ "[]" C₂ "," rhs "⟩" => ·⟨pGCL.nonDet C₁ C₂, rhs⟩
notation:90 "·⟨" C₁ "[" p "]" C₂ "," rhs "⟩" => ·⟨pGCL.prob C₁ p C₂, rhs⟩
notation:90 "·⟨while (" B ") " C "," rhs "⟩" => ·⟨pGCL.loop B C, rhs⟩
notation:90 "·⟨tick " E "," rhs "⟩" => ·⟨pGCL.tick E, rhs⟩

instance : Bot (Conf ϖ) := ⟨none⟩

instance : Coe (Option (pGCL ϖ) × States ϖ) (Conf ϖ) where
  coe := some

def isNone_iff (c : Conf ϖ) : Option.isNone c ↔ c = ⊥ := by
  simp [Bot.bot]
def isSome_iff (c : Conf ϖ) : Option.isSome c ↔ c ≠ ⊥ := by
  simp [Bot.bot]
  symm
  exact Option.ne_none_iff_isSome

-- @[reducible]
-- def C (c' : Conf ϖ) (h : c' ≠ ⊥) : pGCL ϖ := (c'.get (by simp [isSome_iff, h])).1
-- @[reducible]
-- def σ (c' : Conf ϖ) (h : c' ≠ ⊥) : States ϖ := (c'.get (by simp [isSome_iff, h])).2

noncomputable instance decidableEq : DecidableEq (Conf ϖ) := Classical.typeDecidableEq (Conf ϖ)

inductive Act := | L | R | N
deriving BEq, DecidableEq, Inhabited

noncomputable instance Act.instFintype : Fintype Act where
  elems := {.L, .R, .N}
  complete := fun a ↦ by cases a <;> simp only [Finset.mem_insert, reduceCtorEq, Finset.mem_singleton, or_self, or_false, or_true]

@[reducible]
def Choice (ϖ : Type*) := Act × Conf ϖ × { p : ENNReal // 0 < p ∧ p ≤ 1 }

namespace Choice

@[reducible]
def Act  (c: Choice ϖ) : Act      := c.1
@[reducible]
def Conf (c: Choice ϖ) : Conf ϖ   := c.2.1
-- @[reducible]
-- def C    (c: Choice ϖ) (h : c.Conf ≠ ⊥) : pGCL ϖ   := c.Conf.C h
-- @[reducible]
-- def σ    (c: Choice ϖ) (h : c.Conf ≠ ⊥) : States ϖ := c.Conf.σ h
@[reducible]
def P    (c: Choice ϖ) : { p : ENNReal // 0 < p ∧ p ≤ 1 }  := c.2.2

noncomputable instance : One { p : ENNReal // 0 < p ∧ p ≤ 1 } := ⟨1, by simp⟩

@[simp]
theorem one_prob_is₀₁ : is₀₁ (1 : { p : ENNReal // 0 < p ∧ p ≤ 1 }).val := Or.inr rfl

end Choice

end Conf

abbrev wrap (C₂ : pGCL ϖ) : Conf ϖ → Conf ϖ
  | ·⟨c', σ'⟩ => ·⟨c' ; C₂, σ'⟩
  | ·⟨⇓ ϖ, σ'⟩ => ·⟨C₂, σ'⟩
  | ⊥ => ⊥

theorem wrap.inj {C₂ : pGCL ϖ} : Function.Injective C₂.wrap := by
  intro c₁ c₂
  simp_all [wrap]
  split <;> split <;> try (simp ; done)
  all_goals
    simp
    intro h
    absurd h
    apply SizeOf.ne_if
    simp

namespace Conf

variable {ϖ : Type*}
variable [DecidableEq ϖ]

theorem Prod.eq {α β} {a₁ a₂ : α} {b₁ b₂ : β} (h₁ : a₁ = a₂) (h₂ : b₁ = b₂) : (a₁, b₁) = (a₂, b₂) :=
  instDecidableEqProd.proof_1 a₁ b₁ a₂ b₂ h₁ h₂

@[reducible]
def op_seq (C' : pGCL ϖ) : Choice ϖ ↪ Choice ϖ :=
  ⟨fun c ↦ (c.Act,C'.wrap c.Conf,c.P), by
    intro a b h
    simp at h
    obtain ⟨h₁, h₂, h₃⟩ := h
    apply Prod.ext_iff.mpr
    simp_all
    apply Prod.ext_iff.mpr
    simp_all
    by_contra q
    absurd h₂
    simp [Choice.Conf]
    refine Function.Injective.ne ?intro.intro.hf q
    exact wrap.inj⟩

@[reducible]
noncomputable def op' : pGCL ϖ → States ϖ → Finset (Choice ϖ)
  | .skip => λσ ↦ {(.N,some ⟨none, σ⟩,1)}
  | .assign x A => λσ ↦ {(.N,some ⟨none, σ[x ↦ A σ]⟩,1)}
  | .seq C₁ C₂ => λσ ↦ Finset.map (op_seq C₂) (op' C₁ σ)
  | .prob C₁ b C₂ => λσ ↦
    if C₁ = C₂ then
      {(.N,some ⟨C₁, σ⟩,1)}
    else
      let p := b.val σ
      if h : p = 1 then
        {(.N,some ⟨C₁, σ⟩,⟨p, by simp [h]⟩)}
      else
        let p' : { p : ENNReal // 0 < p ∧ p ≤ 1 } := ⟨1 - p, by simp [tsub_le_iff_right, self_le_add_right, lt_of_le_of_ne (b.property σ).right h]⟩
        {(.N,some ⟨C₁, σ⟩,⟨p, b.property σ⟩), (.N,some ⟨C₂, σ⟩,p')}
  | .nonDet C₁ C₂ => λσ ↦
    {(.L,some ⟨C₁, σ⟩,1), (.R,some ⟨C₂, σ⟩,1)}
  | .ite B C₁ C₂ => λσ ↦
    if B σ then {(.N,some ⟨C₁, σ⟩,1)} else {(.N,some ⟨C₂, σ⟩,1)}
  | .loop B C => λσ ↦
    if B σ then {(.N,some ⟨C ; .loop B C, σ⟩,1)} else {(.N,some ⟨none, σ⟩,1)}
  | .tick _ => λσ ↦ {(.N,some ⟨none, σ⟩,1)}


noncomputable def op'' : Conf ϖ → Finset (Choice ϖ)
  | ⊥ => {⟨.N,⊥,1⟩}
  | ·⟨⇓ ϖ, _⟩ => {⟨.N,⊥,1⟩}
  | ·⟨skip, σ⟩ => {(.N,some ⟨none, σ⟩,1)}
  | ·⟨x ::= A, σ⟩ => {(.N,some ⟨none, σ[x ↦ A σ]⟩,1)}
  | ·⟨C₁ ; C₂, σ⟩ => Finset.map (op_seq C₂) (op' C₁ σ)
  | ·⟨.prob C₁ b C₂, σ⟩ =>
    if C₁ = C₂ then
      {(.N,some ⟨C₁, σ⟩,1)}
    else
      let p := b.val σ
      if h : p = 1 then
        {(.N,some ⟨C₁, σ⟩,⟨p, by simp [h]⟩)}
      else
        let p' : { p : ENNReal // 0 < p ∧ p ≤ 1 } := ⟨1 - p, by simp [tsub_le_iff_right, self_le_add_right, lt_of_le_of_ne (b.property σ).right h]⟩
        {(.N,some ⟨C₁, σ⟩,⟨p, b.property σ⟩), (.N,some ⟨C₂, σ⟩,p')}
  | ·⟨C₁ [] C₂, σ⟩ =>
    {(.L,some ⟨C₁, σ⟩,1), (.R,some ⟨C₂, σ⟩,1)}
  | ·⟨if B then C₁ else C₂, σ⟩ =>
    if B σ then {(.N,some ⟨C₁, σ⟩,1)} else {(.N,some ⟨C₂, σ⟩,1)}
  | ·⟨while (B) C, σ⟩ =>
    if B σ then {(.N,some ⟨C ; .loop B C, σ⟩,1)} else {(.N,some ⟨none, σ⟩,1)}
  | ·⟨tick _, σ⟩ => {(.N,some ⟨none, σ⟩,1)}

noncomputable def op : Conf ϖ → Finset (Choice ϖ)
  | ⊥ => {⟨.N,⊥,1⟩}
  | ·⟨⇓ ϖ, _⟩ => {⟨.N,⊥,1⟩}
  | ·⟨c, σ⟩ => op' c σ

noncomputable def op.induct (p : Conf ϖ → Prop) (c : Conf ϖ)
  (bot : p ⊥)
  (sink : (σ : States ϖ) →
    p (·⟨⇓ ϖ, σ⟩))
  (skip : (σ : States ϖ) →
    p (·⟨skip, σ⟩))
  (assign : (σ : States ϖ) → (x : ϖ) → (e : Exp ϖ) →
    p (·⟨x ::= e, σ⟩))
  (seq : (σ : States ϖ) → (C₁ C₂ : pGCL ϖ) → (ih₁ : ∀ σ', p (·⟨C₁, σ'⟩)) → (ih₂ : ∀ σ', p (·⟨C₂, σ'⟩)) →
    p (·⟨C₁ ; C₂, σ⟩))
  (prob : (σ : States ϖ) → (C₁ : pGCL ϖ) → (b : ProbExp ϖ) → (C₂ : pGCL ϖ) → (ih₁ : ∀ σ', p (·⟨C₁, σ'⟩)) → (ih₂ : ∀ σ', p (·⟨C₂, σ'⟩)) →
    p (·⟨.prob C₁ b C₂, σ⟩))
  (nonDet : (σ : States ϖ) → (C₁ C₂ : pGCL ϖ) → (ih₁ : ∀ σ', p (·⟨C₁, σ'⟩)) → (ih₂ : ∀ σ', p (·⟨C₂, σ'⟩)) →
    p (·⟨C₁ [] C₂, σ⟩))
  (ite : (σ : States ϖ) → (b : BExpr ϖ) → (C₁ C₂ : pGCL ϖ) → (ih₁ : ∀ σ', p (·⟨C₁, σ'⟩)) → (ih₂ : ∀ σ', p (·⟨C₂, σ'⟩)) →
    p (·⟨if b then C₁ else C₂, σ⟩))
  (loop : (σ : States ϖ) → (b : BExpr ϖ) → (C' : pGCL ϖ) → (ih : ∀ σ', p (·⟨C', σ'⟩)) →
    p (·⟨while (b) C', σ⟩))
  (tick : (σ : States ϖ) → (r : Exp ϖ) →
    p (·⟨tick r, σ⟩))
:
  p c
:= by
  rcases c with _ | ⟨_ | C, σ⟩
  · exact bot
  · exact sink σ
  · induction C generalizing σ with
  | skip => exact skip σ
  | assign _ _ => apply assign σ
  | seq C₁ C₂ ih₁ ih₂ => exact seq σ C₁ C₂ ih₁ ih₂
  | prob C₁ b C₂ ih₁ ih₂ => apply prob σ C₁ b C₂ ih₁ ih₂
  | nonDet C₁ C₂ ih₁ ih₂ => exact nonDet σ C₁ C₂ ih₁ ih₂
  | ite b C₁ C₂ ih₁ ih₂ => exact ite σ b C₁ C₂ ih₁ ih₂
  | loop b C' ih => exact loop σ b C' ih
  | tick _ => apply tick σ

theorem op_is₀₁ (s : Conf ϖ) (a : Act) : is₀₁ (op s |>.filter (·.1 = a) |>.sum (·.2.2.val)) := by
  simp [op]
  induction s using op.induct with
  | bot | skip _ =>
    all_goals try (simp [Bot.bot, op, Finset.filter_singleton] ; split_ifs <;> simp)
  | seq σ c₁ c₂ ih₁ =>
    letI compute (set : Finset (Choice ϖ)) := set.filter (·.Act = a) |>.sum (·.P.val)
    have : compute (op' (c₁ ; c₂) σ) = compute (op' c₁ σ) := by
      simp only [Finset.sum_filter, op', Finset.sum_map, Function.Embedding.coeFn_mk, compute]
    dsimp only [compute] at this
    rw [this]
    exact ih₁ σ
  | prob σ c₁ b c₂ _ _ =>
    dsimp only [op']
    by_cases h : Act.N = a <;> split_ifs with h'
    all_goals simp_all [h, h', b.property, Finset.filter_singleton, Finset.sum_filter, Choice.one_prob_is₀₁]
  | nonDet =>
    simp [op', Finset.filter_singleton, Finset.sum_filter]
    split_ifs with h₁ h₂ <;> try simp only [add_zero, zero_add, is₀₁_one, is₀₁_zero, Choice.one_prob_is₀₁]
    · rw [←h₁] at h₂ ; contradiction
  | _ =>
    simp [op, op', Finset.filter_singleton, Finset.sum_filter, Choice.one_prob_is₀₁]
    split_ifs <;> simp [Finset.sum_empty, Finset.sum_singleton, is₀₁_zero, is₀₁_one, is₀₁_if_zero_or_one, Choice.one_prob_is₀₁]
    all_goals split_ifs <;> simp only [Choice.one_prob_is₀₁, is₀₁_zero]

theorem exists_mem_singleton {α : Type*} [Nonempty α] : ∃ x, x ∈ ({x} : Finset α) := by
  simp only [Finset.mem_singleton, exists_const]

theorem op_progress (C : Conf ϖ) : ∃ (a : Act) (C' : Conf ϖ) (p : { p : ENNReal // 0 < p ∧ p ≤ 1 }), (a, C', p) ∈ C.op := by
  dsimp only [op]
  induction C using op.induct with
  | bot | skip => simp
  | seq σ c₁ c₂ ih =>
    simp_all only [Subtype.exists, op', op_seq, Finset.mem_map, Function.Embedding.coeFn_mk,
      Prod.mk.injEq, Prod.exists, wrap, Choice.Conf]
    rcases ih σ with ⟨a', C', p', hp', h'⟩
    use a', c₂.wrap C', p', hp'
    use a', C', p', hp'
  | prob σ c₁ b c₂ =>
    dsimp only [op', op_seq]
    simp
    by_cases h : c₁ = c₂
    · simp [h]
      use 1
      simp only [zero_lt_one, le_refl, and_self, exists_true_left]
      rfl
    · simp only [h, ↓reduceIte]
      by_cases h : b.val σ = 1
      · simp [h]
      · simp [h]
        use .N, some ⟨c₁, σ⟩, b.val (σ)
        simp only [and_self, and_true, true_and, true_or]
        exact b.property (σ)
  | nonDet σ C₁ C₂ =>
    dsimp only [op']
    use .L, some (some C₁, σ), 1
    exact Finset.mem_insert_self _ _
  | loop σ b C' =>
    dsimp only [op', op_seq]
    by_cases h : b σ = true
    · simp [h, ↓reduceIte, Finset.mem_singleton, Prod.mk.injEq, exists_and_left,
      exists_eq_right, exists_eq]
    · simp [h, Bool.false_eq_true, ↓reduceIte, Finset.mem_singleton, Prod.mk.injEq,
      exists_and_left, exists_eq_right, exists_eq]
  | ite σ b C₁ C₂ =>
    dsimp only [op', op_seq]
    by_cases h : b σ = true
    · use .N, some (C₁, σ), 1
      simp [h]
    · use .N, some (C₂, σ), 1
      simp [h]
  | _ =>
    dsimp [op']
    simp [exists_mem_singleton]

noncomputable def MDP : MDP (Conf ϖ) Act :=
  MDP.mk_from_op op op_is₀₁ op_progress

noncomputable def act (C : Conf ϖ) : Finset Act := Conf.MDP.act₀ C
noncomputable def act_nonempty (C : Conf ϖ) : C.act.Nonempty := MDP.act₀_nonempty MDP C
noncomputable def act_inf (C : Conf ϖ) (f : Act → ENNReal) : ENNReal := C.act.inf' C.act_nonempty f
@[simp] theorem act_inf_def (C : Conf ϖ) (f : Act → ENNReal) : C.act_inf f = C.act.inf' C.act_nonempty f := rfl

noncomputable def cost_X (X : Exp ϖ)
  | ·⟨⇓ ϖ, σ⟩ => X σ
  | ·⟨tick r, σ⟩ => r σ
  | ·⟨c' ; _, σ⟩ => cost_X X (·⟨c', σ⟩)
  | _ => 0

omit [DecidableEq ϖ] in
theorem cost_X.mono (C : Conf ϖ) : Monotone (fun X ↦ cost_X X C) := by
  intro X₁ X₂ h
  rcases C with _ | ⟨_ | c', _⟩
  · simp [cost_X]
  · simp [cost_X]
    apply_assumption
  · induction c' <;> simp [cost_X]
    assumption

end Conf

variable {ϖ : Type*}
variable [DecidableEq ϖ]

open MDP Conf

noncomputable def dop (C : pGCL ϖ) (X : Exp ϖ) : Exp ϖ := fun σ ↦ lfp_Φ MDP (cost_X X) (some ⟨C, σ⟩)

noncomputable def dop.monotone (C : pGCL ϖ) : Monotone C.dop := by
  intro _ _ h σ
  simp [pGCL.dop]
  exact MDP.lfp_Φ.mono Conf.MDP _ (cost_X.mono · h)

namespace Conf

variable {σ : States ϖ}

-- @[reducible]
noncomputable abbrev P (C₁ : Conf ϖ) (a : Act) (C₂ : Conf ϖ) := Conf.MDP.P C₁ a C₂

@[simp] theorem cost_X.final   : cost_X X none                  = 0             := by simp [cost_X]
@[simp] theorem cost_X.skip    : cost_X X (·⟨.skip, σ⟩)         = 0             := by simp [cost_X]
@[simp] theorem cost_X.sink    : cost_X X (some (none, σ))      = X σ           := by simp [cost_X]
@[simp] theorem cost_X.assign  : cost_X X (·⟨x ::= e, σ⟩)       = 0             := by simp [cost_X]
@[simp] theorem cost_X.prob    : cost_X X (·⟨.prob C₁ p C₂, σ⟩) = 0             := by simp [cost_X]
@[simp] theorem cost_X.nonDet  : cost_X X (·⟨.nonDet C₁ C₂, σ⟩) = 0             := by simp [cost_X]
@[simp] theorem cost_X.ite     : cost_X X (·⟨.ite b C₁ C₂, σ⟩)  = 0             := by simp [cost_X]
@[simp] theorem cost_X.loop    : cost_X X (·⟨.loop b C', σ⟩)    = 0             := by simp [cost_X]
@[simp] theorem cost_X.tick    : cost_X X (·⟨.tick r, σ⟩)       = r σ           := by simp [cost_X]

theorem P_reduces (C₁ C₂ : Conf ϖ) (a : Act) : P C₁ a C₂ = (op C₁ |>.filter (fun x ↦ x.1 = a ∧ x.2.1 = C₂) |>.sum (·.2.2.val)) := by
  simp [P, Conf.MDP]
  simp [MDP.mk_from_op]
  simp [MDP.mk_from_succs]
  simp [Finset.sum_filter]
  simp_all [Finset.sum_filter]
  congr
  ext x
  by_cases h : x.1 = a
  · simp_all
  · simp_all

theorem act₀_reduces (C₁ : Conf ϖ) : Conf.MDP.act₀ C₁ = (op C₁ |>.image (·.1)) := by
  ext a
  rw [MDP.act₀_mem_iff_act_mem]
  rw [MDP.act]
  simp
  rw [←MDP.P_pos_iff_sum_eq_one]
  rw [MDP]
  rw [MDP.mk_from_op, MDP.mk_from_succs]
  simp only [Fintype.complete, true_and]
  simp only [Finsupp.support_onFinset, ne_eq, Finset.sum_eq_zero_iff, Finset.mem_filter,
    Finset.mem_image, Prod.exists, exists_eq_right, and_imp, Prod.forall, Subtype.forall,
    not_forall, Classical.not_imp, exists_and_right]
  constructor <;> intro h
  · rcases h with ⟨q, h⟩
    simp_all
    rcases h with ⟨h₁, _⟩
    use q
  · rcases h with ⟨q, p, hp, h⟩
    use q
    simp
    constructor
    · use p
      constructor
      · use hp
      · simp_all
    · use q, p
      simp_all
      exact hp.left.ne.symm
@[simp] theorem act₀_eq_act (C : Conf ϖ) : Conf.MDP.act₀ C = C.act := rfl
theorem act_reduces (C₁ : Conf ϖ) : C₁.act = (op C₁ |>.image (·.1)) := by simp only [act, act₀_reduces]

theorem succs_reduces (C₁ : Conf ϖ) (a : Act) : Conf.MDP.succs a C₁ = (op C₁ |>.filter (·.1 = a) |>.image (·.2.1)) := by
  rw [Conf.MDP]
  rw [MDP.mk_from_op]
  rw [MDP.mk_from_succs]
  rw [MDP.succs]
  simp only [Finset.sum_filter]
  simp_all only [Finset.mem_filter, and_imp, Prod.forall, Subtype.forall, implies_true,
    Finset.sum_image, Finset.sum_filter]
  ext x
  simp_all only [Finsupp.mem_support_iff, Finsupp.onFinset_apply, ne_eq, Finset.sum_eq_zero_iff,
    ite_eq_right_iff, Prod.forall, Subtype.forall, not_forall, Classical.not_imp, exists_and_right,
    Finset.mem_image, Finset.mem_filter, Prod.exists, Subtype.exists, exists_eq_right]
  constructor
  · simp_all only [exists_prop, exists_and_left, exists_and_right, forall_exists_index, and_imp]
    intro a' c p p_le_1 h a_'_eq_a h
    intros
    use p
    simp_all only [and_self, exists_const]
  · simp_all only [exists_prop, exists_and_left, exists_and_right, forall_exists_index]
    intro p hp h
    use a, x
    simp only [Prod.mk.eta, true_and]
    use p
    simp_all only [and_self, exists_const, true_and]
    exact hp.left.ne.symm

theorem mem_op_if {C C' : Conf ϖ} {α : Act} (hs : ¬Conf.MDP.P C α C' = 0) :
  ∃p, (α, C', p) ∈ C.op
:= by
  simp [P_reduces] at hs
  obtain ⟨α', C'', p, ⟨hp, hp'⟩, _⟩ := hs
  use ⟨p, hp⟩
  simp_all

@[simp] theorem act.none     : Conf.act (none : Conf ϖ)       = {.N} := by simp [act_reduces, op, op', Finset.filter_singleton, Bot.bot]
@[simp] theorem act.skip     : Conf.act (·⟨.skip, σ⟩)         = {.N} := by simp [act_reduces, op, op', Finset.filter_singleton]
@[simp] theorem act.sink     : Conf.act (·⟨⇓ ϖ, σ⟩)           = {.N} := by simp [act_reduces, op, op', Finset.filter_singleton]
@[simp] theorem act.assign   : Conf.act (·⟨x ::= e, σ⟩)       = {.N} := by simp [act_reduces, op, op', Finset.filter_singleton]
@[simp] theorem act.seq      : Conf.act (·⟨C₁ ; C₂, σ⟩)    = Conf.act (some ⟨C₁, σ⟩) := by
  simp only [act_reduces, op, op', op_seq, Finset.map_eq_image, Function.Embedding.coeFn_mk, Finset.image_image]
  ext α
  simp [Choice.Act]
@[simp] theorem act.prob     : Conf.act (·⟨.prob C₁ p C₂, σ⟩) = {.N} := by
  simp only [act_reduces, act_reduces, op, ne_eq, not_false_eq_true, ↓reduceDIte, op']
  split_ifs <;> simp [act_reduces, op, op', Finset.filter_singleton, Finset.filter_pair]
@[simp] theorem act.nonDet_L : Conf.act (·⟨.nonDet C₁ C₂, σ⟩) = {.L, .R} := by simp [act_reduces, op, op', Finset.filter_singleton, Finset.filter_pair]
@[simp] theorem act.ite      : Conf.act (·⟨.ite b C₁ C₂, σ⟩)  = {.N} := by
  simp only [act_reduces, act_reduces, op, ne_eq, not_false_eq_true, ↓reduceDIte, op', Option.get_some]
  split_ifs with h
  · simp only [Finset.image_singleton]
  · simp only [Finset.image_singleton]
@[simp] theorem act.loop     : Conf.act (·⟨.loop b C', σ⟩)    = {.N} := by
  simp only [act_reduces, act_reduces, op, ne_eq, not_false_eq_true, ↓reduceDIte, op']
  split_ifs with h
  · simp only [Finset.image_singleton]
  · simp only [Finset.image_singleton]
@[simp] theorem act.tick     : Conf.act (·⟨.tick r, σ⟩)       = {.N} := by simp [act_reduces, op, op', Finset.filter_singleton]


@[simp] theorem succs.none_none: Conf.MDP.succs .N (none : Conf ϖ) = {none} := by simp [succs_reduces, op, op', Finset.filter_singleton, Bot.bot]
@[simp] theorem succs.skip     : Conf.MDP.succs .N (·⟨.skip, σ⟩)   = {·⟨⇓ ϖ, σ⟩} := by simp [succs_reduces, op, op', Finset.filter_singleton]
@[simp] theorem succs.sink     : Conf.MDP.succs .N (·⟨⇓ ϖ, σ⟩)     = {none} := by simp [succs_reduces, op, op', Finset.filter_singleton, Bot.bot]
@[simp] theorem succs.assign   : Conf.MDP.succs .N (·⟨x ::= e, σ⟩) = {·⟨⇓ ϖ, σ[x ↦ e σ]⟩} := by simp [succs_reduces, op, op', Finset.filter_singleton]
@[simp] theorem succs.prob     : Conf.MDP.succs .N (·⟨.prob C₁ p C₂, σ⟩) = if p.val σ = 1 then {some ⟨C₁, σ⟩} else {some ⟨C₁, σ⟩, some ⟨C₂, σ⟩} := by
  split_ifs with h
  · simp only [succs_reduces, op, ne_eq, not_false_eq_true, ↓reduceDIte, op',
    Option.get_some, h]
    split_ifs
    · simp only [Finset.filter_singleton, ↓reduceIte, Finset.image_singleton]
    · simp only [Finset.filter_singleton, ↓reduceIte, Finset.image_singleton]
  · simp only [succs_reduces, op, ne_eq, not_false_eq_true, ↓reduceDIte, op',
    Option.get_some, h]
    split_ifs with h'
    · simp [Finset.filter_singleton, h']
    · simp [Finset.filter_pair, h']
@[simp] theorem succs.nonDet_L : Conf.MDP.succs .L (·⟨.nonDet C₁ C₂, σ⟩) = {some ⟨C₁, σ⟩} := by simp [succs_reduces, op, op', Finset.filter_singleton, Finset.filter_pair]
@[simp] theorem succs.nonDet_R : Conf.MDP.succs .R (·⟨.nonDet C₁ C₂, σ⟩) = {some ⟨C₂, σ⟩} := by simp [succs_reduces, op, op', Finset.filter_singleton, Finset.filter_pair]
@[simp] theorem succs.ite      : Conf.MDP.succs .N (·⟨.ite b C₁ C₂, σ⟩)  = if b σ then {some ⟨C₁, σ⟩} else {some ⟨C₂, σ⟩} := by
  split_ifs with h
  · simp [succs_reduces, op, op', Finset.filter_singleton, h]
  · simp [succs_reduces, op, op', Finset.filter_singleton, h]
@[simp] theorem succs.loop     : Conf.MDP.succs .N (·⟨.loop b C', σ⟩)    = if b σ then {some ⟨C' ; .loop b C', σ⟩} else {·⟨⇓ ϖ, σ⟩} := by
  simp only [succs_reduces, op, ne_eq, not_false_eq_true, ↓reduceDIte, op', Option.get_some]
  split_ifs with h
  · simp [Finset.filter_singleton]
  · simp [Finset.filter_singleton]
@[simp] theorem succs.tick     : Conf.MDP.succs .N (·⟨.tick r, σ⟩)       = {·⟨⇓ ϖ, σ⟩} := by simp [succs_reduces, op, op', Finset.filter_singleton]

noncomputable instance : DecidableEq (Option (pGCL ϖ) × States ϖ) := Classical.typeDecidableEq (Option (pGCL ϖ) × States ϖ)

@[simp] theorem Prob_one_eq_one : (1 : {p : ENNReal // 0 < p ∧ p ≤ 1}) = (1 : ENNReal) := by rfl

noncomputable example (C : pGCL ϖ) (σ : States ϖ) : op (some (.skip ; C, σ)) = {(((.N, some (C, σ), 1)) : Choice ϖ)} := by
  simp [op, op', Choice.Conf]

@[simp] theorem P.none_one : P (none : Conf ϖ) .N none                = 1 := by simp [P_reduces, op, op', Finset.filter_singleton, Bot.bot]
@[simp] theorem P.none_zero: P (none : Conf ϖ) .N ((some x) : Conf ϖ) = 0 := by simp [P_reduces, op, op', Finset.filter_singleton, Bot.bot]
@[simp] theorem P.skip     : P (·⟨.skip, σ⟩) .N (·⟨⇓ ϖ, σ⟩) = 1 := by simp [P_reduces, op, op', Finset.filter_singleton]
@[simp] theorem P.sink     : P (·⟨⇓ ϖ, σ⟩) .N none              = 1 := by simp [P_reduces, op, op', Finset.filter_singleton, Bot.bot]
@[simp] theorem P.sink' (α : Act) (C' : Option (pGCL ϖ) × States ϖ) : P (·⟨⇓ ϖ, σ⟩) α (some C') = 0 := by simp [P_reduces, op, op', Finset.filter_singleton]
@[simp] theorem P.assign   : P (·⟨x ::= e, σ⟩) .N (·⟨⇓ ϖ, σ[x ↦ e σ]⟩) = 1 := by simp [P_reduces, op, op', Finset.filter_singleton]
@[simp] theorem P.seq_skip : P (·⟨.skip ; C₂, σ⟩) .N (some ⟨C₂, σ⟩) = 1 := by
  simp [P_reduces, op, op', Finset.filter_singleton, Choice.Act, Choice.Conf, Choice.P]
@[simp] theorem P.prob     : P (·⟨.prob C₁ p C₂, σ⟩) .N (some ⟨C₁, σ⟩) = if C₁ = C₂ then 1 else p.val σ := by
  simp only [P_reduces, op, ne_eq, not_false_eq_true, ↓reduceDIte, op', Option.get_some]
  split_ifs with h₁ h₂
  · simp [h₁, Finset.filter_singleton]
  · simp [h₁, h₂, Finset.filter_singleton]
  · simp only [Option.get_some, Finset.filter_pair, and_self, Option.some.injEq,
    Prod.mk.injEq, and_true, true_and, ↓reduceIte]
    split_ifs
    · simp_all
    · simp_all
@[simp] theorem P.prob'    : P (·⟨.prob C₁ p C₂, σ⟩) .N (some ⟨C₂, σ⟩) = if C₁ = C₂ then 1 else 1 - p.val σ := by
  simp only [P_reduces, op, ne_eq, not_false_eq_true, ↓reduceDIte, op', Option.get_some]
  split_ifs with h₁ h₂
  · simp [h₁, Finset.filter_singleton]
  · simp [h₁, h₂, Finset.filter_singleton]
  · simp [h₁, h₂, Finset.filter_pair]
@[simp] theorem P.nonDet_L : P (·⟨.nonDet C₁ C₂, σ⟩) .L (some ⟨C₁, σ⟩) = 1 := by simp [P_reduces, op, op', Finset.filter_singleton, Finset.filter_pair]
@[simp] theorem P.nonDet_R : P (·⟨.nonDet C₁ C₂, σ⟩) .R (some ⟨C₂, σ⟩) = 1 := by simp [P_reduces, op, op', Finset.filter_singleton, Finset.filter_pair]
@[simp] theorem P.ite      : P (·⟨if b then C₁ else C₂, σ⟩) .N (some ⟨C₁, σ⟩)  = if b σ ∨ C₁ = C₂ then 1 else 0 := by
  split_ifs with h
  · rcases h with h | h
    · simp [P_reduces, op, op', Finset.filter_singleton, h]
    · simp [P_reduces, op, op', Finset.filter_singleton, h]
  · simp [P_reduces, op, op', Finset.sum_eq_zero_iff, Finset.mem_filter, and_imp, Prod.forall,
    Subtype.forall, Prod.mk.injEq]
    split_ifs
    · simp_all
    · intros
      simp_all
@[simp] theorem P.ite'     : P (·⟨if b then C₁ else C₂, σ⟩) .N (some ⟨C₂, σ⟩)  = if ¬b σ ∨ C₁ = C₂ then 1 else 0 := by
  split_ifs with h
  · rcases h with h | h
    · simp [P_reduces, op, op', Finset.filter_singleton, h]
    · simp [P_reduces, op, op', Finset.filter_singleton, h]
  · simp only [P_reduces, op, ne_eq, not_false_eq_true, ↓reduceDIte, op', Option.get_some,
    Finset.sum_eq_zero_iff, Finset.mem_filter, and_imp, Prod.forall, Subtype.forall]
    split_ifs
    · simp_all
    · intros
      simp_all
@[simp] theorem P.loop     : P (·⟨while (b) C', σ⟩) .N (some ⟨C' ; .loop b C', σ⟩) = b.probOf σ := by
  simp only [P_reduces, op, op']
  split
  · simp_all [Finset.filter_singleton]
  · simp_all
@[simp] theorem P.loop'    : P (·⟨while (b) C', σ⟩) .N (·⟨⇓ ϖ, σ⟩) = b.not.probOf σ := by
  simp only [P_reduces, op, op']
  split
  · simp_all
  · simp_all [Finset.filter_singleton]
@[simp] theorem P.tick     : P (·⟨.tick r, σ⟩) .N (·⟨⇓ ϖ, σ⟩) = 1 := by simp [P_reduces, op, op', Finset.filter_singleton]

end Conf

@[simp]
theorem Conf.Φ_bot {f : Exp ϖ} : (Conf.MDP.Φ (cost_X f))^[n] ⊥ none = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [Φf, ih, Φ_iterate_succ]

@[simp]
theorem Conf.Φ_sink {X : Exp ϖ} {σ : States ϖ} : (Conf.MDP.Φ (cost_X X))^[n] ⊥ (·⟨⇓ ϖ, σ⟩) = if n = 0 then 0 else X σ := by
  cases n with
  | zero => simp
  | succ n => simp [Φf, Φ_iterate_succ]


@[simp]
theorem lfp_Φ_bot (X : Exp ϖ) : Conf.MDP.lfp_Φ (cost_X X) none = 0 := by
  rw [lfp_Φ_eq_iSup'_Φ]
  simp [iSup'_Φ]

@[simp]
theorem lfp_Φ_sink (X : Exp ϖ) : Conf.MDP.lfp_Φ (cost_X X) (some (none, σ)) = X σ := by
  rw [←lfp_Φ_step]
  simp [Φ, act_reduces, op, Φf]

noncomputable def step :
  (pGCL ϖ → Exp ϖ → Exp ϖ) →o pGCL ϖ → Exp ϖ → Exp ϖ
:=
  ⟨fun Y ↦ (fun C X σ ↦
    Conf.MDP.Φ (cost_X X) (fun C' ↦
      match C' with
      | ·⟨⇓ ϖ, σ'⟩ => X σ'
      | ·⟨C', σ'⟩ => Y C' X σ'
      | ⊥ => 0
      ) (·⟨C, σ⟩))
    , by
      intro a b h C X σ
      simp
      apply (MDP.Φ _ _).mono
      intro C'
      rcases C' with _ | ⟨_ | _, _⟩ <;> try rfl
      apply_assumption⟩

theorem dop_step : pGCL.dop = step (ϖ:=ϖ) pGCL.dop  := by
  funext C X σ
  rw [pGCL.dop, ←lfp_Φ_step]
  simp [step, dop]
  congr! 3 with C'
  rcases C' with ⟨none, σ'⟩ | ⟨C', σ'⟩ | _ <;> simp only [lfp_Φ_bot, lfp_Φ_sink]

theorem succs_match_pGCL (C : Conf ϖ) (α : Act) (f : Conf ϖ → ENNReal) :
    ∑ s' ∈ Conf.MDP.succs α C, f s'
  = (∑ s' ∈ Conf.MDP.succs α C, match s' with | ·⟨⇓ ϖ, σ'⟩ => f (·⟨⇓ ϖ,σ'⟩) | ·⟨C', σ'⟩ => f (·⟨C', σ'⟩) | none => f none)
:= by
  apply Finset.sum_bij (fun a _ ↦ a) <;> try simp
  intro C' hC'
  split <;> simp

theorem dop_lfp_step :
  pGCL.dop = OrderHom.lfp (step (ϖ:=ϖ))
:= by
  symm
  apply lfp_eq_iff step
  · rw [← dop_step]
  · intro b h
    apply le_trans _ h
    intro C X σ
    rw [pGCL.dop, MDP.lfp_Φ_eq_iSup'_Φ, MDP.iSup'_Φ]
    simp
    intro n
    induction n generalizing C σ with
    | zero => simp
    | succ n ih =>
      simp only [Φ_iterate_succ, act₀_eq_act, Φf, OmegaCompletePartialOrder.ContinuousHom.coe_mk, OrderHom.coe_mk]
      conv => left ; right ; arg 3 ; ext α ; rw [succs_match_pGCL]
      simp
      simp [step, Φ, Φf]
      gcongr
      simp
      intro α hα ; use α, hα
      gcongr with C' hC'
      rcases C' with _ | ⟨_ | C', σ'⟩
      · simp
      · simp only [Φ_sink, mul_ite, mul_zero] ; split_ifs with hn <;> simp
      · simp only
        gcongr
        apply le_trans (ih C' σ') (h C' X σ')

theorem dwp.loop_fp (b : BExpr ϖ) (C : pGCL ϖ) :
  (pGCL.loop b C).dwp = fun X ↦ b.probOf * (C ; pGCL.loop b C).dwp X + b.not.probOf * X
:= by
  ext X
  conv => right ; rw [pGCL.dwp]
  simp only [dwp_loop, dwp_loop_f]
  conv => left ; rw [←OrderHom.map_lfp]
  rfl

theorem cost_X_dwp_seq (X : Exp ϖ) (C₁ C₂ : pGCL ϖ) (σ : States ϖ) :
  cost_X (C₂.dwp X) (some (C₁, σ)) = cost_X X (some (C₁ ; C₂, σ))
:= by
  simp [cost_X]
  induction C₁ <;> simp [cost_X]
  assumption

theorem cost_X_dop_seq (X : Exp ϖ) (C₁ C₂ : pGCL ϖ) (σ : States ϖ) :
  cost_X (C₂.dop X) (some (C₁, σ)) = cost_X X (some (C₁ ; C₂, σ))
:= by
  simp [cost_X]
  induction C₁ <;> simp [cost_X]
  assumption

theorem succs_seq_eq_succs_wrap (C₁ C₂ : pGCL ϖ) (σ : States ϖ) :
  Conf.MDP.succs α (·⟨C₁ ; C₂,σ⟩) = (Conf.MDP.succs α (·⟨C₁,σ⟩)).map ⟨C₂.wrap, wrap.inj⟩
:= by
  ext C'
  simp_all [succs_reduces, op, Choice.Act, Choice.Conf, Choice.P]
  constructor
  · simp_all
    intro p _ _ α C' _ hp h _ h' _
    subst_eqs
    simp_all only
    use C'
    constructor
    · use p, hp
    · simp [wrap]
  · simp_all
    intro C' p hp h h'
    subst_eqs
    use p, hp, α, C', p
    constructor
    · use hp
    · simp [wrap]

theorem P_seq_wrap_eq {C₁ C₂ : pGCL ϖ} {σ : States ϖ} {α : Act} {C' : Conf ϖ} :
  P (·⟨C₁ ; C₂,σ⟩) α (C₂.wrap C') = P (·⟨C₁,σ⟩) α C'
:= by
  simp only [wrap, instBot, P_reduces, op, op', op_seq, Choice.Act, Choice.Conf, Choice.P,
    Finset.sum_filter, Finset.sum_map, Function.Embedding.coeFn_mk]
  congr! 3
  constructor
  · split <;> split <;> simp_all only [Option.some.injEq, Prod.mk.injEq, seq.injEq, and_true, and_imp, implies_true]
    all_goals
      intro h ; absurd h
      apply SizeOf.ne_if <| by simp
  · intros ; simp_all

theorem dwp_step :
  pGCL.dwp = step (ϖ:=ϖ) pGCL.dwp
:= by
  funext C
  simp [step]
  induction C with
  | skip => simp [pGCL.dwp, Φ, Φf]
  | assign x e =>
    simp [pGCL.dwp, Φ, Φf]
    funext X σ
    simp
  | seq C₁ C₂ ih₁ =>
    simp [pGCL.dwp, Φ, Φf, ih₁, cost_X_dwp_seq, succs_seq_eq_succs_wrap, P_seq_wrap_eq]
    congr! 6
    split <;> rfl
  | prob C₁ p C₂ ih₁ ih₂ =>
    simp [pGCL.dwp, Φ, Φf] at *
    funext X σ
    split_ifs
    · simp_all
    · by_cases h : C₁ = C₂
      · simp [h]
        exact prob_complete p (C₂.dwp X σ) σ
      · simp [h]
  | nonDet C₁ C₂ =>
    simp [pGCL.dwp, Φ, Φf]
    rfl
  | ite b C₁ C₂ =>
    simp [pGCL.dwp, Φ, Φf]
    funext X σ
    split_ifs with h
    · simp [h]
    · simp [h]
  | loop b C' =>
    rw [pGCL.dwp.loop_fp]
    ext X σ
    simp only [Pi.add_apply, Pi.mul_apply, Φ, act₀_eq_act, Φf,
      OmegaCompletePartialOrder.ContinuousHom.coe_mk, OrderHom.coe_mk, cost_X.loop, act.loop,
      Finset.inf'_singleton, succs.loop, zero_add]
    split_ifs with h <;> simp [h]
  | tick r =>
    simp [pGCL.dwp, Φ, Φf]
    rfl

theorem dop_seq (C₁ C₂ : pGCL ϖ) (X : Exp ϖ) :
  C₁.dop (C₂.dop X) ≤ (C₁ ; C₂).dop X
:= by
  intro σ
  conv => left ; rw [pGCL.dop]
  rw [lfp_Φ_eq_iSup_Φ]
  rw [iSup_Φ]
  simp_all only [Nat.succ_eq_add_one, iSup_apply, iSup_le_iff]
  intro n
  induction n generalizing C₁ C₂ σ with
  | zero =>
    simp only [zero_add, Function.iterate_one, Φ, cost_X_dop_seq, act₀_eq_act, Φf,
      OmegaCompletePartialOrder.ContinuousHom.coe_mk, OrderHom.coe_mk, Pi.bot_apply, bot_eq_zero',
      mul_zero, Finset.sum_const_zero, Finset.inf'_const, add_zero]
    rw [dop_step, step]
    simp [cost_X, Φ, Φf]
  | succ n ih =>
    rw [Φ_iterate_succ]
    simp only [Φf]
    simp only [act₀_eq_act, Φ, Φf, OmegaCompletePartialOrder.ContinuousHom.coe_mk, OrderHom.coe_mk]
    conv => left ; right ; arg 3 ; ext α ; rw [succs_match_pGCL]
    have :
      (cost_X (C₂.dop X) (·⟨C₁,σ⟩) +
        Conf.act_inf (·⟨C₁,σ⟩) fun x ↦
          ∑ s' ∈ Conf.MDP.succs x (·⟨C₁,σ⟩),
            match s' with
            | ·⟨⇓ ϖ,σ'⟩ => (Conf.MDP.P (·⟨C₁,σ⟩) x) (·⟨⇓ ϖ,σ'⟩) * (Conf.MDP.Φ (cost_X (C₂.dop X)))^[n + 1] ⊥ (·⟨⇓ ϖ,σ'⟩)
            | ·⟨C',σ'⟩ => (Conf.MDP.P (·⟨C₁,σ⟩) x) (·⟨C',σ'⟩) * (Conf.MDP.Φ (cost_X (C₂.dop X)))^[n + 1] ⊥ (·⟨C',σ'⟩)
            | none => (Conf.MDP.P (·⟨C₁,σ⟩) x) none * (Conf.MDP.Φ (cost_X (C₂.dop X)))^[n + 1] ⊥ none) ≤
      (cost_X (C₂.dop X) (·⟨C₁,σ⟩) +
        Conf.act_inf (·⟨C₁,σ⟩) fun x ↦
          ∑ s' ∈ Conf.MDP.succs x (·⟨C₁,σ⟩),
            match s' with
            | ·⟨⇓ ϖ,σ'⟩ => (Conf.MDP.P (·⟨C₁,σ⟩) x) (·⟨⇓ ϖ,σ'⟩) * C₂.dop X σ'
            | ·⟨C',σ'⟩ => (Conf.MDP.P (·⟨C₁,σ⟩) x) (·⟨C',σ'⟩) * (C' ; C₂).dop X σ'
            | none => (Conf.MDP.P (·⟨C₁,σ⟩) x) none * (Conf.MDP.Φ (cost_X (C₂.dop X)))^[n + 1] ⊥ none)
    := by
      gcongr
      simp only [act_inf_def, Finset.le_inf'_iff, Finset.inf'_le_iff]
      intro α hα
      use α, hα
      gcongr with C' hC'
      rcases C' with _ | ⟨_ | _, _⟩ <;> simp
      gcongr
      apply_assumption
    apply le_trans this
    apply le_of_eq
    simp only [cost_X_dop_seq, act_inf_def]
    conv => right ; rw [dop_step, step]
    simp only [Φ_bot, mul_zero, OrderHom.coe_mk]
    simp only [Φ, act₀_eq_act, Φf, OmegaCompletePartialOrder.ContinuousHom.coe_mk, OrderHom.coe_mk,
      act.seq, succs_seq_eq_succs_wrap, Finset.sum_map, Function.Embedding.coeFn_mk, P_seq_wrap_eq]
    congr! 3
    split <;> simp

theorem dwp_le_dop.loop (b : BExpr ϖ) {C' : pGCL ϖ} (ih : C'.dwp ≤ C'.dop) :
  (pGCL.loop b C').dwp ≤ (pGCL.loop b C').dop
:= by
  intro X
  let C := pGCL.loop b C'
  apply OrderHom.lfp_le (pGCL.dwp_loop_f b C' X)
  simp [dwp_loop_f]
  calc
    b.probOf * C'.dwp (C.dop X) + b.not.probOf * X
      ≤ b.probOf * C'.dop (C.dop X) + b.not.probOf * X := by gcongr ; exact ih (C.dop X)
    _ ≤ b.probOf * (C' ; C).dop X + b.not.probOf * X := by gcongr ; exact dop_seq C' C X
  conv => right ; rw [dop_step]
  intro σ
  by_cases h : b σ = true <;> simp [step, h, Φ, Φf]

theorem dwp_le_dop :
  pGCL.dwp (ϖ:=ϖ) ≤ pGCL.dop
:= by
  intro C
  induction C with rw [dop_step]
  | skip =>
    simp [pGCL.dwp, step, Φ, Φf]
  | assign x e =>
    simp [pGCL.dwp, step, Φ, Φf]
    rfl
  | seq C₁ C₂ ih₁ ih₂ =>
    rw [←dop_step] at *
    intro X
    simp only [pGCL.dwp]
    have h := (ih₁ (C₂.dwp X)).trans <| pGCL.dop.monotone C₁ (ih₂ X)
    exact h.trans <| dop_seq C₁ C₂ X
  | prob C₁ p C₂ ih₁ ih₂ =>
    simp [pGCL.dwp, step, Φ, Φf]
    intro X σ
    have := ih₁ X σ
    have := ih₂ X σ
    by_cases C₁ = C₂
    · simp_all [prob_complete]
    · simp
      split_ifs <;> simp_all
      gcongr
  | nonDet C₁ C₂ ih₁ ih₂ =>
    simp [pGCL.dwp, step, Φ, Φf]
    intro X σ
    simp
    constructor
    · left ; apply_assumption
    · right ; apply_assumption
  | ite b C₁ C₂ ih₁ ih₂ =>
    simp [pGCL.dwp, step, Φ, Φf]
    intro X σ
    simp
    split_ifs <;> simp_all only [Bool.false_eq_true, not_true_eq_false]
    · simp_all [ih₁ X σ]
    · simp_all [ih₂ X σ]
  | loop b C' ih =>
    rw [←dop_step]
    exact dwp_le_dop.loop b ih
  | tick r =>
    simp [pGCL.dwp, step, Φ, Φf]
    rfl

@[simp]
theorem Φ_none_eq_zero (X : Exp ϖ) : (Conf.MDP.Φ (cost_X X))^[i] ⊥ none = 0 := by
  cases i with
  | zero => simp
  | succ i => simp [Φ_iterate_succ, Φf]

@[simp]
theorem Φ_sink_eq_X (X : Exp ϖ) : (Conf.MDP.Φ (cost_X X))^[i + 1] ⊥ (·⟨⇓ ϖ, σ⟩) = X σ := by
  simp [Φ_iterate_succ, Φf]

theorem dop_le_dwp : dop ≤ dwp (ϖ:=ϖ) :=
  dop_lfp_step.trans_le <| OrderHom.lfp_le_fixed step dwp_step.symm

theorem dop_eq_dwp : dop = dwp (ϖ:=ϖ) :=
  le_antisymm dop_le_dwp dwp_le_dop
