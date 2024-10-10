
-- inductive SmallStep : Conf ϖ → Act → ENNReal → Conf ϖ → Prop where
--   | skip     : SmallStep (·⟨skip, σ⟩)          .N 1 (·⟨⇓ ϖ, σ⟩)
--   | sink     : SmallStep (·⟨⇓ ϖ, σ⟩)           .N 1 none
--   | assign   : SmallStep (·⟨x ::= e, σ⟩)       .N 1 (·⟨⇓ ϖ, σ[x ↦ e σ]⟩)
--   | prob_L   : SmallStep (·⟨.prob C₁ p C₂, σ⟩) .N (p.val σ)     (some (C₁, σ))
--   | prob_R   : SmallStep (·⟨.prob C₁ p C₂, σ⟩) .N (1 - p.val σ) (some (C₂, σ))
--   | nonDet_L : SmallStep (·⟨C₁ [] C₂, σ⟩)      .L 1 (·⟨C₁, σ⟩)
--   | nonDet_R : SmallStep (·⟨C₁ [] C₂, σ⟩)      .R 1 (·⟨C₁, σ⟩)
--   | tick     : SmallStep (·⟨.tick r, σ⟩)       .N 1 (·⟨⇓ ϖ, σ⟩)
--   | seq_L    : SmallStep (·⟨C₁, σ⟩) α p (some (none, σ)) → SmallStep (·⟨C₁ ; C₂, σ⟩) .N 1 (·⟨C₂, τ⟩)
--   | seq_R    : SmallStep (·⟨C₁, σ⟩) α p (·⟨C₁', σ⟩)      → SmallStep (·⟨C₁ ; C₂, σ⟩) .N 1 (·⟨C₁' ; C₂, τ⟩)


-- theorem SmallStep.Finite (c : Conf ϖ) : { (α, p, c') | SmallStep c α p c' }.Finite := by
--   simp
--   constructor
--   constructor
--   · simp_all
--   · simp_all
--   · simp_all
--   · simp_all

-- noncomputable def SmallStep.act (c : Conf ϖ) : Finset Act :=
--   let p := fun (α : Act) ↦ ∃ c' p, SmallStep c α p c'
--   have : DecidablePred p := Classical.decPred p
--   Act.instFintype.elems.filter p

-- theorem SmallStep.act_if (c : Conf ϖ) (h : (∃ c' p, SmallStep c .N p c')) : SmallStep.act c = {.N} := by
--   simp [act]
--   ext α
--   simp [Fintype.complete]
--   constructor
--   · simp_all
--     intro C' p
--     intro h
--     cases h <;> try simp
--     all_goals
--       obtain ⟨c', p, h⟩ := h
--       cases h
--   · intro h
--     subst_eqs
--     exact h

-- theorem SmallStep.sink_act : SmallStep.act (·⟨⇓ ϖ, σ⟩) = {.N} := by
--   apply SmallStep.act_if
--   repeat apply Exists.intro
--   constructor
-- theorem SmallStep.skip_act : SmallStep.act (ϖ:=ϖ) (·⟨skip, σ⟩) = {.N} := by
--   apply SmallStep.act_if
--   repeat apply Exists.intro
--   constructor
-- theorem SmallStep.assign_act : SmallStep.act (ϖ:=ϖ) (·⟨x ::= e, σ⟩) = {.N} := by
--   apply SmallStep.act_if
--   repeat apply Exists.intro
--   constructor

-- instance (c c' : Conf ϖ) : AddCommMonoid { p // SmallStep c α p c' } := by
--   have : AddCommMonoid ENNReal := by exact AddCommMonoidWithOne.toAddCommMonoid
--   sorry
-- noncomputable def Px (c : Conf ϖ) (α : Act) : Conf ϖ →₀ ENNReal :=
--   ⟨by sorry, (fun c' ↦ ∑' p : { p // SmallStep c α p c'}, p), by sorry⟩
