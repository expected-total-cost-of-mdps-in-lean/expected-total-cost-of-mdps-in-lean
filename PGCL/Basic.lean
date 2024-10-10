import PGCL.OperationalSemantics
import MDP.InfSup_SupInf

theorem pGCL.sup_inf_EC'_eq_dwp {ϖ : Type*} [DecidableEq ϖ] (X : Exp ϖ) (C : pGCL ϖ) (σ : States ϖ) :
  ⨅ 𝒮, ⨆ n, MDP.EC' (M:=Conf.MDP) (Conf.cost_X X) n (·⟨C,σ⟩) 𝒮 = C.dwp X σ
:= by
  convert Conf.MDP.sup_inf_EC'_eq_inf_sup_EC' (Conf.cost_X X) (·⟨C, σ⟩) |>.symm
  convert congrFun₃ pGCL.dop_eq_dwp C X σ |>.symm
  rw [dop, ←MDP.sup_inf_EC₀'_eq_lfp_Φ, ←MDP.sup_inf_EC'_eq_sup_inf_EC₀']
