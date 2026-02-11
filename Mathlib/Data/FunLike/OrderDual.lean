module

public import Mathlib.Data.FunLike.Equiv
public import Mathlib.Order.Basic

@[expose] public section

variable {F : Type*} {α : Type*} {β : Type*}

@[instance_reducible]
def instFunLikeOrderDual [FunLike F α β] : FunLike F αᵒᵈ βᵒᵈ := by assumption

@[instance_reducible]
def instEquivLikeOrderDual [EquivLike F α β] : EquivLike F αᵒᵈ βᵒᵈ := by assumption
