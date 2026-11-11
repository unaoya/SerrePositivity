module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# 単体集合に区別された孤立点を加える構成

概要：各次数の Option と元の全単体作用素を使い、some の単射を構成する。
方針：元の写像の恒等・合成則を Option.map に渡す。
規約：none は全単体作用素で固定する。
使われ方：非空部分の余極限の包含の単射性を検査する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.OptionSpace
open CategoryTheory

variable (K : SSet.{u})

def space : SSet.{u} where
  obj n := Option (K.obj n)
  map θ := ↾fun x => x.map (K.map θ)
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro x
    cases x with
    | none => rfl
    | some x => exact congrArg some (K.map_id_apply n x)
  map_comp θ φ := by
    apply ConcreteCategory.hom_ext
    intro x
    cases x with
    | none => rfl
    | some x => exact congrArg some (K.map_comp_apply θ φ x)

def inclusion : K ⟶ space K where
  app _ := ↾some
  naturality _ _ _ := rfl

lemma inclusion_injective (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((inclusion K).app n) := fun _ _ h => Option.some.inj h

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.OptionSpace
