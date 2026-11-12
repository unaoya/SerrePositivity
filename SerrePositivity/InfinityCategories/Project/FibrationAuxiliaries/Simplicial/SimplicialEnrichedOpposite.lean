module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NervePostcomposition
public import Mathlib.CategoryTheory.Enriched.Opposite

/-!
概要：単体的豊穣関手を、両圏の反対豊穣圏の間へ移す。
方針：Hom の向きを逆に読み、合成の両側の変数を交換する。
規約：coherent nerve の反対と厳密に同定することは要求しない。
使われ方：表現可能な Hom の族の始域での前合成を明示する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- 豊穣関手を両圏の反対豊穣圏の間へ移す。 -/
def simplicialEnrichedOpposite {C D : Type v}
    [Category.{u} C] [SimplicialCategory C] [Category.{u} D] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) : EnrichedFunctor SSet.{u} Cᵒᵖ Dᵒᵖ where
  obj X := Opposite.op (F.obj X.unop)
  map X Y := F.map Y.unop X.unop
  map_id X := F.map_id X.unop
  map_comp X Y Z := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨f, g⟩
    exact congrArg (fun k ↦ k.app n (g, f)) (F.map_comp Z.unop Y.unop X.unop)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
