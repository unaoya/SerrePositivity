module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorSpaceDown
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.Reflection

/-!
概要：関手空間のホモトピー圏の下降を、元の小宇宙の具体的な関手頂点で表示する。
方針：元の頂点表示を計算し、射の下降の合成・持ち上げの式を使う。
規約：対象の等式を明示。使われ方：指定可換式の下降時の四端点の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 大きい実際の関手頂点の下降は、同じ射を降ろした小さい関手頂点。 -/
lemma functorSpaceDown_obj {X Y : SSet.{u}}
    (f : (SSet.uliftFunctor.{v, u}).obj X ⟶ (SSet.uliftFunctor.{v, u}).obj Y) :
    (functorSpaceDown.{u, v} X Y).obj (SSet.HomotopyCategory.mk (functorVertex f)) =
      SSet.HomotopyCategory.mk (functorVertex (uliftMorphismDown f)) := rfl

/-- 持ち上げた元の関手頂点は下降により同じ元の頂点に厳密に戻る。 -/
lemma functorSpaceDown_obj_map {X Y : SSet.{u}} (f : X ⟶ Y) :
    (functorSpaceDown.{u, v} X Y).obj
      (SSet.HomotopyCategory.mk (functorVertex ((SSet.uliftFunctor.{v, u}).map f))) =
        SSet.HomotopyCategory.mk (functorVertex f) := by
  rw [functorSpaceDown_obj, uliftMorphismDown_map]

/-- 大きい二射の合成の頂点の下降は、元の二射の下降の合成を表す頂点。 -/
lemma functorSpaceDown_obj_comp {X Y Z : SSet.{u}}
    (f : (SSet.uliftFunctor.{v, u}).obj X ⟶ (SSet.uliftFunctor.{v, u}).obj Y)
    (g : (SSet.uliftFunctor.{v, u}).obj Y ⟶ (SSet.uliftFunctor.{v, u}).obj Z) :
    (functorSpaceDown.{u, v} X Z).obj (SSet.HomotopyCategory.mk (functorVertex (f ≫ g))) =
      SSet.HomotopyCategory.mk (functorVertex (uliftMorphismDown f ≫ uliftMorphismDown g)) := by
  rw [functorSpaceDown_obj, uliftMorphismDown_comp]

end SerrePositivity.InfinityCategories.F2
