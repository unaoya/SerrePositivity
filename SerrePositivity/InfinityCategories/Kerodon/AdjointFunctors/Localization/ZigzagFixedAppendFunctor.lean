module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramFixed
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramAppend
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor

/-!
# 固定端点での元の図式の連結関手の回収

概要：元の二つの固定端点図式の連結は、同じ二つの関手の連結関手に一致する。
方針：元の全対象・全縦成分の定義を照合する。
規約：接合点の移送の証明の選択には依存しない。
使われ方：内部切断の refined 全図式と元の合成の標準射の照合。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y Z : C}

lemma append_fixedFunctor
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W a ((Functor.const D).obj X) ((Functor.const D).obj Y))
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W b ((Functor.const D).obj Y) ((Functor.const D).obj Z)) :
    (F.append G).fixedFunctor = F.fixedFunctor.prod' G.fixedFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (append_fixedFunctor)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
