module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordActionMovingMap
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramFixed

/-!
# 元の語の作用による動く全図式の圧縮

概要：元の WordAction を動く端点の図式へ適用し、同じ全縦射を cut に沿って回収する。
方針：元の対象作用と MovingHom の同じ成分による作用を束ねる。
規約：固定端点では元の WordAction.functor への後合成に厳密に一致する。
使われ方：三列 collapse の元の全図式への適用。

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
  {W : MorphismProperty C} [W.IsMultiplicative] {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {A B : D ⥤ C}

def wordAction (f : a ⟶ b) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W a A B) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W b A B where
  obj d := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f (F.obj d)
  map g := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingMap f (F.map g)
  map_id d := by rw [F.map_id]; exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingMap_id f (F.obj d)
  map_comp g h := by rw [F.map_comp]; exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingMap_comp f (F.map g) (F.map h)
  first g := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.app_heq (F.map g) f.cut_zero).trans (F.first g)
  last g := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.app_heq (F.map g) f.cut_last).trans (F.last g)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (wordAction)


lemma wordAction_fixedFunctor (f : a ⟶ b) {X Y : C}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W a ((Functor.const D).obj X) ((Functor.const D).obj Y)) :
    (wordAction f F).fixedFunctor = F.fixedFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (wordAction_fixedFunctor)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
