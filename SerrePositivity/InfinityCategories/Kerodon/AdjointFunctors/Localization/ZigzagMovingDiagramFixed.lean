module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramHomAppend

/-!
# 全体の両端を固定した図式と自然変換への回収

概要：元の全体の端点が定数なら、動く局所図式の連結から通常の関手を得る。
方針：両端の恒等条件だけを回収し、同じ全頂点の恒等・合成・自然性を使う。
規約：内側の動く局所接合点を固定する必要はない。
使われ方：prefix/core/suffix を貼った後の元の固定端点の zigzag 図式。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramFixed
open CategoryTheory

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}
  (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W w ((Functor.const D).obj X) ((Functor.const D).obj Y))

def fixedFunctor : D ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y where
  obj := F.obj
  map f := (F.map f).toHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.first_of_heq_id _ (F.first f))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.last_of_heq_id _ (F.last f))
  map_id d := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
    intro j
    exact congrArg (fun h => h.app j) (F.map_id d)
  map_comp f g := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
    intro j
    exact congrArg (fun h => h.app j) (F.map_comp f g)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramFixed (fixedFunctor)


namespace Hom
variable {F} {G : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W w ((Functor.const D).obj X) ((Functor.const D).obj Y)}
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramHom.Hom F G)

def natTrans : F.fixedFunctor ⟶ G.fixedFunctor where
  app d := (h.app d).toHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.first_of_heq_id _ (h.first d))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.last_of_heq_id _ (h.last d))
  naturality _ _ f := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
    intro j
    exact congrArg (fun k => k.app j) (h.naturality f)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramHom.Hom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramFixed.Hom (natTrans)


end Hom
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramFixed
