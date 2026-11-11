module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendParts
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramEvaluation

/-!
# 動く端点を持つ図式の前後の部分

概要：元の連結語の図式を、動く接合対象を共有する二つの図式に分ける。
方針：各頂点と全縦射を元の左右の位置へ制限する。
規約：二度の分割で任意の prefix/core/suffix を抽出できる。
使われ方：前後の語を保持した局所 MovingFamily の構成。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramParts
open CategoryTheory

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {A B : D ⥤ C}
  (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) A B)

def jointFunctor : D ⥤ C := F.evaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a b (Fin.last a.length))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramParts (jointFunctor)


def leftPartMap {d d' : D} (f : d ⟶ d') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj (F.obj d))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj (F.obj d')) where
  app i := (F.map f).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a b i)
  app_mem _i := (F.map f).app_mem _
  comm i := (F.map f).square_transport _ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.source_left a b i).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.target_left a b i)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramParts (leftPartMap)


def rightPartMap {d d' : D} (f : d ⟶ d') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj (F.obj d))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj (F.obj d')) where
  app i := (F.map f).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a b i)
  app_mem _i := (F.map f).app_mem _
  comm i := (F.map f).square_transport _ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.source_right a b i).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.target_right a b i)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramParts (rightPartMap)


def leftPart : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W a A F.jointFunctor where
  obj d := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj (F.obj d)
  map := F.leftPartMap
  map_id d := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
    intro i
    exact congrArg (fun g => g.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a b i)) (F.map_id d)
  map_comp f g := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
    intro i
    exact congrArg (fun h => h.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a b i)) (F.map_comp f g)
  first f := F.first f
  last _ := HEq.rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramParts (leftPart)


def rightPart : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W b F.jointFunctor B where
  obj d := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj (F.obj d)
  map := F.rightPartMap
  map_id d := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
    intro i
    exact congrArg (fun g => g.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a b i)) (F.map_id d)
  map_comp f g := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
    intro i
    exact congrArg (fun h => h.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a b i)) (F.map_comp f g)
  first f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.app_heq (F.map f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.jointVertex a b).symm
  last f := F.last f

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramParts (rightPart)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramParts
