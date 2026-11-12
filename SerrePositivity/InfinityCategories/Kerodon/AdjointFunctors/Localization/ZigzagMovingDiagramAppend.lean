module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagram

/-!
# 動く接合点を持つ元の二つの図式の連結

概要：同じ端点関手を共有する二つの局所図式を全対象・全縦射で貼る。
方針：元の端点回収により接合点の射を照合し、Moving.map の恒等・合成則を使う。
規約：共有する端点の全縦射も動く。
使われ方：元の prefix/core/suffix の図式の連結。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramAppend
open CategoryTheory

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {A B E : D ⥤ C}
  (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W a A B) (G : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W b B E)

def append : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) A E where
  obj d := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (F.obj d) (G.obj d)
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map (F.map f) (G.map f) ((F.last f).trans (G.first f).symm)
  map_id d := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
    intro j
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app (F.map (𝟙 d)) (G.map (𝟙 d)) j = 𝟙 _
    rw [F.map_id, G.map_id]
    exact congrArg (fun h => h.app j) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendLaws.map_id (F.obj d) (G.obj d)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id_last _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id_first _).symm))
  map_comp f g := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
    intro j
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app (F.map (f ≫ g)) (G.map (f ≫ g)) j =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app (F.map f) (G.map f) j ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app (F.map g) (G.map g) j
    have hj := (F.last (f ≫ g)).trans (G.first (f ≫ g)).symm
    rw [F.map_comp, G.map_comp] at hj
    rw [F.map_comp, G.map_comp]
    exact (congrArg (fun h => h.app j) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendLaws.map_comp (F.map f) (G.map f)
      (F.map g) (G.map g) ((F.last f).trans (G.first f).symm)
      ((F.last g).trans (G.first g).symm) hj)).symm
  first f := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq (F.map f) (G.map f) 0).trans (F.first f)
  last f := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq (F.map f) (G.map f)
    ((F.last f).trans (G.first f).symm)
    (Fin.last b.length)).trans (G.last f)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramAppend (append)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramAppend
