module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramHom

/-!
# 動く接合点での元の比較の連結

概要：局所端点を保つ二つの図式間の自然な比較を同じ接合点で貼る。
方針：Moving.map の合成則を各頂点へ移し、元の二つの自然性を使う。
規約：前後の語の元の縦射と接合点を保持する。
使われ方：局所の counit/unit を元の prefix/suffix に拡張する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramHomAppend
open CategoryTheory

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {A B E : D ⥤ C}
  {F F' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W a A B} {G G' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W b B E}
  (α : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramHom.Hom F F') (β : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramHom.Hom G G')

def append : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramHom.Hom (F.append G) (F'.append G') where
  app d := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map (α.app d) (β.app d) ((α.last d).trans (β.first d).symm)
  naturality f := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
    intro j
    have hj : HEq (((F.map f).comp (α.app _)).app (Fin.last a.length))
        (((G.map f).comp (β.app _)).app 0) :=
      heq_comp ((F.obj _).last.trans (G.obj _).first.symm)
        ((F.obj _).last.trans (G.obj _).first.symm)
        ((F'.obj _).last.trans (G'.obj _).first.symm)
        ((F.last f).trans (G.first f).symm) ((α.last _).trans (β.first _).symm)
    have hj' : HEq (((α.app _).comp (F'.map f)).app (Fin.last a.length))
        (((β.app _).comp (G'.map f)).app 0) := by
      rw [← α.naturality f, ← β.naturality f]
      exact hj
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app (F.map f) (G.map f) j ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app (α.app _) (β.app _) j =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app (α.app _) (β.app _) j ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app (F'.map f) (G'.map f) j
    calc
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app ((F.map f).comp (α.app _))
          ((G.map f).comp (β.app _)) j :=
        congrArg (fun h => h.app j) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendLaws.map_comp (F.map f) (G.map f)
          (α.app _) (β.app _) ((F.last f).trans (G.first f).symm)
          ((α.last _).trans (β.first _).symm) hj)
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app ((α.app _).comp (F'.map f))
          ((β.app _).comp (G'.map f)) j := by rw [α.naturality f, β.naturality f]
      _ = _ := (congrArg (fun h => h.app j) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendLaws.map_comp (α.app _) (β.app _)
        (F'.map f) (G'.map f) ((α.last _).trans (β.first _).symm)
        ((F'.last f).trans (G'.first f).symm) hj')).symm
  first d := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq (α.app d) (β.app d) 0).trans (α.first d)
  last d := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq (α.app d) (β.app d)
    ((α.last d).trans (β.first d).symm) (Fin.last b.length)).trans (β.last d)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramHom.Hom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramHomAppend (append)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramHomAppend
