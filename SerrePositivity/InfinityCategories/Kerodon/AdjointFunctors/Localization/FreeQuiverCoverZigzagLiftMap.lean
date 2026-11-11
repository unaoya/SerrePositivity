module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverZigzagLift

/-!
# 元の全縦射と全可換正方形の持ち上げ

概要：値を固定した元の zigzag 間の全縦射を固定端点のまま持ち上げる。
方針：接頭ラベルの自然性で各成分を持ち上げ、忠実性で正方形を照合する。
規約：元の全成分・端点の恒等射・正方形を射影で回収する。
使われ方：固定端点の zigzag の圏の持ち上げ関手。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {Y : Paths Q}
  {β : (Quiver.FreeGroupoid.of Q).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.obj Y}

def zigzagLiftMap {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueFiber A w Y β} (f : S ⟶ T) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLift A S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLift A T) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection_faithful A
  let app : ∀ j, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLift A S).vertex j ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLift A T).vertex j := fun j =>
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftPathTo A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagVertex A S.obj j) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagVertex A T.obj j) (f.hom.app j)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix_naturality A f.hom j)
  have hp : ∀ j, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection A).map (app j) = f.hom.app j := fun j =>
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftPathTo_projection A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagVertex A S.obj j) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagVertex A T.obj j) (f.hom.app j)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix_naturality A f.hom j)
  exact
    { app := app
      app_mem := fun _ => trivial
      first := by
        apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection A).map_injective
        calc
          _ = f.hom.app 0 := hp 0
          _ = eqToHom (S.obj.first.trans T.obj.first.symm) := f.hom.first
          _ = _ := (eqToHom_map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection A)
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLift A S).first.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLift A T).first.symm)).symm
      last := by
        apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection A).map_injective
        calc
          _ = f.hom.app (Fin.last w.length) := hp _
          _ = eqToHom (S.obj.last.trans T.obj.last.symm) := f.hom.last
          _ = _ := (eqToHom_map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection A)
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLift A S).last.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLift A T).last.symm)).symm
      comm := fun i => by
        apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection A).map_injective
        rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLift_arrow_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLift_arrow_projection, hp, hp]
        exact f.hom.comm i }

lemma zigzagLiftMap_app_projection {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueFiber A w Y β} (f : S ⟶ T)
    (j : Fin (w.length + 1)) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection A).map ((zigzagLiftMap A f).app j) = f.hom.app j := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftPathTo_projection A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagVertex A S.obj j) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagVertex A T.obj j) (f.hom.app j)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix_naturality A f.hom j)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
