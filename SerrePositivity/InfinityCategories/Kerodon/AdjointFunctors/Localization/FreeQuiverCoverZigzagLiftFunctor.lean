module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverZigzagLiftMap

/-!
# 元の値の fiber の固定端点への持ち上げ関手

概要：元の全指定 zigzag の値を固定した全部分圏を被覆の zigzag 圏へ送る。
方針：証明済みの対象・全縦射の持ち上げを関手に束ねる。
規約：元の恒等射と合成を忠実な射影で検査する。
使われ方：元の hammock の fiber と木上の hammock の比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (Y : Paths Q)
  (β : (Quiver.FreeGroupoid.of Q).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.obj Y)

def zigzagLiftFunctor :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueFiber A w Y β ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A))) w
      ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.root A))
      ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fiberEndpoint A Y β)) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection_faithful A
  exact
    { obj := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLift A
      map := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLiftMap A
      map_id := fun S => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext _ _ (fun j => by
        apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection A).map_injective
        exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLiftMap_app_projection A (𝟙 S) j).trans
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection A).map_id ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLift A S).vertex j)).symm)
      map_comp := fun f g => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext _ _ (fun j => by
        apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection A).map_injective
        change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection A).map ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLiftMap A (f ≫ g)).app j) =
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection A).map ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLiftMap A f).app j ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLiftMap A g).app j)
        rw [CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLiftMap_app_projection,
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLiftMap_app_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLiftMap_app_projection]
        rfl) }

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
