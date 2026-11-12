module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverZigzagFiber

/-!
# 値を固定した元の zigzag の固定端点への持ち上げ

概要：元の語・全頂点・全横列を固定根と指定終点の間へ持ち上げる。
方針：接頭ラベルで頂点を作り、指定両端の射列の持ち上げを使う。
規約：終点の groupoid の値は元の値そのものである。
使われ方：元の値の fiber と被覆の hammock の比較。

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

def zigzagLift (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueFiber A w Y β) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A))) w
      ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.root A))
      ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fiberEndpoint A Y β)) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact
    { vertex := fun j => (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagVertex A S.obj j)
      first := congrArg (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagVertex_first A S.obj)
      last := congrArg (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagVertex_last A S)
      arrow := fun i => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftPathTo A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagVertex A S.obj (w.source i))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagVertex A S.obj (w.target i)) (S.obj.arrow i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix_arrow A S.obj i)
      backward_mem := fun _ _ => trivial }

lemma zigzagLift_arrow_projection (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueFiber A w Y β) (i : Fin w.length) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection A).map ((zigzagLift A S).arrow i) = S.obj.arrow i := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftPathTo_projection A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagVertex A S.obj (w.source i))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagVertex A S.obj (w.target i)) (S.obj.arrow i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix_arrow A S.obj i)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
