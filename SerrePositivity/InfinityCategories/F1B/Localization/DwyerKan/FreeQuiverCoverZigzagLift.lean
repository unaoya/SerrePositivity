module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FreeQuiverCoverZigzagFiber

/-!
# 値を固定した元の zigzag の固定端点への持ち上げ

概要：元の語・全頂点・全横列を固定根と指定終点の間へ持ち上げる。
方針：接頭ラベルで頂点を作り、指定両端の射列の持ち上げを使う。
規約：終点の groupoid の値は元の値そのものである。
使われ方：元の値の fiber と被覆の hammock の比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) {w : Word} {Y : Paths Q}
  {β : (Quiver.FreeGroupoid.of Q).obj A ⟶ positiveEvaluation.obj Y}

def zigzagLift (S : ZigzagValueFiber A w Y β) :
    letI := quiver A
    Zigzag (⊤ : MorphismProperty (Paths (Vertex A))) w
      ((Paths.of (Vertex A)).obj (root A))
      ((Paths.of (Vertex A)).obj (fiberEndpoint A Y β)) := by
  letI := quiver A
  exact
    { vertex := fun j => (Paths.of (Vertex A)).obj (zigzagVertex A S.obj j)
      first := congrArg (Paths.of (Vertex A)).obj (zigzagVertex_first A S.obj)
      last := congrArg (Paths.of (Vertex A)).obj (zigzagVertex_last A S)
      arrow := fun i => liftPathTo A (zigzagVertex A S.obj (w.source i))
        (zigzagVertex A S.obj (w.target i)) (S.obj.arrow i) (zigzagPrefix_arrow A S.obj i)
      backward_mem := fun _ _ => trivial }

lemma zigzagLift_arrow_projection (S : ZigzagValueFiber A w Y β) (i : Fin w.length) :
    letI := quiver A
    (pathProjection A).map ((zigzagLift A S).arrow i) = S.obj.arrow i := by
  let := quiver A
  exact liftPathTo_projection A (zigzagVertex A S.obj (w.source i))
    (zigzagVertex A S.obj (w.target i)) (S.obj.arrow i) (zigzagPrefix_arrow A S.obj i)

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
