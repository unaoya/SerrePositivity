module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverZigzagLiftFunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor

/-!
# 持ち上げた元の全 zigzag の射影による回収

概要：持ち上げ関手と元の射影の合成は値の fiber の包含に一致する。
方針：元の全頂点・全列・全縦成分の等式を使う。
規約：元の値を固定した全部分圏への包含そのものを回収する。
使われ方：元の hammock の成分と木上の hammock の比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

def pathProjectionRelative :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    LocalizerMorphism (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)))
      (⊤ : MorphismProperty (Paths Q)) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection A, fun _ _ _ _ => trivial⟩

variable (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (Y : Paths Q)
  (β : (Quiver.FreeGroupoid.of Q).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.obj Y)

def zigzagProjection :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A))) w
      ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.root A))
      ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fiberEndpoint A Y β)) ⥤
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (Paths Q)) w ((Paths.of Q).obj A) Y := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (pathProjectionRelative A)

variable {w Y β}

lemma zigzagLift_projection (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueFiber A w Y β) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    (zigzagProjection A w Y β).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLift A S) = S.obj := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext
  · intro j
    rfl
  · intro i
    exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLift_arrow_projection A S i)

lemma zigzagLiftFunctor_projection :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLiftFunctor A w Y β ⋙ zigzagProjection A w Y β =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagValueProperty A w Y β).ι := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  apply CategoryTheory.Functor.hext
    (F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLiftFunctor A w Y β ⋙ zigzagProjection A w Y β)
    (G := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagValueProperty A w Y β).ι)
  · exact zigzagLift_projection A
  · intro S T f
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (zigzagLift_projection A S) (zigzagLift_projection A T)
      _ _ (fun j => heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLiftMap_app_projection A f j))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
