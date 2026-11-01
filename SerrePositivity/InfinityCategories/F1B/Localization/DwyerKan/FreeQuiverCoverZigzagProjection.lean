module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FreeQuiverCoverZigzagLiftFunctor
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeZigzagFunctor

/-!
# 持ち上げた元の全 zigzag の射影による回収

概要：持ち上げ関手と元の射影の合成は値の fiber の包含に一致する。
方針：元の全頂点・全列・全縦成分の等式を使う。
規約：元の値を固定した全部分圏への包含そのものを回収する。
使われ方：元の hammock の成分と木上の hammock の比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

def pathProjectionRelative :
    letI := quiver A
    LocalizerMorphism (⊤ : MorphismProperty (Paths (Vertex A)))
      (⊤ : MorphismProperty (Paths Q)) := by
  letI := quiver A
  exact ⟨pathProjection A, fun _ _ _ _ => trivial⟩

variable (w : Word) (Y : Paths Q)
  (β : (Quiver.FreeGroupoid.of Q).obj A ⟶ positiveEvaluation.obj Y)

def zigzagProjection :
    letI := quiver A
    Zigzag (⊤ : MorphismProperty (Paths (Vertex A))) w
      ((Paths.of (Vertex A)).obj (root A))
      ((Paths.of (Vertex A)).obj (fiberEndpoint A Y β)) ⥤
        Zigzag (⊤ : MorphismProperty (Paths Q)) w ((Paths.of Q).obj A) Y := by
  letI := quiver A
  exact Zigzag.Relative.functor (pathProjectionRelative A)

variable {w Y β}

lemma zigzagLift_projection (S : ZigzagValueFiber A w Y β) :
    letI := quiver A
    (zigzagProjection A w Y β).obj (zigzagLift A S) = S.obj := by
  let := quiver A
  apply Zigzag.object_ext
  · intro j
    rfl
  · intro i
    exact heq_of_eq (zigzagLift_arrow_projection A S i)

lemma zigzagLiftFunctor_projection :
    letI := quiver A
    zigzagLiftFunctor A w Y β ⋙ zigzagProjection A w Y β =
      (zigzagValueProperty A w Y β).ι := by
  let := quiver A
  apply CategoryTheory.Functor.hext
    (F := zigzagLiftFunctor A w Y β ⋙ zigzagProjection A w Y β)
    (G := (zigzagValueProperty A w Y β).ι)
  · exact zigzagLift_projection A
  · intro S T f
    exact Zigzag.hom_hext (zigzagLift_projection A S) (zigzagLift_projection A T)
      _ _ (fun j => heq_of_eq (zigzagLiftMap_app_projection A f j))

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
