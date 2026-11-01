module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FreeQuiverCoverZigzagProjection
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagValueRelative

/-!
# 射影した元の zigzag の列と被覆頂点のラベル

概要：元の被覆の横列は射影後にも元の頂点ラベルの合成を回収する。
方針：既存の相対関手による列の照合と正向きの終点の式を使う。
規約：元の被覆の順向きと逆向きの射列を保持する。
使われ方：射影後の接頭値から元の全頂点を回収する。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

lemma Vertex.path_heq {x y : Vertex A} (h : x = y) : HEq x.path y.path := by
  cases h
  rfl

variable {w : Word} {Y : Paths Q}
  {β : (Quiver.FreeGroupoid.of Q).obj A ⟶ positiveEvaluation.obj Y}

lemma projected_forward_label :
    letI := quiver A
    ∀ (Z : Zigzag (⊤ : MorphismProperty (Paths (Vertex A))) w
      ((Paths.of (Vertex A)).obj (root A))
      ((Paths.of (Vertex A)).obj (fiberEndpoint A Y β)))
      (i : Fin w.length) (hi : w.direction i = .forward),
      (Z.vertex i.castSucc).path ≫ positiveEvaluation.map
        (Direction.arrow .forward ((zigzagProjection A w Y β).obj Z) i hi) =
          (Z.vertex i.succ).path := by
  let := quiver A
  intro Z i hi
  have he := eq_of_heq (Zigzag.Value.arrow_relative_heq
    (pathProjectionRelative A) .forward Z i hi)
  exact (congrArg (fun p => (Z.vertex i.castSucc).path ≫ positiveEvaluation.map p) he).trans
    (positive_endpoint A (Z.vertex i.castSucc) (Z.vertex i.succ)
      (Direction.arrow .forward Z i hi))

lemma projected_backward_label :
    letI := quiver A
    ∀ (Z : Zigzag (⊤ : MorphismProperty (Paths (Vertex A))) w
      ((Paths.of (Vertex A)).obj (root A))
      ((Paths.of (Vertex A)).obj (fiberEndpoint A Y β)))
      (i : Fin w.length) (hi : w.direction i = .backward),
      (Z.vertex i.succ).path ≫ positiveEvaluation.map
        (Direction.arrow .backward ((zigzagProjection A w Y β).obj Z) i hi).unop =
          (Z.vertex i.castSucc).path := by
  let := quiver A
  intro Z i hi
  have he := congrArg Quiver.Hom.unop (eq_of_heq (Zigzag.Value.arrow_relative_heq
    (pathProjectionRelative A) .backward Z i hi))
  exact (congrArg (fun p => (Z.vertex i.succ).path ≫ positiveEvaluation.map p) he).trans
    (positive_endpoint A (Z.vertex i.succ) (Z.vertex i.castSucc)
      (Direction.arrow .backward Z i hi).unop)

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
