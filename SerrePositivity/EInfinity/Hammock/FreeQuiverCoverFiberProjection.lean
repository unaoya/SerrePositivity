module

public import SerrePositivity.EInfinity.Hammock.FreeQuiverCoverProjectedPrefix

/-!
# 被覆の元の zigzag から元の値の fiber への射影

概要：元の固定端点の被覆 zigzag は射影後に指定した元の値を持つ。
方針：最後の接頭ラベルと元の終点のラベルを照合する。
規約：全部分圏への射影関手の包含との合成は元の射影である。
使われ方：固定語ごとの元の圏同値。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) (w : Word) (Y : Paths Q)
  (β : (Quiver.FreeGroupoid.of Q).obj A ⟶ positiveEvaluation.obj Y)

lemma projectedValue_eq :
    letI := quiver A
    ∀ Z : Zigzag (⊤ : MorphismProperty (Paths (Vertex A))) w
      ((Paths.of (Vertex A)).obj (root A))
      ((Paths.of (Vertex A)).obj (fiberEndpoint A Y β)),
      Zigzag.Value.value positiveEvaluation positiveEvaluation_inverts_top
        ((zigzagProjection A w Y β).obj Z) = β := by
  let := quiver A
  intro Z
  have he := Vertex.path_heq A (show (show Vertex A from Z.vertex (Fin.last w.length)) =
    fiberEndpoint A Y β from Z.last)
  exact eq_of_heq ((zigzagPrefix_last_heq_value A _).symm.trans
    ((heq_of_eq (projectedPrefix_eq_label A Z _)).trans he))

def zigzagFiberProjection :
    letI := quiver A
    Zigzag (⊤ : MorphismProperty (Paths (Vertex A))) w
      ((Paths.of (Vertex A)).obj (root A))
      ((Paths.of (Vertex A)).obj (fiberEndpoint A Y β)) ⥤ ZigzagValueFiber A w Y β := by
  letI := quiver A
  exact
    { obj := fun Z => ⟨(zigzagProjection A w Y β).obj Z, projectedValue_eq A w Y β Z⟩
      map := fun f => ObjectProperty.homMk ((zigzagProjection A w Y β).map f)
      map_id := fun Z => ObjectProperty.hom_ext (zigzagValueProperty A w Y β)
        ((zigzagProjection A w Y β).map_id Z)
      map_comp := fun f g => ObjectProperty.hom_ext (zigzagValueProperty A w Y β)
        ((zigzagProjection A w Y β).map_comp f g) }

lemma zigzagFiberProjection_inclusion :
    letI := quiver A
    zigzagFiberProjection A w Y β ⋙ (zigzagValueProperty A w Y β).ι =
      zigzagProjection A w Y β := by
  let := quiver A
  apply CategoryTheory.Functor.hext
    (F := zigzagFiberProjection A w Y β ⋙ (zigzagValueProperty A w Y β).ι)
    (G := zigzagProjection A w Y β)
  · intro Z
    rfl
  · intro Z T f
    rfl

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
