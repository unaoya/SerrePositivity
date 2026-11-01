module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FreeQuiverCoverFiberWordAction
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeWordAction

/-!
# 持ち上げと射影の元の全語の作用への整合

概要：元の列の圧縮・恒等列の挿入と両関手は厳密に可換する。
方針：元の射影の全語への自然性と証明済みの両逆を使う。
規約：元の全部分圏の語の作用そのものを使う。
使われ方：全語の圏値・nerve 図式の同型。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) (Y : Paths Q)
  (β : (Quiver.FreeGroupoid.of Q).obj A ⟶ positiveEvaluation.obj Y)

lemma fiberProjection_word_obj :
    letI := quiver A
    ∀ {a b : Word} (f : a ⟶ b)
      (Z : Zigzag (⊤ : MorphismProperty (Paths (Vertex A))) a
        ((Paths.of (Vertex A)).obj (root A))
        ((Paths.of (Vertex A)).obj (fiberEndpoint A Y β))),
      (zigzagFiberProjection A b Y β).obj (WordAction.obj f Z) =
        (zigzagFiberWordAction A Y β f).obj ((zigzagFiberProjection A a Y β).obj Z) := by
  let := quiver A
  intro a b f Z
  apply ObjectProperty.FullSubcategory.ext
  exact (Zigzag.Relative.wordAction_obj_eq (pathProjectionRelative A) f Z).symm

lemma zigzagFiberProjection_wordAction :
    letI := quiver A
    ∀ {a b : Word} (f : a ⟶ b),
      WordAction.functor f ⋙ zigzagFiberProjection A b Y β =
        zigzagFiberProjection A a Y β ⋙ zigzagFiberWordAction A Y β f := by
  let := quiver A
  intro a b f
  apply CategoryTheory.Functor.hext
    (F := WordAction.functor f ⋙ zigzagFiberProjection A b Y β)
    (G := zigzagFiberProjection A a Y β ⋙ zigzagFiberWordAction A Y β f)
  · exact fiberProjection_word_obj A Y β f
  · intro S T g
    apply valueFiber_hom_hext A (fiberProjection_word_obj A Y β f S)
      (fiberProjection_word_obj A Y β f T)
    exact Zigzag.hom_hext
      (Zigzag.Relative.wordAction_obj_eq (pathProjectionRelative A) f S).symm
      (Zigzag.Relative.wordAction_obj_eq (pathProjectionRelative A) f T).symm
      _ _ (fun _ => HEq.rfl)

lemma zigzagLiftFunctor_wordAction :
    letI := quiver A
    ∀ {a b : Word} (f : a ⟶ b),
      zigzagFiberWordAction A Y β f ⋙ zigzagLiftFunctor A b Y β =
        zigzagLiftFunctor A a Y β ⋙ WordAction.functor f := by
  let := quiver A
  intro a b f
  calc
    _ = (zigzagLiftFunctor A a Y β ⋙ zigzagFiberProjection A a Y β) ⋙
        zigzagFiberWordAction A Y β f ⋙ zigzagLiftFunctor A b Y β := by
      rw [zigzagLiftFunctor_fiberProjection, CategoryTheory.Functor.id_comp]
    _ = zigzagLiftFunctor A a Y β ⋙
        (zigzagFiberProjection A a Y β ⋙ zigzagFiberWordAction A Y β f) ⋙
          zigzagLiftFunctor A b Y β := rfl
    _ = zigzagLiftFunctor A a Y β ⋙
        (WordAction.functor f ⋙ zigzagFiberProjection A b Y β) ⋙
          zigzagLiftFunctor A b Y β := by rw [zigzagFiberProjection_wordAction]
    _ = (zigzagLiftFunctor A a Y β ⋙ WordAction.functor f) ⋙
        (zigzagFiberProjection A b Y β ⋙ zigzagLiftFunctor A b Y β) := rfl
    _ = _ := by rw [zigzagFiberProjection_liftFunctor, CategoryTheory.Functor.comp_id]

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
