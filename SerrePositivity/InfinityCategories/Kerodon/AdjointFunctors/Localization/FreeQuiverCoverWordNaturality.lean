module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverFiberWordAction
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeWordAction

/-!
# 持ち上げと射影の元の全語の作用への整合

概要：元の列の圧縮・恒等列の挿入と両関手は厳密に可換する。
方針：元の射影の全語への自然性と証明済みの両逆を使う。
規約：元の全部分圏の語の作用そのものを使う。
使われ方：全語の圏値・nerve 図式の同型。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) (Y : Paths Q)
  (β : (Quiver.FreeGroupoid.of Q).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.obj Y)

lemma fiberProjection_word_obj :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b)
      (Z : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A))) a
        ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.root A))
        ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fiberEndpoint A Y β))),
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberProjection A b Y β).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f Z) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberWordAction A Y β f).obj ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberProjection A a Y β).obj Z) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro a b f Z
  apply ObjectProperty.FullSubcategory.ext
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeWordAction.wordAction_obj_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjectionRelative A) f Z).symm

lemma zigzagFiberProjection_wordAction :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b),
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberProjection A b Y β =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberProjection A a Y β ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberWordAction A Y β f := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro a b f
  apply CategoryTheory.Functor.hext
    (F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberProjection A b Y β)
    (G := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberProjection A a Y β ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberWordAction A Y β f)
  · exact fiberProjection_word_obj A Y β f
  · intro S T g
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.valueFiber_hom_hext A (fiberProjection_word_obj A Y β f S)
      (fiberProjection_word_obj A Y β f T)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeWordAction.wordAction_obj_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjectionRelative A) f S).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeWordAction.wordAction_obj_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjectionRelative A) f T).symm
      _ _ (fun _ => HEq.rfl)

lemma zigzagLiftFunctor_wordAction :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b),
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberWordAction A Y β f ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLiftFunctor A b Y β =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLiftFunctor A a Y β ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro a b f
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLiftFunctor A a Y β ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberProjection A a Y β) ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberWordAction A Y β f ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLiftFunctor A b Y β := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLiftFunctor_fiberProjection, CategoryTheory.Functor.id_comp]
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLiftFunctor A a Y β ⋙
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberProjection A a Y β ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberWordAction A Y β f) ⋙
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLiftFunctor A b Y β := rfl
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLiftFunctor A a Y β ⋙
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberProjection A b Y β) ⋙
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLiftFunctor A b Y β := by rw [zigzagFiberProjection_wordAction]
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLiftFunctor A a Y β ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) ⋙
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberProjection A b Y β ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLiftFunctor A b Y β) := rfl
    _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberProjection_liftFunctor, CategoryTheory.Functor.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
