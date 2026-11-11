module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendUnit
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GraphComposition

/-!
# 固定語の graph の左右単位則

概要：元の空語の単位との合成は、語の単位遷移の後で単位同型に一致する。
方針：全単体の元の射列を、zigzag の厳密な関手の単位則で照合する。
規約：全次数・全縦射の一致を使い、零単体での一致だけでは代用しない。
使われ方：元の全語の余極限上の合成の左右単位則。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C)

lemma graphComposition_left_unit :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphUnit W X ⊗ₘ 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphComposition W _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty a X X Y ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit.empty_append a)) =
      (λ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y)).hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram_map]
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  change ((Functor.const (Fin (n.unop.len + 1))).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W X)).prod' p.2 ⋙
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit.empty_append a)) = p.2
  apply Functor.hext (fun j => eq_of_heq
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj_eqToHom_heq _ _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.empty_left_obj_heq (p.2.obj j))))
  intro i j f
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.map_eqToHom_heq _ _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.empty_left_map_heq (p.2.map f))

lemma graphComposition_right_unit :
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphUnit W Y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphComposition W a _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty X Y Y ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit.append_empty a)) =
      (ρ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y)).hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram_map]
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  change p.1.prod' ((Functor.const (Fin (n.unop.len + 1))).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W Y)) ⋙
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit.append_empty a)) = p.1
  apply Functor.hext (fun j => eq_of_heq
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj_eqToHom_heq _ _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.empty_right_obj_heq (p.1.obj j))))
  intro i j f
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.map_eqToHom_heq _ _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.empty_right_map_heq (p.1.map f))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
