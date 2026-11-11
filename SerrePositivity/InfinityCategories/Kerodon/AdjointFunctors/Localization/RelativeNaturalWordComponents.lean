module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalWordRows
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingHomHEq
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendNaturality

/-!
# 相対自然変換の比較成分と元の全語の作用

概要：同じ切断位置で元の成分を回収し、全語での比較の整合を示す。
方針：動く貼り合わせの語の自然性と元の相対関手の厳密な回収を使う。
規約：元の全縦成分と接合点を保持する。
使われ方：固定語のホモトピーを全語の余極限へ降ろす。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {D : Type u'} [Category.{v'} D] {V : MorphismProperty D} [V.IsMultiplicative]
  {a b a' b' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y Z X' Y' Z' : D}
  {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag V a X Y} {S' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag V a X' Y'}
  {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag V b Y Z} {T' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag V b Y' Z'}

lemma wordAction_map_heq (f : a ⟶ a') (g : b ⟶ b')
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S S') (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom T T')
    (hj : HEq (η.app (Fin.last a.length)) (θ.app 0)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map η θ hj))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingMap f η) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingMap g θ)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.app_heq η f.cut_last).trans
          (hj.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.app_heq θ g.cut_zero).symm))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingHomHEq.hext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.obj_naturality f g S T) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.obj_naturality f g S' T')
  intro k
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendNaturality.app_naturality f g η θ hj k

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  {F G : LocalizerMorphism W V} (η : F.functor ⟶ G.functor)
  (hη : ∀ X, V (η.app X)) {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

lemma movingHom_wordAction (f : a ⟶ b) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalMoving.movingHom η hη S))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalMoving.movingHom η hη (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingHomHEq.hext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeWordAction.wordAction_obj_eq F f S)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeWordAction.wordAction_obj_eq G f S)
  intro j
  rfl

lemma innerHom_wordAction (f : a ⟶ b) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap f (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.innerHom η hη S)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.innerHom η hη (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S)) := by
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction_map_heq f (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalMoving.movingHom η hη S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.rightEdge η hη Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalMoving.movingHom_last η hη S)
  exact hs.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingHomHEq.append_heq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeWordAction.wordAction_obj_eq F f S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeWordAction.wordAction_obj_eq G f S)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.obj_id _) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.obj_id _)
    (movingHom_wordAction η hη f S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingHomHEq.wordAction_id_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.rightEdge η hη Y))
    _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalMoving.movingHom_last η hη (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S)))

lemma component_wordAction (f : a ⟶ b) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordFunctor.map f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.component η hη S))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.component η hη (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeRow_wordAction η f S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterRow_wordAction η f S)
  intro k
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction_map_heq (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap f (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.leftEdge η hη X) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.innerHom η hη S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.innerHom_first η hη S).symm
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap f (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj F S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (η.app Y))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj F (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (η.app Y)) := by
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.obj_naturality, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.obj_id,
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeWordAction.wordAction_obj_eq]
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap f (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj G S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (𝟙 (G.functor.obj Y)))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj G (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (𝟙 (G.functor.obj Y))) := by
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.obj_naturality, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.obj_id,
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeWordAction.wordAction_obj_eq]
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingHomHEq.append_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.obj_id _) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.obj_id _)
    h₀ h₁ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingHomHEq.wordAction_id_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.leftEdge η hη X))
    (innerHom_wordAction η hη f S)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.app_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.leftEdge η hη X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom.cut_last (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)))).trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.innerHom_first η hη S).symm.trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.app_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.innerHom η hη S)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom.cut_zero (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap f (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward))))).symm))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.innerHom_first η hη (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S)).symm
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingHomHEq.app_heq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeRow_wordAction η f S)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterRow_wordAction η f S) (hs.trans ht) k

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
