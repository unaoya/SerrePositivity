module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeNaturalWordRows
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingHomHEq
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingAppendNaturality

/-!
# 相対自然変換の比較成分と元の全語の作用

概要：同じ切断位置で元の成分を回収し、全語での比較の整合を示す。
方針：動く貼り合わせの語の自然性と元の相対関手の厳密な回収を使う。
規約：元の全縦成分と接合点を保持する。
使われ方：固定語のホモトピーを全語の余極限へ降ろす。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ZigzagAppend.Moving
open CategoryTheory

variable {D : Type u'} [Category.{v'} D] {V : MorphismProperty D} [V.IsMultiplicative]
  {a b a' b' : Word} {X Y Z X' Y' Z' : D}
  {S : Zigzag V a X Y} {S' : Zigzag V a X' Y'}
  {T : Zigzag V b Y Z} {T' : Zigzag V b Y' Z'}

lemma wordAction_map_heq (f : a ⟶ a') (g : b ⟶ b')
    (η : Zigzag.MovingHom S S') (θ : Zigzag.MovingHom T T')
    (hj : HEq (η.app (Fin.last a.length)) (θ.app 0)) :
    HEq (WordAction.movingMap (Word.appendMap f g) (map η θ hj))
      (map (WordAction.movingMap f η) (WordAction.movingMap g θ)
        ((Zigzag.MovingHom.app_heq η f.cut_last).trans
          (hj.trans (Zigzag.MovingHom.app_heq θ g.cut_zero).symm))) := by
  apply Zigzag.MovingHom.hext (obj_naturality f g S T) (obj_naturality f g S' T')
  intro k
  exact app_naturality f g η θ hj k

end SerrePositivity.EInfinity.Hammock.ZigzagAppend.Moving
namespace SerrePositivity.EInfinity.Hammock.RelativeNatural
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  {F G : LocalizerMorphism W V} (η : F.functor ⟶ G.functor)
  (hη : ∀ X, V (η.app X)) {a b : Word} {X Y : C}

lemma movingHom_wordAction (f : a ⟶ b) (S : Zigzag W a X Y) :
    HEq (WordAction.movingMap f (movingHom η hη S))
      (movingHom η hη (WordAction.obj f S)) := by
  apply Zigzag.MovingHom.hext (Zigzag.Relative.wordAction_obj_eq F f S)
    (Zigzag.Relative.wordAction_obj_eq G f S)
  intro j
  rfl

lemma innerHom_wordAction (f : a ⟶ b) (S : Zigzag W a X Y) :
    HEq (WordAction.movingMap (Word.appendMap f (𝟙 (Word.single .forward)))
      (innerHom η hη S)) (innerHom η hη (WordAction.obj f S)) := by
  have hs := ZigzagAppend.Moving.wordAction_map_heq f (𝟙 (Word.single .forward))
    (movingHom η hη S) (rightEdge η hη Y) (movingHom_last η hη S)
  exact hs.trans (Zigzag.MovingHom.append_heq
    (Zigzag.Relative.wordAction_obj_eq F f S) (Zigzag.Relative.wordAction_obj_eq G f S)
    (WordAction.obj_id _) (WordAction.obj_id _)
    (movingHom_wordAction η hη f S) (Zigzag.MovingHom.wordAction_id_heq (rightEdge η hη Y))
    _ (movingHom_last η hη (WordAction.obj f S)))

lemma component_wordAction (f : a ⟶ b) (S : Zigzag W a X Y) :
    HEq (WordAction.map (wordFunctor.map f) (component η hη S))
      (component η hη (WordAction.obj f S)) := by
  apply Zigzag.hom_hext (beforeRow_wordAction η f S) (afterRow_wordAction η f S)
  intro k
  have hs := ZigzagAppend.Moving.wordAction_map_heq (𝟙 (Word.single .forward))
    (Word.appendMap f (𝟙 (Word.single .forward)))
    (leftEdge η hη X) (innerHom η hη S) (innerHom_first η hη S).symm
  have h₀ : WordAction.obj (Word.appendMap f (𝟙 (Word.single .forward)))
      (ZigzagAppend.obj (Zigzag.Relative.obj F S) (ForwardZigzag.obj (η.app Y))) =
      ZigzagAppend.obj (Zigzag.Relative.obj F (WordAction.obj f S))
        (ForwardZigzag.obj (η.app Y)) := by
    simp only [ZigzagAppend.obj_naturality, WordAction.obj_id,
      Zigzag.Relative.wordAction_obj_eq]
  have h₁ : WordAction.obj (Word.appendMap f (𝟙 (Word.single .forward)))
      (ZigzagAppend.obj (Zigzag.Relative.obj G S) (ForwardZigzag.obj (𝟙 (G.functor.obj Y)))) =
      ZigzagAppend.obj (Zigzag.Relative.obj G (WordAction.obj f S))
        (ForwardZigzag.obj (𝟙 (G.functor.obj Y))) := by
    simp only [ZigzagAppend.obj_naturality, WordAction.obj_id,
      Zigzag.Relative.wordAction_obj_eq]
  have ht := Zigzag.MovingHom.append_heq (WordAction.obj_id _) (WordAction.obj_id _)
    h₀ h₁ (Zigzag.MovingHom.wordAction_id_heq (leftEdge η hη X))
    (innerHom_wordAction η hη f S)
    ((Zigzag.MovingHom.app_heq (leftEdge η hη X)
      (Word.Hom.cut_last (𝟙 (Word.single .forward)))).trans
      ((innerHom_first η hη S).symm.trans
        (Zigzag.MovingHom.app_heq (innerHom η hη S)
          (Word.Hom.cut_zero (Word.appendMap f (𝟙 (Word.single .forward))))).symm))
    (innerHom_first η hη (WordAction.obj f S)).symm
  exact Zigzag.MovingHom.app_heq_of_heq (beforeRow_wordAction η f S)
    (afterRow_wordAction η f S) (hs.trans ht) k

end SerrePositivity.EInfinity.Hammock.RelativeNatural
