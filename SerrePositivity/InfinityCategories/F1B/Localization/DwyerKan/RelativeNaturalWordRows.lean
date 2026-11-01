module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeNaturalFunctors
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeWordAction
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendNaturality
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordPadding

/-!
# 相対自然変換の二行と元の全語の作用

概要：外側の二列を保つ元の sandwich 関手で両行を移す。
方針：元の連結の自然性と相対関手の語作用との整合を使う。
規約：元の全生成列と語の全単調写像を保持する。
使われ方：比較の全語への降下。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.RelativeNatural
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  {F G : LocalizerMorphism W V} (η : F.functor ⟶ G.functor)
  {a b : Word} {X Y : C}

abbrev wordFunctor : Word ⥤ Word :=
  Word.sandwichFunctor (Word.single .forward) (Word.single .forward)

lemma beforeRow_wordAction (f : a ⟶ b) (S : Zigzag W a X Y) :
    WordAction.obj (wordFunctor.map f) (beforeRow η S) =
      beforeRow η (WordAction.obj f S) := by
  change WordAction.obj (Word.appendMap (𝟙 _) (Word.appendMap f (𝟙 _))) _ = _
  simp only [beforeRow, ZigzagAppend.obj_naturality, WordAction.obj_id,
    Zigzag.Relative.wordAction_obj_eq]

lemma afterRow_wordAction (f : a ⟶ b) (S : Zigzag W a X Y) :
    WordAction.obj (wordFunctor.map f) (afterRow η S) =
      afterRow η (WordAction.obj f S) := by
  change WordAction.obj (Word.appendMap (𝟙 _) (Word.appendMap f (𝟙 _))) _ = _
  simp only [afterRow, ZigzagAppend.obj_naturality, WordAction.obj_id,
    Zigzag.Relative.wordAction_obj_eq]

end SerrePositivity.EInfinity.Hammock.RelativeNatural
