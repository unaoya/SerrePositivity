module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeNaturalRows
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendFunctor

/-!
# 相対自然変換の両行を与える元の関手

概要：[id,F(S),ηY] と [ηX,G(S),id] を全縦射に作用させる。
方針：元の相対関手、定数一列、元の連結関手を合成する。
規約：全体の端点と元の全縦射を保持する。
使われ方：固定語の比較自然変換と nerve ホモトピー。
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
  {F G : LocalizerMorphism W V} (η : F.functor ⟶ G.functor) (w : Word) (X Y : C)

def beforeFunctor : Zigzag W w X Y ⥤
    Zigzag V (Word.append (Word.single .forward) (Word.append w (Word.single .forward)))
      (F.functor.obj X) (G.functor.obj Y) :=
  ((Functor.const (Zigzag W w X Y)).obj (ForwardZigzag.obj (𝟙 (F.functor.obj X)))).prod'
    ((Zigzag.Relative.functor F).prod'
      ((Functor.const (Zigzag W w X Y)).obj (ForwardZigzag.obj (η.app Y))) ⋙
        ZigzagAppend.functor) ⋙ ZigzagAppend.functor

def afterFunctor : Zigzag W w X Y ⥤
    Zigzag V (Word.append (Word.single .forward) (Word.append w (Word.single .forward)))
      (F.functor.obj X) (G.functor.obj Y) :=
  ((Functor.const (Zigzag W w X Y)).obj (ForwardZigzag.obj (η.app X))).prod'
    ((Zigzag.Relative.functor G).prod'
      ((Functor.const (Zigzag W w X Y)).obj (ForwardZigzag.obj (𝟙 (G.functor.obj Y)))) ⋙
        ZigzagAppend.functor) ⋙ ZigzagAppend.functor

lemma beforeFunctor_obj (S : Zigzag W w X Y) :
    (beforeFunctor η w X Y).obj S = beforeRow η S := rfl

lemma afterFunctor_obj (S : Zigzag W w X Y) :
    (afterFunctor η w X Y).obj S = afterRow η S := rfl

end SerrePositivity.EInfinity.Hammock.RelativeNatural
