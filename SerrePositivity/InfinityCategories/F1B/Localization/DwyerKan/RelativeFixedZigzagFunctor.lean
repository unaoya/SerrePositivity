module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeZigzagFunctor
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagEndpointChange

/-!
# 指定した端点の表示を保つ相対 zigzag 関手

概要：元の相対関手の像の端点を、指定した元の対象へ等式で戻す。
方針：元の相対関手と端点移送を合成する。
規約：端点の等式の証明には依存しない。全縦射を保持する。
使われ方：自由解像の固定した両対象での全単体作用素。
-/

@[expose] public section
universe u v u' v' u'' v''
noncomputable section
namespace SerrePositivity.EInfinity.Hammock.Zigzag.Relative
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  {U : MorphismProperty E} [U.IsMultiplicative] {w : Word}
  {X Y : C} {X' Y' : D} {X'' Y'' : E}

def fixedFunctor (F : LocalizerMorphism W V) (hX : F.functor.obj X = X')
    (hY : F.functor.obj Y = Y') : Zigzag W w X Y ⥤ Zigzag V w X' Y' :=
  functor F ⋙ EndpointChange.functor hX hY

lemma fixedFunctor_id (hX : X = X) (hY : Y = Y) :
    fixedFunctor (W := W) (w := w) (LocalizerMorphism.id W) hX hY = 𝟭 _ := rfl

lemma fixedFunctor_comp (F : LocalizerMorphism W V) (G : LocalizerMorphism V U)
    (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
    (hX' : G.functor.obj X' = X'') (hY' : G.functor.obj Y' = Y'') :
    fixedFunctor (w := w) (F.comp G) ((congrArg G.functor.obj hX).trans hX')
      ((congrArg G.functor.obj hY).trans hY') =
        fixedFunctor F hX hY ⋙ fixedFunctor G hX' hY' := rfl

lemma fixedFunctor_congr {F G : LocalizerMorphism W V} (h : F.functor = G.functor)
    (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
    (hX' : G.functor.obj X = X') (hY' : G.functor.obj Y = Y') :
    fixedFunctor (w := w) F hX hY = fixedFunctor G hX' hY' := by
  cases F
  cases G
  cases h
  rfl

end SerrePositivity.EInfinity.Hammock.Zigzag.Relative
