module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange

/-!
# 指定した端点の表示を保つ相対 zigzag 関手

概要：元の相対関手の像の端点を、指定した元の対象へ等式で戻す。
方針：元の相対関手と端点移送を合成する。
規約：端点の等式の証明には依存しない。全縦射を保持する。
使われ方：自由解像の固定した両対象での全単体作用素。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v' u'' v''
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  {U : MorphismProperty E} [U.IsMultiplicative] {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}
  {X Y : C} {X' Y' : D} {X'' Y'' : E}

def fixedFunctor (F : LocalizerMorphism W V) (hX : F.functor.obj X = X')
    (hY : F.functor.obj Y = Y') : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag V w X' Y' :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange.functor hX hY

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Relative.fixedFunctor export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor (fixedFunctor)


lemma fixedFunctor_id (hX : X = X) (hY : Y = Y) :
    fixedFunctor (W := W) (w := w) (LocalizerMorphism.id W) hX hY = 𝟭 _ := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Relative.fixedFunctor_id export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor (fixedFunctor_id)


lemma fixedFunctor_comp (F : LocalizerMorphism W V) (G : LocalizerMorphism V U)
    (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
    (hX' : G.functor.obj X' = X'') (hY' : G.functor.obj Y' = Y'') :
    fixedFunctor (w := w) (F.comp G) ((congrArg G.functor.obj hX).trans hX')
      ((congrArg G.functor.obj hY).trans hY') =
        fixedFunctor F hX hY ⋙ fixedFunctor G hX' hY' := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Relative.fixedFunctor_comp export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor (fixedFunctor_comp)


lemma fixedFunctor_congr {F G : LocalizerMorphism W V} (h : F.functor = G.functor)
    (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
    (hX' : G.functor.obj X = X') (hY' : G.functor.obj Y = Y') :
    fixedFunctor (w := w) F hX hY = fixedFunctor G hX' hY' := by
  cases F
  cases G
  cases h
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Relative.fixedFunctor_congr export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor (fixedFunctor_congr)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor
