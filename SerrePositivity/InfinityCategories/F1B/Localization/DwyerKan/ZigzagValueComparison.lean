module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagValueRelative
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagValuePostcompose
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagValueTransport
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeFixedZigzagFunctor

/-!
# 元の関手の可換正方形による zigzag 評価の比較

概要：元の相対関手と反転関手の可換性は、同じ zigzag の値の異種等式を与える。
方針：元の相対関手の像・関手の等式・後合成の三つの回収を合成する。
規約：固定対象へ端点を戻した場合の比較も含む。
使われ方：自由解像の作用素に沿う元の局所化 Hom への右射の自然性。
-/

@[expose] public section
universe u
noncomputable section
namespace SerrePositivity.EInfinity.Hammock.Zigzag.Value
open CategoryTheory

variable {C D A B : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} A] [Category.{u} B]
  {W : MorphismProperty C} {V : MorphismProperty D}
  (F : LocalizerMorphism W V) (L : C ⥤ A) (hL : W.IsInvertedBy L)
  (M : D ⥤ B) (hM : V.IsInvertedBy M) (K : A ⥤ B) {w : Word} {X Y : C}

lemma value_comparison (h : L ⋙ K = F.functor ⋙ M) (S : Zigzag W w X Y) :
    HEq (value M hM (Relative.obj F S)) (K.map (value L hL S)) :=
  (heq_of_eq (value_relative F M hM S)).trans
    ((value_functor_congr h.symm (relativeInverts F M hM) (postInverts L hL K) S).trans
      (heq_of_eq (value_postcompose L hL K S)))

variable [W.IsMultiplicative] [V.IsMultiplicative] {X' Y' : D}

lemma value_fixed_comparison (h : L ⋙ K = F.functor ⋙ M)
    (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y') (S : Zigzag W w X Y) :
    HEq (value M hM ((Relative.fixedFunctor F hX hY).obj S)) (K.map (value L hL S)) :=
  (value_endpoint_change M hM hX hY (Relative.obj F S)).trans
    (value_comparison F L hL M hM K h S)

end SerrePositivity.EInfinity.Hammock.Zigzag.Value
