module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueRelative
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePostcompose
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueTransport
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor

/-!
# 元の関手の可換正方形による zigzag 評価の比較

概要：元の相対関手と反転関手の可換性は、同じ zigzag の値の異種等式を与える。
方針：元の相対関手の像・関手の等式・後合成の三つの回収を合成する。
規約：固定対象へ端点を戻した場合の比較も含む。
使われ方：自由解像の作用素に沿う元の局所化 Hom への右射の自然性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C D A B : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} A] [Category.{u} B]
  {W : MorphismProperty C} {V : MorphismProperty D}
  (F : LocalizerMorphism W V) (L : C ⥤ A) (hL : W.IsInvertedBy L)
  (M : D ⥤ B) (hM : V.IsInvertedBy M) (K : A ⥤ B) {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

lemma value_comparison (h : L ⋙ K = F.functor ⋙ M) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value M hM (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj F S)) (K.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value L hL S)) :=
  (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.value_relative F M hM S)).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.value_functor_congr h.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.relativeInverts F M hM) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postInverts L hL K) S).trans
      (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.value_postcompose L hL K S)))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.value_comparison export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (value_comparison)


variable [W.IsMultiplicative] [V.IsMultiplicative] {X' Y' : D}

lemma value_fixed_comparison (h : L ⋙ K = F.functor ⋙ M)
    (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y') (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value M hM ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F hX hY).obj S)) (K.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value L hL S)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.value_endpoint_change M hM hX hY (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj F S)).trans
    (value_comparison F L hL M hM K h S)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.value_fixed_comparison export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (value_fixed_comparison)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
