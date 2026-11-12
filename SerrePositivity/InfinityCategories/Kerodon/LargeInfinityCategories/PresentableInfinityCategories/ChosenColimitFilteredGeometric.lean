module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ChosenColimitAdjunction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftAdjointCoconePreservation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FilteredGeometricFunctorOperations
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorPostcompColimitPreservation
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition

/-!
概要：選んだ余極限関手と後合成関手の filtered 余極限・幾何学的実現保存。
方針：余極限と定値の随伴、および元の関手圏の各点計算を使う。
規約：選んだ全関手と元の指定余錐を保つ。
使われ方：有限余積比較の両側の生成操作保存。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
attribute [local instance] CategoryTheory.uliftCategory
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：選んだ余極限関手は小さい filtered 余極限を保存する。
方針：定値図式の左随伴として保存性を適用する。
規約：元の選んだ全関手を使う。
使われ方：有限余積全関手の生成操作保存。 -/
lemma chosenColimitFunctor_preservesSmallFiltered {K X : SSet.{u + 1}} [Quasicategory X]
    (hX : ∀ p : K ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesSmallKappaFilteredColimits Cardinal.aleph0 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitFunctor K X hX) := by
  intro I hI hκ p c hc
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.mapJoinCocone_isColimit_of_adjunction_of_quasicategoryShape
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitAdjunction K X hX) c hc

/-- 概要：選んだ余極限関手は小さい幾何学的実現を保存する。
方針：元の反対単体圏形状の余極限へ随伴の保存を適用する。
規約：指定実現の全余錐を保つ。
使われ方：有限余積全関手の単体的生成操作保存。 -/
lemma chosenColimitFunctor_preservesSmallGeometric {K X : SSet.{u + 1}} [Quasicategory X]
    (hX : ∀ p : K ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExactnessAndAnimation.SimplicialObjectsOfInfinityCategories.PreservesSmallGeometricRealizations (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitFunctor K X hX) := by
  intro p c hc
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.mapJoinCocone_isColimit_of_adjunction_of_quasicategoryShape
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitAdjunction K X hX) c hc

/-- 概要：filtered 保存関手の後合成は関手圏でも同じ余極限を保存する。
方針：元の指定余極限の各点計算を使う。
規約：始域の小余極限存在を明示する。
使われ方：有限余積比較の左側の保存条件。 -/
lemma postcomposition_preservesSmallFiltered {A X Y : SSet.{u + 1}}
    [Quasicategory X] [Quasicategory Y] (hX : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits X) (q : X ⟶ Y)
    (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesSmallKappaFilteredColimits Cardinal.aleph0 q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesSmallKappaFilteredColimits Cardinal.aleph0 ((ihom A).map q) := by
  intro I hI hκ p c hc
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.postcomposition_map_isColimit (hX I) q (hq I) c hc

/-- 概要：実現保存関手の後合成は関手圏でも元の実現を保存する。
方針：元の単体的余極限を各点で計算する。
規約：始域の小余極限存在を明示する。
使われ方：有限余積比較の左側の実現保存条件。 -/
lemma postcomposition_preservesSmallGeometric {A X Y : SSet.{u + 1}}
    [Quasicategory X] [Quasicategory Y] (hX : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits X) (q : X ⟶ Y)
    (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.ExactnessAndAnimation.SimplicialObjectsOfInfinityCategories.PreservesSmallGeometricRealizations q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExactnessAndAnimation.SimplicialObjectsOfInfinityCategories.PreservesSmallGeometricRealizations ((ihom A).map q) := by
  intro p c hc
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.postcomposition_map_isColimit (hX (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallSimplexOpposite.{u})) q hq c hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
