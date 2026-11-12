module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.FiniteColimitClosure
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.CoherentFiniteLimitExchange
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：κ-compact 対象の有限余極限閉性を、交換の追加仮定なしに結論する。
方針：証明済みの全有限形状の交換を、元の Hom 錐族に適用する既存定理へ代入する。
規約：元の指定余極限余錐と頂点を保持し、添字と標的の宇宙を区別する。
使われ方：I-2 d、旧 N-6 c の無条件化と compact 全部分圏の有限余極限。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

/-- 元の有限余極限の全図式が κ-compact なら、その同じ元の頂点も κ-compact。 -/
@[kerodon 064Y]
lemma isKappaCompact_finiteColimit {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    {K C : SSet.{max u v}} [K.Finite] [Quasicategory C] {D : K ⟶ C}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone a)
    (hD : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, v} κ (D.app (Opposite.op ⦋0⦌) k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, v} κ a.vertex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_finiteColimit_of_exchange hκ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.indFiniteLimitExchangeInput a ha hD

/-- 周囲に有限余極限があれば、compact 全部分圏にも交換入力なしに存在する。 -/
@[kerodon 064Y]
lemma hasFiniteColimits_kappaCompactObjects (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (C : SSet.{max u v}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, v} κ C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.hasFiniteColimits_kappaCompactObjects_of_exchange κ hκ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.indFiniteLimitExchangeInput C

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
