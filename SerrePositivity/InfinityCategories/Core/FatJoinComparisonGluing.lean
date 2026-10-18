module

public import SerrePositivity.InfinityCategories.Core.JoinPushout
public import SerrePositivity.InfinityCategories.Core.FatJoinPushout
public import SerrePositivity.InfinityCategories.Core.FatJoinLeftMono
public import SerrePositivity.InfinityCategories.Core.FatJoinComparisonNaturality
public import SerrePositivity.InfinityCategories.Core.PrecompositionPushoutGluing

/-!
概要：左因子の単射を含む貼り合わせによる fat join 比較の同値条件。
方針：通常の join と fat join の pushout を一般の比較の貼り合わせ補題に入れる。
規約：三つの比較が同値条件を満たすことを仮定する。
使われ方：Kerodon Lemma 4.6.2.10 のセル分解への帰納。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：三つの左因子で fat join 比較が同値条件を満たせば、単射の pushout でも満たす。
方針：両方の join の pushout 保存と比較の自然性を使う。
規約：f のみが単射。固定因子 K と他の貼り合わせ射は任意。
使われ方：Kerodon Lemma 4.6.2.10 の左因子のセル分解。 -/
lemma isPrecompositionEquivalence_fatJoinComparison_of_pushout_left
    {A B C D : SSet.{u}} {f : A ⟶ B} [Mono f] {g : A ⟶ C}
    {r : B ⟶ D} {t : C ⟶ D} (h : IsPushout f g r t) (K : SSet.{u})
    (hA : IsPrecompositionEquivalence (fatJoinComparison A K))
    (hB : IsPrecompositionEquivalence (fatJoinComparison B K))
    (hC : IsPrecompositionEquivalence (fatJoinComparison C K)) :
    IsPrecompositionEquivalence (fatJoinComparison D K) := by
  exact isPrecompositionEquivalence_of_pushout_gluing
    (fatJoin_left_isPushout h K) (join_left_isPushout h K)
    (fatJoinComparison A K) (fatJoinComparison B K) (fatJoinComparison C K)
    (fatJoinComparison D K) (fatJoinComparison_naturality f (𝟙 K))
    (fatJoinComparison_naturality g (𝟙 K)) (fatJoinComparison_naturality r (𝟙 K))
    (fatJoinComparison_naturality t (𝟙 K)) hA hB hC

end SerrePositivity.InfinityCategories
