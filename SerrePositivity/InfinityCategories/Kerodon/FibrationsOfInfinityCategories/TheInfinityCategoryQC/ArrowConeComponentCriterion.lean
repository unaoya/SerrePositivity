module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseLimitCriterion

/-!
概要：矢印圏の錐の極限性を二つの端点で判定する。
方針：区間の全頂点を二つの端点へ場合分けし、関手圏の点ごとの判定を使う。
規約：元の矢印圏内の錐を変更しない。
使われ方：lax pullback の矢印成分と両入力の極限性の接続。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：両端で極限錐である矢印圏内の錐は極限錐。
方針：区間の二頂点を列挙し、関手圏の点ごとの極限判定を適用する。
規約：添字 J は任意の単体集合。
使われ方：Tamme Lemma 8 の lax pullback の成分ごとの極限。 -/
lemma isLimitCone_arrow_of_endpoints {J C : SSet.{u}} [Quasicategory C]
    {r : J ⟶ (ihom (Δ[1] : SSet.{u})).obj C} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone r)
    (h0 : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorCone c (stdSimplex.obj₀Equiv.symm 0)))
    (h1 : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorCone c (stdSimplex.obj₀Equiv.symm 1))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_of_pointwise
  intro k
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective k
  fin_cases i
  · exact h0
  · exact h1

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
