module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorPostcompColimitPreservation

/-!
概要：余完備な標的への全関手圏の小余極限と各点計算を構成する。
方針：元の小形状に対する点ごとの普遍余錐族をまとめる。
規約：関手の始域の小ささや quasicategory 性を要求しない。
使われ方：HTT 5.5.3.6 の Fun(K,C) の presentable 性の余極限側。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorSmallColimits

/-- 概要：全小余極限を持つ標的への関手圏も全小余極限を持つ。
方針：各点の余極限余錐を全関手圏の普遍余錐へまとめる。
規約：始域 A は大きくてもよい。
使われ方：関手圏の presentable 性の余完備性。 -/
lemma functor_hasSmallColimits (A : SSet.{u + 1}) {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits ((ihom A).obj C) := by
  intro K D
  obtain ⟨c, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_pointwiseColimitCocone (hC K) D
  exact ⟨c, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isColimitCone_of_pointwise c hc⟩

/-- 概要：全関手圏の元の小余極限は各点で計算される。
方針：元の標的の同じ小形状の余極限存在を使う。
規約：元の指定全余錐を保持する。
使われ方：関手圏からの評価と後合成の保存性。 -/
lemma functor_isColimitCone_iff_pointwise (A : SSet.{u + 1})
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    {K : SSet.{u}} {D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ (ihom A).obj C}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone c :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isPointwiseColimitCone_of_hasColimits (hC K) c, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isColimitCone_of_pointwise c⟩

/-- 概要：全関手圏の各評価は全小余極限を保存する。
方針：元の余極限余錐の各点計算を指定頂点で評価する。
規約：評価対象は元の始域 A の頂点。
使われ方：関手圏の生成と評価による保存性判定。 -/
lemma evaluateFunctorAt_preservesSmallColimits {A C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (a : A.obj (Opposite.op (SimplexCategory.mk 0))) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a : (ihom A).obj C ⟶ C) := by
  intro K D c hc
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isPointwiseColimitCone_of_hasColimits (hC K) c hc) a

/-- 概要：小余極限保存関手による後合成も関手圏上の全小余極限を保つ。
方針：元の指定小形状の点ごと保存をまとめる。
規約：随伴関手定理は使わない。
使われ方：前層の反映を関手圏へ移す。 -/
lemma functorPostcomp_preservesSmallColimits (A : SSet.{u + 1})
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (F : C ⟶ D) (hF : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits F) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits ((ihom A).map F) := by
  intro K p c hc
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.postcomposition_map_isColimit (hC K) F (hF K) c hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorSmallColimits
