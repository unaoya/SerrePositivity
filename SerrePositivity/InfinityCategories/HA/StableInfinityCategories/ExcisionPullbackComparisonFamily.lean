module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionRawSuspensionSquare
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorPullbackComparisonEvaluation

/-!
概要：全パラメーターに整合する実錐比較を、矢印圏の四角形へ移す。
方針：元の全単体・同じ比較辺・指定頂点への錐の移送を保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第二条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

def excisionPullbackComparisonFamily {X : SSet.{u}}
    {F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured) ≫ F))
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial c))))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorPullbackComparisonFamily
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial c)) d hd

lemma excisionPullbackComparisonFamily_source {X : SSet.{u}}
    {F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured) ≫ F))
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial c))))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d) :
    excisionPullbackComparisonFamily c d hd ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) =
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareEmbedding ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial c := by
  rw [excisionPullbackComparisonFamily, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorPullbackComparisonFamily_source,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare_source_vertex]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply _

lemma excisionPullbackComparisonFamily_source_isPullback {X : SSet.{u}} [Quasicategory X]
    {F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured) ≫ F))
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial c))))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (excisionPullbackComparisonFamily c d hd ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)) := by
  rw [excisionPullbackComparisonFamily_source]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial_input_isPullback c hc

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
