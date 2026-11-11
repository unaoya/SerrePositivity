module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionRawSuspensionEvaluation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullCoreConeChoice

/-!
概要：同じ実比較辺を元の θ と照合し、対角の可逆性から入力面の普遍性へ戻す。
方針：全錐の写像と射影辺を保つ等号輸送、錐の圏の終性、右 fibration の反映を使う。
規約：一般安定性は仮定しない。使われ方：HA 1.4.2.15 の二条件からの切除判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma excisionRawSuspensionSquare_replaced_sourceConeAt_core_val {X : SSet.{u}}
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured) ≫ F))
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionCorePunctured) ≫
      (nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreInclusion ≫ nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridMiddleInclusion ≫ F)))
    (hr : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c (nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedToFull.toFunctor)).val =
      d.val) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2),
      stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial c)))).val =
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedOuterCone d).val := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare_sourceConeAt_val]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial_coreOuterCone_val F c d hr

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
