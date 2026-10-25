module

public import SerrePositivity.InfinityCategories.F2.Ind.FiniteBousfieldKanContinuity
public import SerrePositivity.InfinityCategories.F2.Presentable.WithInitialFilteredLimits

/-!
概要：有限 poset 上の共同 WithInitial 錐の filtered 余極限は元の極限性を保つ。
方針：元の比較自然変換の両関手の保存性と点ごとの弱同値保存を組み合わせる。
規約：濃度変更境界を用いず、指定された strict 余極限の全脚を保持する。
使われ方：I-2 d′ の有限形状に対する coherent 交換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
open Presentable HomotopyLimits

/-- 有限 poset 上の各段階の極限錐は、同じ strict filtered 余極限でも極限。 -/
lemma finiteWithInitialFilteredColimit_isLimit
    (I : Type u) [PartialOrder I] [Finite I]
    (J : Type u) [SmallCategory J] [IsFiltered J]
    (F : J ⥤ WithInitial I ⥤ KanObject.{u})
    (hc : ∀ j, IsLimitCone (strictCoherentCone (withInitialKanCone (F.obj j)))) :
    IsLimitCone (strictCoherentCone (withInitialKanCone (cardinalFilteredKanDiagram F))) := by
  have := bousfieldKanHolimFunctor_finite_poset_preservesFilteredColimits I J
  have ht : PreservesColimitsOfShape J
      ((Functor.whiskeringLeft I (WithInitial I) SSet.{u}).obj WithInitial.incl ⋙
        bousfieldKanHolimFunctor I) := inferInstance
  apply kanCone_isLimit_of_bousfieldKanComparison
  change IsWeakHomotopyEquivalence
    ((withInitialConeComparison I).app (colimit (kanConeFamilyUnderlying F)))
  apply comparison_colimit_isWeakHomotopyEquivalence
    (withInitialConeComparison I) (kanConeFamilyUnderlying F) (by infer_instance) ht
  intro j
  change IsWeakHomotopyEquivalence
    (bousfieldKanConeComparison (kanObjectForget.mapCone (withInitialKanCone (F.obj j))))
  exact bousfieldKanComparison_of_kanCone_isLimit _ (hc j)

end SerrePositivity.InfinityCategories.F2.Ind
