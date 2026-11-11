module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.KanTerminalComparison
public import SerrePositivity.KST.Fibration.KanClosedEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanAnodyneLocalization
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SpaceTerminal
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanInvertible
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityLocalization

/-! # 元の一点射の可逆性から、同じ Ex∞ 値の空間の ∞ 圏での終対象性へ接続する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories

open SerrePositivity.KST.SConstruction

open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の一点射が可逆な実現の、同じ Ex∞ Kan 値は空間の ∞ 圏の終対象である。 -/
theorem exInfinityVertex_isTerminal_of_localized_toPoint (V : SSet.{u})
    (hV : IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from V))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (exInfinityClosedKanEnrichedFunctor.obj ⟨V⟩)) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanVertex_isTerminal_of_localized_toPoint
  let Q := AnodyneHomotopy.anodyneQ.{u}
  have hu : IsIso (Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app V)) := inferInstance
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app V ≫ terminal.from (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj V) =
      terminal.from V := terminal.hom_ext _ _
  have hc : IsIso (Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app V) ≫
      Q.map (terminal.from (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj V))) := by
    rw [← Functor.map_comp, he]
    exact hV
  exact (isIso_comp_left_iff _ _).mp hc

end SerrePositivity.KST.Fibration
