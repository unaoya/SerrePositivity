module
public import SerrePositivity.InfinityCategories.Stable.KanModels.KanTerminalComparison
public import SerrePositivity.KST.Fibration.KanClosedEvaluation
public import SerrePositivity.InfinityCategories.F1.KanModels.KanAnodyneLocalization
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpaceTerminal
public import SerrePositivity.InfinityCategories.F1.Coherent.KanInvertible
public import SerrePositivity.KST.Comparison.ExInfinityLocalization

/-! # 元の一点射の可逆性から、同じ Ex∞ 値の空間の ∞ 圏での終対象性へ接続する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Comparison
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の一点射が可逆な実現の、同じ Ex∞ Kan 値は空間の ∞ 圏の終対象である。 -/
theorem exInfinityVertex_isTerminal_of_localized_toPoint (V : SSet.{u})
    (hV : IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from V))) :
    IsTerminalVertex (coherentNerveVertex (exInfinityClosedKanEnrichedFunctor.obj ⟨V⟩)) := by
  apply kanVertex_isTerminal_of_localized_toPoint
  let Q := AnodyneHomotopy.anodyneQ.{u}
  have hu : IsIso (Q.map (exInfinityUnit.app V)) := inferInstance
  have he : exInfinityUnit.app V ≫ terminal.from (exInfinity.obj V) =
      terminal.from V := terminal.hom_ext _ _
  have hc : IsIso (Q.map (exInfinityUnit.app V) ≫
      Q.map (terminal.from (exInfinity.obj V))) := by
    rw [← Functor.map_comp, he]
    exact hV
  exact (isIso_comp_left_iff _ _).mp hc

end SerrePositivity.KST.Fibration
