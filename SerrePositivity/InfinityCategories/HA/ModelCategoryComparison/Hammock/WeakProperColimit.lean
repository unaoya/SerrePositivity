module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakLengthStages
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakSequentialColimit

/-!
# proper 図式の元の余極限の弱同値不変性

概要：proper 図式間の成分ごとの弱同値は元の全語の余極限でも弱同値となる。
方針：全有限長さ段階での帰納と Nat の filtered 余極限を、元の比較同型で結ぶ。
規約：結論は元の colim.map。全語の添字圏の filtered 性を仮定しない。
使われ方：Dwyer–Kan §4.5、hammock の比較図式の反転。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.InfinityCategories

lemma weakProperColimitMap {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}} (η : F ⟶ G)
    (hF : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram F) (hG : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram G)
    (hη : ∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (η.app a)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (colim.map η) := by
  have hw := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.weakSequentialColimitMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthDiagramMap η)
    (fun n => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.weakLengthStageMap η hF hG hη n)
  have hF' := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthColimitIso F))
  have hG' := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthColimitIso G))
  apply hF'.isWeakHomotopyEquivalence.cancel_left
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthColimitIso_naturality]
  exact hw.comp hG'.isWeakHomotopyEquivalence

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
