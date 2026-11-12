module

public import SerrePositivity.EInfinity.Hammock.WeakLengthStages
public import SerrePositivity.EInfinity.Hammock.WeakSequentialColimit

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
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories

lemma weakProperColimitMap {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}} (η : F ⟶ G)
    (hF : ProperDiagram F) (hG : ProperDiagram G)
    (hη : ∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (η.app a)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (colim.map η) := by
  have hw := weakSequentialColimitMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthDiagramMap η)
    (fun n => weakLengthStageMap η hF hG hη n)
  have hF' := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthColimitIso F))
  have hG' := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthColimitIso G))
  apply hF'.isWeakHomotopyEquivalence.cancel_left
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthColimitIso_naturality]
  exact hw.comp hG'.isWeakHomotopyEquivalence

end SerrePositivity.EInfinity.Hammock
