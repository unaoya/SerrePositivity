module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LengthZero
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakStageSuccessor

/-!
# proper 図式の元の全有限長さ段階の弱同値

概要：proper 図式間の成分ごとの弱同値は、全有限段階の元の比較を弱同値にする。
方針：長さ零の元の同型を基底にし、元の次段階の pushout 比較で帰納する。
規約：段階や成分の Kan 性を追加仮定にしない。
使われ方：長さ濾過の filtered 余極限による proper 余極限の比較。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory
open _root_.SerrePositivity.InfinityCategories

variable {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}} (η : F ⟶ G)

lemma weakLengthStageMap_zero (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (η.app _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageMap η 0) := by
  have hF := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthZeroIso F).symm)
  have hG := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthZeroIso G).symm)
  apply hF.isWeakHomotopyEquivalence.cancel_left
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F 0 _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty (le_refl 0) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageMap η 0)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion_map]
  exact hη.comp hG.isWeakHomotopyEquivalence

lemma weakLengthStageMap (hF : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram F) (hG : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram G)
    (hη : ∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (η.app a)) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageMap η n) := by
  induction n with
  | zero => exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.weakLengthStageMap_zero η (hη _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty)
  | succ n ih => exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.weakLengthStageMap_succ η hF hG hη n ih

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
