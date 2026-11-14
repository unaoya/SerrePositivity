module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.BousfieldKanCoherentCocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.CoherentConeFamilyHomotopy

/-!
概要：構成した Bousfield–Kan 余錐の普遍性を、実際の切断の持ち上げの照合へ還元する。
方針：任意の coherent な錐の族の比較を反対圏の構成済みの錐へ適用する。
規約：比較の同値性だけで余極限性を結論しない。頂点評価と制限の両方を照合する。
使われ方：HTT 4.2.4.1 の γ3c の一般の coend 比較の残る幾何的入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {I : Type u} [SmallCategory I]

local instance bkCriterionOppositeHomKan (X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}ᵒᵖ) :
    KanComplex (SimplicialCategory.sHom X Y) :=
  inferInstanceAs (KanComplex (SimplicialCategory.sHom Y.unop X.unop))

/-- 概要：coend の比較が頂点を保つ錐全体上の族へ持ち上がれば、構成済みの錐は極限錐。
方針：既証の coend 比較の同値性と、一般の族の持ち上げによる判定を使う。
規約：持ち上げの構成はこの補題の仮定。余極限性の無条件の主張ではない。
使われ方：HTT 4.2.4.1 の実際の coend 余錐の普遍性を証明する最終照合。 -/
lemma bousfieldKanCoherentOppositeCone_isLimit_of_comparison_lifts
    (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (a : ∀ Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}, (SSet.uliftFunctor.{u + 1, u}).obj
        (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F) Y).op ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentOppositeCone F).val
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op Y)))
    (ha : ∀ Y, a Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeApexEvaluation (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentOppositeCone F)
        (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F))
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentOppositeCone_vertex F) (Opposite.op Y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentCosliceFiberComparison (Opposite.op Y)
        (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F)))
    (hr : ∀ Y, a Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneSectionRestriction (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentOppositeCone F)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op Y)) = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentConeComparison F Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentOppositeCone F) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentCone_isLimit_of_family_lifts (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentOppositeCone F)
    (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F))
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentOppositeCone_vertex F) (fun Y ↦ a Y.unop)
  · intro Y
    exact ha Y.unop
  · intro Y
    rw [hr]
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentConeComparison_homotopyEquivalence F Y.unop

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
