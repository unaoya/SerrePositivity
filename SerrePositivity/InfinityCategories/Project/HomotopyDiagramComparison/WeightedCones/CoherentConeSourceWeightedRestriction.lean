module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.CoherentConeSourceFamily
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceSourceWeighted

/-!
概要：weighted な切断で表される錐の明示的な Hom の族の制限を計算する。
方針：錐の切断の表示を coslice の前合成へ代入する。
規約：図式と錐と表示する切断を独立の変数として保持する。
使われ方：coend の大きな具体的な錐を展開せず、普遍点での比較を行う。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

/-- weighted な表示を持つ錐の族の制限は、その表示に対する weighted な前合成になる。 -/
lemma coherentConeSourceFamily_restriction_weighted (F : I ⥤ C)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) (z : C)
    (hz : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z)
    (s : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶
      (SSet.uliftFunctor.{v, u}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F z ⋙ SSet.opFunctor)))
    (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeCosliceSection c ≫ eqToHom (congrArg
      (fun w ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm w)) hz) = s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCosliceComparison F z)
    (x : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentConeSourceFamily c z hz x ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneSectionRestriction c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)) =
      (s ▷ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op) ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedCoslicePrecompositionFamily F x z := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentConeSourceFamily_restriction_uncurry, hs, comp_whiskerRight_assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coherentCosliceSourcePrecomposition_weighted]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
