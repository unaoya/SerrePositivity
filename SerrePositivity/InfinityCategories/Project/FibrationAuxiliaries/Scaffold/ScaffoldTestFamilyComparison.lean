module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldJointTestComparison
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialOverTestFamily

/-!
概要：復元 span の逆を全始域の Hom 関手の族の一つの同型として表す。
方針：共同テスト同型を実際の関手圏に curry し、二つの脚を同じ族で合成する。
規約：同型は全始域・全標的・全高次で自然。全空間側の比較とはまだ区別する。
使われ方：表現可能な族から元の全空間側へ比較を回収するための入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold

/-- universal scaffold の前合成は、全始域の Hom 関手の族の一つの同型。 -/
def universalScaffoldTestFamilyIso (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialOverTestFamily (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationOverEnriched (nerve C)))
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialOverTestFamily (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.strictTransportReplacementOverEnriched C)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.universalScaffoldOverComparison C).testFamilyIso
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.universalScaffoldOverComparison_isPrecompositionEquivalence C)

/-- taut scaffold も同じ始域の Hom 関手の族の同型を与える。 -/
def tautScaffoldTestFamilyIso (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialOverTestFamily (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.strictTransportWeightedOverEnriched C))
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialOverTestFamily (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.strictTransportReplacementOverEnriched C)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.tautScaffoldOverComparison C).testFamilyIso
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.tautScaffoldOverComparison_isPrecompositionEquivalence C)

/-- 元と復元後の全始域の Hom 関手の族は、一つの関手同型を持つ。 -/
def leftStrictTransportReconstructionTestFamilyIso (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialOverTestFamily (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationOverEnriched (nerve C)))
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialOverTestFamily (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.strictTransportWeightedOverEnriched C)) :=
  universalScaffoldTestFamilyIso C ≪≫ (tautScaffoldTestFamilyIso C).symm

/-- strict transport を weighted nerve へ戻す自己豊穣関手。 -/
def strictTransportWeightedEnriched (C : Type u) [Category.{u} C] :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject (nerve C))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject (nerve C)) :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStrictTransportEnriched (C := C)).comp SSet _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictTransportKanDiagramEnriched).comp
    SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveKanEnriched C)

/-- 同じ自己作用を全底上対象の圏へ含めると、既存の復元 span の終域になる。 -/
lemma strictTransportWeightedEnriched_over (C : Type u) [Category.{u} C] :
    (strictTransportWeightedEnriched C).comp SSet (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationOverEnriched (nerve C)) =
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.strictTransportWeightedOverEnriched C := rfl

/-- 標準 Hom の族は、実際の復元自己関手による前合成と一つの関手同型を持つ。 -/
def leftStrictTransportReconstructionHomFamilyIso (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationHomTestFamily (nerve C))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialEnrichedOpposite (strictTransportWeightedEnriched C)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationHomTestFamily (nerve C)) := by
  have e := leftStrictTransportReconstructionTestFamilyIso C
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationHomTestFamily (nerve C))
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialOverTestFamily ((strictTransportWeightedEnriched C).comp SSet
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationOverEnriched (nerve C)))) at e
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialOverTestFamily_leftFibration] at e
  exact e

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold
