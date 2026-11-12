module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldTestComparison
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialOverTestComparison

/-!
概要：strict transport の自然な復元 span を二変数の共同テスト同型へ実現する。
方針：両脚の全 Hom の自然性と前合成同値性を同じ共同実現に適用する。
規約：始域も標的も固定せず、各対象で逆を独立に選ばない。
使われ方：復元 span の逆を全空間側の coherent な比較へ接続するための入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold

/-- universal scaffold の前合成同値を、全始域・全標的の共同同型へ実現する。 -/
def universalScaffoldJointTestIso (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialOverJointTest (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationOverEnriched (nerve C)))
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialOverJointTest (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.strictTransportReplacementOverEnriched C)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.universalScaffoldOverComparison C).jointTestIso
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.universalScaffoldOverComparison_isPrecompositionEquivalence C)

/-- taut scaffold も同じ二変数の共同族の同型を与える。 -/
def tautScaffoldJointTestIso (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialOverJointTest (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.strictTransportWeightedOverEnriched C))
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialOverJointTest (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.strictTransportReplacementOverEnriched C)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.tautScaffoldOverComparison C).jointTestIso
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.tautScaffoldOverComparison_isPrecompositionEquivalence C)

/-- 元と復元後からの相対 Hom を、始域・標的・全高次で同時に比較する。 -/
def leftStrictTransportReconstructionJointTestIso (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialOverJointTest (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationOverEnriched (nerve C)))
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialOverJointTest (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.strictTransportWeightedOverEnriched C)) :=
  universalScaffoldJointTestIso C ≪≫ (tautScaffoldJointTestIso C).symm

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold
