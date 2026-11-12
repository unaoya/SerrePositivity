module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomTestFamilyFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldTestFamilyComparison

/-!
概要：標準 Hom の族の共同比較から、実際の復元自己関手の全空間側の同型を回収する。
方針：Hom の族への後合成の充満忠実性で、既存の全パラメーターの同型を戻す。
規約：対象ごとの逆射を選び直さず、一つの関手同型を構成する。
使われ方：weighted nerve と元の left fibration の自然な復元比較。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

local instance {B : SSet.{u}} :
    ∀ X Y : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B)ᵒᵖ, KanComplex (SimplicialCategory.sHom X Y) :=
  fun X Y ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom Y.unop X.unop))

/-- 元の復元自己関手の反変表示は、全空間上の恒等関手と一つの関手同型を持つ。 -/
def leftStrictTransportReconstructionOppositeIso (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (𝟙 (SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject (nerve C))ᵒᵖ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialEnrichedOpposite (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.strictTransportWeightedEnriched C))) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftFibrationHomTestFamily_isFullyFaithful (nerve C)).preimageFunctorIso
  simpa only [Category.id_comp] using _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.leftStrictTransportReconstructionHomFamilyIso C

/-- 同じ復元同型を全空間の恒等射へ結ぶ、反変表示上の実際の単体的ホモトピー。 -/
def leftStrictTransportReconstructionOppositeHomotopy (C : Type u) [Category.{u} C] :
    SSet.Homotopy (𝟙 (SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject (nerve C))ᵒᵖ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialEnrichedOpposite (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.strictTransportWeightedEnriched C))) :=
  (leftStrictTransportReconstructionOppositeIso C).simplicialHomotopy

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
