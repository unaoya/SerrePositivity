module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomotopyIntervalPath
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StrictPathPullbackMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
/-! # 恒等変形の全区間 path と既存の定値 path の一致

概要：恒等変形を curry した path は、元写像に既存の定値 path を後合成したものに厳密一致する。
方針：Core の包含等式を uncurry し、積の二射影を比較する。
規約：path の代表と元入力を保持する。
使われ方：正本の定値対角 path を、実正方形による引き戻しホモトピーの始点へ照合する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed SSet
lemma dgGluingHomotopyIntervalPath_refl {K Z : SSet.{u}} (f : K ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyIntervalPath (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl f) =
      f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConstantIntervalPath Z := by
  apply uncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyIntervalPath, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConstantIntervalPath,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.equivalencePathRefl_ι, uncurry_curry, uncurry_natural_left, uncurry_curry]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
