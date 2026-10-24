module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyIntervalPath
public import SerrePositivity.InfinityCategories.Derived.Gluing.StrictPathPullbackMap
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
/-! # 恒等変形の全区間 path と既存の定値 path の一致

概要：恒等変形を curry した path は、元写像に既存の定値 path を後合成したものに厳密一致する。
方針：Core の包含等式を uncurry し、積の二射影を比較する。
規約：path の代表と元入力を保持する。
使われ方：正本の定値対角 path を、実正方形による引き戻しホモトピーの始点へ照合する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed SSet
lemma dgGluingHomotopyIntervalPath_refl {K Z : SSet.{u}} (f : K ⟶ Z) :
    dgGluingHomotopyIntervalPath (functorHomotopyRefl f) =
      f ≫ dgGluingConstantIntervalPath Z := by
  apply uncurry_injective
  rw [dgGluingHomotopyIntervalPath, dgGluingConstantIntervalPath,
    equivalencePathRefl_ι, uncurry_curry, uncurry_natural_left, uncurry_curry]
  rfl
end SerrePositivity.InfinityCategories
