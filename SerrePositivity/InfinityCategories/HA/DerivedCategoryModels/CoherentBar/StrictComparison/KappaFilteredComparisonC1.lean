module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyColimit
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.StrictAugmentationQuasiIso
public import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered

/-!
概要：正則 κ の filtered poset に対する coherent C1 と strict 特殊化を公開する。
方針：より強い通常の filtered 版を、IsCardinalFiltered からの帰結で適用する。
規約：native 余錐の普遍性を仮定せず、coherent 入力の全 HA 成分を保つ。
使われ方：D-bar B 到着後の strict/native 比較 C2。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u}) [Fact κ.IsRegular]
  {J : Type u} [PartialOrder J] [IsCardinalFiltered J κ]

def dgKappaCoherentBarHomologyColimitIso
    (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)) (x : D) (q : ℤ) :
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleUnconditional R D G).obj (Opposite.op x)).homology q ≅
      colimit (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x q) := by
  letI := isFiltered_of_isCardinalFiltered J κ
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyColimitIso R D G x q

include κ in
lemma dgKappaStrictBarColimitAugmentation_quasiIso (F : J ⥤ _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) :
    moduleQuasiIso R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictColimitAugmentation R D F) := by
  letI := isFiltered_of_isCardinalFiltered J κ
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictColimitAugmentation_quasiIso R D F

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
