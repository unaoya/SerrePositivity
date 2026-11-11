module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyBarCokernel

/-!
概要：filtered poset 上の coherent 正規化 bar のホモロジーは頂点ホモロジーの余極限。
方針：実 bar のホモロジーを非退化 H(G) bar の一次微分の余核に同定する。
規約：入力は正規化 bar と同じ全 HA 成分つき図式である。
使われ方：strict augmentation の擬同型性と native filtered 余極限比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] [IsFiltered J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

def dgCoherentBarHomologyNondegZeroIso (x : D) (p : ℤ) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegComplex R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x (p + 1))).homology 0 ≅
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleUnconditional R D G).obj (Opposite.op x)).homology (p + 1) := by
  let K := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegComplex R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x (p + 1))
  have hg : (K.sc' 1 0 0).g = 0 := K.shape 0 0 (by simp)
  exact K.homologyIsoSc' 1 0 0 (by simp) (by simp) ≪≫
    (ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork (K.sc' 1 0 0) hg
      (CokernelCofork.ofπ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyBarAugmentation R D G x (p + 1))
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyBarAugmentation_d_one R D G x p))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyBarIsCokernel R D G x p)).homologyIso

def dgCoherentBarHomologyColimitSuccIso (x : D) (p : ℤ) :
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleUnconditional R D G).obj (Opposite.op x)).homology (p + 1) ≅
      colimit (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x (p + 1)) :=
  (dgCoherentBarHomologyNondegZeroIso R D G x p).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegZeroHomologyIso R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x (p + 1))

def dgCoherentBarHomologyColimitIso (x : D) (q : ℤ) :
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleUnconditional R D G).obj (Opposite.op x)).homology q ≅
      colimit (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x q) := by
  simpa only [sub_add_cancel] using! dgCoherentBarHomologyColimitSuccIso R D G x (q - 1)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
