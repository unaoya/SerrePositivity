module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.DegreeSubcomplex

/-!
概要：元の coherent 正規化 bar の単体次元による実部分複体。
方針：実微分で保たれる部分加群を複体へ制限し、元の複体への包含を作る。
規約：高次 HA 成分を全て保ち、整数次数は非有界のままで扱う。
使われ方：段階の商、有限 support による cycle の帰納。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

def dgCoherentBarNormalizedStageComplex (x : D) (n : ℕ) : Complex R :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarDegreeSubcomplex R
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleUnconditional R D G).obj (Opposite.op x))
    (fun q => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedDegreeFiltration R D G x q n)
    (fun q z hz => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedDegreeFiltration_d R D G x q n z hz)

def dgCoherentBarNormalizedStageInclusion (x : D) (n : ℕ) :
    dgCoherentBarNormalizedStageComplex R D G x n ⟶
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleUnconditional R D G).obj (Opposite.op x) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarDegreeSubcomplexInclusion R _ _ _

def dgCoherentBarNormalizedStageMap (x : D) {n m : ℕ} (h : n ≤ m) :
    dgCoherentBarNormalizedStageComplex R D G x n ⟶
      dgCoherentBarNormalizedStageComplex R D G x m :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarDegreeSubcomplexMap R _ _ _ _ _
    (fun q => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedDegreeFiltration_mono R D G x q h)

@[reassoc]
lemma dgCoherentBarNormalizedStageMap_inclusion (x : D) {n m : ℕ} (h : n ≤ m) :
    dgCoherentBarNormalizedStageMap R D G x h ≫
      dgCoherentBarNormalizedStageInclusion R D G x m =
        dgCoherentBarNormalizedStageInclusion R D G x n :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarDegreeSubcomplexMap_inclusion R _ _ _ _ _ _

lemma dgCoherentBarNormalizedStages_exhaustive (x : D) (q : ℤ)
    (z : ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleUnconditional R D G).obj (Opposite.op x)).X q) :
    ∃ (n : ℕ) (a : (dgCoherentBarNormalizedStageComplex R D G x n).X q),
      (dgCoherentBarNormalizedStageInclusion R D G x n).f q a = z := by
  obtain ⟨n, hn⟩ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedDegreeFiltration_exhaustive R D G x q z
  exact ⟨n, ⟨z, hn⟩, rfl⟩

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
