module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentCutGradedSplit
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentCutZero
public import SerrePositivity.DifferentialGraded.Derived.Basic

/-!
概要：h-projective 頂点の coherent bar の各有限次元段階は h-projective。
方針：零段階から始め、次数付き分裂拡大と各次元層の射影性で帰納する。
規約：高次 HA 成分を持つ元の coherent 図式を用いる。
使われ方：全 bar の射影性を与える可算段階列。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarCutModule_projective
    (hG : ∀ s : I _⦋0⦌, _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective R D
      (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex G s))) (n : ℕ) :
    _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective R D
      (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModule R D G n)) := by
  induction n with
  | zero => exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutZero_projective R D G hG
  | succ n ih =>
    exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGradedSplit R D G n).homotopicallyProjective R D ih
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded_projective R D G hG (n + 1))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
