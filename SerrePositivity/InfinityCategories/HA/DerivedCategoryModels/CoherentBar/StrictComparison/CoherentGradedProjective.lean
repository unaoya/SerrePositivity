module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentCutModule
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentDimensionLayers
public import SerrePositivity.DifferentialGraded.Derived.Basic


/-!
概要：h-projective 頂点の各実次元層と、微分変更前の切断直和は h-projective。
方針：同じ始点加群の整数 shift と、任意の小さい直和の閉性を使う。
規約：評価ごとの K-projective 性には置き換えない。
使われ方：単体次元フィルトレーションの各商の射影性。
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
  (hG : ∀ s : I _⦋0⦌, _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective R D
    (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex G s)))

include hG in
lemma dgCoherentBarFamily_projective (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) :
    moduleHomotopicallyProjective R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G s) := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective_shift R D
  exact hG _

include hG in
lemma dgCoherentBarCutGraded_projective (n : ℕ) :
    moduleHomotopicallyProjective R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGraded R D G n) :=
  _root_.SerrePositivity.DifferentialGraded.moduleCoproduct_homotopicallyProjective R D _
    (fun s => dgCoherentBarFamily_projective R D G hG s.val.val)

include hG in
lemma dgCoherentBarLayerGraded_projective (n : ℕ) :
    moduleHomotopicallyProjective R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G n) :=
  _root_.SerrePositivity.DifferentialGraded.moduleCoproduct_homotopicallyProjective R D _
    (fun s => dgCoherentBarFamily_projective R D G hG s.val.val)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
