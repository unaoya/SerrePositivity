module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentDimensionLayers

/-!
概要：指定次元より低い支持は、その次元層への射影で消える。
方針：次数フィルトレーションの像部分加群について帰納し、各包含先で判定する。
規約：元の直和と正規化射影を使う。
使われ方：段階商で実 theta の低次項を消す。
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

lemma dgCoherentBarDegreeFiltration_annihilate {M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D}
    (f : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D G ⟶ M) (x : D) (q : ℤ) (n : ℕ)
    (hf : ∀ s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I, s.1 ≤ n →
      Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G) s ≫ f = 0)
    (z : (moduleDegreeEvaluation R D x q).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D G))
    (hz : z ∈ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarDegreeFiltration R D G x q n) :
    (_root_.SerrePositivity.DifferentialGraded.moduleDegreeEvaluation R D x q).map f z = 0 := by
  refine Submodule.iSup_induction
    (motive := fun z => (_root_.SerrePositivity.DifferentialGraded.moduleDegreeEvaluation R D x q).map f z = 0)
    (fun s : {s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I // s.1 ≤ n} =>
      LinearMap.range ((_root_.SerrePositivity.DifferentialGraded.moduleDegreeEvaluation R D x q).map
        (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G) s.val)).hom) hz ?_ ?_ ?_
  · intro s a ha
    obtain ⟨b, rfl⟩ := ha
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, hf s.val s.property, Functor.map_zero]
    rfl
  · exact map_zero _
  · intro a b ha hb
    rw [map_add, ha, hb, add_zero]

lemma dgCoherentBarLayerProjection_annihilate (x : D) (q : ℤ) {m n : ℕ} (hmn : m < n)
    (z : (moduleDegreeEvaluation R D x q).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D G))
    (hz : z ∈ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedDegreeFiltration R D G x q m) :
    (moduleDegreeEvaluation R D x q).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection R D G n) z = 0 := by
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hz
  erw [← ModuleCat.comp_apply, ← Functor.map_comp]
  exact dgCoherentBarDegreeFiltration_annihilate R D G _ x q m
    (fun s hs => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection_raw_ι_of_lt R D G n s (hs.trans_lt hmn)) a ha

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
