module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarNondegCokernel

/-!
概要：非退化 bar の標準増大は各零単体で元の余錐の脚である。
方針：零次数で正規化射影が恒等であることと直和の普遍性を使う。
規約：与えた余錐の全脚を保つ。
使われ方：strict bar のホモロジー余核射との一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits Opposite SSet AlgebraicTopology HomologicalComplex
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] {J : Type u} [PartialOrder J]
  (F : J ⥤ ModuleCat.{u} R) (c : Cocone F)

@[reassoc]
lemma dgHomologyBarNondegAugmentation_ι (s : (nerve J).nonDegenerate 0) :
    Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegFamily R F 0) s ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegAugmentation R F c = c.ι.app (s.val.obj 0) := by
  unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegAugmentation
  rw [SimplicialObject.Splitting.fromNondegComplex_f,
    AlgebraicTopology.DoldKan.PInfty_f_0]
  simp only [Category.comp_id]
  change Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegFamily R F 0) s ≫
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegInclusion R F 0 ≫ _) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegInclusion_ι]
  simp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarAugmentationComponent, Sigma.ι_comp_desc]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
