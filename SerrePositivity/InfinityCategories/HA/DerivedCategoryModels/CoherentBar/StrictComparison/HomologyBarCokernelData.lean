module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarDegreeOne

/-!
概要：一次境界を消す bar の零次写像から、元の図式の余錐を回収する。
方針：元の各辺の境界関係を使い、頂点係数への制限の自然性を示す。
規約：同じホモロジー図式 F と同じ bar を使う。
使われ方：零次ホモロジーと余極限の普遍性の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits Opposite SSet AlgebraicTopology
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] {J : Type u} [PartialOrder J]
  (F : J ⥤ ModuleCat.{u} R)

lemma dgHomologyBarAugmentation_d_one (c : Cocone F) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarComplex R F).d 1 0 ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarAugmentationComponent R F c (op ⦋0⦌) = 0 := by
  have h (i : Fin 2) : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSimplicial R F).δ i ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarAugmentationComponent R F c (op ⦋0⦌) =
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarAugmentationComponent R F c (op ⦋1⦌) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarAugmentation, Functor.const_obj_map, Category.comp_id] using!
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarAugmentation R F c).naturality (SimplexCategory.δ i).op
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarDifferential_one, Preadditive.sub_comp, h 0, h 1, sub_self]

def dgHomologyBarCoconeOfBoundaryZero {P : ModuleCat R}
    (g : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarComplex R F).X 0 ⟶ P)
    (hg : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarComplex R F).d 1 0 ≫ g = 0) : Cocone F where
  pt := P
  ι :=
    { app j := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarVertex R F j ≫ g
      naturality j k f := by
        have h := congrArg (fun w =>
          Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarFamily R F (op ⦋1⦌)) (CategoryTheory.nerve.edgeMk f).edge ≫ w) hg
        erw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarEdge_d, Preadditive.sub_comp,
          comp_zero, sub_eq_zero] at h
        simpa only [Category.assoc, Functor.const_obj_map, Category.comp_id] using! h }

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
