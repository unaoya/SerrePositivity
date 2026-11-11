module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarSplitting

/-!
概要：非退化 H(G) bar の標準増大も一次微分の余核である。
方針：splitting の相互射と零次数で恒等な正規化射影で通常の bar の余核を移す。
規約：filtered 性は不要で、与えた余錐の全ての脚を使う。
使われ方：strict 標準増大のホモロジー射の擬同型判定。
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

def dgHomologyBarNondegAugmentation : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegComplex R F).X 0 ⟶ c.pt :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSplitting R F).fromNondegComplex.f 0 ≫
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarAugmentationComponent R F c (op ⦋0⦌)

lemma dgHomologyBarNondegAugmentation_d_one :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegComplex R F).d 1 0 ≫ dgHomologyBarNondegAugmentation R F c = 0 := by
  unfold dgHomologyBarNondegAugmentation
  rw [← Category.assoc, ← (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSplitting R F).fromNondegComplex.comm 1 0,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarAugmentation_d_one, comp_zero]

lemma dgHomologyBarToNondeg_augmentation :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSplitting R F).toNondegComplex.f 0 ≫
      dgHomologyBarNondegAugmentation R F c =
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarAugmentationComponent R F c (op ⦋0⦌) := by
  unfold dgHomologyBarNondegAugmentation
  rw [← Category.assoc, ← HomologicalComplex.comp_f,
    SimplicialObject.Splitting.toNondegComplex_fromNondegComplex,
    AlgebraicTopology.DoldKan.PInfty_f_0, Category.id_comp]

def dgHomologyBarNondegAugmentationIsCokernel (hc : IsColimit c) :
    IsColimit (CokernelCofork.ofπ (dgHomologyBarNondegAugmentation R F c)
      (dgHomologyBarNondegAugmentation_d_one R F c)) := by
  let h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarAugmentationIsCokernel R F c hc
  letI : Epi (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarAugmentationComponent R F c (op ⦋0⦌)) :=
    epi_of_isColimit_cofork h
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun g hg => h.desc (CokernelCofork.ofπ
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSplitting R F).toNondegComplex.f 0 ≫ g) (by
        rw [← Category.assoc, ← (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSplitting R F).toNondegComplex.comm 1 0,
          Category.assoc, hg, comp_zero]))) ?_ ?_
  · intro P g hg
    have hf : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarAugmentationComponent R F c (op ⦋0⦌) ≫
        h.desc (CokernelCofork.ofπ
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSplitting R F).toNondegComplex.f 0 ≫ g) (by
        rw [← Category.assoc, ← (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSplitting R F).toNondegComplex.comm 1 0,
          Category.assoc, hg, comp_zero])) =
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSplitting R F).toNondegComplex.f 0 ≫ g :=
      Cofork.IsColimit.π_desc h
    unfold dgHomologyBarNondegAugmentation
    rw [Category.assoc, hf, ← Category.assoc, ← HomologicalComplex.comp_f,
      SimplicialObject.Splitting.fromNondegComplex_toNondegComplex,
      HomologicalComplex.id_f, Category.id_comp]
  · intro P g hg m hm
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarAugmentationComponent R F c (op ⦋0⦌))).mp
    have hf : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarAugmentationComponent R F c (op ⦋0⦌) ≫
        h.desc (CokernelCofork.ofπ
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSplitting R F).toNondegComplex.f 0 ≫ g) (by
        rw [← Category.assoc, ← (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSplitting R F).toNondegComplex.comm 1 0,
          Category.assoc, hg, comp_zero])) =
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSplitting R F).toNondegComplex.f 0 ≫ g :=
      Cofork.IsColimit.π_desc h
    rw [hf, ← hm, ← Category.assoc, dgHomologyBarToNondeg_augmentation]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
