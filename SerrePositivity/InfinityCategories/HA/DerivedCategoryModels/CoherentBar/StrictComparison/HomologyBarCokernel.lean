module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarCokernelData
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
概要：bar の零次から余極限への増大は、一次微分の cokernel である。
方針：境界を消す写像を元の図式の余錐へ戻し、その余極限性を使う。
規約：余極限の普遍性以外の追加仮定はない。
使われ方：零次ホモロジーと colim H(G) の同定。
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
  (F : J ⥤ ModuleCat.{u} R) (c : Cocone F) (hc : IsColimit c)

def dgHomologyBarAugmentationIsCokernel :
    IsColimit (CokernelCofork.ofπ
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarAugmentationComponent R F c (op ⦋0⦌))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarAugmentation_d_one R F c)) := by
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun g hg => hc.desc (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarCoconeOfBoundaryZero R F g hg)) ?_ ?_
  · intro P g hg
    apply Sigma.hom_ext
    intro s
    obtain ⟨j, rfl⟩ := nerveEquiv.symm.surjective s
    erw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarAugmentationComponent_ι]
    exact hc.fac (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarCoconeOfBoundaryZero R F g hg) j
  · intro P g hg m hm
    apply hc.hom_ext
    intro j
    have h := congrArg (fun w => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarVertex R F j ≫ w) hm
    erw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarAugmentationComponent_ι] at h
    exact h.trans (hc.fac (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarCoconeOfBoundaryZero R F g hg) j).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
