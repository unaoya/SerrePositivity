module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.ArrowHomotopies.IntervalPathHomotopy
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-! 区間族から読んだ同じホモトピーは、区間を第一因子へ戻すと元の全区間族を回収する。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed
open scoped _root_.Simplicial

lemma dgGluingIntervalPathHomotopy_prism {K X : SSet.{u}}
    (p : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    (β_ (Δ[1] : SSet.{u}) K).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalPathHomotopy p).h = uncurry p := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  rfl

lemma dgGluingIntervalPathHomotopy_post_prism {K X Y : SSet.{u}}
    (p : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X) (q : X ⟶ Y) :
    (β_ (Δ[1] : SSet.{u}) K).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalPathHomotopy p) q).h = uncurry p ≫ q := by
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun z => z ≫ q) (dgGluingIntervalPathHomotopy_prism p))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
