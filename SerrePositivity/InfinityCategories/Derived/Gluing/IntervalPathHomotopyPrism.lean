module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalPathHomotopy
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering

/-! 区間族から読んだ同じホモトピーは、区間を第一因子へ戻すと元の全区間族を回収する。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed
open scoped Simplicial

lemma dgGluingIntervalPathHomotopy_prism {K X : SSet.{u}}
    (p : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    (β_ (Δ[1] : SSet.{u}) K).hom ≫ (dgGluingIntervalPathHomotopy p).h = uncurry p := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  rfl

lemma dgGluingIntervalPathHomotopy_post_prism {K X Y : SSet.{u}}
    (p : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X) (q : X ⟶ Y) :
    (β_ (Δ[1] : SSet.{u}) K).hom ≫
        (functorHomotopyPostcomp (dgGluingIntervalPathHomotopy p) q).h = uncurry p ≫ q := by
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun z => z ≫ q) (dgGluingIntervalPathHomotopy_prism p))

end SerrePositivity.InfinityCategories
