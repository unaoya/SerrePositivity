module
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulIntervalMapping

/-! 一つの端点対での実 pinched Hom の同値性を、同じ区間 Hom の後合成へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial

lemma dgGluingIntervalPost_equivalence_of_pinched {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) (x y : X _⦋0⦌)
    (hf : IsSimplicialHomotopyEquivalence (pinchedHomMap f x y)) :
    IsQCatEquivalence (intervalMappingPost f x y) := by
  have h := hf.isQCatEquivalence.comp
    (pinchedHomToIntervalMappingSpace_isQCatEquivalence (f.app _ x) (f.app _ y))
  have hc := pinchedHomToIntervalMappingSpace_postOfEq f x y rfl rfl
  simp only [eqToHom_refl, Category.comp_id, intervalMappingPostOfEq_refl] at hc
  rw [hc] at h
  exact (pinchedHomToIntervalMappingSpace_isQCatEquivalence x y).cancel_left h

end SerrePositivity.InfinityCategories
