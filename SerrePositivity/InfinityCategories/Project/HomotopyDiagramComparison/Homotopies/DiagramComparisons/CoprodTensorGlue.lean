module

public import Mathlib.CategoryTheory.Distributive.Cartesian
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FixedExtensionCurry

/-!
概要：二つの形状上のパラメータ族を、同じ余積形状の族へ厳密に貼る。
方針：直積の余積に対する分配同型を使う。
規約：各枝の raw な射を保持する。使われ方：二端点の同時制限の相対関手空間。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {D C T E : SSet.{u}}

/-- 余積の両枝の同じパラメータ族を貼り合わせる。 -/
def coprodTensorGlue (a : D ⊗ T ⟶ E) (b : C ⊗ T ⟶ E) : (D ⨿ C) ⊗ T ⟶ E :=
  (rightDistrib T D C).inv ≫ coprod.desc a b

/-- 左枝への制限は元の族そのもの。 -/
lemma coprodTensorGlue_inl (a : D ⊗ T ⟶ E) (b : C ⊗ T ⟶ E) :
    (coprod.inl ▷ T) ≫ coprodTensorGlue a b = a := by
  rw [coprodTensorGlue, ← Category.assoc, whiskerRight_coprod_inl_rightDistrib_inv,
    coprod.inl_desc]

/-- 右枝への制限も元の族そのもの。 -/
lemma coprodTensorGlue_inr (a : D ⊗ T ⟶ E) (b : C ⊗ T ⟶ E) :
    (coprod.inr ▷ T) ≫ coprodTensorGlue a b = b := by
  rw [coprodTensorGlue, ← Category.assoc, whiskerRight_coprod_inr_rightDistrib_inv,
    coprod.inr_desc]

/-- 全パラメータの族は、二つの枝での制限で厳密に決まる。 -/
lemma coprodTensor_hom_ext {f g : (D ⨿ C) ⊗ T ⟶ E}
    (h₀ : (coprod.inl ▷ T) ≫ f = (coprod.inl ▷ T) ≫ g)
    (h₁ : (coprod.inr ▷ T) ≫ f = (coprod.inr ▷ T) ≫ g) : f = g := by
  apply (cancel_epi (rightDistrib T D C).hom).mp
  apply coprod.hom_ext
  · simpa only [← Category.assoc, coprod_inl_rightDistrib_hom] using h₀
  · simpa only [← Category.assoc, coprod_inr_rightDistrib_hom] using h₁

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
