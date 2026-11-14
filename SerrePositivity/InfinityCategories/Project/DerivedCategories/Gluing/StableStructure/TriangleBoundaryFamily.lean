module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.TriangleBoundaryFamilyCompatibility

/-! パラメーターを保った境界の貼り合わせと、ホーン・三面の厳密な回収。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory SSet
open scoped _root_.Simplicial
variable {T X : SSet.{u}}
variable (a : (horn 2 1 : SSet.{u}) ⊗ T ⟶ X) (b : (Δ[1] : SSet.{u}) ⊗ T ⟶ X)
variable (h₀ : (stdSimplex.δ (1 : Fin 2) ▷ T) ≫ b =
  (stdSimplex.δ (1 : Fin 2) ▷ T) ≫ (horn₂₁.ι₀₁ ▷ T) ≫ a)
variable (h₂ : (stdSimplex.δ (0 : Fin 2) ▷ T) ≫ b =
  (stdSimplex.δ (0 : Fin 2) ▷ T) ≫ (horn₂₁.ι₁₂ ▷ T) ≫ a)

def dgGluingTriangleBoundaryFamily : (boundary 2 : SSet.{u}) ⊗ T ⟶ X :=
  (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundary_isPushout.map (tensorRight T)).desc a
    ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleDiagonalFaceIso.inv ▷ T) ≫ b)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleBoundaryFamily_compatible a b h₀ h₂)

lemma dgGluingTriangleBoundaryFamily_horn :
    (Subcomplex.homOfLE _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundary_bicartSq.le₂₄ ▷ T) ≫
      dgGluingTriangleBoundaryFamily a b h₀ h₂ = a := by
  simpa only [dgGluingTriangleBoundaryFamily, tensorRight, Functor.flip, curriedTensor] using
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundary_isPushout.map (tensorRight T)).inl_desc a
      ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleDiagonalFaceIso.inv ▷ T) ≫ b)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleBoundaryFamily_compatible a b h₀ h₂)

lemma dgGluingTriangleBoundaryFamily_diagonal_face :
    (Subcomplex.homOfLE _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundary_bicartSq.le₃₄ ▷ T) ≫
      dgGluingTriangleBoundaryFamily a b h₀ h₂ = (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleDiagonalFaceIso.inv ▷ T) ≫ b := by
  simpa only [dgGluingTriangleBoundaryFamily, tensorRight, Functor.flip, curriedTensor] using
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundary_isPushout.map (tensorRight T)).inr_desc a
      ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleDiagonalFaceIso.inv ▷ T) ≫ b)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleBoundaryFamily_compatible a b h₀ h₂)

lemma dgGluingTriangleBoundaryFamily_face_one :
    (boundary.ι (1 : Fin 3) ▷ T) ≫ dgGluingTriangleBoundaryFamily a b h₀ h₂ = b := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleDiagonalFaceIso_hom_boundary, comp_whiskerRight, Category.assoc,
    dgGluingTriangleBoundaryFamily_diagonal_face, ← Category.assoc,
    ← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight, Category.id_comp]

lemma dgGluingTriangleBoundaryFamily_face_two :
    (boundary.ι (2 : Fin 3) ▷ T) ≫ dgGluingTriangleBoundaryFamily a b h₀ h₂ =
      (horn₂₁.ι₀₁ ▷ T) ≫ a := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundary_horn_front, comp_whiskerRight, Category.assoc,
    dgGluingTriangleBoundaryFamily_horn]

lemma dgGluingTriangleBoundaryFamily_face_zero :
    (boundary.ι (0 : Fin 3) ▷ T) ≫ dgGluingTriangleBoundaryFamily a b h₀ h₂ =
      (horn₂₁.ι₁₂ ▷ T) ≫ a := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundary_horn_back, comp_whiskerRight, Category.assoc,
    dgGluingTriangleBoundaryFamily_horn]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
