module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.TriangleBoundaryFamily

/-! パラメーター付き境界図式は、合成ホーンと対角辺への制限で決まる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory SSet
open scoped _root_.Simplicial
variable {T X : SSet.{u}}

lemma dgGluingTriangleBoundaryFamily_hom_ext
    {f g : (boundary 2 : SSet.{u}) ⊗ T ⟶ X}
    (hh : (Subcomplex.homOfLE _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundary_bicartSq.le₂₄ ▷ T) ≫ f =
      (Subcomplex.homOfLE _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundary_bicartSq.le₂₄ ▷ T) ≫ g)
    (hd : (boundary.ι (1 : Fin 3) ▷ T) ≫ f = (boundary.ι (1 : Fin 3) ▷ T) ≫ g) :
    f = g := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundary_isPushout.map (tensorRight T)).hom_ext
  · simpa only [tensorRight, Functor.flip, curriedTensor] using hh
  · apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleDiagonalFaceIso.hom ▷ T)).mp
    simpa only [tensorRight, Functor.flip, curriedTensor, ← Category.assoc,
      ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleDiagonalFaceIso_hom_boundary] using hd

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
