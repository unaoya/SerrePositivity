module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramDiagonalFunctor
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramOrdinaryMixedHom
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramConstantParameter
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QCatDiagramPrism

/-!
概要：同じ自然変換の二点図式の対角関手は、元の prism に使う区間と底の積上の関手。
方針：通常の混合評価を三つの可能な区間射で計算する。
規約：同じ自然変換と元の底の射を保持する。
使われ方：元の自然変換の辺の実現と prism の全単体の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 同じ自然変換を、元の QCat 値図式の間の自然変換として読む。 -/
def quasicategoryDiagramQCatTransformation {C : Type u} [Category.{u} C]
    {F G : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramCategory C}
    (η : F.val ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget ⟶ G.val ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramValueFunctor F ⟶ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramValueFunctor G where
  app := η.app
  naturality _ _ f := η.naturality f

/-- 同じ自然変換の二点図式の通常の対角評価は、元の prism の積上の図式。 -/
lemma quasicategoryDiagramDiagonalFunctor_arrow {C : Type u} [Category.{u} C]
    {F G : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramCategory C}
    (η : F.val ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget ⟶ G.val ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramDiagonalFunctor (CategoryTheory.Prod.snd (Fin 2) C)
      (CategoryTheory.Prod.fst (Fin 2) C ⋙
        ComposableArrows.mk₁ (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramHom η)) =
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramArrow (quasicategoryDiagramQCatTransformation η) := by
  refine CategoryTheory.Functor.ext (fun ⟨i, c⟩ ↦ by fin_cases i <;> rfl) ?_
  rintro ⟨i, c⟩ ⟨j, d⟩ f
  fin_cases i <;> fin_cases j
  · simp only [eqToHom_refl, Category.comp_id]
    apply (eHomEquiv SSet.{u}).injective
    change eHomEquiv SSet.{u} ((eHomEquiv SSet.{u}).symm
      (eHomEquiv SSet.{u} (𝟙 F) ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramMixedHom f.2 F F)) =
      eHomEquiv SSet.{u} (show _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramValue F c ⟶ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramValue F d
        from F.val.map f.2)
    rw [Equiv.apply_symm_apply]
    exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramMixedHom_ordinary_id F f.2
  · simp only [eqToHom_refl, Category.comp_id]
    apply (eHomEquiv SSet.{u}).injective
    change eHomEquiv SSet.{u} ((eHomEquiv SSet.{u}).symm
      (eHomEquiv SSet.{u} (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramHom η) ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramMixedHom f.2 F G)) =
      eHomEquiv SSet.{u} (show _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramValue F c ⟶ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramValue G d
        from η.app c ≫ G.val.map f.2)
    rw [Equiv.apply_symm_apply]
    exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramHom_mixed η f.2
  · have hf := leOfHom f.1
    change (1 : Fin 2) ≤ 0 at hf
    omega
  · simp only [eqToHom_refl, Category.comp_id]
    apply (eHomEquiv SSet.{u}).injective
    change eHomEquiv SSet.{u} ((eHomEquiv SSet.{u}).symm
      (eHomEquiv SSet.{u} (𝟙 G) ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramMixedHom f.2 G G)) =
      eHomEquiv SSet.{u} (show _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramValue G c ⟶ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramValue G d
        from G.val.map f.2)
    rw [Equiv.apply_symm_apply]
    exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramMixedHom_ordinary_id G f.2

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
