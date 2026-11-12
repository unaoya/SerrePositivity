module

public import
  SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.RetractionPrecompositionUnit

/-!
概要：切断と射影を固定する収縮から、前合成作用の随伴を構成する。
方針：元の収縮の単位と厳密な引き戻しの余単位で両三角恒等式を計算する。
規約：始域・標的の quasicategory 性を要求しない。
使われ方：余錐の右端での Hom 対応と全パラメーター判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 切断と射影を固定する収縮は、切断への前合成と射影への前合成の随伴を与える。 -/
def retractionPrecompositionAdjunction {A B : SSet.{u}} (i : B ⟶ A) (r : A ⟶ B)
    (hir : i ≫ r = 𝟙 B) (H : SSet.Homotopy (𝟙 A) (r ≫ i))
    (hi : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst B Δ[1] ≫ i)
    (hr : H.h ≫ r = fst A Δ[1] ≫ r) (X : SSet.{u}) :
    (hoFunctor.map ((pre i).app X)).toFunctor ⊣
      (hoFunctor.map ((pre r).app X)).toFunctor where
  unit := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.retractionPrecompositionUnit i r H X
  counit := eqToHom (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.retractionPrecomposition_retraction i r hir X)
  left_triangle_components x := by
    obtain ⟨v, rfl⟩ := Truncated.HomotopyCategory.mk_surjective x
    obtain ⟨U, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ X).surjective v
    change (hoFunctor.map ((pre i).app X)).toFunctor.map
      ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.retractionPrecompositionUnit i r H X).app
        (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U))) ≫ _ = 𝟙 _
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.retractionPrecompositionUnit_app]
    simp only [eqToHom_app]
    rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom]
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyHom_eqToHom _ (by
      simp only [Category.assoc, reassoc_of% hir, Category.id_comp]) (by
      change (i ▷ (Δ[1] : SSet.{u})) ≫ (H.h ≫ U) = _
      rw [← Category.assoc, hi, Category.assoc]
      rfl)]
    simp
  right_triangle_components y := by
    obtain ⟨v, rfl⟩ := Truncated.HomotopyCategory.mk_surjective y
    obtain ⟨G, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ X).surjective v
    change (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.retractionPrecompositionUnit i r H X).app
      (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (r ≫ G))) ≫ _ = 𝟙 _
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.retractionPrecompositionUnit_app]
    simp only [eqToHom_app, eqToHom_map]
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyHom_eqToHom _ (by
      simp only [Category.assoc, reassoc_of% hir, Category.id_comp]) (by
      change H.h ≫ (r ≫ G) = _
      rw [← Category.assoc, hr, Category.assoc]
      rfl)]
    simp

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
