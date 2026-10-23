module

public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryDiagramDiagonalFunctor
public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryDiagramOrdinaryMixedHom
public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryDiagramConstantParameter
public import SerrePositivity.InfinityCategories.F1.Categories.QCatDiagramPrism

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
namespace SerrePositivity.InfinityCategories

/-- 同じ自然変換を、元の QCat 値図式の間の自然変換として読む。 -/
def quasicategoryDiagramQCatTransformation {C : Type u} [Category.{u} C]
    {F G : QuasicategoryDiagramCategory C}
    (η : F.val ⋙ quasicategoryObjectForget ⟶ G.val ⋙ quasicategoryObjectForget) :
    quasicategoryDiagramValueFunctor F ⟶ quasicategoryDiagramValueFunctor G where
  app := η.app
  naturality _ _ f := η.naturality f

/-- 同じ自然変換の二点図式の通常の対角評価は、元の prism の積上の図式。 -/
lemma quasicategoryDiagramDiagonalFunctor_arrow {C : Type u} [Category.{u} C]
    {F G : QuasicategoryDiagramCategory C}
    (η : F.val ⋙ quasicategoryObjectForget ⟶ G.val ⋙ quasicategoryObjectForget) :
    quasicategoryDiagramDiagonalFunctor (CategoryTheory.Prod.snd (Fin 2) C)
      (CategoryTheory.Prod.fst (Fin 2) C ⋙
        ComposableArrows.mk₁ (quasicategoryDiagramHom η)) =
    qCatDiagramArrow (quasicategoryDiagramQCatTransformation η) := by
  refine CategoryTheory.Functor.ext (fun ⟨i, c⟩ ↦ by fin_cases i <;> rfl) ?_
  rintro ⟨i, c⟩ ⟨j, d⟩ f
  fin_cases i <;> fin_cases j
  · simp only [eqToHom_refl, Category.comp_id]
    apply (eHomEquiv SSet.{u}).injective
    change eHomEquiv SSet.{u} ((eHomEquiv SSet.{u}).symm
      (eHomEquiv SSet.{u} (𝟙 F) ≫ quasicategoryDiagramMixedHom f.2 F F)) =
      eHomEquiv SSet.{u} (show quasicategoryDiagramValue F c ⟶ quasicategoryDiagramValue F d
        from F.val.map f.2)
    rw [Equiv.apply_symm_apply]
    exact quasicategoryDiagramMixedHom_ordinary_id F f.2
  · simp only [eqToHom_refl, Category.comp_id]
    apply (eHomEquiv SSet.{u}).injective
    change eHomEquiv SSet.{u} ((eHomEquiv SSet.{u}).symm
      (eHomEquiv SSet.{u} (quasicategoryDiagramHom η) ≫ quasicategoryDiagramMixedHom f.2 F G)) =
      eHomEquiv SSet.{u} (show quasicategoryDiagramValue F c ⟶ quasicategoryDiagramValue G d
        from η.app c ≫ G.val.map f.2)
    rw [Equiv.apply_symm_apply]
    exact quasicategoryDiagramHom_mixed η f.2
  · have hf := leOfHom f.1
    change (1 : Fin 2) ≤ 0 at hf
    omega
  · simp only [eqToHom_refl, Category.comp_id]
    apply (eHomEquiv SSet.{u}).injective
    change eHomEquiv SSet.{u} ((eHomEquiv SSet.{u}).symm
      (eHomEquiv SSet.{u} (𝟙 G) ≫ quasicategoryDiagramMixedHom f.2 G G)) =
      eHomEquiv SSet.{u} (show quasicategoryDiagramValue G c ⟶ quasicategoryDiagramValue G d
        from G.val.map f.2)
    rw [Equiv.apply_symm_apply]
    exact quasicategoryDiagramMixedHom_ordinary_id G f.2

end SerrePositivity.InfinityCategories
