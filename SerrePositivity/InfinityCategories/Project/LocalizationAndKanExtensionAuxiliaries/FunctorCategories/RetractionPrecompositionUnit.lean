module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.PrecompositionHomotopy
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
概要：固定された切断への収縮から、前合成作用の単位を構成する。
方針：元の実ホモトピーを豊穣前合成作用へ移す。
規約：元の切断・射影・収縮を保持し、既存の円柱モジュールを変更しない。
使われ方：余錐の右端への制限の Hom 対応の一般化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
variable {A B : SSet.{u}} (i : B ⟶ A) (r : A ⟶ B)

/-- 指定切断への収縮が誘導する前合成作用の単位。 -/
def retractionPrecompositionUnit (H : SSet.Homotopy (𝟙 A) (r ≫ i)) (X : SSet.{u}) :
    𝟭 (hoFunctor.obj ((ihom A).obj X)) ⟶
      (hoFunctor.map ((pre i).app X)).toFunctor ⋙
        (hoFunctor.map ((pre r).app X)).toFunctor :=
  eqToHom (by simp only [pre_id, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Cat.Hom.id_toFunctor]) ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.precompositionNatTrans H X ≫ eqToHom (by
      simp only [pre_map, NatTrans.comp_app, CategoryTheory.Functor.map_comp,
        Cat.Hom.comp_toFunctor])

/-- 切断と射影の恒等式は前合成作用の厳密な引き戻しの恒等式となる。 -/
lemma retractionPrecomposition_retraction (hir : i ≫ r = 𝟙 B) (X : SSet.{u}) :
    (hoFunctor.map ((pre r).app X)).toFunctor ⋙
      (hoFunctor.map ((pre i).app X)).toFunctor = 𝟭 _ := by
  rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp, ← NatTrans.comp_app, ← pre_map,
    hir, pre_id, NatTrans.id_app, CategoryTheory.Functor.map_id, Cat.Hom.id_toFunctor]

/-- 単位の関手 U での成分は指定収縮を U で写した辺の類。 -/
lemma retractionPrecompositionUnit_app (H : SSet.Homotopy (𝟙 A) (r ≫ i))
    {X : SSet.{u}} (U : A ⟶ X) :
    (retractionPrecompositionUnit i r H X).app (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U)) =
      Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H U)) := by
  unfold retractionPrecompositionUnit
  simp only [NatTrans.comp_app, eqToHom_app, eqToHom_refl, Category.id_comp,
    Category.comp_id]
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.precompositionNatTrans_app H U

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
