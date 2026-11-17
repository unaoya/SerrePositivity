module
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumnComponentArrow
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefixColumnRoof
/-!
概要：既存の全列自然性を元の指定通常射の成分正方形へ回収する。
方針：同じ指定射の定値列へ全列自然性を適用し、両経路を評価する。
規約：閉包内の全列比較を再利用し、元の成分射を保持する。
使われ方：実 U の全源比較と cofibrant 置換 augmentation の端点整合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn
open _root_.CategoryTheory _root_.SSet _root_.CategoryTheory.MonoidalClosed _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open scoped _root_.Simplicial

/-- 概要：元の指定射の定値列に沿う全源同型の自然性は同じ成分正方形を与える。
方針：既存の全列自然性と元の円柱成分を両経路で比較する。
規約：元の射の両像を全 Arrow で保持。使われ方：指定置換射での全源比較。 -/
lemma hom_naturality_const_component {C : Type u} [Category.{u} C]
    {D : SSet.{u}} [Quasicategory D] {F G : nerve C ⟶ D}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) {x y : C} (f : x ⟶ y) :
    Arrow.mk (Truncated.HomotopyCategory.homMk ((nerve.edgeMk f).map F).toTruncated ≫
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate e.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex y)) =
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate e.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex x) ≫
      Truncated.HomotopyCategory.homMk ((nerve.edgeMk f).map G).toTruncated) := by
  let a : (Functor.const C).obj x ⟶ (Functor.const C).obj y := (Functor.const C).map f
  have h := congrArg (fun α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom
      (nerveMap ((Functor.const C).obj x) ≫ F)
      (nerveMap ((Functor.const C).obj y) ≫ G) =>
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate α (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex x)) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom_naturality e a)
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_comp, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_comp] at h
  have hf := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom_component_arrow F a x
  have hg := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom_component_arrow G a x
  have hx := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.constRestriction_component_arrow (I := C) e.hom x x
  have hy := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.constRestriction_component_arrow (I := C) e.hom y x
  have hl := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.comp_arrow_eq _ _ _ _ hf hy
  have hr := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.comp_arrow_eq _ _ _ _ hx hg
  exact hl.symm.trans ((congrArg Arrow.mk h).trans hr)

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn
