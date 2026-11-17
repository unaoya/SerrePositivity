module
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumnRoofNaturality
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality
/-!
概要：元の通常列の全関手射の評価を同じ成分辺の像へ比較する。
方針：元の自然変換円柱の成分式を同じ後合成へ送る。
規約：元の成分辺と両端表示を全 Arrow 等式で保持する。
使われ方：閉包内の全列自然性から実 U の指定成分正方形を回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn
open _root_.CategoryTheory _root_.SSet _root_.CategoryTheory.MonoidalClosed _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C]

/-- 概要：全列射の評価は同じ元の成分辺の像と全 Arrow として一致する。
方針：元の全円柱の成分式と同じ評価公式を使う。
規約：端点表示を捨てない。使われ方：全列自然性の指定成分への適用。 -/
lemma hom_component_arrow {D : SSet.{u}} (q : nerve C ⟶ D)
    {V W : I ⥤ C} (a : V ⟶ W) (i : I) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom q a) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)) =
      Arrow.mk (Truncated.HomotopyCategory.homMk
        ((nerve.edgeMk (a.app i)).map q).toTruncated) := by
  have hb : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom a = Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy a)) :=
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy_hom a).symm
  rw [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom, hb, ← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomEvaluate_homotopy]
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  exact congrArg (q.app (Opposite.op ⦋1⦌)) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy_component a i)

/-- 概要：全関手射の定値通常列での評価は同じ頂点成分と全 Arrow として一致する。
方針：既存の前合成評価公式と元の零単体の計算を使う。
規約：同じ全関手射を保持。使われ方：全源比較の定値列への制限。 -/
lemma constRestriction_component_arrow {D : SSet.{u}} {F G : nerve C ⟶ D}
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) (c : C) (i : I) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate
      (U := nerveMap ((Functor.const I).obj c) ≫ F)
      (V := nerveMap ((Functor.const I).obj c) ≫ G)
      ((hoFunctor.map ((pre (nerveMap ((Functor.const I).obj c))).app D)).toFunctor.map a)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)) = Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate a (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_precomp]
  have h : (nerveMap ((Functor.const I).obj c)).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c := ComposableArrows.ext₀ rfl
  exact congrArg (fun v => (Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate a v) : Arrow (hoFunctor.obj D))) h

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn
