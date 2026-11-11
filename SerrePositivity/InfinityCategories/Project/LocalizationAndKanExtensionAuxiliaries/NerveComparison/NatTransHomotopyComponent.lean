module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransHomotopyNaturality

/-!
概要：通常の自然変換と指定錐の後合成を実際のホモトピーへ移す。
方針：nerve の指数比較の辺を uncurry して成分を計算する。
規約：元の図式と自然変換を保ち、可逆性を仮定しない。
使われ方：B5 の指定単位・余単位の局所錐の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

variable {C D : Type u} [Category.{u} C] [Category.{u} D] {F G : C ⥤ D}


/-- 概要：各頂点でのホモトピーの辺は通常の自然変換の成分を表す。
方針：指定された辺の指数比較と自然性を使う。
規約：同じ宇宙の小さい圏と元の指定変換を扱う。
使われ方：B5 の指定局所錐の古典比較。 -/
lemma nerveNatTransHomotopy_component (η : F ⟶ G) (x : C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy η) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex x)).edge =
      (nerve.edgeMk (η.app x)).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransEdge η).toTruncated) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex x)).edge = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_edge]
  let t : (nerve (C × (C ⥤ D))) _⦋1⦌ :=
    (ComposableArrows.mk₁ (𝟙 x)).prod' (ComposableArrows.mk₁ η)
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso_uncurry C D) (Opposite.op ⦋1⦌)) t
  change (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso C D).hom.app (Opposite.op ⦋1⦌)
    (ComposableArrows.mk₁ η)).app (Opposite.op ⦋1⦌)
    (𝟙 (Opposite.op ⦋1⦌))) (ComposableArrows.mk₁ (𝟙 x)) = _ at h
  change (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso C D).hom.app (Opposite.op ⦋1⦌)
    (ComposableArrows.mk₁ η)).app (Opposite.op ⦋1⦌)
    (𝟙 (Opposite.op ⦋1⦌))) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex x) 1) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]
  have hi := congrArg SSet.Edge.edge (nerve.edgeMk_id x)
  change ComposableArrows.mk₁ (𝟙 x) =
    (SSet.Truncated.Edge.id (X := (truncation 2).obj (nerve C)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex x)).edge at hi
  rw [← hi]
  refine h.trans ?_
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · rfl
  · rfl
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change F.map (𝟙 x) ≫ η.app x = η.app x
    rw [F.map_id, Category.id_comp]

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
