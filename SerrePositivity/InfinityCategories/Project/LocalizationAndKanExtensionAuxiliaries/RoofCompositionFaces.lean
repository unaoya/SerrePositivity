module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle

/-! # 指定二辺を持つ実関手二単体の合成辺

概要：指定した前後二辺を保つ実二単体から、同じ二単体を持つ合成ホモトピーを回収する。
方針：対角面の二端点を単体恒等式で照合し、実関手辺を uncurry する。
規約：入力二単体自体を変更しない。使われ方：動く境界付き輸送の相対合成。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial

/-- 実関手二単体の指定二外面から、同じ二単体の合成ホモトピーを回収できる。 -/
lemma roofCompositionTriangle_of_outerFaces {K X : SSet.{u}} {U V W : K ⟶ X}
    (l : SSet.Homotopy U V) (r : SSet.Homotopy V W)
    (D : (Δ[2] : SSet.{u}) ⟶ (ihom K).obj X)
    (h₀ : stdSimplex.δ (0 : Fin 3) ≫ D = curry r.h)
    (h₂ : stdSimplex.δ (2 : Fin 3) ≫ D = curry l.h) :
    ∃ d : SSet.Homotopy U W, ∃ T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d, T.diagram = D := by
  let Y := (ihom K).obj X
  let s := SSet.yonedaEquiv D
  have hs₂ : Y.δ 2 s = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l).edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, h₂]
    rfl
  have hs₀ : Y.δ 0 s = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r).edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, h₀]
    rfl
  have hsrc : Y.δ 1 (Y.δ 1 s) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U := by
    have he : Y.δ 1 (Y.δ 1 s) = Y.δ 1 (Y.δ 2 s) := by
      simp only [SimplicialObject.δ, ← Functor.map_comp_apply, ← op_comp]
      apply congrArg (fun α : ⦋0⦌ ⟶ ⦋2⦌ => Y.map α.op s)
      decide
    rw [he, hs₂]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l).src_eq
  have htgt : Y.δ 0 (Y.δ 1 s) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex W := by
    have he : Y.δ 0 (Y.δ 1 s) = Y.δ 0 (Y.δ 0 s) := by
      simp only [SimplicialObject.δ, ← Functor.map_comp_apply, ← op_comp]
      apply congrArg (fun α : ⦋0⦌ ⟶ ⦋2⦌ => Y.map α.op s)
      decide
    rw [he, hs₀]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r).tgt_eq
  let e : SSet.Truncated.Edge (X := (truncation 2).obj Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex W) :=
    ⟨Y.δ 1 s, hsrc, htgt⟩
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e
  have h₁ : stdSimplex.δ (1 : Fin 3) ≫ D = curry d.h := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp]
    change Y.δ 1 s = SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm e.edge)))
    rw [curry_uncurry, Equiv.apply_symm_apply]
  exact ⟨d, ⟨D, h₀, h₁, h₂⟩, rfl⟩

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
