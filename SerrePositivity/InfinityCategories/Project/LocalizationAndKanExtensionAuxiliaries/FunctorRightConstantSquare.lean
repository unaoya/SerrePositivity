module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.DegenerateFunctorHomSquare

/-!
概要：右辺が恒等の実関手正方形から三辺の合成関係を得る。
方針：実二三角形の合成関係を使う。規約：標的の充填性を仮定しない。
使われ方：slice prism の全パラメータ評価。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
/-- 右辺が恒等の実正方形は、左辺と上辺の合成を下辺に同定する。 -/
lemma functorHom_comp_eq_of_rightConstantSquare {A X : SSet.{u}} {U V W : A ⟶ X}
    (l : SSet.Homotopy U V) (r : SSet.Homotopy U W) (t : SSet.Homotopy V W)
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom A).obj X)
    (hb : SSet.ι₀ ≫ Q = curry r.h)
    (ht : SSet.ι₁ ≫ Q = curry t.h)
    (hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ Q = curry l.h)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ Q =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex W)) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy t) =
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r) := by
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
    apply stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  have h := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homMk_comp_eq_of_square
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy t)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l)
    (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom A).obj X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex W)) Q
    (by
      change Q.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge, _) = _
      rw [← hi]
      exact congrArg SSet.yonedaEquiv hb)
    (by
      change Q.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge, _) = _
      rw [← hi]
      exact congrArg SSet.yonedaEquiv ht)
    (by
      change Q.app (Opposite.op ⦋1⦌) (_, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _
      rw [← hi]
      exact congrArg SSet.yonedaEquiv hl)
    (by
      change Q.app (Opposite.op ⦋1⦌) (_, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _
      rw [← hi]
      change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ Q) = _
      rw [hr]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex W))
  simpa only [SSet.Truncated.HomotopyCategory.homMk_id, Category.comp_id] using h.symm
end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
