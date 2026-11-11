module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.SquareComposition

/-!
概要：関手単体集合の正方形から h Fun の合成関係を得る。
方針：下辺が退化する四辺の正方形に一般の合成関係を適用する。
規約：三つの辺は実際のホモトピーで表し、始域の quasicategory 性は不要。
使われ方：comma の正方形が単位比較の導来 fiber に入ることの検証。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：下辺が恒等の関手正方形では左辺と上辺の合成は右辺。
方針：代表辺の四境界を確認し、二つの三角形の合成の等式を使う。
規約：辺のホモトピー代表を取り替えない。
使われ方：comma の coherence を h Fun の合成へ移す。 -/
lemma functorHom_comp_eq_of_square {A X : SSet.{u}} {U V W : A ⟶ X}
    (l : SSet.Homotopy U V) (r : SSet.Homotopy U W) (t : SSet.Homotopy V W)
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom A).obj X)
    (hb : SSet.ι₀ ≫ Q = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U))
    (ht : SSet.ι₁ ≫ Q = curry t.h)
    (hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ Q = curry l.h)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ Q = curry r.h) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy t) =
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r) := by
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
    apply stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  have h := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homMk_comp_eq_of_square
    (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom A).obj X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy t) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r) Q
    (by
      change Q.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge, _) = _
      rw [← hi]
      change SSet.yonedaEquiv (SSet.ι₀ ≫ Q) = _
      rw [hb]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U))
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
      exact congrArg SSet.yonedaEquiv hr)
  simpa only [SSet.Truncated.HomotopyCategory.homMk_id, Category.id_comp] using h.symm

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
