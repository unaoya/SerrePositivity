module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomSquare
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.CommutativeSquareRealization

/-!
概要：h Fun の可換性を、四つの指定ホモトピーを境界とする実際の正方形へ戻す。
方針：関手単体集合に可換正方形の実現を適用し、四辺の curry を回収する。
規約：四辺の代表を固定する。使われ方：共通 path end 内の全パラメータの整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 合成の等式から、同じ四つの円柱を境界に持つ関手正方形が存在する。 -/
lemma nonempty_functorHomSquare_of_homEq {A X : SSet.{u}} [Quasicategory X]
    {U₀ U₁ V₀ V₁ : A ⟶ X} (b : SSet.Homotopy U₀ U₁) (t : SSet.Homotopy V₀ V₁)
    (l : SSet.Homotopy U₀ V₀) (r : SSet.Homotopy U₁ V₁)
    (h : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy b) ≫
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l) ≫
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy t)) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomSquare b t l r) := by
  obtain ⟨Q, hb, ht, hl, hr⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_stableSquare_of_homMk_comm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy b) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy t)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r) h
  have hbottom : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge = (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) := by
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide
  have htop : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge = (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) := by
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide
  have hleft : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) := by
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide
  have hright : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) := by
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ Q = SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry b.h)) at hb
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ Q = SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry t.h)) at ht
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ Q = SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry l.h)) at hl
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ Q = SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry r.h)) at hr
  refine ⟨⟨Q, ?_, ?_, ?_, ?_⟩⟩
  · simpa only [hbottom, Equiv.symm_apply_apply] using hb
  · simpa only [htop, Equiv.symm_apply_apply] using ht
  · simpa only [hleft, Equiv.symm_apply_apply] using hl
  · simpa only [hright, Equiv.symm_apply_apply] using hr

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
