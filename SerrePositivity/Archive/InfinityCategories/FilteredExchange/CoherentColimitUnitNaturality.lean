module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantEdge

/-!
概要：元の native 余錐の両単位と元の余極限の指定辺の合成整合を証明する。
方針：構成済みの全正方形の四辺を固定し、同じ対角の二つの合成を比較する。
規約：元の辺の代表を保持。使われ方：a6 の native 写像との単位を通した照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の変換の後の標的単位と、始域単位の後の余極限の指定辺は同じ合成を表す。 -/
lemma coherentColimitUnitNaturality (B : SSet.{u})
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (H : SSet.Homotopy F G) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (coconeTransformationHomotopy (coherentDiagramTotalCocone F))) ≫
      SSet.Truncated.HomotopyCategory.homMk (coherentColimitConstantEdge B H) =
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (coconeTransformationHomotopy (coherentDiagramTotalCocone G))) := by
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u + 1})) = homotopyIntervalEdge.edge := by
    apply SSet.stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  apply homMk_comp_eq_of_square _ _ _ _ (coherentColimitUnitSquare B H)
  · change (coherentColimitUnitSquare B H).app (Opposite.op ⦋1⦌)
      (homotopyIntervalEdge.edge, _) = _
    rw [← hi]
    change SSet.yonedaEquiv (SSet.ι₀ ≫ coherentColimitUnitSquare B H) = _
    rw [coherentColimitUnitSquare_bottom]
    rfl
  · change (coherentColimitUnitSquare B H).app (Opposite.op ⦋1⦌)
      (homotopyIntervalEdge.edge, _) = _
    rw [← hi]
    change SSet.yonedaEquiv (SSet.ι₁ ≫ coherentColimitUnitSquare B H) = _
    rw [coherentColimitUnitSquare_top]
    rfl
  · change (coherentColimitUnitSquare B H).app (Opposite.op ⦋1⦌)
      (_, homotopyIntervalEdge.edge) = _
    rw [← hi]
    change SSet.yonedaEquiv (prismEndpoint 0 Δ[1] ≫ coherentColimitUnitSquare B H) = _
    rw [coherentColimitUnitSquare_source]
    rfl
  · change (coherentColimitUnitSquare B H).app (Opposite.op ⦋1⦌)
      (_, homotopyIntervalEdge.edge) = _
    rw [← hi]
    change SSet.yonedaEquiv (prismEndpoint 1 Δ[1] ≫ coherentColimitUnitSquare B H) = _
    rw [coherentColimitUnitSquare_target, ← coherentColimitConstantEdge_curry,
      Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.F2
