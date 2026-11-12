module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.AppendEdgeConeInverse
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinAssociatorMiddle

/-!
概要：追加錐の中間終点を除く面は、元の実終辺の終点に沿う全面。
方針：元の結合同型の中間因子の包含を使う。
規約：元の全図式を保持。使われ方：実四面体の 013 面。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 中間終点を除いた元の全面は、同じ実辺の終点に沿う全面。 -/
lemma appendEdgeConeCoordinatesInverse_middle (A : SSet.{u}) :
    joinMap (joinInl A Δ[0]) (𝟙 Δ[0]) ≫ appendEdgeConeCoordinatesInverse A =
      joinMap (𝟙 A) (stdSimplex.δ (0 : Fin 2)) := by
  rw [appendEdgeConeCoordinatesInverse, ← Category.assoc, stableJoinAssociator_middle,
    ← joinMap_comp, Category.id_comp, joinStdSimplexIso_rightPoint_inr,
    PinchedHom.lastVertex_zero]
  rfl

/-- 元の実辺の終点に沿う全面は、元の二重錐の中間終点を除いた全面。 -/
lemma appendEdgeConeCoordinates_end (A : SSet.{u}) :
    joinMap (𝟙 A) (stdSimplex.δ (0 : Fin 2)) ≫ appendEdgeConeCoordinates A =
      joinMap (joinInl A Δ[0]) (𝟙 Δ[0]) := by
  have h : (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
      (joinStdSimplexIso 0 0).inv = joinInr Δ[0] Δ[0] := by
    change stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫
      (joinStdSimplexIso 0 0).inv = joinInr Δ[0] Δ[0]
    rw [← PinchedHom.lastVertex_zero, ← joinStdSimplexIso_rightPoint_inr,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [appendEdgeConeCoordinates, ← Category.assoc, ← joinMap_comp, Category.id_comp, h,
    stableJoinAssociator_middle_inv]

end SerrePositivity.InfinityCategories.F2
