module

public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationCoconeCoordinates
public import SerrePositivity.InfinityCategories.F1.Scaffold.ScaffoldFirstVertex
public import SerrePositivity.InfinityCategories.Core.TerminalUniqueness

/-!
概要：区間図式を、その終点 slice の標準切断へ持ち上げる。
方針：区間の右余錐の最後の点を終点に潰し、同じ図式を後合成する。
規約：射影は元の全区間図式、始点の辺も元の辺。使われ方：円柱持ち上げの終端側面。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 最初の点と最後の点を結ぶ join の評価は、同じ標準区間そのもの。 -/
lemma intervalTerminalJoin_first :
    joinMap (stdSimplex.δ 1 : (Δ[0] : SSet.{u}) ⟶ Δ[1]) (𝟙 Δ[0]) ≫
      stableLastJoinEvaluation 1 = (joinStdSimplexIso 0 0).hom := by
  apply (cancel_epi (joinStdSimplexIso 0 0).inv).mp
  rw [Iso.inv_hom_id]
  apply SSet.yonedaEquiv.injective
  decide

variable {X : SSet.{u}} (d : (Δ[1] : SSet.{u}) ⟶ X)

/-- 最後の頂点を終点に潰した全余錐は、元の同じ区間の終点を持つ。 -/
lemma intervalTerminalSlice_fixed :
    joinInr (Δ[1] : SSet.{u}) Δ[0] ≫ (stableLastJoinEvaluation 1 ≫ d) =
      stdSimplex.δ 0 ≫ d := by
  rw [← Category.assoc, arrowInterpolationInterval_inr, stdSimplex.δ_zero_eq_const]

/-- 元の全区間図式を、その終点の実 slice へ持ち上げる標準切断。 -/
def intervalTerminalSliceSection : (Δ[1] : SSet.{u}) ⟶ sliceOver (stdSimplex.δ 0 ≫ d) :=
  sliceOverCurry (stableLastJoinEvaluation 1 ≫ d) (intervalTerminalSlice_fixed d)

/-- 標準切断は、元の全区間図式を厳密に被覆する。 -/
lemma intervalTerminalSliceSection_projection :
    intervalTerminalSliceSection d ≫ sliceOverProjection (stdSimplex.δ 0 ≫ d) = d := by
  rw [intervalTerminalSliceSection, sliceOverCurry_projection,
    ← Category.assoc, stableLastJoinEvaluation_inl, Category.id_comp]

/-- 標準切断の始点側の全辺は、元の区間の同じ辺。 -/
lemma intervalTerminalSliceSection_first :
    sliceOverUncurry (stdSimplex.δ 1 ≫ intervalTerminalSliceSection d) =
      (joinStdSimplexIso 0 0).hom ≫ d := by
  rw [sliceOverUncurry_precomp, intervalTerminalSliceSection,
    sliceOverUncurry_curry, ← Category.assoc, intervalTerminalJoin_first]

end SerrePositivity.InfinityCategories.F2.Ind
