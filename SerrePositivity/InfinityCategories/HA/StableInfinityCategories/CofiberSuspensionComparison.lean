module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSpanComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCoconeEdges
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangleHoMap
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence

/-! # Cofiber 四角形から suspension 四角形への比較

概要：押し出し四角形から同じ始点の suspension 四角形への、始点を固定したホモトピーがある。
方針：span の比較を両端の普遍余錐へ持ち上げ、正方形の表示へ戻す。
規約：元の始点の全パラメーターでの固定を保持する。
使われ方：S4 の接続射と cofiber 三角形の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：押し出し四角形から同じ始点の suspension への始点固定の比較がある。
方針：span の始点固定のホモトピーを普遍余錐の間へ延長し、四角形へ戻す。
規約：元の四角形の零角はこの存在定理には不要。
使われ方：cofiber 対象から suspension 対象への接続射。 -/
lemma exists_cofiberSuspensionComparison {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 0 0)) :
    ∃ Q : SSet.Homotopy F s.square,
      ((stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫ Q.h =
        CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫ SSet.const (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 0 0) := by
  obtain ⟨H, hH⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_suspensionSpanComparison F s
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H
  obtain ⟨G, hG⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_colimitCoconeHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone s.square) hF s.isPushout e
  have hG' : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (horn 2 0 : SSet.{u}) Δ[0] ▷ (Δ[1] : SSet.{u})) ≫ G.h = H.h := by
    rw [hG]
    change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry H.h))) = H.h
    rw [Equiv.symm_apply_apply, uncurry_curry]
  let Q : SSet.Homotopy F s.square := {
    h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv ▷ (Δ[1] : SSet.{u})) ≫ G.h
    h₀ := by
      rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, G.h₀]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ F) = _
      rw [Iso.inv_hom_id_assoc]
      rfl
    h₁ := by
      rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, G.h₁]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ s.square) = _
      rw [Iso.inv_hom_id_assoc]
      rfl
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro z
      exact False.elim z.1.property }
  have hbase : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ▷ (Δ[1] : SSet.{u})) ≫ Q.h = H.h := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ▷ (Δ[1] : SSet.{u})) ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv ▷ (Δ[1] : SSet.{u})) ≫ G.h) = H.h
    rw [← Category.assoc, ← comp_whiskerRight]
    have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (horn 2 0 : SSet.{u}) Δ[0] := by
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hi]
    exact hG'
  refine ⟨Q, ?_⟩
  have hp : stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge =
      (stdSimplex.δ (1 : Fin 2) ≫ horn₂₀.ι₀₁) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary := by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge]
  let U : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⊗ Δ[1] ⟶ X := Q.h
  change ((stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫ U = _
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ▷ (Δ[1] : SSet.{u})) ≫ U = H.h at hbase
  rw [hp, comp_whiskerRight, Category.assoc, hbase]
  exact hH

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
