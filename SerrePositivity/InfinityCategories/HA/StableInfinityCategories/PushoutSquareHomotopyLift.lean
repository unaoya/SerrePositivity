module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCoconeEdges
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangleHoMap
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence

/-! # 押し出し四角形間への span ホモトピーの持ち上げ

概要：押し出し四角形の span 間の任意のホモトピーを四角形間へ延長する。
方針：両端の普遍余錐へ辺を持ち上げ、正方形の表示へ戻す。
規約：span 上のホモトピーを厳密に保持する。
使われ方：S4 の TR3 の cofiber 図式の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：span 間のホモトピーは押し出し四角形間へ厳密に延長できる。
方針：普遍余錐間の辺を持ち上げ、余錐と正方形の同型を適用する。
規約：両端は押し出し。使われ方：TR3 の第三成分の構成。 -/
lemma exists_pushoutSquareHomotopy_lift_span {X : SSet.{u}} [Quasicategory X]
    (F G : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare G)
    (H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan G)) :
    ∃ Q : SSet.Homotopy F G,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ▷ (Δ[1] : SSet.{u})) ≫ Q.h = H.h := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H
  obtain ⟨J, hJ⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_colimitCoconeHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone G) hF hG e
  have hJ' : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (horn 2 0 : SSet.{u}) Δ[0] ▷ (Δ[1] : SSet.{u})) ≫ J.h = H.h := by
    rw [hJ]
    change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry H.h))) = H.h
    rw [Equiv.symm_apply_apply, uncurry_curry]
  let Q : SSet.Homotopy F G := {
    h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv ▷ (Δ[1] : SSet.{u})) ≫ J.h
    h₀ := by
      rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, J.h₀]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ F) = _
      rw [Iso.inv_hom_id_assoc]
      rfl
    h₁ := by
      rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, J.h₁]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ G) = _
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
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv ▷ (Δ[1] : SSet.{u})) ≫ J.h) = H.h
    rw [← Category.assoc, ← comp_whiskerRight]
    have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (horn 2 0 : SSet.{u}) Δ[0] := by
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hi]
    exact hJ'
  exact ⟨Q, hbase⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
