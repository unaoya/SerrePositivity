module
public import SerrePositivity.InfinityCategories.F1.ColimitCoconeEdges
public import SerrePositivity.InfinityCategories.Stable.ZeroTriangleHoMap
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence

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
namespace SerrePositivity.InfinityCategories

/-- 概要：span 間のホモトピーは押し出し四角形間へ厳密に延長できる。
方針：普遍余錐間の辺を持ち上げ、余錐と正方形の同型を適用する。
規約：両端は押し出し。使われ方：TR3 の第三成分の構成。 -/
lemma exists_pushoutSquareHomotopy_lift_span {X : SSet.{u}} [Quasicategory X]
    (F G : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hF : IsPushoutSquare F) (hG : IsPushoutSquare G)
    (H : SSet.Homotopy (pushoutSpan F) (pushoutSpan G)) :
    ∃ Q : SSet.Homotopy F G,
      (spanSquareBoundary ▷ (Δ[1] : SSet.{u})) ≫ Q.h = H.h := by
  let e := functorEdgeOfSimplicialHomotopy H
  obtain ⟨J, hJ⟩ := exists_colimitCoconeHomotopy (pushoutCocone F)
    (pushoutCocone G) hF hG e
  have hJ' : (joinInl (horn 2 0 : SSet.{u}) Δ[0] ▷ (Δ[1] : SSet.{u})) ≫ J.h = H.h := by
    rw [hJ]
    change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry H.h))) = H.h
    rw [Equiv.symm_apply_apply, uncurry_curry]
  let Q : SSet.Homotopy F G := {
    h := (spanCoconeSquareIso.inv ▷ (Δ[1] : SSet.{u})) ≫ J.h
    h₀ := by
      rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, J.h₀]
      change spanCoconeSquareIso.inv ≫ (spanCoconeSquareIso.hom ≫ F) = _
      rw [Iso.inv_hom_id_assoc]
      rfl
    h₁ := by
      rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, J.h₁]
      change spanCoconeSquareIso.inv ≫ (spanCoconeSquareIso.hom ≫ G) = _
      rw [Iso.inv_hom_id_assoc]
      rfl
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro z
      exact False.elim z.1.property }
  have hbase : (spanSquareBoundary ▷ (Δ[1] : SSet.{u})) ≫ Q.h = H.h := by
    change (spanSquareBoundary ▷ (Δ[1] : SSet.{u})) ≫
      ((spanCoconeSquareIso.inv ▷ (Δ[1] : SSet.{u})) ≫ J.h) = H.h
    rw [← Category.assoc, ← comp_whiskerRight]
    have hi : spanSquareBoundary ≫ spanCoconeSquareIso.inv =
        joinInl (horn 2 0 : SSet.{u}) Δ[0] := by
      simp only [spanSquareBoundary, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hi]
    exact hJ'
  exact ⟨Q, hbase⟩

end SerrePositivity.InfinityCategories
