module
public import SerrePositivity.InfinityCategories.F1.ColimitHomotopyInvertible
public import SerrePositivity.InfinityCategories.Stable.PushoutSquareHomotopyLift

/-! # 押し出し四角形の比較の可逆性

概要：span 上で可逆な比較は押し出し四角形全体でも可逆であり、指定 span 同型を延長できる。
方針：四角形を普遍余錐へ移し、充満忠実射影で可逆性を反映する。
規約：指定した比較の類を保持する。使われ方：cofiber の同型不変性と射の同型判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：押し出し四角形間のホモトピーは span への制限が可逆なら全体も可逆。
方針：標準 join 同型で普遍余錐の判定へ移し、逆同型で元へ戻す。
規約：両端の押し出し性のみを使う。使われ方：実際の比較四角形の可逆性。 -/
lemma pushoutSquareHomotopy_isInvertible_of_span {X : SSet.{u}} [Quasicategory X]
    (F G : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hF : IsPushoutSquare F) (hG : IsPushoutSquare G)
    (Q : SSet.Homotopy F G)
    (hQ : IsInvertibleEdge (functorEdgeOfSimplicialHomotopy
      (stableHomotopyPrecomp spanSquareBoundary Q))) :
    IsInvertibleEdge (functorEdgeOfSimplicialHomotopy Q) := by
  let J := stableHomotopyPrecomp spanCoconeSquareIso.hom Q
  have hJ : IsInvertibleEdge (functorEdgeOfSimplicialHomotopy J) := by
    apply colimitCoconeHomotopy_isInvertible_of_precomp
      (pushoutCocone F) (pushoutCocone G) hF hG J
    exact hQ
  have hi := hJ.map ((pre spanCoconeSquareIso.inv).app X)
  rw [functorEdgeOfSimplicialHomotopy_precomp] at hi
  have ha := homMk_functorEdge_precomp_inv_hom_arrow spanCoconeSquareIso Q
  change IsIso (Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
    (functorEdgeOfSimplicialHomotopy Q))).hom
  rw [← ha]
  exact hi

/-- 概要：指定した span の関手同型は押し出し四角形の関手同型へ延長できる。
方針：同型の順射を辺で表して延長し、前補題でその延長を可逆と認証する。
規約：制限した順射の h の類を厳密に保持する。使われ方：cofiber 図式の同型輸送。 -/
lemma exists_pushoutSquareFunctorIso_lift_span {X : SSet.{u}} [Quasicategory X]
    (F G : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hF : IsPushoutSquare F) (hG : IsPushoutSquare G)
    (e : FunctorIso (pushoutSpan F) (pushoutSpan G)) :
    ∃ d : FunctorIso F G,
      (hoFunctor.map ((pre spanSquareBoundary).app X)).toFunctor.map d.hom = e.hom := by
  obtain ⟨a, ha⟩ := homotopyCategory_homMk_surjective
    (functorVertex (pushoutSpan F)) (functorVertex (pushoutSpan G)) e.hom
  let H := simplicialHomotopyOfFunctorEdge a
  obtain ⟨Q, hQ⟩ := exists_pushoutSquareHomotopy_lift_span F G hF hG H
  have he : functorEdgeOfSimplicialHomotopy
      (stableHomotopyPrecomp spanSquareBoundary Q) = a := by
    apply SSet.Truncated.Edge.ext
    change SSet.yonedaEquiv (curry ((spanSquareBoundary ▷ (Δ[1] : SSet.{u})) ≫ Q.h)) = a.edge
    rw [hQ]
    change SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm a.edge))) = a.edge
    rw [curry_uncurry, Equiv.apply_symm_apply]
  have hm : (hoFunctor.map ((pre spanSquareBoundary).app X)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy Q)) = e.hom := by
    rw [homMk_functorEdge_precomp, he, ha]
  have hpre : IsInvertibleEdge (functorEdgeOfSimplicialHomotopy
      (stableHomotopyPrecomp spanSquareBoundary Q)) := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk _)
    rw [he, ha]
    infer_instance
  let hi := pushoutSquareHomotopy_isInvertible_of_span F G hF hG Q hpre
  exact ⟨asIso (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy Q)), hm⟩

end SerrePositivity.InfinityCategories
