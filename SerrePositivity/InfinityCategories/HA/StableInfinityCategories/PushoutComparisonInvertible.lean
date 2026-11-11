module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitHomotopyInvertible
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PushoutSquareHomotopyLift

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：押し出し四角形間のホモトピーは span への制限が可逆なら全体も可逆。
方針：標準 join 同型で普遍余錐の判定へ移し、逆同型で元へ戻す。
規約：両端の押し出し性のみを使う。使われ方：実際の比較四角形の可逆性。 -/
lemma pushoutSquareHomotopy_isInvertible_of_span {X : SSet.{u}} [Quasicategory X]
    (F G : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare G)
    (Q : SSet.Homotopy F G)
    (hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary Q))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy Q) := by
  let J := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom Q
  have hJ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy J) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeHomotopy_isInvertible_of_precomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone G) hF hG J
    exact hQ
  have hi := hJ.map ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv).app X)
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorEdgeOfSimplicialHomotopy_precomp] at hi
  have ha := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homMk_functorEdge_precomp_inv_hom_arrow _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso Q
  change IsIso (Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy Q))).hom
  rw [← ha]
  exact hi

/-- 概要：指定した span の関手同型は押し出し四角形の関手同型へ延長できる。
方針：同型の順射を辺で表して延長し、前補題でその延長を可逆と認証する。
規約：制限した順射の h の類を厳密に保持する。使われ方：cofiber 図式の同型輸送。 -/
lemma exists_pushoutSquareFunctorIso_lift_span {X : SSet.{u}} [Quasicategory X]
    (F G : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare G)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan G)) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G,
      (hoFunctor.map ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app X)).toFunctor.map d.hom = e.hom := by
  obtain ⟨a, ha⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan G)) e.hom
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge a
  obtain ⟨Q, hQ⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_pushoutSquareHomotopy_lift_span F G hF hG H
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary Q) = a := by
    apply SSet.Truncated.Edge.ext
    change SSet.yonedaEquiv (curry ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ▷ (Δ[1] : SSet.{u})) ≫ Q.h)) = a.edge
    rw [hQ]
    change SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm a.edge))) = a.edge
    rw [curry_uncurry, Equiv.apply_symm_apply]
  have hm : (hoFunctor.map ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app X)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy Q)) = e.hom := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homMk_functorEdge_precomp, he, ha]
  have hpre : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary Q)) := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk _)
    rw [he, ha]
    infer_instance
  let hi := pushoutSquareHomotopy_isInvertible_of_span F G hF hG Q hpre
  exact ⟨asIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy Q)), hm⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
