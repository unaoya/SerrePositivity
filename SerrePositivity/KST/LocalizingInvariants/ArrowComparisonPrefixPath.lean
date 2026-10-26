module

public import SerrePositivity.KST.LocalizingInvariants.ArrowIsoRealization
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorPrismFiber
public import SerrePositivity.InfinityCategories.Stable.SuspensionDiagramArrows

/-!
概要：前段の全比較の指定成分を共有する、次辺の実可逆比較を構成する。
方針：同じ成分辺を四角形の縦辺に指定し、一点関手評価の厳密同型で全共有経路を回収する。
規約：共有経路の一致を追加入力にせず、元の比較と四辺の可換性から証明する。
使われ方：c5 の実右分数から有限単体の全比較を貼り合わせる工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 次辺の可逆比較を構成し、前段の指定点上の全経路と厳密に一致させる。 -/
lemma exists_arrowComparison_preservingPrefixPath {K X : SSet.{u}} [Quasicategory X]
    {F G : K ⟶ X}
    (a : SSet.Edge (X := (ihom K).obj X) (functorVertex F) (functorVertex G))
    (j : (Δ[0] : SSet.{u}) ⟶ K) {z z' : X _⦋0⦌}
    (f : SSet.Edge (F.app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv j)) z)
    (g : SSet.Edge (G.app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv j)) z')
    (w : SSet.Edge z z')
    (ha : IsInvertibleEdge a.toTruncated) (hw : IsInvertibleEdge w.toTruncated)
    (hc : Truncated.HomotopyCategory.homMk f.toTruncated ≫
        Truncated.HomotopyCategory.homMk w.toTruncated =
      Truncated.HomotopyCategory.homMk (functorEdgeAt a (SSet.yonedaEquiv j)).toTruncated ≫
        Truncated.HomotopyCategory.homMk g.toTruncated) :
    ∃ b : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[1] : SSet.{u})).obj X))
      (functorVertex (SSet.yonedaEquiv.symm f.edge))
      (functorVertex (SSet.yonedaEquiv.symm g.edge)),
      IsInvertibleEdge (X := (ihom (Δ[1] : SSet.{u})).obj X) b ∧
      SSet.yonedaEquiv.symm b.edge ≫ (pre (stdSimplex.δ (1 : Fin 2))).app X =
        SSet.yonedaEquiv.symm a.edge ≫ (pre j).app X := by
  let c := functorEdgeAt a (SSet.yonedaEquiv j)
  have hci : IsInvertibleEdge c.toTruncated := by
    exact (isInvertibleEdge_congr (e := a.toTruncated.map ((truncation 2).map
      (evaluateFunctorAt (Y := X) (SSet.yonedaEquiv j)))) (f := c.toTruncated) rfl).mp
      (ha.map (evaluateFunctorAt (Y := X) (SSet.yonedaEquiv j)))
  obtain ⟨H, h0, h1⟩ := exists_arrowHomotopy_of_homMk_comm
    f.toTruncated g.toTruncated c.toTruncated w.toTruncated hc
  refine ⟨functorEdgeOfSimplicialHomotopy H,
    arrowHomotopy_isInvertible_of_endpointPaths H c.toTruncated w.toTruncated hci hw h0 h1,
    ?_⟩
  change SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry H.h)) ≫ _ = _
  rw [Equiv.symm_apply_apply, curry_pre_app, h0]
  apply (cancel_mono (pointFunctorEvaluationIso X).hom).mp
  change curry (snd (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm c.edge) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) =
    (SSet.yonedaEquiv.symm a.edge ≫ (pre j).app X) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  rw [curry_evaluateFunctorAt_vertex, Category.assoc, stable_pre_evaluateFunctorAt]
  simp only [← Category.assoc, lift_snd, Category.id_comp]
  have hp : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
      SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by decide
  have hj : j.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) =
      SSet.yonedaEquiv j := by
    rw [hp, ← SSet.yonedaEquiv_comp, Category.id_comp]
  rw [hj]
  change SSet.yonedaEquiv.symm
      ((evaluateFunctorAt (Y := X) (SSet.yonedaEquiv j)).app (Opposite.op ⦋1⦌) a.edge) = _
  rw [SSet.yonedaEquiv_symm_comp]

end SerrePositivity.KST.LocalizingInvariants
