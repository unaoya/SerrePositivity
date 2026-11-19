module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.ArrowIsoRealization
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorPrismFiber
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SuspensionDiagramArrows

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants

/-- 次辺の可逆比較を構成し、前段の指定点上の全経路と厳密に一致させる。 -/
lemma exists_arrowComparison_preservingEndpointPaths {K X : SSet.{u}} [Quasicategory X]
    {F G : K ⟶ X}
    (a : SSet.Edge (X := (ihom K).obj X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
    (j : (Δ[0] : SSet.{u}) ⟶ K) {z z' : X _⦋0⦌}
    (f : SSet.Edge (F.app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv j)) z)
    (g : SSet.Edge (G.app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv j)) z')
    (w : SSet.Edge z z')
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge a.toTruncated) (hw : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge w.toTruncated)
    (hc : Truncated.HomotopyCategory.homMk f.toTruncated ≫
        Truncated.HomotopyCategory.homMk w.toTruncated =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgeAt a (SSet.yonedaEquiv j)).toTruncated ≫
        Truncated.HomotopyCategory.homMk g.toTruncated) :
    ∃ b : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[1] : SSet.{u})).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm f.edge))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm g.edge)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (ihom (Δ[1] : SSet.{u})).obj X) b ∧
      SSet.yonedaEquiv.symm b.edge ≫ (pre (stdSimplex.δ (1 : Fin 2))).app X =
        SSet.yonedaEquiv.symm a.edge ≫ (pre j).app X ∧
      SSet.yonedaEquiv.symm b.edge ≫ (pre (stdSimplex.δ (0 : Fin 2))).app X =
        curry (snd (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm w.edge) := by
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgeAt a (SSet.yonedaEquiv j)
  have hci : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge c.toTruncated := by
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := a.toTruncated.map ((truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (SSet.yonedaEquiv j)))) (f := c.toTruncated) rfl).mp
      (ha.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (SSet.yonedaEquiv j)))
  obtain ⟨H, h0, h1⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.exists_arrowHomotopy_of_homMk_comm
    f.toTruncated g.toTruncated c.toTruncated w.toTruncated hc
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.arrowHomotopy_isInvertible_of_endpointPaths H c.toTruncated w.toTruncated hci hw h0 h1,
    ?_, ?_⟩
  · change SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry H.h)) ≫ _ = _
    rw [Equiv.symm_apply_apply, curry_pre_app, h0]
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso X).hom).mp
    change curry (snd (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm c.edge) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) =
      (SSet.yonedaEquiv.symm a.edge ≫ (pre j).app X) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
    simp only [← Category.assoc, lift_snd, Category.id_comp]
    have hp : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
        SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by decide
    have hj : j.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) =
        SSet.yonedaEquiv j := by
      rw [hp, ← SSet.yonedaEquiv_comp, Category.id_comp]
    rw [hj]
    change SSet.yonedaEquiv.symm
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (SSet.yonedaEquiv j)).app (Opposite.op ⦋1⦌) a.edge) = _
    rw [SSet.yonedaEquiv_symm_comp]
  · change SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry H.h)) ≫ _ = _
    rw [Equiv.symm_apply_apply, curry_pre_app, h1]
    rfl

/-- 前段の指定全経路を回収する従来の入口。 -/
lemma exists_arrowComparison_preservingPrefixPath {K X : SSet.{u}} [Quasicategory X]
    {F G : K ⟶ X}
    (a : SSet.Edge (X := (ihom K).obj X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
    (j : (Δ[0] : SSet.{u}) ⟶ K) {z z' : X _⦋0⦌}
    (f : SSet.Edge (F.app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv j)) z)
    (g : SSet.Edge (G.app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv j)) z')
    (w : SSet.Edge z z')
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge a.toTruncated) (hw : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge w.toTruncated)
    (hc : Truncated.HomotopyCategory.homMk f.toTruncated ≫
        Truncated.HomotopyCategory.homMk w.toTruncated =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgeAt a (SSet.yonedaEquiv j)).toTruncated ≫
        Truncated.HomotopyCategory.homMk g.toTruncated) :
    ∃ b : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[1] : SSet.{u})).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm f.edge))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm g.edge)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (ihom (Δ[1] : SSet.{u})).obj X) b ∧
      SSet.yonedaEquiv.symm b.edge ≫ (pre (stdSimplex.δ (1 : Fin 2))).app X =
        SSet.yonedaEquiv.symm a.edge ≫ (pre j).app X := by
  obtain ⟨b, hi, hp, _⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.exists_arrowComparison_preservingEndpointPaths a j f g w ha hw hc
  exact ⟨b, hi, hp⟩

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
