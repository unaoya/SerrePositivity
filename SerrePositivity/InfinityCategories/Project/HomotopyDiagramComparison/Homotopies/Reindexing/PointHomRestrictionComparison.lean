module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.Reindexing.PointHomRestrictionFamily

/-!
概要：任意の頂点からの全 Hom の族の制限を、実際の比較辺による前合成と照合する。
方針：底の点図式の表示変更を fiber に移し、始対象の Hom 比較の相対ホモトピーを適用する。
規約：元の頂点の始対象性は要求しない。使われ方：貼った余錐の各枝の普遍点の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (q : F ⟶ B)
  (r : E ⟶ F) (hr : r ≫ q = p) (d : E _⦋0⦌)
  {c : F _⦋0⦌} (e : F.Edge c (r.app (Opposite.op ⦋0⦌) d)) (y : B _⦋0⦌)

/-- 元の全 Hom のパラメータを、比較辺の底の終点の点図式で表示する。 -/
def pointRestrictionBaseHom :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (p.app (Opposite.op ⦋0⦌) d) y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (stdSimplex.δ (0 : Fin 2) ≫ (SSet.yonedaEquiv.symm e.edge ≫ q)) y :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso p d y).inv ≫
    eqToHom (congrArg (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection t) y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionEdgeBase_eq p q r hr d e))

omit [Quasicategory B] in
/-- この表示の包含は、全 Hom の族を関手で写した底への射影と一致。 -/
lemma pointRestrictionBaseHom_ι :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionEdgeFamily p q r hr d e y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge) q =
      pointRestrictionBaseHom p q r hr d e y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection
          (stdSimplex.δ (0 : Fin 2) ≫ (SSet.yonedaEquiv.symm e.edge ≫ q))) y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionEdgeFamily_base]
  have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.stableCosliceFiberChange_ι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionEdgeBase_eq p q r hr d e) y
  simpa only [pointRestrictionBaseHom, Category.assoc] using
    congrArg (fun f ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso p d y).inv ≫ f) hh.symm

omit [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] in
/-- 底の表示を戻すと、比較辺による左 Hom の既存の前合成そのものを得る。 -/
lemma pointRestrictionBaseHom_precomposition :
    pointRestrictionBaseHom p q r hr d e y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFiberPrecomposition (SSet.yonedaEquiv.symm e.edge ≫ q)
          (SSet.yonedaEquiv.symm c ≫ q)
          (stdSimplex.δ (0 : Fin 2) ≫ (SSet.yonedaEquiv.symm e.edge ≫ q))
          (by rw [← Category.assoc, e.δ_one_yonedaEquiv_symm]) rfl y ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionHomPrecomposition p q r hr d e y := by
  have hh := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cosliceEdgeFiberPrecomposition_points (SSet.yonedaEquiv.symm e.edge ≫ q)
    (by rw [← Category.assoc, e.δ_one_yonedaEquiv_symm])
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionEdgeBase_eq p q r hr d e).symm
    (by rw [← Category.assoc, e.δ_one_yonedaEquiv_symm]) rfl
    rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionEdgeBase_eq p q r hr d e) y
  simp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointCoconeMappingIso, eqToIso_refl, Iso.refl_hom, eqToIso.hom] at hh
  erw [Category.comp_id] at hh
  simpa only [pointRestrictionBaseHom, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionHomPrecomposition,
    Category.assoc] using congrArg (fun f ↦
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso p d y).inv ≫ f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y).hom) hh.symm

/-- 任意の元の頂点の全 Hom の族を制限し始対象の Hom 比較で測ると、実際の辺の前合成とホモトピック。 -/
lemma pointHomFamily_restriction_comparison_homotopy [InnerFibration q] (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex c) :
    Nonempty (SSet.Homotopy
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationPointHomFamily p d y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q r hr y) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialHomComparison q c hc y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionHomPrecomposition p q r hr d e y)) := by
  have H := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialHomComparison_pointFamily_homotopy q c
    (SSet.yonedaEquiv.symm e.edge) e.δ_one_yonedaEquiv_symm y
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionEdgeFamily p q r hr d e y)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionEdgeFamily_fixed p q r hr d e y)
    (pointRestrictionBaseHom p q r hr d e y)
    (pointRestrictionBaseHom_ι p q r hr d e y) hc
  rwa [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionEdgeFamily_vertexFiberLift, pointRestrictionBaseHom_precomposition] at H

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
