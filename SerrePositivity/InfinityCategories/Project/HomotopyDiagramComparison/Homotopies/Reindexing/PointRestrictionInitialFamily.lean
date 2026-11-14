module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.PointHomEdgeLift
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialDiagramHomFamily

/-!
概要：元の全 Hom の比較辺全体の族を、枝の始点の初期 Hom 空間へ移す。
方針：既存の全辺族を初期頂点へ制限し、評価と底の同じ式を回収する。
規約：指定した比較辺と全辺族を保持。使われ方：枝の Hom 比較と native 根辺の整合性。
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
  (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (q : F ⟶ B) [InnerFibration q]
  (r : E ⟶ F) (hr : r ≫ q = p) (d : E _⦋0⦌)
  {c : F _⦋0⦌} (e : F.Edge c (r.app (Opposite.op ⦋0⦌) d)) (y : B _⦋0⦌)
local notation "t" => SSet.yonedaEquiv.symm e.edge
local notation "W" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionFullEdgeFamily p q r hr d e y

/-- 比較辺全体の元の全 Hom の族は、底の同じ可変終点上に留まる。 -/
lemma pointRestrictionFullEdgeFamily_fixed :
    (W ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection t) ≫ q = SSet.const y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionFullEdgeFamily_endpoint, Category.assoc, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, SSet.comp_const]

/-- 全辺族の初期制限を、同じ指定比較辺の始点の初期 Hom 空間へ戻す。 -/
def pointRestrictionInitialHomFamily :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (p.app (Opposite.op ⦋0⦌) d) y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialTotal q c y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily q c t (stdSimplex.δ (1 : Fin 2)) e.δ_one_yonedaEquiv_symm y W
    (pointRestrictionFullEdgeFamily_fixed p q r hr d e y)

/-- 初期 Hom 空間への包含後は、元の全辺族の初期頂点制限そのもの。 -/
lemma pointRestrictionInitialHomFamily_ι :
    pointRestrictionInitialHomFamily p q r hr d e y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm c) ≫ q) y =
      W ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction t (stdSimplex.δ (1 : Fin 2))
        e.δ_one_yonedaEquiv_symm := by
  rw [pointRestrictionInitialHomFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]

/-- 初期制限の評価は、元の全 Hom の族の同じ枝への制限そのもの。 -/
lemma pointRestrictionInitialHomFamily_evaluation :
    pointRestrictionInitialHomFamily p q r hr d e y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q c y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationPointHomFamily p d y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q r hr y := by
  rw [pointRestrictionInitialHomFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily_evaluation]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q y
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionFullEdgeFamily_endpoint]
  exact (Category.assoc _ _ _).symm

/-- 底の通常 Hom 表示は、同じ指定比較辺の実際の前合成そのもの。 -/
lemma pointRestrictionInitialHomFamily_projection :
    pointRestrictionInitialHomFamily p q r hr d e y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionHomPrecomposition p q r hr d e y := by
  have hbase : pointRestrictionInitialHomFamily p q r hr d e y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionBaseHom p q r hr d e y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFiberPrecomposition (t ≫ q)
        (SSet.yonedaEquiv.symm c ≫ q) (stdSimplex.δ (0 : Fin 2) ≫ (t ≫ q))
        (by rw [← Category.assoc, e.δ_one_yonedaEquiv_symm]) rfl y := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ q)) y
    simp only [Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFiberPrecomposition_ι]
    rw [pointRestrictionInitialHomFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily_base,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionFullEdgeFamily_base]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionBaseEdgeFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgePrecompositionAt,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgePrecomposition, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction, eqToHom_refl,
      Category.id_comp, Category.assoc]
  rw [← Category.assoc, hbase, Category.assoc]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionBaseHom_precomposition p q r hr d e y

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
