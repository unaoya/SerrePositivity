module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointHomRestrictionComparison

/-!
概要：任意の余錐の全 Hom の族を、底の指定された辺の合成族を保って比較辺全体へ持ち上げる。
方針：既存の始点固定族の底を計算し、終点への相対 coslice 制限を持ち上げる。
規約：底の合成の切断を保持し、後から別の前合成へ置き換えない。
使われ方：指定右修正三角形へ全 Hom の族を延長する際の長辺側の入力。
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

/-- 比較辺の底に沿う全 Hom の合成族。底の coslice の既存の切断そのものを使う。 -/
def pointRestrictionBaseEdgeFamily :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (p.app (Opposite.op ⦋0⦌) d) y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm e.edge ≫ q) :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionBaseHom p q r hr d e y ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection
      (stdSimplex.δ (0 : Fin 2) ≫ (SSet.yonedaEquiv.symm e.edge ≫ q))) y) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSection (SSet.yonedaEquiv.symm e.edge ≫ q)

/-- 底の全辺の族を終点へ制限すると、全 Hom の元の始点固定族の底と厳密に一致する。 -/
lemma pointRestrictionBaseEdgeFamily_target :
    pointRestrictionBaseEdgeFamily p q r hr d e y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (SSet.yonedaEquiv.symm e.edge ≫ q) (stdSimplex.δ (0 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionEdgeFamily p q r hr d e y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge) q := by
  rw [pointRestrictionBaseEdgeFamily, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSection_target,
    Category.comp_id, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionBaseHom_ι]

/-- 任意の元の頂点の全 Hom を、底の選んだ合成族を保持する比較辺全体の族へ持ち上げる。 -/
def pointRestrictionFullEdgeFamily [InnerFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (p.app (Opposite.op ⦋0⦌) d) y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm e.edge) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.exists_relativeEdgeCosliceLift (SSet.yonedaEquiv.symm e.edge) q
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionEdgeFamily p q r hr d e y)
    (pointRestrictionBaseEdgeFamily p q r hr d e y)
    (pointRestrictionBaseEdgeFamily_target p q r hr d e y).symm).choose

/-- 持ち上げた比較辺全体の族は、終点側で元の全 Hom の族を回収する。 -/
lemma pointRestrictionFullEdgeFamily_target [InnerFibration q] :
    pointRestrictionFullEdgeFamily p q r hr d e y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (SSet.yonedaEquiv.symm e.edge) (stdSimplex.δ (0 : Fin 2)) =
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionEdgeFamily p q r hr d e y :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.exists_relativeEdgeCosliceLift (SSet.yonedaEquiv.symm e.edge) q
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionEdgeFamily p q r hr d e y)
    (pointRestrictionBaseEdgeFamily p q r hr d e y)
    (pointRestrictionBaseEdgeFamily_target p q r hr d e y).symm).choose_spec.1

/-- 比較辺全体の族の底は、元の Hom の前合成を定義する合成族そのもの。 -/
lemma pointRestrictionFullEdgeFamily_base [InnerFibration q] :
    pointRestrictionFullEdgeFamily p q r hr d e y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (SSet.yonedaEquiv.symm e.edge) q =
        pointRestrictionBaseEdgeFamily p q r hr d e y :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.exists_relativeEdgeCosliceLift (SSet.yonedaEquiv.symm e.edge) q
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionEdgeFamily p q r hr d e y)
    (pointRestrictionBaseEdgeFamily p q r hr d e y)
    (pointRestrictionBaseEdgeFamily_target p q r hr d e y).symm).choose_spec.2

/-- 比較辺全体の族の可変終点は、元の全 Hom の族の関手による像そのもの。 -/
lemma pointRestrictionFullEdgeFamily_endpoint [InnerFibration q] :
    pointRestrictionFullEdgeFamily p q r hr d e y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm e.edge) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationPointHomFamily p d y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q r hr y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q y := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection (SSet.yonedaEquiv.symm e.edge)
    (stdSimplex.δ (0 : Fin 2)), ← Category.assoc, pointRestrictionFullEdgeFamily_target,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionEdgeFamily_endpoint]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
