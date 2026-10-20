module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialTotalEdgeFamily

/-!
概要：実際の比較辺を前置する、同じ底の終点を持つ初期 Hom 空間間の写像。
方針：終点側の包含を相対的に延長した全辺族を、元の始点へ制限する。
規約：始点・終点の始対象性は不要。評価と底の指定した前合成を厳密に保持する。
使われ方：枝の比較円柱を共通部分の始対象 c の初期 Hom 空間へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E B : SSet.{u}} [Quasicategory B] (q : E ⟶ B) [InnerFibration q]
  {c d : E _⦋0⦌} (e : E.Edge c d) (y : B _⦋0⦌)
local notation "t" => SSet.yonedaEquiv.symm (SSet.Edge.edge e)

/-- 入力の初期 Hom の点を保ち、同じ底の比較辺を前置する写像。 -/
def initialTotalEdgePrecomposition :
    leftFibrationInitialTotal q d y ⟶ leftFibrationInitialTotal q c y :=
  initialDiagramHomFamily q c t (stdSimplex.δ (1 : Fin 2))
    (SSet.Edge.δ_one_yonedaEquiv_symm e) y (initialTotalEdgeFamily q e y)
    (initialTotalEdgeFamily_fixed q e y)

/-- 前置写像の包含後は、保持した同じ全辺族の始点への制限である。 -/
lemma initialTotalEdgePrecomposition_ι :
    initialTotalEdgePrecomposition q e y ≫
        vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm c) ≫ q) y =
      initialTotalEdgeFamily q e y ≫ normalizedCoconeRestriction t (stdSimplex.δ (1 : Fin 2))
        (SSet.Edge.δ_one_yonedaEquiv_symm e) := by
  rw [initialTotalEdgePrecomposition, initialDiagramHomFamily, vertexFiberLift_ι]

/-- 前置は、入力の可変終点を同じ fiber の点として厳密に保持する。 -/
lemma initialTotalEdgePrecomposition_evaluation :
    initialTotalEdgePrecomposition q e y ≫ leftFibrationInitialEvaluation q c y =
      leftFibrationInitialEvaluation q d y := by
  rw [initialTotalEdgePrecomposition, initialDiagramHomFamily_evaluation]
  apply vertexFiber_hom_ext q y
  rw [vertexFiberLift_ι, initialTotalEdgeFamily_endpoint]
  exact (vertexFiberMap_ι _ _ _ _ _).symm

/-- 前置の底への射影は、同じ実際の辺の底による元の前合成そのもの。 -/
lemma initialTotalEdgePrecomposition_projection :
    initialTotalEdgePrecomposition q e y ≫ leftFibrationInitialProjection q c y =
      leftFibrationInitialProjection q d y ≫ cosliceEdgeFiberPrecomposition (t ≫ q)
        (SSet.yonedaEquiv.symm c ≫ q) (SSet.yonedaEquiv.symm d ≫ q)
        (initialTotalEdgeBase_source q e) (initialTotalEdgeBase_target q e) y := by
  apply vertexFiber_hom_ext (sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ q)) y
  simp only [Category.assoc, cosliceEdgeFiberPrecomposition_ι]
  rw [initialTotalEdgePrecomposition, initialDiagramHomFamily_base, initialTotalEdgeFamily_base]
  simp only [cosliceEdgePrecompositionAt, cosliceEdgePrecomposition,
    normalizedCoconeRestriction, Category.assoc]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
