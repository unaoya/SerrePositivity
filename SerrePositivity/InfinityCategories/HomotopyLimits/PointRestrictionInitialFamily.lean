module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PointHomEdgeLift
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialDiagramHomFamily

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [LeftFibration p] (q : F ⟶ B) [InnerFibration q]
  (r : E ⟶ F) (hr : r ≫ q = p) (d : E _⦋0⦌)
  {c : F _⦋0⦌} (e : F.Edge c (r.app (Opposite.op ⦋0⦌) d)) (y : B _⦋0⦌)
local notation "t" => SSet.yonedaEquiv.symm e.edge
local notation "W" => pointRestrictionFullEdgeFamily p q r hr d e y

/-- 比較辺全体の元の全 Hom の族は、底の同じ可変終点上に留まる。 -/
lemma pointRestrictionFullEdgeFamily_fixed :
    (W ≫ sliceUnderProjection t) ≫ q = SSet.const y := by
  rw [pointRestrictionFullEdgeFamily_endpoint, Category.assoc, Category.assoc,
    vertexFiberι_comp, SSet.comp_const, SSet.comp_const]

/-- 全辺族の初期制限を、同じ指定比較辺の始点の初期 Hom 空間へ戻す。 -/
def pointRestrictionInitialHomFamily :
    pinchedHomLeft (p.app (Opposite.op ⦋0⦌) d) y ⟶ leftFibrationInitialTotal q c y :=
  initialDiagramHomFamily q c t (stdSimplex.δ (1 : Fin 2)) e.δ_one_yonedaEquiv_symm y W
    (pointRestrictionFullEdgeFamily_fixed p q r hr d e y)

/-- 初期 Hom 空間への包含後は、元の全辺族の初期頂点制限そのもの。 -/
lemma pointRestrictionInitialHomFamily_ι :
    pointRestrictionInitialHomFamily p q r hr d e y ≫
        vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm c) ≫ q) y =
      W ≫ normalizedCoconeRestriction t (stdSimplex.δ (1 : Fin 2))
        e.δ_one_yonedaEquiv_symm := by
  rw [pointRestrictionInitialHomFamily, initialDiagramHomFamily, vertexFiberLift_ι]

/-- 初期制限の評価は、元の全 Hom の族の同じ枝への制限そのもの。 -/
lemma pointRestrictionInitialHomFamily_evaluation :
    pointRestrictionInitialHomFamily p q r hr d e y ≫ leftFibrationInitialEvaluation q c y =
      leftFibrationPointHomFamily p d y ≫ vertexFiberMap p q r hr y := by
  rw [pointRestrictionInitialHomFamily, initialDiagramHomFamily_evaluation]
  apply vertexFiber_hom_ext q y
  rw [vertexFiberLift_ι, pointRestrictionFullEdgeFamily_endpoint]
  exact (Category.assoc _ _ _).symm

/-- 底の通常 Hom 表示は、同じ指定比較辺の実際の前合成そのもの。 -/
lemma pointRestrictionInitialHomFamily_projection :
    pointRestrictionInitialHomFamily p q r hr d e y ≫ leftFibrationInitialProjection q c y ≫
        (leftFibrationInitialBaseIso q c y).hom =
      initialRestrictionHomPrecomposition p q r hr d e y := by
  have hbase : pointRestrictionInitialHomFamily p q r hr d e y ≫
      leftFibrationInitialProjection q c y =
      pointRestrictionBaseHom p q r hr d e y ≫ cosliceEdgeFiberPrecomposition (t ≫ q)
        (SSet.yonedaEquiv.symm c ≫ q) (stdSimplex.δ (0 : Fin 2) ≫ (t ≫ q))
        (by rw [← Category.assoc, e.δ_one_yonedaEquiv_symm]) rfl y := by
    apply vertexFiber_hom_ext (sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ q)) y
    simp only [Category.assoc]
    rw [cosliceEdgeFiberPrecomposition_ι]
    rw [pointRestrictionInitialHomFamily, initialDiagramHomFamily_base,
      pointRestrictionFullEdgeFamily_base]
    simp only [pointRestrictionBaseEdgeFamily, cosliceEdgePrecompositionAt,
      cosliceEdgePrecomposition, normalizedCoconeRestriction, eqToHom_refl,
      Category.id_comp, Category.assoc]
  rw [← Category.assoc, hbase, Category.assoc]
  exact pointRestrictionBaseHom_precomposition p q r hr d e y

end
end SerrePositivity.InfinityCategories.HomotopyLimits
