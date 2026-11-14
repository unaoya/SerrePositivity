module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierClosedLegTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofSliceOneSimplexOfTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.FullSubcomplexEdgeLift

/-! # 閉始点細分の頂点ごとの単一実脚と頂点錐

概要：固定細分脚三角形を、同じ共通始点から各図式頂点への実分母 over 辺へ戻す。
方針：三角形の両面から端点を照合し、同じ台を全部分複体へ持ち上げる。
規約：辺の充填に依存しない。使われ方：高次の全辺錐の共通頂点脚。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}
variable {C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f}
variable (R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement A D C)

omit [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] in
/-- 固定脚三角形の零面は、元の図式頂点の指定分母辺。 -/
lemma DGVerdierClosedVertexRefinement.legTriangle_map_face0 (v : K _⦋0⦌) :
    stdSimplex.δ (0 : Fin 3) ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.legTriangle A D R v) =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) (f.app _ v).val).edge := by
  rw [stdSimplex.δ_comp_yonedaEquiv_symm,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.legTriangle_face0 A D R v]
  rfl

/-- 固定脚三角形から回収した、辺に依存しない実 over 一単体。 -/
def DGVerdierClosedVertexRefinement.vertexLegSimplex (v : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))) _⦋1⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceOneSimplexOfTriangle _ (f.app _ v).val
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.legTriangle A D R v))
    (DGVerdierClosedVertexRefinement.legTriangle_map_face0 A D R v)

omit [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] in
/-- 回収した頂点脚の三角形は、固定した細分脚三角形そのもの。 -/
lemma DGVerdierClosedVertexRefinement.vertexLegSimplex_triangle (v : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle _ (DGVerdierClosedVertexRefinement.vertexLegSimplex A D R v) =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.legTriangle A D R v) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceOneSimplexOfTriangle_triangle _ _ _ _

/-- 全頂点脚の始点は、同じ共通閉細分頂点。 -/
lemma DGVerdierClosedVertexRefinement.vertexLegSimplex_source (v : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 1 (DGVerdierClosedVertexRefinement.vertexLegSimplex A D R v) =
      R.commonApex.val := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge_injective
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_leg _ _ 1,
    DGVerdierClosedVertexRefinement.vertexLegSimplex_triangle A D R v,
    stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.legTriangle_face1 A D R v

omit [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] in
/-- 全頂点脚の終点は、元の指定図式頂点。 -/
lemma DGVerdierClosedVertexRefinement.vertexLegSimplex_target (v : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 0 (DGVerdierClosedVertexRefinement.vertexLegSimplex A D R v) =
      (f.app _ v).val := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge_injective
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_leg _ _ 0,
    DGVerdierClosedVertexRefinement.vertexLegSimplex_triangle A D R v,
    stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.legTriangle_face0 A D R v

/-- 同じ共通閉分母から全頂点へ向かう、頂点ごとの単一の実分母脚。 -/
def DGVerdierClosedVertexRefinement.vertexLeg (v : K _⦋0⦌) :
    Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet))
      R.commonApex (f.app _ v) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullSubcomplexEdgeLift _ _ _ (DGVerdierClosedVertexRefinement.vertexLegSimplex A D R v)
    (DGVerdierClosedVertexRefinement.vertexLegSimplex_source A D R v)
    (DGVerdierClosedVertexRefinement.vertexLegSimplex_target A D R v)

/-- 頂点ごとの実脚を、一つの共通閉分母を持つ実頂点錐へ束ねる。 -/
def DGVerdierClosedVertexRefinement.vertexCone : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f where
  denominator := R.commonDenominator
  leg := DGVerdierClosedVertexRefinement.vertexLeg A D R
  leg_mem v := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource_edge_mem A D P x
    (DGVerdierClosedVertexRefinement.vertexLeg A D R v).edge

end SerrePositivity.InfinityCategories.Project.DerivedCategories
