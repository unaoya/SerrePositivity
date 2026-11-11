module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteLegTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofSliceOneSimplexOfTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FullSubcomplexEdgeLift

/-! # 有限同時細分の頂点ごとの単一実脚

概要：辺から独立に固定した脚三角形を、同じ共通始点からの実 over 辺へ戻す。
方針：零面で終点を固定し、対角面で共通始点を照合して全部分複体へ上げる。
規約：辺に現れない頂点にも同じ方法で脚を供給する。使われ方：共通頂点錐の構成。
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
variable {C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f} {m : ℕ} {e : Fin m → K _⦋1⦌}
variable (T : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement A D C e)

omit [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] in
/-- 固定脚三角形の零面は、元の図式頂点の指定分母辺。 -/
lemma DGVerdierFiniteEdgeRefinement.legTriangle_map_face0 (v : K _⦋0⦌) :
    stdSimplex.δ (0 : Fin 3) ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement.legTriangle A D T v) =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) (f.app _ v).val).edge := by
  rw [stdSimplex.δ_comp_yonedaEquiv_symm,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement.legTriangle_face0 A D T v]
  rfl

/-- 固定脚三角形から回収した、辺に依存しない実 over 一単体。 -/
def DGVerdierFiniteEdgeRefinement.vertexLegSimplex (v : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))) _⦋1⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceOneSimplexOfTriangle _ (f.app _ v).val
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement.legTriangle A D T v))
    (DGVerdierFiniteEdgeRefinement.legTriangle_map_face0 A D T v)

omit [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] in
/-- 回収した頂点脚の三角形は、固定した細分脚三角形そのもの。 -/
lemma DGVerdierFiniteEdgeRefinement.vertexLegSimplex_triangle (v : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle _ (DGVerdierFiniteEdgeRefinement.vertexLegSimplex A D T v) =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement.legTriangle A D T v) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceOneSimplexOfTriangle_triangle _ _ _ _

/-- 全頂点脚の始点は、同じ共通閉細分頂点。 -/
lemma DGVerdierFiniteEdgeRefinement.vertexLegSimplex_source (v : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 1 (DGVerdierFiniteEdgeRefinement.vertexLegSimplex A D T v) =
      T.commonApex.val := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge_injective
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_leg _ _ 1,
    DGVerdierFiniteEdgeRefinement.vertexLegSimplex_triangle A D T v,
    stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement.legTriangle_face1 A D T v

omit [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] in
/-- 全頂点脚の終点は、元の指定図式頂点。 -/
lemma DGVerdierFiniteEdgeRefinement.vertexLegSimplex_target (v : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 0 (DGVerdierFiniteEdgeRefinement.vertexLegSimplex A D T v) =
      (f.app _ v).val := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge_injective
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_leg _ _ 0,
    DGVerdierFiniteEdgeRefinement.vertexLegSimplex_triangle A D T v,
    stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement.legTriangle_face0 A D T v

/-- 同じ共通閉分母から全頂点へ向かう、頂点ごとの単一の実分母脚。 -/
def DGVerdierFiniteEdgeRefinement.vertexLeg (v : K _⦋0⦌) :
    Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet))
      T.commonApex (f.app _ v) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullSubcomplexEdgeLift _ _ _ (DGVerdierFiniteEdgeRefinement.vertexLegSimplex A D T v)
    (DGVerdierFiniteEdgeRefinement.vertexLegSimplex_source A D T v)
    (DGVerdierFiniteEdgeRefinement.vertexLegSimplex_target A D T v)

/-- 頂点ごとの実脚を、一つの共通閉分母を持つ実頂点錐へ束ねる。 -/
def DGVerdierFiniteEdgeRefinement.vertexCone : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f where
  denominator := T.commonDenominator
  leg := DGVerdierFiniteEdgeRefinement.vertexLeg A D T
  leg_mem v := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource_edge_mem A D P x
    (DGVerdierFiniteEdgeRefinement.vertexLeg A D T v).edge

end SerrePositivity.InfinityCategories.Project.DerivedCategories
