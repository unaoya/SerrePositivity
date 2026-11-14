module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.CoherentTransportTriangleVertex
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.RelativeTriangleLongSection
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.PointHomEdgeLift

/-!
概要：標準輸送三角形の実際の点の三角形に、終点の全 Hom の整合する三面の族を付ける。
方針：対角辺の全 Hom の族を保ち、任意の三角形の相対長辺切断で全三角形へ延長する。
規約：元の二単体と同じ長辺の族・可変終点を全パラメータで保つ。余極限性は仮定しない。
使われ方：指定輸送比較を元の全 Hom の族へ接続する際の、同じ実際の三角形の族。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
  {a b c : B _⦋0⦌} {e : B.Edge a b} {f : B.Edge b c} {g : B.Edge a c}
  (σ : SSet.Edge.CompStruct e f g) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌)

/-- 同じ二段階輸送で得た、点の三角形の終点。 -/
def transportTriangleTerminalVertex : E _⦋0⦌ :=
  (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p f).app (Opposite.op ⦋0⦌)) v).val

omit [Quasicategory B] in
/-- この終点の底は、元の二単体の終点そのもの。 -/
lemma transportTriangleTerminalVertex_projection :
    p.app (Opposite.op ⦋0⦌) (transportTriangleTerminalVertex p (e := e) (f := f) v) = c :=
  (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p f).app (Opposite.op ⦋0⦌)) v).property.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero c)

local notation "dᵀ" => transportTriangleTerminalVertex p (e := e) (f := f) v

variable (y : B _⦋0⦌)

/-- 元の対角辺全体の全 Hom の族を、同じ三角形の長辺として表示する。 -/
def transportTriangleHomLongFamily :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (p.app (Opposite.op ⦋0⦌) (dᵀ)) y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex p σ v) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionFullEdgeFamily p p (𝟙 E) (Category.id_comp p)
    (dᵀ) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleDiagonalPointEdge p σ v) y ≫
      eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex_long p σ v).symm)

/-- 元の対角辺の族と底を保って、実際の非退化な輸送三角形全体に延長した全 Hom の族。 -/
def transportTriangleHomFamily :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (p.app (Opposite.op ⦋0⦌) (dᵀ)) y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex p σ v) :=
  transportTriangleHomLongFamily p σ v y ≫
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeTriangleLongSection (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex p σ v) p

/-- 三角形の全 Hom の族を長辺へ制限すると、元の同じ対角辺の全族を回収する。 -/
lemma transportTriangleHomFamily_long :
    transportTriangleHomFamily p σ v y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex p σ v) (stdSimplex.δ (1 : Fin 3)) =
        transportTriangleHomLongFamily p σ v y := by
  rw [transportTriangleHomFamily, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeTriangleLongSection_long,
    Category.comp_id]

/-- この族の底は、元の長辺の底の全族を同じ底の三角形へ延長したもの。 -/
lemma transportTriangleHomFamily_base :
    transportTriangleHomFamily p σ v y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex p σ v) p =
        transportTriangleHomLongFamily p σ v y ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex p σ v) p ≫
            _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.triangleLongCosliceSection (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex p σ v ≫ p) := by
  rw [transportTriangleHomFamily, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeTriangleLongSection_base]

/-- 可変終点は、同じ二段階輸送の終点における元の全 Hom の族そのもの。 -/
lemma transportTriangleHomFamily_endpoint :
    transportTriangleHomFamily p σ v y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex p σ v) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationPointHomFamily p (dᵀ) y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p y := by
  rw [transportTriangleHomFamily, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeTriangleLongSection_projection,
    transportTriangleHomLongFamily, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnder_eqToHom_projection (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex_long p σ v).symm]
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_id, Category.id_comp] using
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionFullEdgeFamily_endpoint p p (𝟙 E) (Category.id_comp p)
      (dᵀ) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleDiagonalPointEdge p σ v) y

/-- 全 Hom の三角形族の可変終点は、同じ指定終点 y の fiber 内に留まる。 -/
lemma transportTriangleHomFamily_fixed :
    (transportTriangleHomFamily p σ v y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex p σ v)) ≫ p = SSet.const y := by
  rw [transportTriangleHomFamily_endpoint, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
