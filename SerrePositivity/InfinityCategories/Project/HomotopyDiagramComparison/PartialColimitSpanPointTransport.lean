module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PartialColimitSpanTriangles
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentTransportTriangleVertex

/-!
概要：普遍 span の左右の実際の輸送終点を、同じ fiber の二頂点として保持する。
方針：元の二つの三角形 prism を同じ始点で評価し、指定済みの同じ境界経路を制限する。
規約：両終点は同じ native な span 頂点上。経路を新たに選ばない。
使われ方：左右の全 Hom の三角形族を同じ Hom パラメータ上で照合する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {A B C : SSet.{u + 1}} {p : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (i : A ⟶ B) (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (hi : i ≫ F = p) (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F)
  (j : A ⟶ C) (G : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (hj : j ≫ G = p) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G)
  {E : SSet.{u + 1}} (q : E ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
  (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q c.vertex) _⦋0⦌)
local notation "z" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc i F hi dB j G hj dC)

/-- 左の実際の二段階輸送の終点を、元の span 頂点上の fiber の頂点として保持する。 -/
def partialColimitSpanLeftTransportVertex : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q z) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexEdge c hc i F hi dB) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg c hc i F hi dB j G hj dC)).app _ v

/-- 右の実際の二段階輸送の終点も、全く同じ span 頂点上の fiber に属する。 -/
def partialColimitSpanRightTransportVertex : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q z) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexEdge c hc j G hj dC) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg c hc i F hi dB j G hj dC)).app _ v

/-- 左の点の三角形は、元の span の左二単体を同じ始点で持ち上げたもの。 -/
def partialColimitSpanLeftTransportTriangle : (Δ[2] : SSet.{u + 1}) ⟶ E :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex q (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftTriangle c hc i F hi dB j G hj dC) v

/-- 右の点の三角形も、元の span の右二単体を同じ始点で持ち上げたもの。 -/
def partialColimitSpanRightTransportTriangle : (Δ[2] : SSet.{u + 1}) ⟶ E :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex q (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightTriangle c hc i F hi dB j G hj dC) v

/-- 左三角形は、元の左二単体を厳密に被覆する。 -/
lemma partialColimitSpanLeftTransportTriangle_projection :
    partialColimitSpanLeftTransportTriangle c hc i F hi dB j G hj dC q v ≫ q =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftTriangle c hc i F hi dB j G hj dC).simplex :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex_projection _ _ _

/-- 右三角形は、元の右二単体を厳密に被覆する。 -/
lemma partialColimitSpanRightTransportTriangle_projection :
    partialColimitSpanRightTransportTriangle c hc i F hi dB j G hj dC q v ≫ q =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightTriangle c hc i F hi dB j G hj dC).simplex :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex_projection _ _ _

/-- 元の二単体の合成比較を、同じ始点の二つの実際の終点で評価した同型。 -/
def partialColimitSpanTransportPointIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (SSet.yonedaEquiv.symm (partialColimitSpanLeftTransportVertex
        c hc i F hi dB j G hj dC q v))
      (SSet.yonedaEquiv.symm (partialColimitSpanRightTransportVertex
        c hc i F hi dB j G hj dC q v)) := by
  simpa only [partialColimitSpanLeftTransportVertex, partialColimitSpanRightTransportVertex,
    SSet.yonedaEquiv_symm_comp] using _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanTransportIso c hc i F hi dB j G hj dC q) (SSet.yonedaEquiv.symm v)

/-- 左右の終点を結ぶ経路は、指定済みの同じ全パラメータ経路の頂点での制限。 -/
def partialColimitSpanTransportPointPath :
    (Δ[0] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q z) :=
  SSet.yonedaEquiv.symm v ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanTransportPath c hc i F hi dB j G hj dC q

/-- 指定経路の始点は、同じ実際の左終点。 -/
lemma partialColimitSpanTransportPointPath_zero :
    partialColimitSpanTransportPointPath c hc i F hi dB j G hj dC q v ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0 = SSet.yonedaEquiv.symm
        (partialColimitSpanLeftTransportVertex c hc i F hi dB j G hj dC q v) := by
  rw [partialColimitSpanTransportPointPath, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanTransportPath_zero,
    SSet.yonedaEquiv_symm_comp]
  rfl

/-- 指定経路の終点は、同じ実際の右終点。 -/
lemma partialColimitSpanTransportPointPath_one :
    partialColimitSpanTransportPointPath c hc i F hi dB j G hj dC q v ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 1 = SSet.yonedaEquiv.symm
        (partialColimitSpanRightTransportVertex c hc i F hi dB j G hj dC q v) := by
  rw [partialColimitSpanTransportPointPath, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanTransportPath_one,
    SSet.yonedaEquiv_symm_comp]
  rfl

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
