module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.TransportTriangleHomParameters
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialFiberEdgePiZero
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconePointHomFamily

/-!
概要：指定余極限余錐からの輸送三角形と、その終点の全 Hom 比較を元の図式上で構成する。
方針：coslice 射影の始対象の fiber 頂点へ、同じ三角形と評価固定の円柱を適用する。
規約：パラメータは元の指定終点 z からの全 Hom。輸送終点の余極限性は仮定しない。
使われ方：部分余極限 span の左右を、同じ共通余錐と同じ終点の Hom で比較する。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  {b z : X _⦋0⦌} {e : X.Edge c.vertex b} {f : X.Edge b z} {g : X.Edge c.vertex z}
  (σ : SSet.Edge.CompStruct e f g) (y : X _⦋0⦌)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p

/-- 元の共通余錐を、その頂点上の fiber の同じ点として保持する。 -/
def coconeTransportTriangleInitialVertex : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q c.vertex) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialFiberVertexAt q c c.vertex rfl
local notation "v₀" => coconeTransportTriangleInitialVertex c

/-- 同じ標準二段階輸送で得た、元の図式上の実際の終点余錐。 -/
def coconeTransportTriangleTerminal : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportTriangleTerminalVertex q (e := e) (f := f) v₀

/-- この実際の余錐の頂点は、元の二単体の指定終点 z そのもの。 -/
lemma coconeTransportTriangleTerminal_vertex :
    (coconeTransportTriangleTerminal c (e := e) (f := f)).vertex = z :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportTriangleTerminalVertex_projection q (e := e) (f := f) v₀

/-- 指定した終点からの同じ Hom パラメータ上での、輸送終点余錐の全 Hom の族。 -/
def coconeTransportTrianglePointHomFamily : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft z y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p y :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportTrianglePointHomNormalized q (e := e) (f := f) v₀ y

/-- この族は、同じ実際の終点余錐の元の全 Hom の族をパラメータだけ移したもの。 -/
lemma coconeTransportTrianglePointHomFamily_eq :
    coconeTransportTrianglePointHomFamily c (e := e) (f := f) y =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportTriangleHomParameterIso q (e := e) (f := f) v₀ y).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily (coconeTransportTriangleTerminal c (e := e) (f := f)) y := rfl

/-- 同じパラメータ上の、実際の三角形全体を通した中間 Hom の族。 -/
def coconeTransportTriangleInitialHomFamily :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft z y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialTotal q c y :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportTriangleInitialHomNormalized q σ v₀ y

/-- 中間 Hom の評価は、元の図式上の同じ全 Hom の族そのもの。 -/
lemma coconeTransportTriangleInitialHomFamily_evaluation :
    coconeTransportTriangleInitialHomFamily c σ y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q c y =
      coconeTransportTrianglePointHomFamily c (e := e) (f := f) y :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportTriangleInitialHomNormalized_evaluation q σ v₀ y

/-- 元の共通余錐の始対象性による、評価を固定する同じ中間 Hom 円柱。 -/
def coconeTransportTriangleInitialComparison : SSet.Homotopy
    (coconeTransportTrianglePointHomFamily c (e := e) (f := f) y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialSection q c hc y)
    (coconeTransportTriangleInitialHomFamily c σ y) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportTriangleInitialHomNormalizedComparison q σ v₀ y hc

/-- 実際の余錐空間の全 Hom の族の評価は、比較円柱の全時刻で固定される。 -/
lemma coconeTransportTriangleInitialComparison_evaluation :
    (coconeTransportTriangleInitialComparison c hc σ y).h ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q c y = fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft z y) Δ[1] ≫
        coconeTransportTrianglePointHomFamily c (e := e) (f := f) y :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportTriangleInitialHomNormalizedComparison_evaluation q σ v₀ y hc

/-- 元の共通余錐の Hom 比較を、同じ実際の三角形全体の族と結ぶ円柱。 -/
def coconeTransportTriangleHomComparison : SSet.Homotopy
    (coconeTransportTrianglePointHomFamily c (e := e) (f := f) y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpaceHomComparison c hc y)
    (coconeTransportTriangleInitialHomFamily c σ y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y).hom) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportTriangleInitialHomNormalizedHomotopy q σ v₀ y hc

/-- 公開した Hom 比較も、評価を固定した同じ中間円柱の像を厳密に保持する。 -/
lemma coconeTransportTriangleHomComparison_projection :
    (coconeTransportTriangleHomComparison c hc σ y).h =
      (coconeTransportTriangleInitialComparison c hc σ y).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y).hom :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportTriangleInitialHomNormalizedHomotopy_projection q σ v₀ y hc

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
