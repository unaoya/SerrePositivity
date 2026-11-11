module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeLegTriangleShape
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconePointHomDiagramFamily

/-!
概要：元の余錐の合成二単体全体に、同じ選択済みの普遍全 Hom の族を制限する。
方針：実際の join 形状と終端の式を、全余錐族の部分図式制限に適用する。
規約：元の二単体と同じ終端係数を保持。使われ方：native span の三角形全族との比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
  {a b : K _⦋0⦌} (e : K.Edge a b) (y : X _⦋0⦌)
local notation "v" => stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)

/-- 元の図式の辺と余錐の脚の、同じ実際の合成二単体の図式。 -/
def coconeLegTriangleDiagram : (Δ[2] : SSet.{u}) ⟶ X :=
  SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLegCompStruct c e).simplex

omit [Quasicategory X] in
/-- 元の二単体の最後の頂点は、同じ元の余錐頂点図式である。 -/
lemma coconeLegTriangleDiagram_tip : v ≫ coconeLegTriangleDiagram c e = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram c :=
  (congrArg (v ≫ ·) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeLegTriangleShape_diagram e c).symm).trans
    ((Category.assoc v (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeLegTriangleShape e) c.val).symm.trans
      ((congrArg (· ≫ c.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeLegTriangleShape_tip e)).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram_inr c)))

/-- 元の実際の合成二単体の下にある、同じ選択済みの普遍全 Hom の族。 -/
def coconeLegTriangleHomFamily :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft c.vertex y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (coconeLegTriangleDiagram c e) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomDiagramFamily c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeLegTriangleShape e) (coconeLegTriangleDiagram c e)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeLegTriangleShape_diagram e c) y

/-- 同じ普遍二単体族は、元の固定終点 y 上に留まる。 -/
lemma coconeLegTriangleHomFamily_fixed :
    coconeLegTriangleHomFamily c e y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (coconeLegTriangleDiagram c e) =
      SSet.const y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomDiagramFamily_fixed c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeLegTriangleShape e) (coconeLegTriangleDiagram c e)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeLegTriangleShape_diagram e c) y

/-- 元の普遍二単体族を、固定終点 fiber の族として保持する。 -/
def coconeLegTriangleHomFiberFamily :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft c.vertex y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (coconeLegTriangleDiagram c e) y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomDiagramFiberFamily c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeLegTriangleShape e) (coconeLegTriangleDiagram c e)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeLegTriangleShape_diagram e c) y

/-- 固定終点の包含後は、元の同じ普遍二単体族そのものである。 -/
lemma coconeLegTriangleHomFiberFamily_ι :
    coconeLegTriangleHomFiberFamily c e y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (coconeLegTriangleDiagram c e)) y =
      coconeLegTriangleHomFamily c e y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomDiagramFiberFamily_ι c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeLegTriangleShape e) (coconeLegTriangleDiagram c e)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeLegTriangleShape_diagram e c) y

/-- 元の二単体の終端係数は、同じ普遍全 Hom の点図式表示に厳密に一致する。 -/
lemma coconeLegTriangleHomFiberFamily_terminal :
    coconeLegTriangleHomFiberFamily c e y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber (coconeLegTriangleDiagram c e) v
          (coconeLegTriangleDiagram_tip c e) y =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) c y).inv :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomDiagramFiberFamily_terminal c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeLegTriangleShape e)
    (coconeLegTriangleDiagram c e) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeLegTriangleShape_diagram e c) y v
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeLegTriangleShape_tip e) (coconeLegTriangleDiagram_tip c e)

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
