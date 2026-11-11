module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.VertexFiberMapFiber

/-!
概要：coherent な錐の slice 内の pinched Hom を比較 span の strict fiber として表示する。
方針：slice の頂点への right fibration に一般の写像空間の span の fiber の同型を適用する。
規約：任意の coherent な錐を扱い、strict な通常の錐に制限しない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の主比較の slice 側。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：任意の錐は、その頂点上の slice 射影の fiber の具体的な点を与える。
方針：slice の射影による錐の頂点の定義を使う。
規約：単体集合の quasicategory 性は不要。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の比較ファイバーの底の coherent な錐のデータ。 -/
def coneVertexFiberPoint {K X : SSet.{u}} {p : K ⟶ X} (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) d.vertex).obj (Opposite.op ⦋0⦌) :=
  ⟨d, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero d.vertex).symm⟩

/-- 概要：錐の slice 内の pinched Hom は始点評価の比較 span の strict fiber と厳密に同型。
方針：一般の span の始点評価の fiber の同型を、錐の頂点への slice 射影へ適用する。
規約：比較対象の錐 d・c は任意の join の錐。導来ファイバーへの移送は別工程。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の主比較の写像空間側の回収。 -/
noncomputable def conePinchedHom_mappingEvaluationFiberIso {K X : SSet.{u}}
    {p : K ⟶ X} (d c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) d c ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) c d.vertex)
        (coneVertexFiberPoint d) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingEvaluationFiberIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) c d.vertex
    (coneVertexFiberPoint d)).symm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
