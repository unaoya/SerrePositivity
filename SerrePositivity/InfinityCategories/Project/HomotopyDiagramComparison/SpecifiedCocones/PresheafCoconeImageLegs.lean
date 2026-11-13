module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.PresheafCoconeImageCones
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeWholeEdgeSquare
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeLeg

/-!
概要：指定前層余錐の元の全評価余錐間の変換として、元の全錐の実際の脚を回収する。
方針：交換評価で写した同じ全錐の頂点と底図式を厳密に読み、全一単体を保持する。
規約：元の全錐・全脚・指定余錐を変更しない。
使われ方：元の評価脚と実際の余極限頂点の脚を、全余錐の可換正方形へ入力する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の全錐を写した native 脚は、元の同じ全一単体の像。 -/
lemma nativeConeLeg_mapJoinCone_edge {K X Y : SSet.{u}} {p : K ⟶ X}
    (f : X ⟶ Y) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (k : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone f c) k).edge =
      f.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c k).edge := rfl

variable {B C K : SSet.{u}}
  {r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C}
  (q : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r) {p : K ⟶ C.op} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)

/-- 元の交換像全錐の頂点は、元の錐頂点で評価した同じ全余錐の関手頂点。 -/
lemma presheafCoconeImageCone_vertex :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeImageCone q c).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c).vertex) q).val := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeImageCone, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone_vertex, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeFlip_vertex]

/-- 元の交換像の底図式の各頂点は、同じ元の全評価余錐の関手頂点。 -/
lemma presheafCoconeImageDiagram_vertex
    (k : ((SSet.uliftFunctor.{u + 1, u}).obj K) _⦋0⦌) :
    ((SSet.uliftFunctor.{u + 1, u}).map p ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeFlip q).app (Opposite.op ⦋0⦌) k =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
          (((SSet.uliftFunctor.{u + 1, u}).map p).app (Opposite.op ⦋0⦌) k)) q).val :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeFlip_vertex q _

/-- 元の同じ全錐の実際の脚を、元の全評価余錐間の変換の代表辺として表示する。 -/
def presheafCoconeImageLeg
    (k : ((SSet.uliftFunctor.{u + 1, u}).obj K) _⦋0⦌) :
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c).vertex) q).val)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
          (((SSet.uliftFunctor.{u + 1, u}).map p).app (Opposite.op ⦋0⦌) k)) q).val) :=
  (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeImageCone q c) k)).ofEq
    (presheafCoconeImageCone_vertex q c) (presheafCoconeImageDiagram_vertex q k)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
