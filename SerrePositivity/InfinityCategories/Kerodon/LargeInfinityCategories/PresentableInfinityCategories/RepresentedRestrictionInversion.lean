module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContravariantContinuity
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Opposite
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InvertibleEdge
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorIsoConstantEdges

/-!
概要：制限前層の表現対象の全 Hom は元の関手が反転する辺を反転する。
方針：元の辺の反転と持ち上げを全表現同型へ通す。
規約：任意の同値な辺ではなく指定した元の辺の像の可逆性を証明する。
使われ方：反映から得た表現対象の局所性の検証。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：辺の像を反転して持ち上げる操作は、反対関手の持ち上げによる像と一致する。
方針：同じ一単体と両端の表示を比較する。
規約：元の辺の両端を厳密に保持する。
使われ方：表現された制限前層の反転条件の計算。 -/
lemma uliftEdgeOp_map {X Y : SSet.{u + 1}} (L : X ⟶ Y) {x y : X _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj X) x y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u + 1, u + 2} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e)).map
      ((truncation 2).map ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map L))) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp (e.map ((truncation 2).map L))) := by
  apply Truncated.Edge.ext
  rfl

/-- 概要：制限前層を表現する元の全 Hom 関手は L が反転する元の辺を反転する。
方針：同じ辺の反転像を F と指定宇宙変更で写し、全表現同型で可逆性を反映する。
規約：F の連続性や表現対象の局所性は仮定しない。
使われ方：反映された表現対象の局所性の最後の写像空間判定。 -/
lemma representedRestriction_inverts_op_edge {X Y : SSet.{u + 1}}
    [Quasicategory X] [Quasicategory Y] (L : X ⟶ Y) (F : Y.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (z : X _⦋0⦌)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity z)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map L ≫ F) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram))
    {x y : X _⦋0⦌} (e : Truncated.Edge (X := (truncation 2).obj X) x y)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map L))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u + 1, u + 2} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e)).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity z))) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.functorIso_map_isInvertible_of_map h
  have hu : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (SSet.uliftFunctor.{u + 2, u + 1}).obj Y.op)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u + 1, u + 2} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e)).map
      ((truncation 2).map ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map L)))) := by
    rw [uliftEdgeOp_map]
    exact he.op.ulift
  have hv := (hu.map ((SSet.uliftFunctor.{u + 2, u + 1}).map F)).map
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram
  have hm : (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u + 1, u + 2} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e)).map
      ((truncation 2).map ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map L)))).map
        ((truncation 2).map ((SSet.uliftFunctor.{u + 2, u + 1}).map F))).map
          ((truncation 2).map _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u + 1, u + 2} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e)).map
        ((truncation 2).map ((SSet.uliftFunctor.{u + 2, u + 1}).map
          (SSet.opFunctor.map L ≫ F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram)) := by
    apply Truncated.Edge.ext
    rfl
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (congrArg Truncated.Edge.edge hm)).mp hv

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
