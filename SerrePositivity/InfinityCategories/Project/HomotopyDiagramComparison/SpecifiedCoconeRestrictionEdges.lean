module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathVertexEdge
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PartialColimitSpecifiedPathCocone

/-!
概要：指定経路で構成した余錐の両制限を fiber の点として計算し、右修正経路自身の辺を保持する。
方針：経路付き貼り合わせの射の式を零単体で評価し、経路の辺の自然性で境界への像を計算する。
規約：右修正の辺は別の代表へ選び直さない。使われ方：共通 end の経路の整合性の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p))

/-- 固定終点の余錐空間の制限は、包含後に元の余錐の制限そのものになる。 -/
lemma coconeRestrictionFiber_vertex_val {K L X : SSet.{u}} {F : K ⟶ X}
    (a : L ⟶ K) (y : X _⦋0⦌) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y) _⦋0⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap F a y).app (Opposite.op ⦋0⦌) v).val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.restrict v.val a := by
  rfl

/-- 指定経路で作った余錐を、指定した元の span 頂点上の fiber の点として保持する。 -/
def partialColimitSpecifiedFiberVertex : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
      g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC).vertex) _⦋0⦌ :=
  SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedBoundaryFamily hp p c hc dB dC)

/-- 左制限の fiber の点は、実際の左脚で輸送した元の左余錐。 -/
lemma partialColimitSpecifiedFiberVertex_left :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p i _).app (Opposite.op ⦋0⦌)
        (partialColimitSpecifiedFiberVertex hp p c hc dB dC) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportedCoconeVertex dB (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg c hc f (i ≫ p) rfl dB
        g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC) := by
  have h := congrArg SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedBoundaryFamily_left hp p c hc dB dC)
  rw [SSet.yonedaEquiv_comp] at h
  exact h.trans (SSet.yonedaEquiv.apply_symm_apply _)

/-- 右制限の fiber の点は、指定した修正経路の終点。 -/
lemma partialColimitSpecifiedFiberVertex_right :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p j _).app (Opposite.op ⦋0⦌)
        (partialColimitSpecifiedFiberVertex hp p c hc dB dC) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 1).app (Opposite.op ⦋0⦌)
        (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedBoundaryCorrection hp p c hc dB dC)) := by
  have h := congrArg SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedBoundaryFamily_right hp p c hc dB dC)
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp] at h
  exact h

/-- 右修正経路の始点は、実際の右脚で輸送した元の右余錐。 -/
lemma partialColimitSpecifiedCorrection_zero :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0).app (Opposite.op ⦋0⦌)
        (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedBoundaryCorrection hp p c hc dB dC)) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportedCoconeVertex dC (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
        g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC) := by
  have h := congrArg SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeBoundaryPathCorrection_zero hp p _
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportedCoconeVertex dC
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
          g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC)))
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanBoundaryPath c hc f (i ≫ p) rfl dB
        g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanBoundaryPath_zero c hc f (i ≫ p) rfl dB
        g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC))
  rw [SSet.yonedaEquiv_comp] at h
  exact h.trans (SSet.yonedaEquiv.apply_symm_apply _)

/-- 指定した右修正経路自身の、元の右輸送像から貼った余錐の右制限への辺。 -/
def partialColimitSpecifiedCorrectionEdge :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (j ≫ p) _).Edge
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportedCoconeVertex dC (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
        g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p j _).app (Opposite.op ⦋0⦌)
        (partialColimitSpecifiedFiberVertex hp p c hc dB dC)) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathVertexEdge
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedBoundaryCorrection hp p c hc dB dC))).edge,
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathVertexEdge _).src_eq.trans
      (partialColimitSpecifiedCorrection_zero hp p c hc dB dC),
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathVertexEdge _).tgt_eq.trans
      (partialColimitSpecifiedFiberVertex_right hp p c hc dB dC).symm⟩

/-- 修正辺の境界への像は、普遍 span の二単体から作った指定境界経路自身の辺。 -/
lemma partialColimitSpecifiedCorrectionEdge_projection :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber (j ≫ p) g (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
          g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC).vertex).app (Opposite.op ⦋1⦌)
        (partialColimitSpecifiedCorrectionEdge hp p c hc dB dC).edge =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (SSet.yonedaEquiv
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanBoundaryPath c hc f (i ≫ p) rfl dB
          g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC)).val := by
  have h := congrArg SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedBoundaryCorrection_projection hp p c hc dB dC)
  rw [SSet.yonedaEquiv_comp] at h
  have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathVertexEdge_map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber (j ≫ p) g (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
        g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC).vertex)
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedBoundaryCorrection hp p c hc dB dC))
  have he := congrArg (fun v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (f ≫ (i ≫ p))
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
        g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC).vertex)) _⦋0⦌ ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge v.val) h
  exact hh.trans he

/-- 右修正経路自身の辺を、実際の余錐の右制限を終点とする coslice の辺として表示する。 -/
def partialColimitSpecifiedCorrectionCosliceEdge :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (j ≫ p)).Edge
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportedCoconeVertex dC (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
        g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC)).val
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC).restrict j) :=
  ⟨(partialColimitSpecifiedCorrectionEdge hp p c hc dB dC).edge.val,
    congrArg Subtype.val (partialColimitSpecifiedCorrectionEdge hp p c hc dB dC).src_eq,
    (congrArg Subtype.val (partialColimitSpecifiedCorrectionEdge hp p c hc dB dC).tgt_eq).trans
      (coconeRestrictionFiber_vertex_val j _
        (partialColimitSpecifiedFiberVertex hp p c hc dB dC))⟩

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
