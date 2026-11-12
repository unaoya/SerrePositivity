module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FiberHomotopyProjection
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionComparisonIso

/-! # Suspension の対象比較を図式上で持ち上げる

概要：Σ の対象比較同型は suspension 図式間の同型の終点評価として表せる。
方針：S3 と同じ始点の fiber 内の二頂点と同じ終対象比較を用いる。
規約：S3 の既存の対象比較同型の定義を変更しない。
使われ方：S4 の標準比較との一致と接続射の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：Σ の構成で選ばれた始点 x 上の suspension 図式の頂点。
方針：始点評価の選んだ逆射を x に適用する。
規約：S3 と同じ選択。使われ方：対象比較の始域。 -/
def suspensionSourceSectionVertex {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagrams X) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramSourceEquivalence X).inv.app (Opposite.op ⦋0⦌) x

/-- 概要：選んだ図式の始点評価は指定した x である。
方針：選んだ逆射の厳密な切断の式を零次で評価する。
規約：厳密な頂点の等式。使われ方：始点の fiber への持ち上げ。 -/
lemma suspensionSourceSectionVertex_source {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0).app (Opposite.op ⦋0⦌)
      (suspensionSourceSectionVertex x) = x :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramSourceEquivalence_inv_source X) (Opposite.op ⦋0⦌)) x

/-- 概要：選んだ図式と指定 suspension は始点評価の fiber 内の比較から同型になる。
方針：S3 と同じ二頂点の終対象比較を fiber の包含で送る。
規約：始域は S3 の選択した逆射の値。使われ方：対象比較の自然性の検査。 -/
def SuspensionSquare.sourceDiagramObjIso {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {x : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    (SSet.HomotopyCategory.mk (suspensionSourceSectionVertex x) :
      hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagrams X)) ≅ SSet.HomotopyCategory.mk s.diagramVertex := by
  let p := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan p x
  let v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x) _⦋0⦌ := ⟨suspensionSourceSectionVertex x, by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact suspensionSourceSectionVertex_source x⟩
  let w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x) _⦋0⦌ := ⟨s.diagramVertex, by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact (s.diagramVertex_evaluation 0 0).trans s.source_eq⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso (hc.isTerminalVertex v) (hc.isTerminalVertex w))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p x)

/-- 概要：図式の対象比較の始点での像は始点 x の恒等射である。
方針：fiber の射が基底で恒等になることを使う。
規約：端点の表示を Arrow の等式に含める。使われ方：標準比較との照合。 -/
lemma SuspensionSquare.sourceDiagramObjIso_source_arrow {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] {x : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    Arrow.mk ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0)).toFunctor.map
      s.sourceDiagramObjIso.hom) = Arrow.mk (𝟙 (SSet.HomotopyCategory.mk x)) := by
  let p := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan p x
  let v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x) _⦋0⦌ := ⟨suspensionSourceSectionVertex x, by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact suspensionSourceSectionVertex_source x⟩
  let w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x) _⦋0⦌ := ⟨s.diagramVertex, by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact (s.diagramVertex_evaluation 0 0).trans s.source_eq⟩
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.vertexFiberHo_projection_arrow p x
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso (hc.isTerminalVertex v) (hc.isTerminalVertex w)).hom

/-- 概要：図式の対象比較を終点で評価すると S3 の対象比較同型になる。
方針：同じ fiber の二頂点の同じ同型を二つの合成射で写す構成を照合する。
規約：既存の suspensionFunctorObjIso をそのまま使う。
使われ方：S3 と S4 の対象比較の一致。 -/
lemma SuspensionSquare.sourceDiagramObjIso_target {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {x : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 1 1)).toFunctor.mapIso s.sourceDiagramObjIso =
      s.suspensionFunctorObjIso := by
  apply Iso.ext
  rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
