module

public import SerrePositivity.KST.Spectra.SpectrumLoopEvaluationLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathIso

/-!
概要：安定性を仮定しない元の Sp の native loop 関手。
方針：loop 図式の終点評価の厳密な切断を選び、反対の角を評価する。
規約：全単体上の関手と任意の指定 loop 四角形との頂点同型を構成する。
使われ方：Sp の loop の関手性と delooping の比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- loop 図式の終点評価そのものを順方向とする実際の同値。 -/
def nativeLoopTargetEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams Sp.{u}) Sp.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1)

/-- 選択した loop 図式の族は元の終点を厳密に保つ。 -/
lemma nativeLoopTargetEquivalence_inv_target :
    nativeLoopTargetEquivalence.{u}.inv ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1 = 𝟙 Sp.{u} :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1))

/-- 元の Sp の全単体上の native loop 関手。 -/
def nativeLoop : Sp.{u} ⟶ Sp.{u} :=
  nativeLoopTargetEquivalence.inv ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 0 0

/-- 同じ終点上の loop 図式の任意の二つの族の可逆な比較。 -/
def nativeLoopDiagramFamilyIso {A : SSet.{u + 1}} (f g : A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams Sp.{u})
    (h : f ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1 = g ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfTrivialKanFibration (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1) f g h

/-- 関手としての loop の値と、指定した実際の loop 四角形の頂点の同型。 -/
def nativeLoopVertexIso {x : Sp.{u} _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (nativeLoop.app (Opposite.op ⦋0⦌) x) s.vertex := by
  let p := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan p x
  let v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x) _⦋0⦌ :=
    ⟨nativeLoopTargetEquivalence.inv.app (Opposite.op ⦋0⦌) x, by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
      exact ConcreteCategory.congr_hom (NatTrans.congr_app
        (nativeLoopTargetEquivalence_inv_target) (Opposite.op ⦋0⦌)) x⟩
  let w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x) _⦋0⦌ := ⟨s.diagramVertex, by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact (s.diagramVertex_evaluation 1 1).trans s.target_eq⟩
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso (hc.isTerminalVertex v) (hc.isTerminalVertex w))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p x ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 0 0)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (nativeLoop.app (Opposite.op ⦋0⦌) x)
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 0 0).app (Opposite.op ⦋0⦌) s.diagramVertex) at hi
  rw [s.diagramVertex_evaluation] at hi
  exact hi

end SerrePositivity.KST.Spectra.OmegaSpectrum
