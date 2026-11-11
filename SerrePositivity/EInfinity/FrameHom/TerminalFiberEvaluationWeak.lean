module

public import SerrePositivity.EInfinity.Hammock.WeakAnodyneLocalization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofTerminalEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.RoofTerminalFiberCofinality

/-!
# 終対象 fiber への実全体評価の弱同値性

概要：同じ終対象 fiber への全体評価は、その実ホモトピーを保って弱同値となる。
方針：fiber 包含の right cofinal 性と、恒等射からの実ホモトピーを反転する。
規約：元の評価・包含を使う。全空間の Kan 性や単体集合モデル構造は要求しない。
使われ方：実屋根 corner から指定次数の Kan Hom への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

lemma terminalFiberEvaluation_weak {E B : SSet.{u}} [SSet.Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (t : B.obj (Opposite.op ⦋0⦌))
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex t) (R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofTerminalEvaluation p t) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence R.evaluation := by
  let Q := AnodyneHomotopy.anodyneQ
  have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.roofLeftFibration_terminalFiber_isRightCofinal p t ht).isWeakHomotopyEquivalence
  have : IsIso (Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p t)) := Hammock.anodyneQ_map_isIso_of_weak _ hi
  have h := AnodyneHomotopy.map_homotopy_eq Q SSet.anodyneExtensions.Q_inverts R.homotopy
  have hc : IsIso (Q.map R.evaluation ≫ Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p t)) := by
    rw [← Q.map_comp, ← h]
    infer_instance
  exact AnodyneWeakDetection.isWeakHomotopyEquivalence _
    ((isIso_comp_right_iff _ _).1 hc)

end SerrePositivity.EInfinity.FrameHom
