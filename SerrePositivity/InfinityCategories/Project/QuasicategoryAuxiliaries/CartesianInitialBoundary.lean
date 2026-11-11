module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CocartesianTerminalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Opposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialBoundary
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexFiberOpposite

/-! # 反転した輸送による相対始対象

概要：反転した射が cocartesian な輸送を持つとき、fiber の始対象は相対始点境界を充填する。
方針：fiber とその始対象を反転し、相対終対象の境界充填を使って戻す。
規約：輸送の仮定を型に明示する。使われ方：余錐の制限射の相対充填への接続。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：反転した射の cocartesian 輸送があれば、fiber の始対象は相対境界充填を持つ。
方針：fiber の反転同型で終対象へ移し、終点境界の充填を反転する。
規約：元・標的は quasicategory、反転した射の輸送を仮定する。
使われ方：余錐の族の始対象から相対始対象への判定。 -/
lemma initialBoundaryLifting_of_isInitialVertex_fiber_op {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration (SSet.opFunctor.map p)]
    (b : B _⦋0⦌) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌) (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p x.val := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialBoundaryLifting_of_terminalBoundaryLifting_op
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalBoundaryLifting_of_isTerminalVertex_fiber (SSet.opFunctor.map p)
    (SSet.opObjEquiv.symm b)
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.vertexFiberOpIso p b).hom.app (Opposite.op ⦋0⦌) (SSet.opObjEquiv.symm x))
    (hx.isTerminalVertex_opFiber p b)

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
