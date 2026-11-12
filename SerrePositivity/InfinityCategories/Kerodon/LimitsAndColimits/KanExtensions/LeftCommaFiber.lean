module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftComma
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexFiberPostIso
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexFiberOpposite

/-!
概要：oriented fiber product の fiber を反転した関手の comma の fiber の反転として表示する。
方針：fiber と反転の同型に、二重反転の底の同型を合成する。
規約：fiber の表示自体は quasicategory 性を要求しない。
使われ方：一般の関手に沿う Kan 拡張の局所添字との比較。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：oriented fiber product の c 上の fiber は反転した comma の固定始域の fiber の反転。
方針：二つの標準の fiber の同型を合成する。
規約：この同型は通常の join を使う slice との同値をまだ含まない。
使われ方：δ(k)→c を表す局所添字へ図式を移す。 -/
def kanLeftCommaFiberIso {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber (SSet.opFunctor.map δ) (SSet.opObjEquiv.symm c)).op ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) c :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.vertexFiberOpIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource (SSet.opFunctor.map δ)) (SSet.opObjEquiv.symm c) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiberPostIso (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource (SSet.opFunctor.map δ)))
      (SSet.opFunctorCompOpFunctorIso.app C)
      (SSet.opObjEquiv.symm (SSet.opObjEquiv.symm c))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
