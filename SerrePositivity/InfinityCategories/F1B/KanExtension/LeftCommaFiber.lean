module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftComma
public import SerrePositivity.InfinityCategories.F1B.Fibrations.VertexFiberPostIso
public import SerrePositivity.InfinityCategories.Core.VertexFiberOpposite

/-!
概要：oriented fiber product の fiber を反転した関手の comma の fiber の反転として表示する。
方針：fiber と反転の同型に、二重反転の底の同型を合成する。
規約：fiber の表示自体は quasicategory 性を要求しない。
使われ方：一般の関手に沿う Kan 拡張の局所添字との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：oriented fiber product の c 上の fiber は反転した comma の固定始域の fiber の反転。
方針：二つの標準の fiber の同型を合成する。
規約：この同型は通常の join を使う slice との同値をまだ含まない。
使われ方：δ(k)→c を表す局所添字へ図式を移す。 -/
def kanLeftCommaFiberIso {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    (unitCommaFiber (SSet.opFunctor.map δ) (SSet.opObjEquiv.symm c)).op ≅
      vertexFiber (kanLeftCommaProjection δ) c :=
  vertexFiberOpIso (unitCommaSource (SSet.opFunctor.map δ)) (SSet.opObjEquiv.symm c) ≪≫
    SerrePositivity.InfinityCategories.F1B.vertexFiberPostIso (SSet.opFunctor.map (unitCommaSource (SSet.opFunctor.map δ)))
      (SSet.opFunctorCompOpFunctorIso.app C)
      (SSet.opObjEquiv.symm (SSet.opObjEquiv.symm c))

end SerrePositivity.InfinityCategories.F1B
