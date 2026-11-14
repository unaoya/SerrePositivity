module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.WeightedConstantSimplex

/-!
概要：頂点 fiber の宇宙の持ち上げと固定頂点の等号による移送。
方針：各次数で ULift と部分型の順序を交換し、固定条件は値で移す。
規約：fiber の包含と厳密に可換な同型を用いる。
使われ方：HTT 4.2.4.1 の比較射の fiber の同値性を実際の全体の射へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 概要：持ち上げた頂点 fiber は持ち上げた射の頂点 fiber と同型。
方針：ULift と固定条件の部分型を各次数で交換する。
規約：頂点も ULift.up で同じ宇宙に持ち上げる。
使われ方：HTT 4.2.4.1 の weighted nerve の fiber の標準表示。 -/
def uliftVertexFiberIso {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((SSet.uliftFunctor.{v, u}).map p) (ULift.up b) :=
  NatIso.ofComponents (fun d ↦ Equiv.toIso {
    toFun a := ⟨ULift.up a.down.val, congrArg ULift.up a.down.property⟩
    invFun a := ULift.up ⟨a.val.down, congrArg ULift.down a.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }) (by
    intro d e α
    apply ConcreteCategory.hom_ext
    intro a
    rfl)

/-- 概要：fiber の持ち上げの同型は包含の持ち上げと厳密に可換。
方針：各次数で部分型の値と ULift の値を計算する。
規約：順方向の同型について述べる。
使われ方：HTT 4.2.4.1 の実際の fiber 射の因子分解。 -/
lemma uliftVertexFiberIso_hom_ι {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (uliftVertexFiberIso.{u, v} p b).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((SSet.uliftFunctor.{v, u}).map p) (ULift.up b) =
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) := rfl

/-- 概要：固定頂点を等号で移した fiber の包含は元の包含と同じ。
方針：頂点の等号を消去する。
規約：始域を変える同型は等号からの標準射。
使われ方：HTT 4.2.4.1 の引き戻しの fiber の端点の同定。 -/
lemma vertexFiber_endpointTransport_ι {E B : SSet.{u}} (p : E ⟶ B)
    {b b' : B _⦋0⦌} (h : b = b') :
    eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p) h) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b' = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b := by
  subst b'
  rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
