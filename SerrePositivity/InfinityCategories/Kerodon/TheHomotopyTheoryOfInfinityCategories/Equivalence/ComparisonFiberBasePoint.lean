module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.KanFiberPathTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathVertices

/-!
概要：底の辺による導来 fiber の固定点の移送と、標的の同値による任意の固定点の回収。
方針：Kan 複体の辺を可逆 path として表示し、同値の逆のホモトピーを各頂点で評価する。
規約：元の比較射には fibration 性を要求しない。逆射や path の持ち上げの選択を含む。
使われ方：HTT 4.2.4.1、Kerodon 4.5.3.24（Tag 02VM）・7.5.4.6（Tag 03BB）、元の q_x と切断比較の fiber の固定点。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
noncomputable section

/-- 概要：Kan 複体の底の指定した辺の両端における任意の比較射の導来 fiber は同値。
方針：辺を可逆 path の頂点へ移し、path に沿う fiber の同値の端点を厳密に同定する。
規約：辺を入力に取り、底の両点や fiber の非空性は前提に置かない。
使われ方：Kerodon 4.5.3.24（Tag 02VM）・7.5.4.6（Tag 03BB）、同値の逆の合成と恒等射の間の固定点の移送。 -/
def comparisonFiberEdgeEquivalence {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) {b₀ b₁ : B _⦋0⦌} (e : SSet.Edge b₀ b₁) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber p b₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber p b₁) := by
  let e' : SSet.Truncated.Edge (X := (truncation 2).obj B) b₀ b₁ := e
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e' := IsGroupoid.all_isIso (C := hoFunctor.obj B)
    (SSet.Truncated.HomotopyCategory.homMk e')
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathVertex e' he
  let e₀ := eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathVertex_zero e' he))
  let e₁ := eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathVertex_one e' he))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e₀.symm).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberPathEquivalence p a).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e₁))

/-- 概要：標的の同値を後合成した比較射の任意の点上の fiber は、逆像の点の元の fiber と同値。
方針：標的の同値による実際の fiber 射を、逆の合成から恒等射への頂点の辺で移送する。
規約：固定点 b が g の厳密な像であることを要求しない。元の射 p の fibration 性も不要。
使われ方：HTT 4.2.4.1、元の end の点と同値な切断模型の任意の点の直接比較。 -/
def comparisonFiberPostInverseEquivalence {E B D : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex D]
    (p : E ⟶ B) (g : B ⟶ D) (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence g) (b : D _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber p ((Classical.choose hg).app _ b))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (p ≫ g) b) := by
  let a := (Classical.choose hg).app (Opposite.op ⦋0⦌) b
  let K := (Classical.choose_spec hg).2.some
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge K b
  change SSet.Edge (g.app (Opposite.op ⦋0⦌) a) b at e
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.comparisonFiberPost_homotopyEquivalence p g hg a).isQCatEquivalence.choose.trans
    (comparisonFiberEdgeEquivalence (p ≫ g) e)

end
end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
