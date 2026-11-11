module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CatPullbackCone
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeLeg
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.EdgeEquiv

/-!
概要：Cat_∞ の引き戻し錐の各脚を実際の関手へ読み戻す。
方針：錐の頂点と図式の値の等式で辺の端点を合わせる。
規約：既存の coherent nerve の射の全単射を再利用する。
使われ方：各脚と元の引き戻し射影との関手同型。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]

/-- 概要：引き戻し錐の脚を指定された QCat 対象間の辺として表示する。
方針：錐の頂点と strict coherent 図式の頂点の式を使う。
規約：元の脚の一単体は変更しない。
使われ方：実際の小さい圏の関手への読み戻し。 -/
def catPullbackConeLegEdge (p : A ⟶ C) (q : B ⟶ C) (i : AsSmall.{u} WalkingCospan) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u}.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackObject p q))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackDiagram p q).obj i)) where
  edge := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.catPullbackCone p q) (ULift.up (ComposableArrows.mk₀ i))).edge
  src_eq := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.catPullbackCone p q) _).src_eq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.catPullbackCone_vertex p q)
  tgt_eq := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.catPullbackCone p q) _).tgt_eq.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_vertex _ i)
/-- 概要：Cat_∞ の引き戻し錐の脚を小さい quasicategory 間の関手へ戻す。
方針：端点を固定した coherent nerve の辺を通常の射へ戻す。
規約：任意の cospan の添字で同じ構成を使う。
使われ方：二射影と指定可換性の具体的な比較。 -/
def catPullbackConeFunctorLeg (p : A ⟶ C) (q : B ⟶ C) (i : AsSmall.{u} WalkingCospan) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackObject p q ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackDiagram p q).obj i :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom (catPullbackConeLegEdge p q i)
/-- 概要：読み戻した関手は元の錐の脚の一単体を厳密に回収する。
方針：coherent nerve の辺と射の往復則を使う。
規約：ホモトピー類の一致には弱めない。
使われ方：ホモトピー圏の正方形を関手の合成の式へ送る。 -/
lemma catPullbackConeFunctorLeg_edge (p : A ⟶ C) (q : B ⟶ C)
    (i : AsSmall.{u} WalkingCospan) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (catPullbackConeFunctorLeg p q i)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.catPullbackCone p q) (ULift.up (ComposableArrows.mk₀ i))).edge := by
  exact congrArg SSet.Edge.edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_hom (catPullbackConeLegEdge p q i))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
