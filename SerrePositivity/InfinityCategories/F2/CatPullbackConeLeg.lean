module

public import SerrePositivity.InfinityCategories.F2.CatPullbackCone
public import SerrePositivity.InfinityCategories.F2.NativeConeLeg
public import SerrePositivity.InfinityCategories.F1.CoherentEdgeEquiv

/-!
概要：Cat_∞ の引き戻し錐の各脚を実際の関手へ読み戻す。
方針：錐の頂点と図式の値の等式で辺の端点を合わせる。
規約：既存の coherent nerve の射の全単射を再利用する。
使われ方：各脚と元の引き戻し射影との関手同型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]

/-- 概要：引き戻し錐の脚を指定された QCat 対象間の辺として表示する。
方針：錐の頂点と strict coherent 図式の頂点の式を使う。
規約：元の脚の一単体は変更しない。
使われ方：実際の小さい圏の関手への読み戻し。 -/
def catPullbackConeLegEdge (p : A ⟶ C) (q : B ⟶ C) (i : AsSmall.{u} WalkingCospan) :
    CatInfinity.{u}.Edge (coherentVertex (catPullbackObject p q))
      (coherentVertex ((catPullbackDiagram p q).obj i)) where
  edge := (nativeConeLeg (catPullbackCone p q) (ULift.up (ComposableArrows.mk₀ i))).edge
  src_eq := (nativeConeLeg (catPullbackCone p q) _).src_eq.trans (catPullbackCone_vertex p q)
  tgt_eq := (nativeConeLeg (catPullbackCone p q) _).tgt_eq.trans
    (HomotopyLimits.strictCoherentDiagram_vertex _ i)
/-- 概要：Cat_∞ の引き戻し錐の脚を小さい quasicategory 間の関手へ戻す。
方針：端点を固定した coherent nerve の辺を通常の射へ戻す。
規約：任意の cospan の添字で同じ構成を使う。
使われ方：二射影と指定可換性の具体的な比較。 -/
def catPullbackConeFunctorLeg (p : A ⟶ C) (q : B ⟶ C) (i : AsSmall.{u} WalkingCospan) :
    catPullbackObject p q ⟶ (catPullbackDiagram p q).obj i :=
  coherentNerveEdgeToHom (catPullbackConeLegEdge p q i)
/-- 概要：読み戻した関手は元の錐の脚の一単体を厳密に回収する。
方針：coherent nerve の辺と射の往復則を使う。
規約：ホモトピー類の一致には弱めない。
使われ方：ホモトピー圏の正方形を関手の合成の式へ送る。 -/
lemma catPullbackConeFunctorLeg_edge (p : A ⟶ C) (q : B ⟶ C)
    (i : AsSmall.{u} WalkingCospan) :
    (coherentNerveEdge (catPullbackConeFunctorLeg p q i)).edge =
      (nativeConeLeg (catPullbackCone p q) (ULift.up (ComposableArrows.mk₀ i))).edge := by
  exact congrArg SSet.Edge.edge (coherentNerveEdge_hom (catPullbackConeLegEdge p q i))

end SerrePositivity.InfinityCategories.F2
