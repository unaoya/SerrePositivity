module

public import SerrePositivity.InfinityCategories.F2.ConeHomotopyDiagonalEdge
public import SerrePositivity.InfinityCategories.F2.CatPullbackConeLeg
public import SerrePositivity.InfinityCategories.F2.CatPullbackConeComparisonEdges

/-!
概要：引き戻し錐の指定対角辺から回収した関手。
方針：指定円柱の辺と既存の coherent nerve の辺の往復則を使う。
規約：新たな三角形や辺の代表を選択しない。
使われ方：各脚の関手同型を指定比較円柱から直接構成する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
/-- 概要：錐の頂点と置換後の図式の値を両端とする指定対角辺。
方針：全錐の辺の式と指定関手の回収を合わせる。
規約：一次単体自体の厳密な等式。
使われ方：同じ対角関手を通る二つの三角形の同型の構成。 -/
def catPullbackConeDiagonalEdge (p : A ⟶ C) (q : B ⟶ C) (i : AsSmall.{u} WalkingCospan) :
    CatInfinity.{u}.Edge (coherentVertex (catPullbackObject p q))
      (coherentVertex ((catPullbackReplacementDiagram p q).obj i)) where
  edge := (coneHomotopyDiagonalEdge (catPullbackConeHomotopy p q)
    (ULift.up (ComposableArrows.mk₀ i))).edge
  src_eq := (coneHomotopyDiagonalEdge (catPullbackConeHomotopy p q) _).src_eq.trans
    (catPullbackCone_vertex p q)
  tgt_eq := (coneHomotopyDiagonalEdge (catPullbackConeHomotopy p q) _).tgt_eq.trans
    (HomotopyLimits.strictCoherentDiagram_vertex _ i)
/-- 概要：同じ指定対角辺を小さい圏の関手へ読み戻す。
方針：全錐の辺の式と指定関手の回収を合わせる。
規約：一次単体自体の厳密な等式。
使われ方：同じ対角関手を通る二つの三角形の同型の構成。 -/
def catPullbackConeDiagonal (p : A ⟶ C) (q : B ⟶ C) (i : AsSmall.{u} WalkingCospan) :
    catPullbackObject p q ⟶ (catPullbackReplacementDiagram p q).obj i :=
  coherentNerveEdgeToHom (catPullbackConeDiagonalEdge p q i)
/-- 概要：読み戻した関手の辺は元の指定対角辺に一致。
方針：全錐の辺の式と指定関手の回収を合わせる。
規約：一次単体自体の厳密な等式。
使われ方：同じ対角関手を通る二つの三角形の同型の構成。 -/
lemma catPullbackConeDiagonal_edge (p : A ⟶ C) (q : B ⟶ C) (i : AsSmall.{u} WalkingCospan) :
    (coherentNerveEdge (catPullbackConeDiagonal p q i)).edge =
      (coneHomotopyDiagonalEdge (catPullbackConeHomotopy p q)
        (ULift.up (ComposableArrows.mk₀ i))).edge := by
  exact congrArg SSet.Edge.edge (coherentNerveEdge_hom (catPullbackConeDiagonalEdge p q i))

end SerrePositivity.InfinityCategories.F2
