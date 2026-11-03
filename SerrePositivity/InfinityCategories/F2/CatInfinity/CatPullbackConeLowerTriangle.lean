module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackConeUpperTriangle
public import SerrePositivity.InfinityCategories.F1.CatInfinity.ConeHomotopyLowerTriangle

/-!
概要：引き戻し錐の下側の比較三角形の三辺。
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
/-- 概要：下側の三角形の最後の辺は切断の指定成分。
方針：全錐の辺の式と指定関手の回収を合わせる。
規約：一次単体自体の厳密な等式。
使われ方：同じ対角関手を通る二つの三角形の同型の構成。 -/
lemma catPullbackConeLowerTriangle_zero (p : A ⟶ C) (q : B ⟶ C)
    (i : AsSmall.{u} WalkingCospan) :
    CatInfinity.δ 0 (coneHomotopyLowerTriangle (catPullbackConeHomotopy p q)
      (ULift.up (ComposableArrows.mk₀ i))) =
      (coherentNerveEdge ((catPullbackReplacementNatTrans p q).app i)).edge :=
  (coneHomotopyLowerTriangle_zero _ _).trans (catPullbackConeHomotopy_diagramEdge p q i)
/-- 概要：下側の三角形の長辺は同じ対角関手。
方針：全錐の辺の式と指定関手の回収を合わせる。
規約：一次単体自体の厳密な等式。
使われ方：同じ対角関手を通る二つの三角形の同型の構成。 -/
lemma catPullbackConeLowerTriangle_one (p : A ⟶ C) (q : B ⟶ C)
    (i : AsSmall.{u} WalkingCospan) :
    CatInfinity.δ 1 (coneHomotopyLowerTriangle (catPullbackConeHomotopy p q)
      (ULift.up (ComposableArrows.mk₀ i))) =
      (coherentNerveEdge (catPullbackConeDiagonal p q i)).edge :=
  (coneHomotopyLowerTriangle_one _ _).trans (catPullbackConeDiagonal_edge p q i).symm
/-- 概要：下側の三角形の最初の辺は元の錐の脚の関手。
方針：全錐の辺の式と指定関手の回収を合わせる。
規約：一次単体自体の厳密な等式。
使われ方：同じ対角関手を通る二つの三角形の同型の構成。 -/
lemma catPullbackConeLowerTriangle_two (p : A ⟶ C) (q : B ⟶ C)
    (i : AsSmall.{u} WalkingCospan) :
    CatInfinity.δ 2 (coneHomotopyLowerTriangle (catPullbackConeHomotopy p q)
      (ULift.up (ComposableArrows.mk₀ i))) =
      (coherentNerveEdge (catPullbackConeFunctorLeg p q i)).edge :=
  (coneHomotopyLowerTriangle_two _ _).trans (catPullbackConeFunctorLeg_edge p q i).symm

end SerrePositivity.InfinityCategories.F2
