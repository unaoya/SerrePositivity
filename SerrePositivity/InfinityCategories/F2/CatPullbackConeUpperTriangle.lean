module

public import SerrePositivity.InfinityCategories.F2.CatPullbackConeDiagonal
public import SerrePositivity.InfinityCategories.F2.ConeHomotopyUpperTriangle
public import SerrePositivity.InfinityCategories.F2.StrictNativeConeLeg

/-!
概要：引き戻し錐の上側の比較三角形の三辺。
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
/-- 概要：上側の三角形の底辺は置換後の通常の脚。
方針：全錐の辺の式と指定関手の回収を合わせる。
規約：一次単体自体の厳密な等式。
使われ方：同じ対角関手を通る二つの三角形の同型の構成。 -/
lemma catPullbackConeUpperTriangle_zero (p : A ⟶ C) (q : B ⟶ C)
    (i : AsSmall.{u} WalkingCospan) :
    CatInfinity.δ 0 (coneHomotopyUpperTriangle (catPullbackConeHomotopy p q)
      (ULift.up (ComposableArrows.mk₀ i))) =
      (coherentNerveEdge ((catPullbackReplacementOrdinaryCone p q).π.app i)).edge :=
  (coneHomotopyUpperTriangle_zero _ _).trans
    (nativeConeLeg_strict (catPullbackReplacementOrdinaryCone p q) i)
/-- 概要：上側の三角形の長辺は読み戻した対角関手。
方針：全錐の辺の式と指定関手の回収を合わせる。
規約：一次単体自体の厳密な等式。
使われ方：同じ対角関手を通る二つの三角形の同型の構成。 -/
lemma catPullbackConeUpperTriangle_one (p : A ⟶ C) (q : B ⟶ C)
    (i : AsSmall.{u} WalkingCospan) :
    CatInfinity.δ 1 (coneHomotopyUpperTriangle (catPullbackConeHomotopy p q)
      (ULift.up (ComposableArrows.mk₀ i))) =
      (coherentNerveEdge (catPullbackConeDiagonal p q i)).edge :=
  (coneHomotopyUpperTriangle_one _ _).trans (catPullbackConeDiagonal_edge p q i).symm
/-- 概要：上側の三角形の最初の辺は頂点の恒等関手。
方針：全錐の辺の式と指定関手の回収を合わせる。
規約：一次単体自体の厳密な等式。
使われ方：同じ対角関手を通る二つの三角形の同型の構成。 -/
lemma catPullbackConeUpperTriangle_two (p : A ⟶ C) (q : B ⟶ C)
    (i : AsSmall.{u} WalkingCospan) :
    CatInfinity.δ 2 (coneHomotopyUpperTriangle (catPullbackConeHomotopy p q)
      (ULift.up (ComposableArrows.mk₀ i))) =
      (coherentNerveEdge (𝟙 (catPullbackObject p q))).edge :=
  (coneHomotopyUpperTriangle_two _ _).trans (catPullbackConeHomotopy_apexEdge p q)

end SerrePositivity.InfinityCategories.F2
