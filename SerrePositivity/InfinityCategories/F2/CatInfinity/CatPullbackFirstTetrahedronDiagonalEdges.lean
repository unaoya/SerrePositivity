module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackFirstTetrahedronConeEdges

/-!
概要：最初の比較三単体の恒等辺と対角関手の辺。
方針：指定円柱の側面と境界射の同定を合わせる。
規約：元の同型と一次単体を保持する。
使われ方：最初の比較三単体の指定同型の合成則。
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
/-- 概要：最初の比較三単体の辺 01 は指定された関手の coherent 辺。
方針：上側の比較三角形または strict な錐の面の式を使う。
規約：一次単体そのものの厳密な等式。
使われ方：四面の合成則の六つの境界関手を固定する。 -/
lemma catPullbackFirstTetrahedron_edge01 (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    CatInfinity.δ 2 (CatInfinity.δ 2 (catPullbackConeTetrahedron p q f 0)) =
      (coherentNerveEdge (𝟙 (catPullbackObject p q))).edge :=
  (congrArg (CatInfinity.δ 2) (catPullbackConeTetrahedron_upper_long p q f)).trans
    (catPullbackConeUpperTriangle_two p q j)
/-- 概要：最初の比較三単体の辺 02 は指定された関手の coherent 辺。
方針：上側の比較三角形または strict な錐の面の式を使う。
規約：一次単体そのものの厳密な等式。
使われ方：四面の合成則の六つの境界関手を固定する。 -/
lemma catPullbackFirstTetrahedron_edge02 (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    CatInfinity.δ 1 (CatInfinity.δ 3 (catPullbackConeTetrahedron p q f 0)) =
      (coherentNerveEdge (catPullbackConeDiagonal p q i)).edge :=
  (congrArg (CatInfinity.δ 1) (catPullbackConeTetrahedron_upper_first p q f)).trans
    (catPullbackConeUpperTriangle_one p q i)
/-- 概要：最初の比較三単体の辺 03 は指定された関手の coherent 辺。
方針：上側の比較三角形または strict な錐の面の式を使う。
規約：一次単体そのものの厳密な等式。
使われ方：四面の合成則の六つの境界関手を固定する。 -/
lemma catPullbackFirstTetrahedron_edge03 (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    CatInfinity.δ 1 (CatInfinity.δ 2 (catPullbackConeTetrahedron p q f 0)) =
      (coherentNerveEdge (catPullbackConeDiagonal p q j)).edge :=
  (congrArg (CatInfinity.δ 1) (catPullbackConeTetrahedron_upper_long p q f)).trans
    (catPullbackConeUpperTriangle_one p q j)

end SerrePositivity.InfinityCategories.F2
