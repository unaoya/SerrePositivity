module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackConeTetrahedronUpperSides
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackConeSpecifiedComparison
public import SerrePositivity.InfinityCategories.F2.CatInfinity.StrictNativeConeTriangle

/-!
概要：最初の比較三単体の置換後の三辺。
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
/-- 概要：最初の比較三単体の辺 12 は指定された関手の coherent 辺。
方針：上側の比較三角形または strict な錐の面の式を使う。
規約：一次単体そのものの厳密な等式。
使われ方：四面の合成則の六つの境界関手を固定する。 -/
lemma catPullbackFirstTetrahedron_edge12 (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    CatInfinity.δ 2 (CatInfinity.δ 0 (catPullbackConeTetrahedron p q f 0)) =
      (coherentNerveEdge ((catPullbackReplacementOrdinaryCone p q).π.app i)).edge :=
  (congrArg (CatInfinity.δ 2) (catPullbackConeTetrahedron_first p q f)).trans
    (nativeConeTriangle_strict_two (catPullbackReplacementOrdinaryCone p q) f)
/-- 概要：最初の比較三単体の辺 13 は指定された関手の coherent 辺。
方針：上側の比較三角形または strict な錐の面の式を使う。
規約：一次単体そのものの厳密な等式。
使われ方：四面の合成則の六つの境界関手を固定する。 -/
lemma catPullbackFirstTetrahedron_edge13 (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    CatInfinity.δ 1 (CatInfinity.δ 0 (catPullbackConeTetrahedron p q f 0)) =
      (coherentNerveEdge ((catPullbackReplacementOrdinaryCone p q).π.app j)).edge :=
  (congrArg (CatInfinity.δ 1) (catPullbackConeTetrahedron_first p q f)).trans
    (nativeConeTriangle_strict_one (catPullbackReplacementOrdinaryCone p q) f)
/-- 概要：最初の比較三単体の辺 23 は指定された関手の coherent 辺。
方針：上側の比較三角形または strict な錐の面の式を使う。
規約：一次単体そのものの厳密な等式。
使われ方：四面の合成則の六つの境界関手を固定する。 -/
lemma catPullbackFirstTetrahedron_edge23 (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    CatInfinity.δ 0 (CatInfinity.δ 0 (catPullbackConeTetrahedron p q f 0)) =
      (coherentNerveEdge ((catPullbackReplacementDiagram p q).map f)).edge :=
  (congrArg (CatInfinity.δ 0) (catPullbackConeTetrahedron_first p q f)).trans
    (nativeConeTriangle_strict_zero (catPullbackReplacementOrdinaryCone p q) f)

end SerrePositivity.InfinityCategories.F2
