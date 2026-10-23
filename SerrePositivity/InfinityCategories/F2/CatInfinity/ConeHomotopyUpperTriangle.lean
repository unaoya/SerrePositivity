module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.ConeHomotopyDiagonalEdge
public import SerrePositivity.InfinityCategories.F2.CatInfinity.HomotopyEdgeTriangleUpperFaces

/-!
概要：全錐の比較正方形の上側の三角形と三辺。
方針：元のホモトピーを標準の脚の比較正方形で制限する。
規約：辺や三角形の充填を新たに選択しない。
使われ方：同じ指定円柱から二脚の比較同型を構成する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の頂点と比較先の頂点・図式対象が張る三角形。
方針：円柱の単体と既存の辺の面の式を使う。
規約：元の一次単体・二単体を保持する。
使われ方：錐の指定された比較三角形の関手同型への移行。 -/
def coneHomotopyUpperTriangle {K X : SSet.{u}} {p q : K ⟶ X}
    {c : JoinCone p} {d : JoinCone q} (G : SSet.Homotopy c.val d.val) (k : K _⦋0⦌) :
    X _⦋2⦌ := homotopyEdgeTriangleUpper G.h (coneDomainLeg k).edge
/-- 概要：上側の三角形の底辺は比較先の錐の脚。
方針：円柱の単体と既存の辺の面の式を使う。
規約：元の一次単体・二単体を保持する。
使われ方：錐の指定された比較三角形の関手同型への移行。 -/
lemma coneHomotopyUpperTriangle_zero {K X : SSet.{u}} {p q : K ⟶ X}
    {c : JoinCone p} {d : JoinCone q} (G : SSet.Homotopy c.val d.val) (k : K _⦋0⦌) :
    X.δ 0 (coneHomotopyUpperTriangle G k) = (nativeConeLeg d k).edge :=
  (homotopyEdgeTriangleUpper_zero G _).trans (by rfl)
/-- 概要：上側の三角形の長辺は指定円柱の対角辺。
方針：円柱の単体と既存の辺の面の式を使う。
規約：元の一次単体・二単体を保持する。
使われ方：錐の指定された比較三角形の関手同型への移行。 -/
lemma coneHomotopyUpperTriangle_one {K X : SSet.{u}} {p q : K ⟶ X}
    {c : JoinCone p} {d : JoinCone q} (G : SSet.Homotopy c.val d.val) (k : K _⦋0⦌) :
    X.δ 1 (coneHomotopyUpperTriangle G k) = (coneHomotopyDiagonalEdge G k).edge :=
  (homotopyEdgeTriangleUpper_one G.h _).trans (homotopyDiagonalEdge_simplex G _).symm
/-- 概要：上側の三角形の最初の辺は頂点の比較辺。
方針：円柱の単体と既存の辺の面の式を使う。
規約：元の一次単体・二単体を保持する。
使われ方：錐の指定された比較三角形の関手同型への移行。 -/
lemma coneHomotopyUpperTriangle_two {K X : SSet.{u}} {p q : K ⟶ X}
    {c : JoinCone p} {d : JoinCone q} (G : SSet.Homotopy c.val d.val) (k : K _⦋0⦌) :
    X.δ 2 (coneHomotopyUpperTriangle G k) = (coneHomotopyApexEdge G).edge := by
  have h := homotopyEdgeTriangleUpper_two G (coneDomainLeg k).edge
  have hs : (join (Δ[0] : SSet.{u}) K).δ 1 (coneDomainLeg k).edge =
      (joinInl Δ[0] K).app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (𝟙 Δ[0])) :=
    (coneDomainLeg k).src_eq
  rw [hs] at h
  exact h

end SerrePositivity.InfinityCategories.F2
