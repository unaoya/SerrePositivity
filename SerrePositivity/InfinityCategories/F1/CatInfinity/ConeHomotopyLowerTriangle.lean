module

public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.Limit
public import SerrePositivity.InfinityCategories.Core.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.CatInfinity.ConeHomotopyDiagonalEdge
public import SerrePositivity.InfinityCategories.F1B.CatInfinity.ConeHomotopyEdges
public import SerrePositivity.InfinityCategories.Core.CatInfinity.HomotopyDiagonalEdge
public import SerrePositivity.InfinityCategories.Core.CatInfinity.HomotopyEdgeTriangleLowerFaces
public import SerrePositivity.InfinityCategories.Core.CatInfinity.NativeConeLeg
public import SerrePositivity.InfinityCategories.Core.CatInfinity.TrianglePrismLowerSides

/-!
概要：全錐の比較正方形の下側の三角形と三辺。
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

/-- 概要：元の頂点・図式対象と比較先の図式対象が張る三角形。
方針：円柱の単体と既存の辺の面の式を使う。
規約：元の一次単体・二単体を保持する。
使われ方：錐の指定された比較三角形の関手同型への移行。 -/
def coneHomotopyLowerTriangle {K X : SSet.{u}} {p q : K ⟶ X}
    {c : JoinCone p} {d : JoinCone q} (G : SSet.Homotopy c.val d.val) (k : K _⦋0⦌) :
    X _⦋2⦌ := homotopyEdgeTriangleLower G.h (coneDomainLeg k).edge
/-- 概要：下側の三角形の最後の辺は図式の比較辺。
方針：円柱の単体と既存の辺の面の式を使う。
規約：元の一次単体・二単体を保持する。
使われ方：錐の指定された比較三角形の関手同型への移行。 -/
lemma coneHomotopyLowerTriangle_zero {K X : SSet.{u}} {p q : K ⟶ X}
    {c : JoinCone p} {d : JoinCone q} (G : SSet.Homotopy c.val d.val) (k : K _⦋0⦌) :
    X.δ 0 (coneHomotopyLowerTriangle G k) = (coneHomotopyDiagramEdge G k).edge := by
  have h := homotopyEdgeTriangleLower_zero G (coneDomainLeg k).edge
  have ht : (join (Δ[0] : SSet.{u}) K).δ 0 (coneDomainLeg k).edge =
      (joinInr Δ[0] K).app (Opposite.op ⦋0⦌) k := (coneDomainLeg k).tgt_eq
  rw [ht] at h
  exact h
/-- 概要：下側の三角形の長辺は同じ指定対角辺。
方針：円柱の単体と既存の辺の面の式を使う。
規約：元の一次単体・二単体を保持する。
使われ方：錐の指定された比較三角形の関手同型への移行。 -/
lemma coneHomotopyLowerTriangle_one {K X : SSet.{u}} {p q : K ⟶ X}
    {c : JoinCone p} {d : JoinCone q} (G : SSet.Homotopy c.val d.val) (k : K _⦋0⦌) :
    X.δ 1 (coneHomotopyLowerTriangle G k) = (coneHomotopyDiagonalEdge G k).edge :=
  (homotopyEdgeTriangleLower_one G.h _).trans (homotopyDiagonalEdge_simplex G _).symm
/-- 概要：下側の三角形の最初の辺は元の錐の脚。
方針：円柱の単体と既存の辺の面の式を使う。
規約：元の一次単体・二単体を保持する。
使われ方：錐の指定された比較三角形の関手同型への移行。 -/
lemma coneHomotopyLowerTriangle_two {K X : SSet.{u}} {p q : K ⟶ X}
    {c : JoinCone p} {d : JoinCone q} (G : SSet.Homotopy c.val d.val) (k : K _⦋0⦌) :
    X.δ 2 (coneHomotopyLowerTriangle G k) = (nativeConeLeg c k).edge :=
  (homotopyEdgeTriangleLower_two G _).trans (by rfl)

end SerrePositivity.InfinityCategories.F2
