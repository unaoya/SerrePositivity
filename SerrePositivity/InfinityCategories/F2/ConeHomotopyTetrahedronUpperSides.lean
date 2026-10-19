module

public import SerrePositivity.InfinityCategories.F2.ConeDomainTriangleFaces
public import SerrePositivity.InfinityCategories.F2.ConeHomotopyUpperTriangle
public import SerrePositivity.InfinityCategories.F2.TrianglePrismUpperSides

/-!
概要：錐の比較三単体の上側の三つの側面。
方針：指定された単体の境界と既存の合成則を使う。
規約：辺と同型の値を新しく選択しない。
使われ方：全錐の比較円柱の三つの合成関係の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：錐の比較三単体の上側の三つの側面の指定単体への一致。
方針：標準三角形の面と円柱の側面の式を使う。
規約：元の二単体と一次単体を保つ。
使われ方：錐の四面の同型を各脚の指定比較同型に結び付ける。 -/
lemma coneHomotopyTetrahedron_upper_long {K X : SSet.{u}} {p q : K ⟶ X}
    {c : JoinCone p} {d : JoinCone q} (G : SSet.Homotopy c.val d.val) (k : K _⦋1⦌) :
    X.δ 2 (coneHomotopyTetrahedron G k 0) = coneHomotopyUpperTriangle G (K.δ 0 k) :=
  (triangleHomotopyTetrahedron_upper_long G.h _).trans
    (congrArg (homotopyEdgeTriangleUpper G.h) (coneDomainTriangle_face k 0))
/-- 概要：錐の比較三単体の上側の三つの側面の指定単体への一致。
方針：標準三角形の面と円柱の側面の式を使う。
規約：元の二単体と一次単体を保つ。
使われ方：錐の四面の同型を各脚の指定比較同型に結び付ける。 -/
lemma coneHomotopyTetrahedron_upper_first {K X : SSet.{u}} {p q : K ⟶ X}
    {c : JoinCone p} {d : JoinCone q} (G : SSet.Homotopy c.val d.val) (k : K _⦋1⦌) :
    X.δ 3 (coneHomotopyTetrahedron G k 0) = coneHomotopyUpperTriangle G (K.δ 1 k) :=
  (triangleHomotopyTetrahedron_upper_first G.h _).trans
    (congrArg (homotopyEdgeTriangleUpper G.h) (coneDomainTriangle_face k 1))
/-- 概要：錐の比較三単体の上側の三つの側面の指定単体への一致。
方針：標準三角形の面と円柱の側面の式を使う。
規約：元の二単体と一次単体を保つ。
使われ方：錐の四面の同型を各脚の指定比較同型に結び付ける。 -/
lemma coneHomotopyTetrahedron_upper_last {K X : SSet.{u}} {p q : K ⟶ X}
    {c : JoinCone p} {d : JoinCone q} (G : SSet.Homotopy c.val d.val) (k : K _⦋1⦌) :
    X.δ 0 (coneHomotopyTetrahedron G k 1) =
      homotopyEdgeTriangleUpper G.h ((joinInr Δ[0] K).app (Opposite.op ⦋1⦌) k) :=
  (triangleHomotopyTetrahedron_upper_last G.h _).trans
    (congrArg (homotopyEdgeTriangleUpper G.h) (coneDomainTriangle_zero k))

end SerrePositivity.InfinityCategories.F2
