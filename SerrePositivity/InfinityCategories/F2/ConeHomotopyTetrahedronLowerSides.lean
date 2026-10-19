module

public import SerrePositivity.InfinityCategories.F2.ConeHomotopyTetrahedronUpperSides
public import SerrePositivity.InfinityCategories.F2.ConeHomotopyLowerTriangle
public import SerrePositivity.InfinityCategories.F2.TrianglePrismLowerSides

/-!
概要：錐の比較三単体の下側の三つの側面。
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

/-- 概要：錐の比較三単体の下側の三つの側面の指定単体への一致。
方針：標準三角形の面と円柱の側面の式を使う。
規約：元の二単体と一次単体を保つ。
使われ方：錐の四面の同型を各脚の指定比較同型に結び付ける。 -/
lemma coneHomotopyTetrahedron_lower_first {K X : SSet.{u}} {p q : K ⟶ X}
    {c : JoinCone p} {d : JoinCone q} (G : SSet.Homotopy c.val d.val) (k : K _⦋1⦌) :
    X.δ 3 (coneHomotopyTetrahedron G k 1) = coneHomotopyLowerTriangle G (K.δ 1 k) :=
  (triangleHomotopyTetrahedron_lower_first G.h _).trans
    (congrArg (homotopyEdgeTriangleLower G.h) (coneDomainTriangle_face k 1))
/-- 概要：錐の比較三単体の下側の三つの側面の指定単体への一致。
方針：標準三角形の面と円柱の側面の式を使う。
規約：元の二単体と一次単体を保つ。
使われ方：錐の四面の同型を各脚の指定比較同型に結び付ける。 -/
lemma coneHomotopyTetrahedron_lower_last {K X : SSet.{u}} {p q : K ⟶ X}
    {c : JoinCone p} {d : JoinCone q} (G : SSet.Homotopy c.val d.val) (k : K _⦋1⦌) :
    X.δ 0 (coneHomotopyTetrahedron G k 2) =
      homotopyEdgeTriangleLower G.h ((joinInr Δ[0] K).app (Opposite.op ⦋1⦌) k) :=
  (triangleHomotopyTetrahedron_lower_last G.h _).trans
    (congrArg (homotopyEdgeTriangleLower G.h) (coneDomainTriangle_zero k))
/-- 概要：錐の比較三単体の下側の三つの側面の指定単体への一致。
方針：標準三角形の面と円柱の側面の式を使う。
規約：元の二単体と一次単体を保つ。
使われ方：錐の四面の同型を各脚の指定比較同型に結び付ける。 -/
lemma coneHomotopyTetrahedron_lower_long {K X : SSet.{u}} {p q : K ⟶ X}
    {c : JoinCone p} {d : JoinCone q} (G : SSet.Homotopy c.val d.val) (k : K _⦋1⦌) :
    X.δ 1 (coneHomotopyTetrahedron G k 2) = coneHomotopyLowerTriangle G (K.δ 0 k) :=
  (triangleHomotopyTetrahedron_lower_long G.h _).trans
    (congrArg (homotopyEdgeTriangleLower G.h) (coneDomainTriangle_face k 0))

end SerrePositivity.InfinityCategories.F2
