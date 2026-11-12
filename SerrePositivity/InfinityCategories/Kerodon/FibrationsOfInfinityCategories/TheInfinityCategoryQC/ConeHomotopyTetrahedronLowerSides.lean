module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeHomotopyTetrahedronUpperSides
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeHomotopyLowerTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.TrianglePrismLowerSides

/-!
概要：錐の比較三単体の下側の三つの側面。
方針：指定された単体の境界と既存の合成則を使う。
規約：辺と同型の値を新しく選択しない。
使われ方：全錐の比較円柱の三つの合成関係の照合。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：錐の比較三単体の下側の三つの側面の指定単体への一致。
方針：標準三角形の面と円柱の側面の式を使う。
規約：元の二単体と一次単体を保つ。
使われ方：錐の四面の同型を各脚の指定比較同型に結び付ける。 -/
lemma coneHomotopyTetrahedron_lower_first {K X : SSet.{u}} {p q : K ⟶ X}
    {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q} (G : SSet.Homotopy c.val d.val) (k : K _⦋1⦌) :
    X.δ 3 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyTetrahedron G k 1) = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyLowerTriangle G (K.δ 1 k) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.triangleHomotopyTetrahedron_lower_first G.h _).trans
    (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyEdgeTriangleLower G.h) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneDomainTriangle_face k 1))
/-- 概要：錐の比較三単体の下側の三つの側面の指定単体への一致。
方針：標準三角形の面と円柱の側面の式を使う。
規約：元の二単体と一次単体を保つ。
使われ方：錐の四面の同型を各脚の指定比較同型に結び付ける。 -/
lemma coneHomotopyTetrahedron_lower_last {K X : SSet.{u}} {p q : K ⟶ X}
    {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q} (G : SSet.Homotopy c.val d.val) (k : K _⦋1⦌) :
    X.δ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyTetrahedron G k 2) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyEdgeTriangleLower G.h ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K).app (Opposite.op ⦋1⦌) k) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.triangleHomotopyTetrahedron_lower_last G.h _).trans
    (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyEdgeTriangleLower G.h) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneDomainTriangle_zero k))
/-- 概要：錐の比較三単体の下側の三つの側面の指定単体への一致。
方針：標準三角形の面と円柱の側面の式を使う。
規約：元の二単体と一次単体を保つ。
使われ方：錐の四面の同型を各脚の指定比較同型に結び付ける。 -/
lemma coneHomotopyTetrahedron_lower_long {K X : SSet.{u}} {p q : K ⟶ X}
    {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q} (G : SSet.Homotopy c.val d.val) (k : K _⦋1⦌) :
    X.δ 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyTetrahedron G k 2) = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyLowerTriangle G (K.δ 0 k) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.triangleHomotopyTetrahedron_lower_long G.h _).trans
    (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyEdgeTriangleLower G.h) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneDomainTriangle_face k 0))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
