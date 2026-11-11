module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.TrianglePrismFaces
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeTriangle

/-!
概要：全錐の比較円柱の三単体と元の三角形の回収。
方針：頂点と形状の辺が張る標準三角形で制限する。
規約：同じ指定ホモトピーを使い、上下と共有面を厳密に保つ。
使われ方：引き戻し錐の二脚の比較と native な可換性の整合。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：錐の形状の辺と頂点が張る始域の標準三角形。
方針：標準三角形の包含を Yoneda で二単体にする。
規約：新しい三単体の充填を選択しない。
使われ方：錐の三角形の指定関手同型の同時比較。 -/
def coneDomainTriangle {K : SSet.{u}} (k : K _⦋1⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K) _⦋2⦌ :=
  SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneTriangleInclusion (SSet.yonedaEquiv.symm k))
/-- 概要：始域の標準三角形の像は錐の元の三角形。
方針：Yoneda の後合成の式を使う。
規約：新しい三単体の充填を選択しない。
使われ方：錐の三角形の指定関手同型の同時比較。 -/
lemma nativeConeTriangle_map {K X : SSet.{u}} {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (k : K _⦋1⦌) :
    c.val.app (Opposite.op ⦋2⦌) (coneDomainTriangle k) = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeTriangle c k := by
  exact (SSet.yonedaEquiv_comp _ _).symm
/-- 概要：全錐の比較ホモトピーが与える三つの三単体。
方針：始域の標準三角形の円柱で制限する。
規約：新しい三単体の充填を選択しない。
使われ方：錐の三角形の指定関手同型の同時比較。 -/
def coneHomotopyTetrahedron {K X : SSet.{u}} {p q : K ⟶ X}
    {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q} (G : SSet.Homotopy c.val d.val)
    (k : K _⦋1⦌) (i : Fin 3) : X _⦋3⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.triangleHomotopyTetrahedron G.h (coneDomainTriangle k) i
/-- 概要：最初の三単体の上面は比較先の錐の三角形。
方針：円柱の時刻一の面の式を使う。
規約：新しい三単体の充填を選択しない。
使われ方：錐の三角形の指定関手同型の同時比較。 -/
lemma coneHomotopyTetrahedron_first {K X : SSet.{u}} {p q : K ⟶ X}
    {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q} (G : SSet.Homotopy c.val d.val) (k : K _⦋1⦌) :
    X.δ 0 (coneHomotopyTetrahedron G k 0) = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeTriangle d k := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.triangleHomotopyTetrahedron_first G _).trans (nativeConeTriangle_map d k)
/-- 概要：最後の三単体の下面は元の錐の三角形。
方針：円柱の時刻零の面の式を使う。
規約：新しい三単体の充填を選択しない。
使われ方：錐の三角形の指定関手同型の同時比較。 -/
lemma coneHomotopyTetrahedron_last {K X : SSet.{u}} {p q : K ⟶ X}
    {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q} (G : SSet.Homotopy c.val d.val) (k : K _⦋1⦌) :
    X.δ 3 (coneHomotopyTetrahedron G k 2) = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeTriangle c k := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.triangleHomotopyTetrahedron_last G _).trans (nativeConeTriangle_map c k)
/-- 概要：最初と中央の錐の比較三単体の共有面は一致。
方針：三角形の円柱の共有面の式を使う。
規約：新しい三単体の充填を選択しない。
使われ方：錐の三角形の指定関手同型の同時比較。 -/
lemma coneHomotopyTetrahedron_glue_first {K X : SSet.{u}} {p q : K ⟶ X}
    {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q} (G : SSet.Homotopy c.val d.val) (k : K _⦋1⦌) :
    X.δ 1 (coneHomotopyTetrahedron G k 0) = X.δ 1 (coneHomotopyTetrahedron G k 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.triangleHomotopyTetrahedron_glue_first G.h _
/-- 概要：中央と最後の錐の比較三単体の共有面は一致。
方針：三角形の円柱の共有面の式を使う。
規約：新しい三単体の充填を選択しない。
使われ方：錐の三角形の指定関手同型の同時比較。 -/
lemma coneHomotopyTetrahedron_glue_last {K X : SSet.{u}} {p q : K ⟶ X}
    {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q} (G : SSet.Homotopy c.val d.val) (k : K _⦋1⦌) :
    X.δ 2 (coneHomotopyTetrahedron G k 1) = X.δ 2 (coneHomotopyTetrahedron G k 2) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.triangleHomotopyTetrahedron_glue_last G.h _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
