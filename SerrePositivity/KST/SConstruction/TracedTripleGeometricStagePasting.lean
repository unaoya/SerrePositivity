module
public import SerrePositivity.KST.SConstruction.TracedTripleBFDiamond
public import SerrePositivity.KST.SConstruction.SixDiamondGeometricFaces

/-! # 元の raw 各段の六対角面を同じ実消去へ渡す
概要：元の各段の十二面と三つの全円柱を、六つの実結合替え四面体へ接続する。
方針：元の面の端点表示だけを揃え、両外側二部分面の全正規化移送も保持する。
規約：各段の実構成であり、隣接段の構造適合と零段固定は別に証明する。
使われ方：元の全高次 prism と同時に選ぶ相対比較の実面データ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の各段の六対角面と共有直接円柱から得られる、同じ全実消去データ。 -/
def monicKTracedTripleGeometricStagePasting (n : ℕ) :=
  sixDiamondGeometricPasting (monicKTracedTripleFirstPairDiamond F f g h n)
    (monicKTracedTripleLastPairDiamond F f g h n)
    (monicKTracedTripleInterchangeDiamond F f g h n)
    (monicKTracedTripleLeftOuterDiamond F f g h n)
    (monicKTracedTripleRightOuterDiamond F f g h n)
    (monicKTracedTripleBFDiamond F f g h n)
    (monicKTracedTripleTypedDirectComparison F f g h n).cylinder

/-- 元の指定左段辺と生成第四段辺の、同じ実消去からの全端点固定比較。 -/
def monicKTracedTripleGeometricStageCylinder (n : ℕ) :=
  (monicKTracedTripleGeometricStagePasting F f g h n).comparison

end SerrePositivity.KST.SConstruction
