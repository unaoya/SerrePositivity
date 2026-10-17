module
public import SerrePositivity.InfinityCategories.DGNerve.CospanCommonRhs

/-! # 左右の境界データの先頭の対象

概要：左右の零未知境界データの先頭の全対象は一致する。
方針：共通面の先頭集合の像の等式を使い、その各対象の一致を大きい添字へ戻す。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：残差の共通の始点を一つに固定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded
open scoped Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：左右の零未知データの先頭の各対象は等しい。
方針：共通面の先頭集合の像であることから元の頂点を選び、共通面の対象の等式を使う。
規約：HTT §1.2.13。使われ方：左と右の残差を同じ始点からの Hom に移す。 -/
lemma cospanBoundaryZeroData_prefix_obj {n : ℕ}
    (F : join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ dgNerve A D)
    (k : Fin (n + 4)) (hk : k ∈ cospanPrefixFaces n) :
    (cospanBoundaryLeftZeroData F).obj k = (cospanBoundaryRightZeroData F).obj k := by
  have hi : k ∈ (cospanCommonFaces n).image (cospanCommonOrderHom n) := by
    rw [cospanCommonFaces_image]
    exact hk
  obtain ⟨i, _, heq⟩ := Finset.mem_image.mp hi
  simpa only [heq] using cospanBoundaryZeroData_common_obj F i

/-- 概要：左右の零未知データの零番目の対象は等しい。
方針：零が先頭集合に属することを使う。
規約：HTT §1.2.13。使われ方：残差の始点 X を左側の零番目の対象に選ぶ。 -/
lemma cospanBoundaryZeroData_zero_obj {n : ℕ}
    (F : join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ dgNerve A D) :
    (cospanBoundaryLeftZeroData F).obj 0 = (cospanBoundaryRightZeroData F).obj 0 :=
  cospanBoundaryZeroData_prefix_obj F 0 ((mem_cospanPrefixFaces _).mpr (by simp))

end SerrePositivity.InfinityCategories.DGNerve
