module
public import SerrePositivity.InfinityCategories.DGNerve.CospanCommonData
public import SerrePositivity.InfinityCategories.DGNerve.DataRhsComponents

/-! # 左右の共通の対象と方程式の右辺

概要：先頭と D からなる共通面のデータの等式を対象と右辺で評価する。
方針：共通面の等式を頂点と単射の像の成分で評価する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：二セルの残差を一つの fiber 座標へまとめる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded
open scoped Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：左右の零未知境界データの共通面の各対象は等しい。
方針：共通面への制限の等式を指定頂点で評価する。
規約：HA Proposition 1.3.1.10。使われ方：先頭と D の射の端点を左右で同定する。 -/
lemma cospanBoundaryZeroData_common_obj {n : ℕ}
    (F : join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ dgNerve A D)
    (i : Fin (n + 3)) :
    (cospanBoundaryLeftZeroData F).obj (cospanCommonOrderHom n i) =
      (cospanBoundaryRightZeroData F).obj (cospanCommonOrderHom n i) :=
  congrArg (fun s => s.obj i) (cospanBoundaryZeroData_common F)

/-- 概要：共通面の任意の集合の像で、左右の方程式の右辺は異種等号で一致する。
方針：共通面のデータの等式から単射の像の右辺の比較を適用する。
規約：HA Proposition 1.3.1.10。使われ方：先頭・D 側の共通の右辺を一つにまとめる。 -/
lemma cospanBoundaryZeroData_common_rhs_heq {n : ℕ}
    (F : join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ dgNerve A D)
    (J : Finset (Fin (n + 3))) (a b : Fin (n + 3)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
    (hb : b = J.max' (Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ)) :
    HEq ((cospanBoundaryLeftZeroData F).rhs (J.image (cospanCommonOrderHom n))
      ((cospanCommonOrderHom n) a) ((cospanCommonOrderHom n) b) k (Index.image_two
      (cospanFirstTail n).succAboveOrderEmb.injective.injOn hJ)
      (Index.image_min (cospanCommonOrderHom n).monotone (by rw [ha]; exact J.isLeast_min' _) _)
      (Index.image_max (cospanCommonOrderHom n).monotone (by rw [hb]; exact J.isGreatest_max' _) _)
      (by
        rw [Finset.card_image_of_injOn (f := cospanCommonOrderHom n) (s := J)
          (show Set.InjOn (cospanCommonOrderHom n) (J : Set (Fin (n + 3))) from
            (cospanFirstTail n).succAboveOrderEmb.injective.injOn)]
        exact hk))
      ((cospanBoundaryRightZeroData F).rhs (J.image (cospanCommonOrderHom n))
        ((cospanCommonOrderHom n) a) ((cospanCommonOrderHom n) b) k (Index.image_two
        (cospanFirstTail n).succAboveOrderEmb.injective.injOn hJ)
      (Index.image_min (cospanCommonOrderHom n).monotone (by rw [ha]; exact J.isLeast_min' _) _)
      (Index.image_max (cospanCommonOrderHom n).monotone (by rw [hb]; exact J.isGreatest_max' _) _)
      (by
        rw [Finset.card_image_of_injOn (f := cospanCommonOrderHom n) (s := J)
          (show Set.InjOn (cospanCommonOrderHom n) (J : Set (Fin (n + 3))) from
            (cospanFirstTail n).succAboveOrderEmb.injective.injOn)]
        exact hk)) :=
  SimplexData.rhs_heq_of_pullback_eq _ _ (cospanCommonOrderHom n) (cospanCommonOrderHom n)
    (cospanBoundaryZeroData_common F) J a b k hJ ha hb hk
    (cospanFirstTail n).succAboveOrderEmb.injective.injOn
    (cospanFirstTail n).succAboveOrderEmb.injective.injOn

end SerrePositivity.InfinityCategories.DGNerve
