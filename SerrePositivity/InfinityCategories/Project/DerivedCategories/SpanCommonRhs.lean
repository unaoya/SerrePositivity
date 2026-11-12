module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanCommonData
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DataRhsComponents

/-! # 左右の共通の対象と方程式の右辺

概要：A と後続頂点からなる共通面のデータの等式を対象と右辺で評価する。
方針：共通面の等式を頂点と単射の像の成分で評価する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：二セルの残差を一つの cofiber 座標へまとめる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 概要：左右の零未知境界データの共通面の各対象は等しい。
方針：共通面への制限の等式を指定頂点で評価する。
規約：HA Proposition 1.3.1.10。使われ方：A と後続頂点の射の端点を左右で同定する。 -/
lemma spanBoundaryZeroData_common_obj {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (i : Fin (n + 3)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n i) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n i) :=
  congrArg (fun s => s.obj i) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryZeroData_common F)

/-- 概要：共通面の任意の集合の像で、左右の方程式の右辺は異種等号で一致する。
方針：共通面のデータの等式から単射の像の右辺の比較を適用する。
規約：HA Proposition 1.3.1.10。使われ方：後続・A 側の共通の右辺を一つにまとめる。 -/
lemma spanBoundaryZeroData_common_rhs_heq {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (J : Finset (Fin (n + 3))) (a b : Fin (n + 3)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).rhs (J.image (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n) a) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n) b) k (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinCommonFace (n + 1)).succAboveOrderEmb.injective.injOn hJ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n).monotone (by rw [ha]; exact J.isLeast_min' _) _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n).monotone (by rw [hb]; exact J.isGreatest_max' _) _)
      (by
        rw [Finset.card_image_of_injOn (f := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n) (s := J)
          (show Set.InjOn (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n) (J : Set (Fin (n + 3))) from
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinCommonFace (n + 1)).succAboveOrderEmb.injective.injOn)]
        exact hk))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).rhs (J.image (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n))
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n) a) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n) b) k (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinCommonFace (n + 1)).succAboveOrderEmb.injective.injOn hJ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n).monotone (by rw [ha]; exact J.isLeast_min' _) _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n).monotone (by rw [hb]; exact J.isGreatest_max' _) _)
      (by
        rw [Finset.card_image_of_injOn (f := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n) (s := J)
          (show Set.InjOn (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n) (J : Set (Fin (n + 3))) from
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinCommonFace (n + 1)).succAboveOrderEmb.injective.injOn)]
        exact hk)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryZeroData_common F) J a b k hJ ha hb hk
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinCommonFace (n + 1)).succAboveOrderEmb.injective.injOn
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinCommonFace (n + 1)).succAboveOrderEmb.injective.injOn

end SerrePositivity.InfinityCategories.Project.DerivedCategories
