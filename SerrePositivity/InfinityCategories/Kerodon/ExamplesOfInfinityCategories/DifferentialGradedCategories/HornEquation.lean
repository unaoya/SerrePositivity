module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Signs

/-! # ホーンの最上位方程式を解く有限和

概要：最上位成分を零とした方程式を、欠けた面の成分について解く。
方針：指定した内部点の項を有限和から分離し、その符号が自分自身の逆元であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：欠けた面の成分の値の構成。
この有限和の解だけでは欠けた面自身の微分方程式やホーン充填の存在は主張しない。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

variable {α : Type*} [LinearOrder α] {M : Type*} [AddCommGroup M]

/-- 概要：最上位方程式から定まる欠けた面の成分。
方針：指定点の合成項から、それ以外の内部点の既知の寄与の符号付き和を引く。
規約：HA Proposition 1.3.1.10、`deleted` は削除成分、`composed` は切断の合成。
使われ方：実際のホーンデータから欠けた成分を与える値の式。 -/
def missingComponent (I K : Finset α) (i : α) (deleted composed : α → M) : M :=
  composed i - _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I i •
    ∑ j ∈ K.erase i, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j • (deleted j - composed j)

/-- 概要：欠けた面の成分を有限和の解で置き換えると、最上位の右辺は零になる。
方針：内部点 i の項を和から分離し、符号を二度掛けたものが一であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：最上位成分を零とした単体の方程式の検証。 -/
lemma sum_missingComponent (I K : Finset α) (i : α) (hi : i ∈ K)
    (deleted composed : α → M) :
    ∑ j ∈ K, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
      ((if j = i then missingComponent I K i deleted composed else deleted j) - composed j) =
        0 := by
  rw [← Finset.add_sum_erase K _ hi]
  have hrest :
      ∑ j ∈ K.erase i, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
        ((if j = i then missingComponent I K i deleted composed else deleted j) - composed j) =
      ∑ j ∈ K.erase i, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j • (deleted j - composed j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [ite_eq_right (Finset.mem_erase.mp hj).1]
  rw [hrest]
  simp [missingComponent, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign, smul_sub, smul_smul]

/-- 概要：欠けた面の解は、全切断の合成の和から既知の削除成分の和を引いた式に等しい。
方針：指定点の合成項を有限和へ戻し、符号付きの和を加法群の恒等式で整理する。
規約：HA Proposition 1.3.1.10。使われ方：N0 に記録したホーン充填の解との一致。 -/
lemma missingComponent_eq (I K : Finset α) (i : α) (hi : i ∈ K)
    (deleted composed : α → M) :
    missingComponent I K i deleted composed =
      (∑ j ∈ K, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I i • (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j • composed j)) -
        ∑ j ∈ K.erase i, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I i • (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j • deleted j) := by
  unfold missingComponent
  rw [← Finset.add_sum_erase K (fun j => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I i • (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j • composed j)) hi]
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I i • (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I i • composed i) = composed i := by
    simp [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign, smul_smul]
  rw [hs]
  simp only [smul_sub, Finset.smul_sum, Finset.sum_sub_distrib]
  abel

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
