module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearBoundary

/-! # 右 pinched 線形方程式の削除作用素

概要：全頂点の削除和を一般の加法群の値で定義し、その二乗が零であると示す。
方針：削除係数は元の符号の負であり、二重削除では二つの負号が消えることを使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）、N0.3 の cochain 符号。
使われ方：欠けた面の線形方程式の整合性。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：右 pinched 方程式の削除係数は右側点数に一を加えた負一冪。
方針：整数の単位群で符号を表す。
規約：Kerodon §4.6.5（Tag 01KW）、N0.3。使われ方：全頂点の削除和。 -/
def deletionSign {α : Type*} [LinearOrder α] (J : Finset α) (j : α) : ℤˣ :=
  (((J.filter (j < ·)).card : ℤ) + 1).negOnePow

/-- 概要：右 pinched 削除係数は元の dg nerve の削除係数の負。
方針：整数負一冪の加法則を一に適用する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：二重削除の相殺の再利用。 -/
lemma deletionSign_eq_neg {α : Type*} [LinearOrder α] (J : Finset α) (j : α) :
    deletionSign J j = -_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign J j := by
  simp only [deletionSign, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign, Int.negOnePow_add, Int.negOnePow_one, mul_neg_one]

/-- 概要：有限部分集合を一つずつ削除する符号付き和。
方針：全ての所属点の削除を同じ加法群の中で足す。
規約：Kerodon §4.6.5（Tag 01KW）、N0.3。使われ方：線形右辺と二重削除の相殺。 -/
def deleteSum {α M : Type*} [LinearOrder α] [AddCommGroup M]
    (f : Finset α → M) (J : Finset α) : M := ∑ j ∈ J, deletionSign J j • f (J.erase j)

/-- 概要：全頂点の削除和を二度適用すると零になる。
方針：二つの負号を消して、二重削除の順序交換の相殺に帰着する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：線形ホーンの欠けた面の整合性。 -/
lemma deleteSum_squared {α M : Type*} [LinearOrder α] [AddCommGroup M]
    (f : Finset α → M) (J : Finset α) : deleteSum (deleteSum f) J = 0 := by
  simpa only [deleteSum, deletionSign_eq_neg, Units.smul_def, Units.val_neg,
    neg_smul, Finset.sum_neg_distrib, smul_neg, neg_neg] using
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nested_double_erase J J (fun _ h => h) f)

/-- 概要：最上位削除和を零にする、指定した面の成分の値。
方針：他の面の符号付き和に、指定面の係数の逆元を掛けて負にする。
規約：Kerodon §4.6.5（Tag 01KW）、N0.3。使われ方：内部点にも端点にも同じ式で線形ホーンを充填する。 -/
def deletionSolution {α M : Type*} [LinearOrder α] [AddCommGroup M]
    (J : Finset α) (i : α) (f : α → M) : M :=
  -((deletionSign J i)⁻¹ • (∑ j ∈ J.erase i, deletionSign J j • f j))

/-- 概要：指定した面に明示解を置けば全頂点の削除和は零になる。
方針：指定面の項を有限和から取り出し、符号の可逆性で残りの和と相殺する。
規約：Kerodon §4.6.5（Tag 01KW）、N0.3。使われ方：最上位成分を零とした方程式の検証。 -/
lemma sum_eq_zero_of_deletionSolution {α M : Type*} [LinearOrder α] [AddCommGroup M]
    (J : Finset α) (i : α) (hi : i ∈ J) (f : α → M)
    (hf : f i = deletionSolution J i f) :
    (∑ j ∈ J, deletionSign J j • f j) = 0 := by
  rw [← Finset.add_sum_erase J _ hi, hf]
  simp only [deletionSolution, smul_neg, smul_smul, mul_inv_cancel,
    one_smul, neg_add_cancel]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
