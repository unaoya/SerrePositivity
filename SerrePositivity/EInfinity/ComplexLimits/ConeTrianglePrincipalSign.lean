module
public import SerrePositivity.EInfinity.ComplexLimits.ConeTriangleMiddleCardinality

/-!
概要：元の両切断の重みと主 cone cochain の符号を比較する。
方針：元の切断・全添字像・端点の等式輸送を保持する。
規約：主切断の合成は別工程。使われ方：大域評価三角形の混合 HA。
-/
@[expose] public section
namespace SerrePositivity.EInfinity.ComplexLimits


lemma principal_cut_sign {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (k : ℤ) (hk : k = 3 - (I.card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I (ConeHeadIndex.penultimate I hI) * k.negOnePow =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I (ConeHeadIndex.second I hI) := by
  rw [ConeHeadIndex.sign_penultimate, sign_second_card, hk,
    Int.negOnePow_sub, Int.negOnePow_sub]
  have h3 : (3 : ℤ).negOnePow = -1 := by decide
  have h2 : (2 : ℤ).negOnePow = 1 := by decide
  rw [h3, h2]
  simp only [neg_one_mul, neg_neg, mul_one]

end SerrePositivity.EInfinity.ComplexLimits
