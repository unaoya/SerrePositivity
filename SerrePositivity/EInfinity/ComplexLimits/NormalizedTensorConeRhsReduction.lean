module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeQuadratic
public import SerrePositivity.EInfinity.ComplexLimits.ConePenultimateCuts

/-!
概要：実 cone の全 HA 右辺を削除和と一つの元の終端切断合成へ還元する。
方針：全非線形和の支持と元の最後の切断の符号を使う。
規約：元の実データ・全有限和・同じ切断成分を保持する。
使われ方：残る混合 HA 方程式の線形右辺との照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open ConeHeadIndex
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorConeData_rhs_reduced {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : 3 ≤ I.card) :
    (normalizedTensorConeData A X Y c).rhs I a b k hI ha hb hk =
    (normalizedTensorConeData A X Y c).linearBoundary I a b k +
      (normalizedTensorConeData A X Y c).cutCompose I a b k (penultimate I hI) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_eq_linear_sub_quadratic,
    normalizedTensorConeData_quadratic_single A X Y c I a b k hI ha hb hk hc,
    sign_penultimate]
  simp only [Units.smul_def, Units.val_neg, Units.val_one, neg_one_smul, sub_neg_eq_add]

end SerrePositivity.EInfinity.ComplexLimits
