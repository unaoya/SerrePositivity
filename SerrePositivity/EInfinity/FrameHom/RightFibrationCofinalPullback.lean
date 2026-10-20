module

public import SerrePositivity.InfinityCategories.F1B.LeftFibrationCofinalPullback
public import SerrePositivity.InfinityCategories.F1B.CofinalOpposite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# 右 fibration に沿う left cofinal な射の底変換

概要：Low 命題 3.7 の固定右脚の比較へ分解の余終性を移す。
方針：F1b の left fibration の結果を反転し、同じ引き戻しの実同型で戻す。
規約：元の両対象の Kan 性や単体集合モデルを要求しない。
使われ方：元の costructured arrow の全図式の比較の余終性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.FrameHom

open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories

/-- 概要：right fibration に沿う left cofinal な射の引き戻しも left cofinal（Quillen A）。
方針：元の左側の底変換を反転関手の引き戻し比較で移す。
規約：元の射の単射性や両端の充填性を要求しない。
使われ方：固定した右脚の元の Hom の比較への余終性の移送。 -/
lemma rightFibration_pullback_isLeftCofinal {E A B : SSet.{u}}
    (p : E ⟶ B) [RightFibration p] (f : A ⟶ B) (hf : IsLeftCofinal f) :
    IsLeftCofinal (pullback.fst p f) := by
  have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  have h := leftFibration_pullback_isRightCofinal (SSet.opFunctor.map p)
    (SSet.opFunctor.map f) hf.op
  let e := PreservesPullback.iso SSet.opFunctor p f
  have hc := (isRightCofinal_of_isIso e.hom).comp h
  have he : e.hom ≫ pullback.fst (SSet.opFunctor.map p) (SSet.opFunctor.map f) =
      SSet.opFunctor.map (pullback.fst p f) := PreservesPullback.iso_hom_fst _ _ _
  rw [he] at hc
  exact (isLeftCofinal_iff_isRightCofinal_op _).mpr hc

/-- 概要：元の引き戻し正方形の上射も left cofinal（Quillen A）。
方針：元の引き戻しの普遍同型で同じ第一射影へ移す。
規約：指定した上射そのものの余終性。
使われ方：通常の comma の元の比較射の判定。 -/
lemma rightFibration_isPullback_isLeftCofinal {E' E A B : SSet.{u}}
    {i : E' ⟶ E} {q : E' ⟶ A} {p : E ⟶ B} {f : A ⟶ B}
    (sq : IsPullback i q p f) [RightFibration p] (hf : IsLeftCofinal f) :
    IsLeftCofinal i := by
  have h := (isLeftCofinal_of_isIso sq.isoPullback.hom).comp
    (rightFibration_pullback_isLeftCofinal p f hf)
  rw [sq.isoPullback_hom_fst] at h
  exact h

end SerrePositivity.EInfinity.FrameHom
