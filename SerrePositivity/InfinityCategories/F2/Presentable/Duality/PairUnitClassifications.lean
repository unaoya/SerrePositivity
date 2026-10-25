module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PairFixedLeftCoslice

/-!
概要：元の全単位族の固定左値を、同じ保存条件付き coslice の分類と比較する。
方針：厳密な引き戻し同型を同じ底上で分類し、元の底変換同型に接続する。
規約：対象ごとに自然性を選び直さない。
使われ方：固定左の普遍単位の表現可能性を全関手族に戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：元の全単位族の固定左値と、元の保存条件付き coslice の分類との全自然な同型。
方針：同じ底上の厳密な全空間同型のファイバー同値性を分類に通す。
規約：単位空間の値ごとの無関係な比較ではなく元の全分類を保持する。
使われ方：全右関手圏上の普遍単位の表現可能性。 -/
def pairUnitHomAtLeft_cosliceIso {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) :
    FunctorIso (pairUnitHomAtLeft v)
      (leftStraighteningInfinityDiagram (preservingLeftUnitProjection v)) := by
  let p := pullback.snd (covariantPairUnitProjection C D) (pairFixedLeftBase v)
  let q := preservingLeftUnitProjection v
  have : LeftFibration p :=
    ⟨leftFibrations.pullback_snd _ _
      (LeftFibration.mem (p := covariantPairUnitProjection C D))⟩
  have : Quasicategory (pullback (covariantPairUnitProjection C D) (pairFixedLeftBase v)) :=
    quasicategory_of_innerFibration p
  let e := pairFixedLeftCosliceIso v
  have he : e.hom ≫ q = p := pairFixedLeftCosliceIso_projection v
  have hf := (leftFibration_precompositionEquivalence_iff_fibers p q e.hom he).mp
    (qCatEquivalenceOfIso e).isQCatEquivalence.isPrecompositionEquivalence
  exact pairUnitHomAtLeft_classificationIso v ≪≫
    leftClassificationComparisonIso p q e.hom he hf

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
