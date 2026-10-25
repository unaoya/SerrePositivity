module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PairCovariantYoneda
public import SerrePositivity.InfinityCategories.F2.Idempotent.EssentialImageLift

/-!
概要：元の全左関手圏から元の全右関手圏の反対への随伴選択の単体写像。
方針：元の単位族を共変 Yoneda の全本質像へ持ち上げ、その同値の逆で右関手を回収する。
規約：全自然変換を含む実際の射を構成し、同値性は別工程で証明する。
使われ方：HTT 5.2.6.2 の対ごとの反変双対性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：元の全単位族を共変 Yoneda の全本質像へ厳密に持ち上げる。
方針：固定左値の表現可能性を全頂点の所属条件として使う。
規約：単位の族の全ての自然変換を同じ単体写像で保持する。
使われ方：右随伴の全関手族としての回収。 -/
def pairUnitHomFamilyImageLift (C D : PresentableInfinityObject.{u}) :
    (SSet.uliftFunctor.{u + 2, u + 1}).obj (PrLFunctorSpace C D) ⟶
      Idempotent.fullEssentialImage (pairCovariantYoneda (PrRFunctorSpace D C)) :=
  fullSubcomplexLift _ (pairUnitHomFamily C D)
    (pairUnitHomFamily_in_covariantYonedaImage C D)

/-- 概要：宇宙を持ち上げた全関手圏の間で右随伴を取る単体写像。
方針：共変 Yoneda の本質像への同値の逆に同じ全単位族を通す。
規約：元の全右関手圏の反対に値を取る。
使われ方：元の宇宙への降下前の反変作用。 -/
def pairRightAdjointFunctorLifted (C D : PresentableInfinityObject.{u}) :
    (SSet.uliftFunctor.{u + 2, u + 1}).obj (PrLFunctorSpace C D) ⟶
      (SSet.uliftFunctor.{u + 2, u + 1}).obj (PrRFunctorSpace D C).op :=
  pairUnitHomFamilyImageLift C D ≫
    (Idempotent.essentialImageEquivalence (pairCovariantYoneda (PrRFunctorSpace D C))
      (pairCovariantYoneda_isFullyFaithful _)).inv

/-- 概要：回収した右族の共変 Yoneda 像は元の全単位族と全自然に同型。
方針：本質像への同値の余単位を元の族で前合成して包含へ戻す。
規約：頂点ごとの無関係な同型ではなく元の全関手族の同型。
使われ方：反変の随伴選択の元の単位との照合。 -/
def pairRightAdjointFunctorLifted_yonedaIso (C D : PresentableInfinityObject.{u}) :
    FunctorIso
      (pairRightAdjointFunctorLifted C D ≫ pairCovariantYoneda (PrRFunctorSpace D C))
      (pairUnitHomFamily C D) := by
  let y := pairCovariantYoneda (PrRFunctorSpace D C)
  let e := Idempotent.essentialImageEquivalence y (pairCovariantYoneda_isFullyFaithful _)
  let f := pairUnitHomFamilyImageLift C D
  let i := (Idempotent.fullEssentialImage y).ι
  have he : e.hom ≫ i = y := Idempotent.essentialImageLift_inclusion y
  have hf : f ≫ i = pairUnitHomFamily C D := fullSubcomplexLift_ι _ _ _
  have h := (e.invHomIso.precomp f).postcomp i
  change FunctorIso ((f ≫ e.inv) ≫ y) (pairUnitHomFamily C D)
  simpa only [Category.assoc, Category.id_comp, he, hf] using h

/-- 概要：元の全左関手圏から元の全右関手圏の反対への実際の単体写像。
方針：単体集合の宇宙持ち上げの完全忠実性で回収した族を元の宇宙へ降ろす。
規約：元の e1 の全関手圏を変更しない。同値性はまだ主張しない。
使われ方：対ごとの反変双対性の順方向の射。 -/
def pairRightAdjointFunctor (C D : PresentableInfinityObject.{u}) :
    PrLFunctorSpace C D ⟶ (PrRFunctorSpace D C).op :=
  HomotopyLimits.uliftSSetFullyFaithful.preimage (pairRightAdjointFunctorLifted C D)

/-- 概要：降下した元の反変作用は、持ち上げると構成した同じ全族を回収する。
方針：宇宙持ち上げの完全忠実性の往復公式を使う。
規約：単体写像の厳密な等式。
使われ方：元の全関手圏での作用と分類による構成との照合。 -/
lemma pairRightAdjointFunctor_ulift (C D : PresentableInfinityObject.{u}) :
    (SSet.uliftFunctor.{u + 2, u + 1}).map (pairRightAdjointFunctor C D) =
      pairRightAdjointFunctorLifted C D :=
  HomotopyLimits.uliftSSetFullyFaithful.map_preimage _

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
