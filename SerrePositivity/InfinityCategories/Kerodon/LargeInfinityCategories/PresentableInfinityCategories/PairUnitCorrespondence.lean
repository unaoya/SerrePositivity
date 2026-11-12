module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TwistedPairFamilies

/-!
概要：presentable な固定二対象の全関手族と実単位図式の母対応。
方針：元の保存関手圏の全単体を含め、twisted arrow 上で恒等関手の coslice に持ち上げる。
規約：core の同値や全 Pr の同値とは区別し、充填性と随伴条件は別工程で扱う。
使われ方：対ごとの全関手 ∞ 圏の反変双対性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の左保存関手圏を全関手圏へ含める。
方針：e1 の全部分複体の包含を使う。
規約：非可逆な自然変換を保持する。
使われ方：二対象の単位の合成写像。 -/
def leftFunctorInclusion (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D ⟶ (ihom C.obj).obj D.obj :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom C.obj).obj D.obj)
    (fun v ↦ _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C.obj D.obj).symm v))).ι

/-- 概要：元の右保存関手圏を全関手圏へ含める。
方針：accessible な小極限保存関手の全部分複体の包含を使う。
規約：全自然変換を保持する。
使われ方：逆向きの右族の実際の関手としての評価。 -/
def rightFunctorInclusion (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace C D ⟶ (ihom C.obj).obj D.obj :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom C.obj).obj D.obj)
    (fun v ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C.obj D.obj).symm v) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C.obj D.obj).symm v))).ι

/-- 概要：固定二対象の全保存関手圏上の LR の実合成。
方針：全部分関手圏の包含の積と内部 Hom の合成を使う。
規約：core に切り詰めない。
使われ方：twisted arrow 上の単位図式の底。 -/
def pairUnitComposition (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C ⟶ (ihom C.obj).obj C.obj :=
  (leftFunctorInclusion C D ⊗ₘ rightFunctorInclusion D C) ≫
    MonoidalClosed.comp C.obj D.obj C.obj

/-- 概要：全関手圏の合成を両 core へ制限すると検証済みの局所単位合成を回収する。
方針：同じ二つの包含と同じ内部 Hom の合成を計算する。
規約：元の局所構成を別の合成で置き換えない。
使われ方：既存の両局所射影の結果との接続。 -/
lemma pairUnitComposition_core (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D)).ι ⊗ₘ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C)).ι) ≫ pairUnitComposition C D =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitComposition C D := by
  rfl

/-- 概要：左右の全保存関手族と恒等関手からの実単位図式の母対応。
方針：twisted arrow の共同評価を恒等関手の coslice 射影へ持ち上げる。
規約：随伴条件を課す前の単体集合であり、quasicategory 性はまだ主張しない。
使われ方：全自然変換を含む対ごとの随伴対応の入力。 -/
def PairRawUnitCorrespondence (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedPairLift
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj))))
    (pairUnitComposition C D)

/-- 概要：母対応から元の全左関手圏への単体射影。
方針：同じ左族を取り出す。
規約：全自然変換を含む e1 の関手圏。
使われ方：対ごとの双対性の左射影の母写像。 -/
def pairRawUnitLeft (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    PairRawUnitCorrespondence C D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedPairLiftLeft _ _

/-- 概要：母対応から元の全右関手圏の反対への単体射影。
方針：同じ逆向きの右族を取り出す。
規約：core ではなく元の全関手圏の反対に着地する。
使われ方：対ごとの双対性の右射影の母写像。 -/
def pairRawUnitRight (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    PairRawUnitCorrespondence C D ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C).op :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedPairLiftRight _ _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
