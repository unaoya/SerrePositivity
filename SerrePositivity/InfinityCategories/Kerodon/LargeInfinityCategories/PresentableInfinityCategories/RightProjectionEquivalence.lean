module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.UnitProjectionFibrations
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RightUnitFiberIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationContractible

/-!
概要：実単位の局所対応の右射影は元の右写像空間への QCat 同値。
方針：全ホーンの持ち上げと各固定ファイバーの可縮性から全境界を持ち上げる。
規約：二対象間の写像空間の射影についての結論であり、Pr 全体の同値とは区別する。
使われ方：全体の随伴対応の右射影の写像空間の同値性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の右写像空間への局所射影は right fibration。
方針：検証済みの全ホーンの持ち上げを右ホーンに制限する。
規約：元の射影の単体集合の射を使う。
使われ方：可縮ファイバーによる全境界の持ち上げ判定。 -/
instance adjointUnitRight_rightFibration (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointUnitRight C D) where
  mem := by
    have h := (SSet.modelCategoryQuillen.fibration_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointUnitRight C D)).mp inferInstance
    intro A B j hj
    cases hj with
    | @intro n i hi => exact h _ (SSet.modelCategoryQuillen.horn_ι_mem_J _ i)

/-- 概要：元の右写像空間への局所射影は全境界を持ち上げる。
方針：右ホーンの持ち上げと全高次ファイバーの可縮性を組み合わせる。
規約：可縮ファイバーだけから結論せず、検証済みの fibration 性を使う。
使われ方：右写像空間への同値性と厳密な選択の存在。 -/
instance adjointUnitRight_trivialKanFibration (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointUnitRight C D) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_trivialKanFibration_of_contractible_fibers _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointUnitRightFiber_isContractibleKan C D)

/-- 概要：実単位の局所対応の右射影は元の右写像空間への QCat 同値。
方針：同じ射影の全境界の持ち上げによる同値判定を適用する。
規約：元の e1 の全高次の右関手同値の写像空間を使う。
使われ方：全体の対応の右射影の充満忠実性を検証する局所入力。 -/
lemma adjointUnitRight_isQCatEquivalence (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointUnitRight C D) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _

/-- 概要：二対象間の実単位の局所対応と元の右写像空間の同値。
方針：同じ右射影の QCat 同値性から逆を選ぶ。
規約：全 Pr 圏の同値ではなく、明示した二対象間の写像空間の同値。
使われ方：全体の対応の右射影の局所同値を組み立てる。 -/
def adjointUnitRightMappingEquivalence (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AdjointUnitMappingSpace C D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRMappingSpace D C) :=
  (adjointUnitRight_isQCatEquivalence C D).choose

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
