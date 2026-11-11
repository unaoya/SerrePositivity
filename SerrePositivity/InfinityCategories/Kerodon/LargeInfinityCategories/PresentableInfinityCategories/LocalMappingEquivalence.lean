module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftProjectionEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RightProjectionEquivalence

/-!
概要：二対象間の元の左・右随伴写像空間を実単位の対応で比較する。
方針：局所対応の左射影の逆同値と右射影の同値を合成する。
規約：二対象間の写像空間の結論であり、全 Pr 圏上の構成は別工程。
使われ方：全体の随伴対応の両射影の局所同値性への入力。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：二対象間の左随伴・右随伴の元の写像空間は QCat 同値。
方針：同じ実単位の局所対応の両射影の同値を合成する。
規約：元の e1 の写像空間を使い、同値の存在を仮定しない。
使われ方：全 Pr の対応の局所の充満忠実性を構成するための界面。 -/
def adjointMappingEquivalence (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLMappingSpace C D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRMappingSpace D C) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointUnitLeftMappingEquivalence C D).symm.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointUnitRightMappingEquivalence C D)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
