module
public import SerrePositivity.InfinityCategories.Derived.DGClosedRoofFinitePairs
public import SerrePositivity.InfinityCategories.Derived.DGActualRoofClosedTransport
public import SerrePositivity.InfinityCategories.Derived.RoofCompatibleTransportComposite

/-! # 一般有限対の実屋根比較のホモトピー相対充填

概要：任意の有限屋根比較正方形に、元の全指定部分と整合する実充填と二比較を供給する。
方針：共通実分母 fiber へ還元し、一般有限係数対を充填して二輸送を相対的に合成する。
規約：全境界・全時刻の一致を保持し、弱同値性の判定自体は別に行う。
使われ方：実屋根比較の有限対による弱い持ち上げ検査。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 任意の有限単体集合対の実屋根比較正方形は、全時刻整合的な相対充填を持つ。 -/
theorem dgActualRoofFinitePairs_nonempty (P : Set D) (hP : localKFlat A D P)
    (x y : D) {L K : SSet.{max u v}} (i : L ⟶ K) [Mono i] [K.Finite]
    (a : L ⟶ dgRoofCorrespondence A D P x y)
    (g : K ⟶ dgQuotientRoofCorrespondence A D P x y)
    (ha : a ≫ dgRoofCorrespondenceMap A D P x y = i ≫ g) :
    Nonempty (RoofHomotopyRelativeFiller i (dgRoofCorrespondenceMap A D P x y) a g) := by
  obtain ⟨R⟩ := dgActualRoofFiberReduction_nonempty A D P x y i a g ha
  obtain ⟨H⟩ := dgClosedRoofFinitePairs_nonempty A D P x y
    (dgActualRoofReductionDenominator A D P x y R) i
    (dgActualRoofClosedSourceCoefficient A D P x y R)
    (dgActualRoofClosedTargetCoefficient A D P x y R) hP
    (dgActualRoofClosedCoefficient_square A D P x y R)
  obtain ⟨T⟩ := roofCompatibleTransportComposite_nonempty
    (i := i) (F := dgRoofCorrespondenceMap A D P x y)
    (lA := H.boundary) (rA := dgActualRoofClosedBoundaryTransport A D P x y R)
    (lK := H.comparison) (rK := dgActualRoofClosedTargetTransport A D P x y R)
    H.compatibility (dgActualRoofClosedTransport_boundary A D P x y R)
  exact ⟨⟨H.filler, T.source, T.target, T.boundary⟩⟩

end SerrePositivity.InfinityCategories
