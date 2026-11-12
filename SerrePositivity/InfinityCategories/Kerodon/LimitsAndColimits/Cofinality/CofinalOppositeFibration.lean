module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeOuterHornOp
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalFactorizationCriterion

/-!
概要：反転による左右の fibration と anodyne 性の交換。
方針：ホーンの反転同型と反転関手の自己随伴で持ち上げ性を移す。
規約：quasicategory 性は要求しない。
使われ方：left cofinality と right cofinality の双対性。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：left fibration を反転すると right fibration。
方針：右ホーンの反転同型で左ホーンの持ち上げへ戻す。
規約：元の二対象は任意。
使われ方：反転関手の随伴で right anodyne 性を左へ移す。 -/
instance cofinalLeftFibration_op_rightFibration {X Y : SSet.{u}} (q : X ⟶ Y)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (SSet.opFunctor.map q) where
  mem := by
    intro A B j hj
    cases hj with
    | @intro n i hn =>
      have hlast : i.rev < Fin.last (n + 1) := by
        change i.rev.val < n + 1
        rw [Fin.val_rev]
        have h : 0 < i.val := hn
        omega
      let e' : Arrow.mk (horn (n + 1) i.rev.rev).ι ≅
          Arrow.mk (SSet.opFunctor.map (horn (n + 1) i.rev).ι) :=
        Arrow.isoMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornReverseIso (n + 1) i.rev) (stdSimplex.opIso ⦋n + 1⦌).symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornReverseIso_hom_ι (n + 1) i.rev)
      have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
      have h : HasLiftingProperty (horn (n + 1) i.rev.rev).ι (SSet.opFunctor.map q) := by
        apply (HasLiftingProperty.iff_of_arrow_iso_left e' _).mpr
        apply (SSet.opFunctor.hasLiftingProperty_iff_of_isEquivalence _ _).mpr
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := q) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions.intro i.rev hlast)
      exact (congrArg (fun k : Fin (n + 2) ↦
        HasLiftingProperty (horn (n + 1) k).ι (SSet.opFunctor.map q)) (Fin.rev_rev i)).mp h

/-- 概要：left anodyne な射の反転は right anodyne。
方針：right fibration の反転の left fibration 性と自己随伴の持ち上げ対応を使う。
規約：反転は単体集合の共変な関手。
使われ方：left cofinal な射の反転の因子分解。 -/
lemma cofinalRightAnodyne_op_of_leftAnodyne {A B : SSet.{u}} (i : A ⟶ B)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (SSet.opFunctor.map i) := by
  intro E D p hp
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p := ⟨hp⟩
  have h : HasLiftingProperty i (SSet.opFunctor.map p) :=
    hi _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := SSet.opFunctor.map p))
  exact (SSet.opEquivalence.toAdjunction.hasLiftingProperty_iff i p).mpr h

/-- 概要：right anodyne な射の反転は left anodyne。
方針：left fibration の反転の right fibration 性と自己随伴の持ち上げ対応を使う。
規約：元の射に単射性を別に仮定しない。
使われ方：right cofinal な射の反転の因子分解。 -/
lemma cofinalLeftAnodyne_op_of_rightAnodyne {A B : SSet.{u}} (i : A ⟶ B)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions i) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions (SSet.opFunctor.map i) := by
  intro E D p hp
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p := ⟨hp⟩
  have h : HasLiftingProperty i (SSet.opFunctor.map p) :=
    hi _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p := SSet.opFunctor.map p))
  exact (SSet.opEquivalence.toAdjunction.hasLiftingProperty_iff i p).mpr h

/-- 概要：trivial Kan fibration の反転も trivial Kan fibration。
方針：反転した単射への持ち上げ性を自己随伴で戻す。
規約：元の二対象の充填性は別に要求しない。
使われ方：cofinality の anodyne・trivial Kan 因子分解の双対化。 -/
instance cofinalTrivialKanFibration_op {E B : SSet.{u}} (p : E ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (SSet.opFunctor.map p) where
  mem := by
    intro A D i hi
    have : Mono i := hi
    have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
    have h : HasLiftingProperty (SSet.opFunctor.map i) p :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := p) _ inferInstance
    exact (SSet.opEquivalence.toAdjunction.hasLiftingProperty_iff i p).mp h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
