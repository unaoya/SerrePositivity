module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalOverLifting

/-!
概要：通常の slice 圏の左随伴による right anodyne 性の生成元からの移送。
方針：右ホーンに関する持ち上げ性を随伴で右随伴へ移し、元の right anodyne 性を使う。
規約：生成元の像の条件と通常の圏の随伴だけを入力とする。
使われ方：引き戻しと依存積の随伴に全右ホーンの引き戻しの定理を適用する。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：右随伴は、左随伴が右ホーンを right anodyne に送れば right fibration を保つ。
方針：ホーンの持ち上げを slice に移し、随伴の持ち上げ対応を使う。
規約：随伴は通常の単体集合の圏の slice 間のもの。
使われ方：生成元から一般の right anodyne な射への拡張。 -/
lemma cofinalRightFibration_rightAdjoint_of_horns {B E : SSet.{u}}
    {L : Over B ⥤ Over E} {R : Over E ⥤ Over B} (adj : L ⊣ R)
    (hL : ∀ {A D : Over B} (i : A ⟶ D), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions i.left →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (L.map i).left)
    {X Y : Over E} (q : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration q.left] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (R.map q).left := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalRightFibration_of_over_lifting
  intro A D i hi
  have : HasLiftingProperty (L.map i).left q.left :=
    hL i hi q.left (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p := q.left))
  have := HasLiftingProperty.over (L.map i) q
  exact (adj.hasLiftingProperty_iff i q).mp inferInstance

/-- 概要：slice の左随伴が右ホーンを right anodyne に送れば、全ての right anodyne な射を保つ。
方針：右随伴の right fibration の保存と持ち上げ性の随伴対応を二度使う。
規約：閉包の保存を新たな公理やフィールドとして要求しない。
使われ方：left fibration に沿う引き戻しの生成元の結果を一般の射へ移す。 -/
lemma cofinalRightAnodyne_leftAdjoint_of_horns {B E : SSet.{u}}
    {L : Over B ⥤ Over E} {R : Over E ⥤ Over B} (adj : L ⊣ R)
    (hL : ∀ {A D : Over B} (i : A ⟶ D), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions i.left →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (L.map i).left)
    {A D : Over B} (i : A ⟶ D) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions i.left) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (L.map i).left := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalRightAnodyne_of_over_lifting
  intro X Y q hq
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration q.left := hq
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (R.map q).left :=
    cofinalRightFibration_rightAdjoint_of_horns adj hL q
  have : HasLiftingProperty i.left (R.map q).left :=
    hi (R.map q).left (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p := (R.map q).left))
  have := HasLiftingProperty.over i (R.map q)
  exact (adj.hasLiftingProperty_iff i q).mpr inferInstance

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
