module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.TrivialFibrationCofinality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalAnodyneRecognition
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：cofinality の fibration による判定と anodyne・trivial Kan 因子分解による特徴づけ。
方針：trivial Kan fibration の左右 cofinality と既存の必要性・合成則を合わせる。
規約：始域と終域の quasicategory 性や Kan 性を要求しない。
使われ方：Kerodon Corollaries 7.2.1.14（Tag 02ND）–7.2.1.15（Tag 02NE）、Quillen A の還元。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：trivial Kan fibration 性は left fibration 性と left cofinality の組に一致する。
方針：全境界の判定と、切断による左右 cofinality の十分性を使う。
規約：left fibration 性も命題の右辺に明記する。
使われ方：Kerodon Corollary 7.2.1.14（Tag 02ND） の (1)⇔(3)。 -/
@[kerodon 02ND]
lemma trivialKanFibration_iff_leftFibration_and_isLeftCofinal {A B : SSet.{u}} (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration f ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration f ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal f := by
  constructor
  · intro hf
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration f := hf
    exact ⟨inferInstance, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_trivialKanFibration f⟩
  · rintro ⟨hf, hc⟩
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration f := hf
    exact hc.trivialKanFibration

/-- 概要：trivial Kan fibration 性は right fibration 性と right cofinality の組に一致する。
方針：可縮 fiber の判定と、切断による左右 cofinality の十分性を使う。
規約：right fibration 性も命題の右辺に明記する。
使われ方：Kerodon Corollary 7.2.1.14（Tag 02ND） の (2)⇔(3)。 -/
@[kerodon 02ND]
lemma trivialKanFibration_iff_rightFibration_and_isRightCofinal {A B : SSet.{u}} (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration f ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration f ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal f := by
  constructor
  · intro hf
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration f := hf
    exact ⟨inferInstance, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_trivialKanFibration f⟩
  · rintro ⟨hf, hc⟩
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration f := hf
    exact hc.trivialKanFibration

/-- 概要：left cofinality は left anodyne・trivial Kan 因子分解の存在と同値。
方針：cofinal な因子分解の必要性と、両因子の cofinality の合成を使う。
規約：因子分解の等式は厳密で、単射性は anodyne 性から従う。
使われ方：Kerodon Corollary 7.2.1.15（Tag 02NE）。 -/
@[kerodon 02NE]
lemma isLeftCofinal_iff_exists_anodyne_trivialKan_factorization {A B : SSet.{u}} (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal f ↔ ∃ (Z : SSet.{u}) (i : A ⟶ Z) (p : Z ⟶ B),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p ∧ i ≫ p = f := by
  constructor
  · intro hf
    obtain ⟨Z, i, p, _, hi, hp, he⟩ := hf.exists_anodyne_trivialKan_factorization
    exact ⟨Z, i, p, hi, hp, he⟩
  · rintro ⟨Z, i, p, hi, hp, he⟩
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p := hp
    exact he ▸ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_leftAnodyne i hi).comp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_trivialKanFibration p)

/-- 概要：right cofinality は right anodyne・trivial Kan 因子分解の存在と同値。
方針：cofinal な因子分解の必要性と、両因子の cofinality の合成を使う。
規約：因子分解の等式は厳密で、元の両対象は任意。
使われ方：Kerodon Corollary 7.2.1.15（Tag 02NE） の双対。 -/
lemma isRightCofinal_iff_exists_anodyne_trivialKan_factorization {A B : SSet.{u}} (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal f ↔ ∃ (Z : SSet.{u}) (i : A ⟶ Z) (p : Z ⟶ B),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions i ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p ∧ i ≫ p = f := by
  constructor
  · intro hf
    obtain ⟨Z, i, p, _, hi, hp, he⟩ := hf.exists_anodyne_trivialKan_factorization
    exact ⟨Z, i, p, hi, hp, he⟩
  · rintro ⟨Z, i, p, hi, hp, he⟩
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p := hp
    exact he ▸ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_rightAnodyne i hi).comp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_trivialKanFibration p)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
