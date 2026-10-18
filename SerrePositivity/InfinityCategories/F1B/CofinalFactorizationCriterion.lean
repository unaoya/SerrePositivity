module

public import SerrePositivity.InfinityCategories.F1B.TrivialFibrationCofinality
public import SerrePositivity.InfinityCategories.F1B.CofinalAnodyneRecognition

/-!
概要：cofinality の fibration による判定と anodyne・trivial Kan 因子分解による特徴づけ。
方針：trivial Kan fibration の左右 cofinality と既存の必要性・合成則を合わせる。
規約：始域と終域の quasicategory 性や Kan 性を要求しない。
使われ方：Kerodon Corollaries 7.2.1.14–7.2.1.15、Quillen A の還元。
-/

@[expose] public section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：trivial Kan fibration 性は left fibration 性と left cofinality の組に一致する。
方針：全境界の判定と、切断による左右 cofinality の十分性を使う。
規約：left fibration 性も命題の右辺に明記する。
使われ方：Kerodon Corollary 7.2.1.14 の (1)⇔(3)。 -/
lemma trivialKanFibration_iff_leftFibration_and_isLeftCofinal {A B : SSet.{u}} (f : A ⟶ B) :
    TrivialKanFibration f ↔ LeftFibration f ∧ IsLeftCofinal f := by
  constructor
  · intro hf
    have : TrivialKanFibration f := hf
    exact ⟨inferInstance, isLeftCofinal_of_trivialKanFibration f⟩
  · rintro ⟨hf, hc⟩
    have : LeftFibration f := hf
    exact hc.trivialKanFibration

/-- 概要：trivial Kan fibration 性は right fibration 性と right cofinality の組に一致する。
方針：可縮 fiber の判定と、切断による左右 cofinality の十分性を使う。
規約：right fibration 性も命題の右辺に明記する。
使われ方：Kerodon Corollary 7.2.1.14 の (2)⇔(3)。 -/
lemma trivialKanFibration_iff_rightFibration_and_isRightCofinal {A B : SSet.{u}} (f : A ⟶ B) :
    TrivialKanFibration f ↔ RightFibration f ∧ IsRightCofinal f := by
  constructor
  · intro hf
    have : TrivialKanFibration f := hf
    exact ⟨inferInstance, isRightCofinal_of_trivialKanFibration f⟩
  · rintro ⟨hf, hc⟩
    have : RightFibration f := hf
    exact hc.trivialKanFibration

/-- 概要：left cofinality は left anodyne・trivial Kan 因子分解の存在と同値。
方針：cofinal な因子分解の必要性と、両因子の cofinality の合成を使う。
規約：因子分解の等式は厳密で、単射性は anodyne 性から従う。
使われ方：Kerodon Corollary 7.2.1.15。 -/
lemma isLeftCofinal_iff_exists_anodyne_trivialKan_factorization {A B : SSet.{u}} (f : A ⟶ B) :
    IsLeftCofinal f ↔ ∃ (Z : SSet.{u}) (i : A ⟶ Z) (p : Z ⟶ B),
      leftAnodyneExtensions i ∧ TrivialKanFibration p ∧ i ≫ p = f := by
  constructor
  · intro hf
    obtain ⟨Z, i, p, _, hi, hp, he⟩ := hf.exists_anodyne_trivialKan_factorization
    exact ⟨Z, i, p, hi, hp, he⟩
  · rintro ⟨Z, i, p, hi, hp, he⟩
    have : TrivialKanFibration p := hp
    exact he ▸ (isLeftCofinal_of_leftAnodyne i hi).comp (isLeftCofinal_of_trivialKanFibration p)

/-- 概要：right cofinality は right anodyne・trivial Kan 因子分解の存在と同値。
方針：cofinal な因子分解の必要性と、両因子の cofinality の合成を使う。
規約：因子分解の等式は厳密で、元の両対象は任意。
使われ方：Kerodon Corollary 7.2.1.15 の双対。 -/
lemma isRightCofinal_iff_exists_anodyne_trivialKan_factorization {A B : SSet.{u}} (f : A ⟶ B) :
    IsRightCofinal f ↔ ∃ (Z : SSet.{u}) (i : A ⟶ Z) (p : Z ⟶ B),
      rightAnodyneExtensions i ∧ TrivialKanFibration p ∧ i ≫ p = f := by
  constructor
  · intro hf
    obtain ⟨Z, i, p, _, hi, hp, he⟩ := hf.exists_anodyne_trivialKan_factorization
    exact ⟨Z, i, p, hi, hp, he⟩
  · rintro ⟨Z, i, p, hi, hp, he⟩
    have : TrivialKanFibration p := hp
    exact he ▸ (isRightCofinal_of_rightAnodyne i hi).comp (isRightCofinal_of_trivialKanFibration p)

end SerrePositivity.InfinityCategories
