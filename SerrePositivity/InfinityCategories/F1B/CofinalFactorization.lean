module

public import SerrePositivity.InfinityCategories.F1B.LeftAnodyneFactorization
public import SerrePositivity.InfinityCategories.F1B.RightAnodyneFactorization
public import SerrePositivity.InfinityCategories.F1B.CofinalComposition

/-!
概要：cofinal な射の因子分解の fibration 側も cofinal となる。
方針：anodyne な左因子の cofinality と最初の因子の消去則を使う。
規約：右因子の trivial Kan fibration 性はここではまだ主張しない。
使われ方：Kerodon Proposition 7.2.1.15 に向けた、cofinal fibration への還元。
-/

@[expose] public section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：left cofinal な射を left anodyne な単射と left cofinal な left fibration に分解する。
方針：ホーンの因子分解を取り、left anodyne の十分性から後の因子の cofinality を得る。
規約：元の二対象は任意の単体集合。
使われ方：cofinal left fibration による判定への還元。 -/
lemma IsLeftCofinal.exists_anodyne_fibration_factorization {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : IsLeftCofinal f) :
    ∃ (Z : SSet.{u}) (i : X ⟶ Z) (p : Z ⟶ Y),
      Mono i ∧ leftAnodyneExtensions i ∧ LeftFibration p ∧ IsLeftCofinal p ∧ i ≫ p = f := by
  obtain ⟨Z, i, p, hm, hi, hp, he⟩ := exists_leftAnodyne_leftFibration_factorization f
  refine ⟨Z, i, p, hm, hi, hp, ?_, he⟩
  exact (isLeftCofinal_of_leftAnodyne i hi).cancel_left (he.symm ▸ hf)

/-- 概要：right cofinal な射を right anodyne な単射と right cofinal な right fibration に分解する。
方針：ホーンの因子分解を取り、right anodyne の十分性から後の因子の cofinality を得る。
規約：元の二対象は任意の単体集合。
使われ方：cofinal right fibration による判定への還元。 -/
lemma IsRightCofinal.exists_anodyne_fibration_factorization {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : IsRightCofinal f) :
    ∃ (Z : SSet.{u}) (i : X ⟶ Z) (p : Z ⟶ Y),
      Mono i ∧ rightAnodyneExtensions i ∧ RightFibration p ∧ IsRightCofinal p ∧ i ≫ p = f := by
  obtain ⟨Z, i, p, hm, hi, hp, he⟩ := exists_rightAnodyne_rightFibration_factorization f
  refine ⟨Z, i, p, hm, hi, hp, ?_, he⟩
  exact (isRightCofinal_of_rightAnodyne i hi).cancel_left (he.symm ▸ hf)

end SerrePositivity.InfinityCategories
