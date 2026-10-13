module

public import SerrePositivity.Spectra.Pointed.InternalHom
public import SerrePositivity.Spectra.Pointed.ReducedPair

/-!
# smash 積と基点付き内部 Hom の curry

## 証明の筋道

二変数で reduced な射を基礎圏で curry する。
第一変数の基点での定数性は内部 Hom の等化子の条件、第二変数の定数性は
その等化子へ送る射が基点を保つ条件となる。
uncurry も同じ二つの条件を満たし、往復が恒等となることを確認する。

## 用途

smash の普遍性と合成して Hom 同値を得る。
モノイダル構造の登録を前提にせず、次に構成する随伴・結合子の基盤にする。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.PointedObject

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [MonoidalClosed C] [HasEqualizers C]

/-- reduced map の curry は、基点付き内部 Hom への基点を保つ射となる。 -/
def reducedCurry {X Y Z : PointedObject C} (f : ReducedPairMap X Y Z) : Y ⟶ basedHom X Z :=
  Under.homMk (equalizer.lift (f := homRestriction X Z) (g := homConstant X Z)
    (curry f.1) (by
      rw [homRestriction, curry_pre_app, f.2.1, curry_constant]
      simp [homConstant, homBasepoint, point])) (by
        apply (cancel_mono (basedHomι X Z)).mp
        rw [Category.assoc, basedHom_basepoint_ι]
        simp only [basedHomι, equalizer.lift_ι]
        rw [← curry_natural_left, f.2.2]
        rfl)

@[reassoc (attr := simp)] lemma reducedCurry_ι {X Y Z : PointedObject C}
    (f : ReducedPairMap X Y Z) : (reducedCurry f).right ≫ basedHomι X Z = curry f.1 :=
  equalizer.lift_ι ..

/-- 基点付き内部 Hom への射を uncurry すると、両変数で reduced な射となる。 -/
def reducedUncurry {X Y Z : PointedObject C} (f : Y ⟶ basedHom X Z) : ReducedPairMap X Y Z :=
  ⟨uncurry (f.right ≫ basedHomι X Z), by
    apply curry_injective
    rw [← curry_pre_app, curry_uncurry, curry_constant]
    have h := basedHomι_condition X Z
    dsimp only [homRestriction] at h
    rw [Category.assoc, h]
    simp [homConstant, homBasepoint, point], by
    rw [← uncurry_natural_left, ← Category.assoc, Under.w f, basedHom_basepoint_ι]
    exact uncurry_curry _⟩

/-- 二変数で reduced な射と、基点付き内部 Hom への射は同値。
往復の等式は基礎圏の curry・uncurry と等化子のモノ射性から得る。 -/
def reducedCurryEquiv (X Y Z : PointedObject C) :
    ReducedPairMap X Y Z ≃ (Y ⟶ basedHom X Z) where
  toFun := reducedCurry
  invFun := reducedUncurry
  left_inv f := by
    apply Subtype.ext
    simp [reducedUncurry]
  right_inv f := by
    apply Under.UnderMorphism.ext
    apply (cancel_mono (basedHomι X Z)).mp
    simp [reducedCurry_ι, reducedUncurry]

variable [HasFiniteColimits C]

/-- smash から出る射を、基点付き内部 Hom への射として curry する。 -/
def smashCurry {X Y Z : PointedObject C} (f : smash X Y ⟶ Z) : Y ⟶ basedHom X Z :=
  reducedCurry (smashToReduced f)

@[reassoc (attr := simp)] lemma smashCurry_ι {X Y Z : PointedObject C}
    (f : smash X Y ⟶ Z) : (smashCurry f).right ≫ basedHomι X Z =
      curry ((smashQuotient X Y).right ≫ f.right) := reducedCurry_ι ..

/-- smash と基点付き内部 Hom の Hom 同値。
軸を潰す商の普遍性と、閉直積圏の curry を順に使う。 -/
def smashBasedHomEquiv (X Y Z : PointedObject C) :
    (smash X Y ⟶ Z) ≃ (Y ⟶ basedHom X Z) :=
  (smashReducedHomEquiv X Y Z).trans (reducedCurryEquiv X Y Z)

@[simp] lemma smashBasedHomEquiv_apply {X Y Z : PointedObject C} (f : smash X Y ⟶ Z) :
    smashBasedHomEquiv X Y Z f = smashCurry f := rfl

end SerrePositivity.PointedObject
