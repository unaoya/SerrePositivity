module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Restriction.Completion
public import SerrePositivity.HomologicalAlgebra.DerivedRestrictionConservative

/-!
# 二座標完備化と任意の係数制限

## 概要
二座標の実導来完備化は任意の環射によるスカラー制限と自然に可換である。

## 方針
一座標の既存の比較を二回合成する。係数制限の完備性保存と同型の反映は既存 API を使う。

## 規約
BS 著者版 Theorem 6.3、D30。上に有界な導来圏に限定しない。

## 使われ方
普遍 prism から一般の基底への制限と、二座標完備化の両立。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 概要：二座標完備化と係数制限の自然同型。
方針：一座標の完備化比較を二回 whisker して合成する。
規約：BS 著者版 Theorem 6.3、D30、任意の非有界な導来対象。
使われ方：普遍基底への制限と二座標完備底変換の比較。 -/
def pairCompletionRestrictionIso (f : R →+* S) (a b : R) :
    derivedRestrictScalars f ⋙
      (derivedComplexCompletionFunctor R a ⋙ derivedComplexCompletionFunctor R b) ≅
      (derivedComplexCompletionFunctor S (f a) ⋙ derivedComplexCompletionFunctor S (f b)) ⋙
        derivedRestrictScalars f :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedCompletionRestrictionIso f a) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (derivedCompletionRestrictionIso f b) ≪≫
    (Functor.associator _ _ _).symm

/-- 概要：二座標完備化の制限比較は任意の導来射と両立する。
方針：上の自然同型の自然性をそのまま取り出す。
規約：BS 著者版 Theorem 6.3、D30。使われ方：比較射を普遍基底で調べる際の可換図式。 -/
@[reassoc] theorem pairCompletionRestrictionIso_naturality (f : R →+* S) (a b : R)
    {X Y : ConcreteDerivedCategory S} (g : X ⟶ Y) :
    (derivedComplexCompletionFunctor R b).map
        ((derivedComplexCompletionFunctor R a).map ((derivedRestrictScalars f).map g)) ≫
      (pairCompletionRestrictionIso f a b).hom.app Y =
    (pairCompletionRestrictionIso f a b).hom.app X ≫
      (derivedRestrictScalars f).map ((derivedComplexCompletionFunctor S (f b)).map
        ((derivedComplexCompletionFunctor S (f a)).map g)) :=
  (pairCompletionRestrictionIso f a b).hom.naturality g

end SerrePositivity.DerivedCompletion
