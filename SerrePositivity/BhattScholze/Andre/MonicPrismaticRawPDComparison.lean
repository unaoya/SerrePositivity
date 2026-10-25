module

public import SerrePositivity.BhattScholze.Andre.MonicPrismaticRawCompletionRestriction
public import SerrePositivity.BhattScholze.Andre.RootedExtension.IteratedPDH0Reflection

/-!
# André E1・E2：モニック源の実 H⁰ と raw PD 完備化環の比較

## 概要

一般モニック f/d 源の実逐次 p,d 完備化の H⁰ は、raw f/d 包の実 PD 完備化 H⁰ と A 線形同型。
BS Rem 7.15（著者版 p.62）の実源と環候補の比較。

## 方針

源の標準 augmentation の H⁰ 比較、G8 の係数制限比較、既存の一般二座標 H⁰ 反射比較を合成する。
原典の Prop 7.11 を使う証明とは異なる具体的係数射を保つ計算。

## 規約

モニック性・正次数・有限性はこの比較には不要。高次消滅は別に証明済みの純性から得る。

## 使われ方

完全 prism 上の有限族の実源の離散性から、raw PD 環の元の係数射の完全忠実平坦性へ移す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "z" => c d
local notation "a" => c (p : A)
local notation "Z" => MonicPrismaticRawInternalIteratedCompletion D d f
local notation "H" => CategoryTheory.Functor.obj (DerivedCategory.homologyFunctor (ModuleCat Raw) 0)

/-- 概要：raw 包自身の逐次実完備化 H⁰ は、元の Raw 線形単位を保って PD 完備化 H⁰ と同型。
方針：一般二座標 H⁰ 反射の既存比較をそのまま適用する。
規約：第一座標の像が自然数 p であることを明示する。
使われ方：BS Rem 7.15（著者版 p.62）の実源から環候補への比較の最終段。 -/
def monicPrismaticRawInternalPDLinearEquiv : H Z ≃ₗ[Raw] PDCompletionH0 Raw p z :=
  iteratedPDH0LinearEquiv Raw a z p (map_natCast c p)

/-- 概要：raw 自身の比較は、すべての raw 係数の元の標準完備化像を保つ。
方針：一般 H⁰ 反射比較の標準単位公式を再利用する。
規約：単位 1 だけでなく任意の raw 元で述べる。
使われ方：BS Rem 7.15（著者版 p.62）の候補係数射との後続比較。 -/
theorem monicPrismaticRawInternalPDLinearEquiv_unit (x : Raw) :
    monicPrismaticRawInternalPDLinearEquiv D d f (iteratedPDH0Unit Raw a z x) =
      koszulCompletionH0Unit Raw (pairKoszulCoordinates Raw (p : Raw) z) x :=
  iteratedPDH0LinearEquiv_unit Raw a z p (map_natCast c p) x

/-- 概要：元の実モニック源の逐次完備化 H⁰ は、raw PD 環の同じ A 係数制限と同型。
方針：標準 augmentation、二度の G8、Raw 線形 H⁰ 反射比較を順に合成する。
規約：元の A 作用を保つ加群同型を構成する。
使われ方：BS Rem 7.15（著者版 p.62）の環候補の完全忠実平坦性への移送。 -/
def monicPrismaticSourcePDH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (MonicPrismaticSourceIteratedPDCompletion D d f).obj ≅
      (ModuleCat.restrictScalars c).obj (ModuleCat.of Raw (PDCompletionH0 Raw p z)) :=
  monicPrismaticSourceInternalRawH0Iso D d f ≪≫
    (ModuleCat.restrictScalars c).mapIso
      (monicPrismaticRawInternalPDLinearEquiv D d f).toModuleIso

end SerrePositivity.BhattScholze.Andre
