module

public import SerrePositivity.BhattScholze.Andre.Unconditional.PowerRootRawCompletionRestriction
public import SerrePositivity.BhattScholze.IteratedPDH0Reflection

/-!
# André E1・E2：モニック源の実 H⁰ と raw PD 完備化環の比較

## 概要

元の無限根モニック源の実逐次 p,d 完備化の H⁰ は、raw f/d 包の実 PD 完備化 H⁰ と A 線形同型。
BS Rem 7.15（著者版 p.62）の実源と環候補の比較。

## 方針

源の標準 augmentation の H⁰ 比較、G8 の係数制限比較、既存の一般二座標 H⁰ 反射比較を合成する。
原典の Prop 7.11 を使う証明とは異なる具体的係数射を保つ計算。

## 規約

モニック性・正次数・有限性はこの比較には不要。高次消滅は別に証明済みの純性から得る。

## 使われ方

完全 prism 上の無限根族の実源の離散性から、raw PD 環の元の係数射の完全忠実平坦性へ移す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hpNat" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "D" => W.deltaStructure
local notation "d" => W.generator
local notation "dP" => algebraMap A (PowerRootPolynomial A p hpNat) d
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "r" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "Raw" => DeltaAdjoinDivision E dP r
local notation "c" => algebraMap A Raw
local notation "z" => c d
local notation "a" => c (p : A)
local notation "Z" => PowerRootPrismMonicRawInternalIteratedCompletion_of_unconditional W hW f
local notation "H" => CategoryTheory.Functor.obj (DerivedCategory.homologyFunctor (ModuleCat Raw) 0)

/-- 概要：raw 包自身の逐次実完備化 H⁰ は、元の Raw 線形単位を保って PD 完備化 H⁰ と同型。
方針：一般二座標 H⁰ 反射の既存比較をそのまま適用する。
規約：第一座標の像が自然数 p であることを明示する。
使われ方：BS Rem 7.15（著者版 p.62）の実源から環候補への比較の最終段。 -/
def powerRootPrismMonicRawInternalPDLinearEquiv_of_unconditional : H Z ≃ₗ[Raw] PDCompletionH0 Raw p z :=
  iteratedPDH0LinearEquiv Raw a z p (map_natCast c p)

/-- 概要：raw 自身の比較は、すべての raw 係数の元の標準完備化像を保つ。
方針：一般 H⁰ 反射比較の標準単位公式を再利用する。
規約：単位 1 だけでなく任意の raw 元で述べる。
使われ方：BS Rem 7.15（著者版 p.62）の候補係数射との後続比較。 -/
theorem powerRootPrismMonicRawInternalPDLinearEquiv_unit_of_unconditional (x : Raw) :
    powerRootPrismMonicRawInternalPDLinearEquiv_of_unconditional W hW f (iteratedPDH0Unit Raw a z x) =
      koszulCompletionH0Unit Raw (pairKoszulCoordinates Raw (p : Raw) z) x :=
  iteratedPDH0LinearEquiv_unit Raw a z p (map_natCast c p) x

/-- 概要：元の実モニック源の逐次完備化 H⁰ は、raw PD 環の同じ A 係数制限と同型。
方針：標準 augmentation、二度の G8、Raw 線形 H⁰ 反射比較を順に合成する。
規約：元の A 作用を保つ加群同型を構成する。
使われ方：BS Rem 7.15（著者版 p.62）の環候補の完全忠実平坦性への移送。 -/
def powerRootPrismMonicSourcePDH0Iso_of_unconditional :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f).obj ≅
      (ModuleCat.restrictScalars c).obj (ModuleCat.of Raw (PDCompletionH0 Raw p z)) :=
  powerRootPrismMonicSourceInternalRawH0Iso_of_unconditional W hW f ≪≫
    (ModuleCat.restrictScalars c).mapIso
      (powerRootPrismMonicRawInternalPDLinearEquiv_of_unconditional W hW f).toModuleIso

end SerrePositivity.BhattScholze.Andre
