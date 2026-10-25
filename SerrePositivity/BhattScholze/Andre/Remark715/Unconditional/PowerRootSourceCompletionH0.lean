module

public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.PowerRootSourceNonpositive
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionH0Comparison

/-!
# André E1・E2：モニック f/d 源と raw 包の実完備化比較

## 概要

元の無限根モニック源の実 H⁰ を、同じ係数作用の raw 包およびその実完備化へ比較する。
BS Rem 7.15（著者版 p.62）の raw PD 環との比較の準備。

## 方針

一般 δ 除算の通常テンソル表示、標準 augmentation、実係数制限と完備化の既存比較を再利用する。
原典の Prop 7.11 を使う経路とは異なる、具体的な元の係数作用を保つ計算。

## 規約

この H⁰ 比較にはモニック性・正次数・有限性は不要。高次ホモロジー消滅は別の証明を使う。

## 使われ方

実完備化源の離散性と組み合わせ、元の係数射の完全忠実平坦性を raw PD 環へ移す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hpNat" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "D" => W.deltaStructure
local notation "d" => W.generator
local notation "dP" => algebraMap A (PowerRootPolynomial A p hpNat) d
local notation "Cp" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A d

/-- 概要：元の実係数源のp,d逐次実完備化も非正である。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem powerRootPrismMonicSourceIteratedPDCompletion_isLE_zero_of_unconditional :
    (PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f).obj.IsLE 0 := by
  apply DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A d _ 0
  exact DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A (p : A) _ 0
    (powerRootPrismMonicSourceCoefficient_isLE_zero_of_unconditional W hW f)

/-- 概要：raw係数対象の同じp,d逐次実完備化も非正である。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem powerRootPrismMonicSourceRawIteratedCompletion_isLE_zero_of_unconditional :
    (PowerRootPrismMonicSourceRawIteratedCompletion_of_unconditional W hW f).obj.IsLE 0 := by
  apply DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A d _ 0
  exact DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A (p : A) _ 0
    (powerRootPrismMonicSourceRawCoefficient_isLE_zero_of_unconditional W hW f)

/-- 概要：同じ元のaugmentationは、実p完備化後にもH0同型を誘導する。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem powerRootPrismMonicSourceRawPComparison_h0_isIso_of_unconditional :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (((Cp).map (powerRootPrismMonicSourceRawCoefficientAugmentation_of_unconditional W hW f)).hom)) := by
  exact DerivedCompletion.boundedAboveDerivedCompletion_h0_map_isIso A (p : A)
    (powerRootPrismMonicSourceRawCoefficientAugmentation_of_unconditional W hW f)
    (powerRootPrismMonicSourceCoefficient_isLE_zero_of_unconditional W hW f)
    (powerRootPrismMonicSourceRawCoefficient_isLE_zero_of_unconditional W hW f)
    (powerRootPrismMonicSourceRawCoefficientAugmentation_h0_isIso_of_unconditional W hW f)

/-- 概要：既存の標準逐次完備化比較射そのものがH0同型を誘導する。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem powerRootPrismMonicSourceRawIteratedComparison_h0_isIso_of_unconditional :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (powerRootPrismMonicSourceRawIteratedComparison_of_unconditional W hW f).hom) := by
  exact DerivedCompletion.boundedAboveDerivedCompletion_h0_map_isIso A d
    ((Cp).map (powerRootPrismMonicSourceRawCoefficientAugmentation_of_unconditional W hW f))
    (DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A (p : A) _ 0
      (powerRootPrismMonicSourceCoefficient_isLE_zero_of_unconditional W hW f))
    (DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A (p : A) _ 0
      (powerRootPrismMonicSourceRawCoefficient_isLE_zero_of_unconditional W hW f))
    (powerRootPrismMonicSourceRawPComparison_h0_isIso_of_unconditional W hW f)

/-- 概要：実逐次源のH0とrawの実逐次完備化のH0を、同じ標準比較射で同定する。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def powerRootPrismMonicSourceRawIteratedH0Iso_of_unconditional :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        (PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f).obj ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        (PowerRootPrismMonicSourceRawIteratedCompletion_of_unconditional W hW f).obj := by
  let := powerRootPrismMonicSourceRawIteratedComparison_h0_isIso_of_unconditional W hW f
  exact asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
    (powerRootPrismMonicSourceRawIteratedComparison_of_unconditional W hW f).hom)

end SerrePositivity.BhattScholze.Andre
