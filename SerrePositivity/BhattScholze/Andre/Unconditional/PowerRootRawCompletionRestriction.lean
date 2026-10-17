module

public import SerrePositivity.BhattScholze.Andre.Unconditional.PowerRootSourceCompletionH0
public import SerrePositivity.BhattScholze.Andre.Unconditional.PowerRootRawCoefficients
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RestrictionCompletion
public import SerrePositivity.HomologicalAlgebra.AlgebraRestrictionSingle

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
local notation "M" => CategoryTheory.Functor.obj
  (DerivedCategory.singleFunctor (ModuleCat Raw) 0) (ModuleCat.of Raw Raw)
local notation "Cp" => derivedComplexCompletionFunctor A (p : A)
local notation "Cd" => derivedComplexCompletionFunctor A d
local notation "Bp" => derivedComplexCompletionFunctor Raw (c (p : A))
local notation "Bd" => derivedComplexCompletionFunctor Raw (c d)
local notation "Res" => derivedRestrictScalars c

/-- 概要：元のraw係数対象は、raw環自身のsingleを実係数射で制限した対象。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def powerRootPrismMonicRawCoefficientRestrictionIso_of_unconditional :
    (PowerRootPrismMonicSourceRawCoefficientObject_of_unconditional W hW f).obj ≅ (Res).obj M :=
  DerivedCategory.Minus.ι.mapIso (powerRootPrismMonicSourceRawCoefficientSingleIso_of_unconditional W hW f) ≪≫
    (algebraRestrictionSingleIso A Raw).symm

/-- 概要：raw環自身の二つの主元についての実逐次完備化。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
abbrev PowerRootPrismMonicRawInternalIteratedCompletion_of_unconditional := (Bd).obj ((Bp).obj M)

/-- 概要：二度のG8を同じ係数射に適用した、元のraw実逐次対象との同型。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def powerRootPrismMonicRawIteratedRestrictionIso_of_unconditional :
    (PowerRootPrismMonicSourceRawIteratedCompletion_of_unconditional W hW f).obj ≅
      (Res).obj (PowerRootPrismMonicRawInternalIteratedCompletion_of_unconditional W hW f) :=
  (Cd).mapIso ((Cp).mapIso (powerRootPrismMonicRawCoefficientRestrictionIso_of_unconditional W hW f)) ≪≫
    (Cd).mapIso ((derivedCompletionRestrictionIso c (p : A)).app M) ≪≫
    (derivedCompletionRestrictionIso c d).app ((Bp).obj M)

/-- 概要：係数比較は両方の元の主元完備化単位を保つ。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem powerRootPrismMonicRawIteratedRestrictionIso_unit_of_unconditional :
    ((derivedComplexCompletionUnit A (p : A)).app
        (PowerRootPrismMonicSourceRawCoefficientObject_of_unconditional W hW f).obj ≫
      (derivedComplexCompletionUnit A d).app
        ((Cp).obj (PowerRootPrismMonicSourceRawCoefficientObject_of_unconditional W hW f).obj)) ≫
      (powerRootPrismMonicRawIteratedRestrictionIso_of_unconditional W hW f).hom =
    (powerRootPrismMonicRawCoefficientRestrictionIso_of_unconditional W hW f).hom ≫
      (Res).map ((derivedComplexCompletionUnit Raw (c (p : A))).app M ≫
        (derivedComplexCompletionUnit Raw (c d)).app ((Bp).obj M)) := by
  let e := powerRootPrismMonicRawCoefficientRestrictionIso_of_unconditional W hW f
  let eP := (Cp).mapIso e ≪≫ (derivedCompletionRestrictionIso c (p : A)).app M
  have hp : (derivedComplexCompletionUnit A (p : A)).app
      (PowerRootPrismMonicSourceRawCoefficientObject_of_unconditional W hW f).obj ≫ eP.hom =
      e.hom ≫ (Res).map ((derivedComplexCompletionUnit Raw (c (p : A))).app M) := by
    have hn := (derivedComplexCompletionUnit A (p : A)).naturality e.hom
    simp only [Functor.id_map] at hn
    dsimp only [eP, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, ← hn, Category.assoc]
    erw [derivedCompletionRestrictionIso_unit]
  have hd := (derivedComplexCompletionUnit A d).naturality eP.hom
  simp only [Functor.id_map] at hd
  have he : (powerRootPrismMonicRawIteratedRestrictionIso_of_unconditional W hW f).hom =
      (Cd).map eP.hom ≫ (derivedCompletionRestrictionIso c d).hom.app ((Bp).obj M) := by
    simp only [powerRootPrismMonicRawIteratedRestrictionIso_of_unconditional, eP, e, Iso.trans_hom,
      Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    rfl
  rw [he]
  simp only [Category.assoc]
  rw [← Category.assoc ((derivedComplexCompletionUnit A d).app _) ((Cd).map eP.hom),
    ← hd]
  simp only [Category.assoc]
  erw [derivedCompletionRestrictionIso_unit]
  rw [← Category.assoc, hp, Category.assoc, ← Functor.map_comp]

/-- 概要：raw環上の同じ実逐次完備化のH0へ、元のA作用を保って比較する。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def powerRootPrismMonicRawIteratedRestrictionH0Iso_of_unconditional :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (PowerRootPrismMonicSourceRawIteratedCompletion_of_unconditional W hW f).obj ≅
      (ModuleCat.restrictScalars c).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Raw) 0).obj
          (PowerRootPrismMonicRawInternalIteratedCompletion_of_unconditional W hW f)) :=
  (DerivedCategory.homologyFunctor (ModuleCat A) 0).mapIso
    (powerRootPrismMonicRawIteratedRestrictionIso_of_unconditional W hW f) ≪≫
      (derivedRestrictScalarsHomologyIso c 0).app _

/-- 概要：元の実モニック族添加源のH0をraw環上の実逐次完備化のH0と同定する。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def powerRootPrismMonicSourceInternalRawH0Iso_of_unconditional :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f).obj ≅
      (ModuleCat.restrictScalars c).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Raw) 0).obj
          (PowerRootPrismMonicRawInternalIteratedCompletion_of_unconditional W hW f)) :=
  powerRootPrismMonicSourceRawIteratedH0Iso_of_unconditional W hW f ≪≫ powerRootPrismMonicRawIteratedRestrictionH0Iso_of_unconditional W hW f

end SerrePositivity.BhattScholze.Andre
