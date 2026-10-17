module

public import SerrePositivity.BhattScholze.Andre.MonicPrismaticSourceCompletionH0
public import SerrePositivity.BhattScholze.Andre.MonicPrismaticRawCoefficients
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RestrictionCompletion
public import SerrePositivity.HomologicalAlgebra.AlgebraRestrictionSingle

/-!
# André E1・E2：モニック f/d 源と raw 包の実完備化比較

## 概要

一般モニック f/d 源の実 H⁰ を、同じ係数作用の raw 包およびその実完備化へ比較する。
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
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
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
def monicPrismaticRawCoefficientRestrictionIso :
    (MonicPrismaticSourceRawCoefficientObject D d f).obj ≅ (Res).obj M :=
  DerivedCategory.Minus.ι.mapIso (monicPrismaticSourceRawCoefficientSingleIso D d f) ≪≫
    (algebraRestrictionSingleIso A Raw).symm

/-- 概要：raw環自身の二つの主元についての実逐次完備化。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
abbrev MonicPrismaticRawInternalIteratedCompletion := (Bd).obj ((Bp).obj M)

/-- 概要：二度のG8を同じ係数射に適用した、元のraw実逐次対象との同型。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def monicPrismaticRawIteratedRestrictionIso :
    (MonicPrismaticSourceRawIteratedCompletion D d f).obj ≅
      (Res).obj (MonicPrismaticRawInternalIteratedCompletion D d f) :=
  (Cd).mapIso ((Cp).mapIso (monicPrismaticRawCoefficientRestrictionIso D d f)) ≪≫
    (Cd).mapIso ((derivedCompletionRestrictionIso c (p : A)).app M) ≪≫
    (derivedCompletionRestrictionIso c d).app ((Bp).obj M)

/-- 概要：係数比較は両方の元の主元完備化単位を保つ。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem monicPrismaticRawIteratedRestrictionIso_unit :
    ((derivedComplexCompletionUnit A (p : A)).app
        (MonicPrismaticSourceRawCoefficientObject D d f).obj ≫
      (derivedComplexCompletionUnit A d).app
        ((Cp).obj (MonicPrismaticSourceRawCoefficientObject D d f).obj)) ≫
      (monicPrismaticRawIteratedRestrictionIso D d f).hom =
    (monicPrismaticRawCoefficientRestrictionIso D d f).hom ≫
      (Res).map ((derivedComplexCompletionUnit Raw (c (p : A))).app M ≫
        (derivedComplexCompletionUnit Raw (c d)).app ((Bp).obj M)) := by
  let e := monicPrismaticRawCoefficientRestrictionIso D d f
  let eP := (Cp).mapIso e ≪≫ (derivedCompletionRestrictionIso c (p : A)).app M
  have hp : (derivedComplexCompletionUnit A (p : A)).app
      (MonicPrismaticSourceRawCoefficientObject D d f).obj ≫ eP.hom =
      e.hom ≫ (Res).map ((derivedComplexCompletionUnit Raw (c (p : A))).app M) := by
    have hn := (derivedComplexCompletionUnit A (p : A)).naturality e.hom
    simp only [Functor.id_map] at hn
    dsimp only [eP, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, ← hn, Category.assoc]
    erw [derivedCompletionRestrictionIso_unit]
  have hd := (derivedComplexCompletionUnit A d).naturality eP.hom
  simp only [Functor.id_map] at hd
  have he : (monicPrismaticRawIteratedRestrictionIso D d f).hom =
      (Cd).map eP.hom ≫ (derivedCompletionRestrictionIso c d).hom.app ((Bp).obj M) := by
    simp only [monicPrismaticRawIteratedRestrictionIso, eP, e, Iso.trans_hom,
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
def monicPrismaticRawIteratedRestrictionH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (MonicPrismaticSourceRawIteratedCompletion D d f).obj ≅
      (ModuleCat.restrictScalars c).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Raw) 0).obj
          (MonicPrismaticRawInternalIteratedCompletion D d f)) :=
  (DerivedCategory.homologyFunctor (ModuleCat A) 0).mapIso
    (monicPrismaticRawIteratedRestrictionIso D d f) ≪≫
      (derivedRestrictScalarsHomologyIso c 0).app _

/-- 概要：元の実モニック族添加源のH0をraw環上の実逐次完備化のH0と同定する。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def monicPrismaticSourceInternalRawH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (MonicPrismaticSourceIteratedPDCompletion D d f).obj ≅
      (ModuleCat.restrictScalars c).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Raw) 0).obj
          (MonicPrismaticRawInternalIteratedCompletion D d f)) :=
  monicPrismaticSourceRawIteratedH0Iso D d f ≪≫ monicPrismaticRawIteratedRestrictionH0Iso D d f

end SerrePositivity.BhattScholze.Andre
