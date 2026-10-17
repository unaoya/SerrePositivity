module

public import SerrePositivity.BhattScholze.Andre.Unconditional.PowerRootRawSourceComparison
public import SerrePositivity.HomologicalAlgebra.DerivedTensorNonpositive

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
/-- 概要：二つの次数零加群の実導来テンソルは、係数制限後も非正次数にある。
方針：非正射影モデルのテンソルと正確な係数制限で計算する。
規約：平坦性・モニック性を仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の元の実源の H⁰ 完備化比較。 -/
theorem unconditionalRestrictedTensor_isLE_zero
    {S T : Type u} [CommRing S] [CommRing T] (k : T →+* S)
    (M N : ModuleCat.{u} S) :
    ((boundedAboveDerivedRestrictScalars k).obj
      (boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N))).obj.IsLE 0 := by
  let Pβ := projectiveResolutionDerivedModel (projectiveResolution M)
  let Pα := projectiveResolutionDerivedModel (projectiveResolution N)
  let K := cochainTensor Pβ.complex Pα.complex
  let KR : CochainComplex (ModuleCat T) ℤ :=
    ((ModuleCat.restrictScalars k).mapHomologicalComplex (.up ℤ)).obj K
  have hβ : Pβ.complex.IsStrictlyLE 0 := Pβ.bounded
  have hα : Pα.complex.IsStrictlyLE 0 := Pα.bounded
  have hK : K.IsStrictlyLE 0 := by
    simpa only [add_zero] using cochainTensor_isStrictlyLE Pβ.complex Pα.complex 0 0
  have hKR : KR.IsStrictlyLE 0 := by
    apply (CochainComplex.isStrictlyLE_iff _ _).mpr
    intro i hi
    change IsZero ((ModuleCat.restrictScalars k).obj (K.X i))
    exact (ModuleCat.restrictScalars k).map_isZero (K.isZero_of_isStrictlyLE 0 i hi)
  let e : ((boundedAboveDerivedRestrictScalars k).obj
      (boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N))).obj ≅
      DerivedCategory.Q.obj KR :=
    (derivedRestrictScalars k).mapIso
        (boundedAboveDerivedTensorModelIso
          (boundedAboveDerivedSingleFunctor.obj M)
          (boundedAboveDerivedSingleFunctor.obj N) Pβ Pα) ≪≫
      (derivedRestrictScalarsFactors k).app K
  exact DerivedCategory.TStructure.t.isLE_of_iso e.symm 0


variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hpNat" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "D" => W.deltaStructure
local notation "d" => W.generator
local notation "dP" => algebraMap A (PowerRootPolynomial A p hpNat) d
local notation "P" => PowerRootPolynomial A p hpNat
local notation "L" => PowerRootUnaryFreeDeltaRing A p hpNat
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "r" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "α" =>
  deltaDivisionSourceMap (σ := PUnit) E dP
local notation "β" => deltaDivisionSourceEval E r
local notation "Mβ" => baseChangeScalarModule β
local notation "Mα" => baseChangeScalarModule α
local notation "X" => CategoryTheory.Functor.obj boundedAboveDerivedTensor
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)
local notation "C₀" => algebraMap A L

set_option maxHeartbeats 800000 in
-- 元の係数作用を保って具体的な非正射影テンソルモデルを照合するため。
set_option backward.isDefEq.respectTransparency true in
/-- 概要：同じ元の実A対象は非正次数の対象であり、離散性や完備性は仮定しない。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem powerRootPrismMonicSourceCoefficient_isLE_zero_of_unconditional :
    (PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f).obj.IsLE 0 := by
  with_reducible exact (unconditionalRestrictedTensor_isLE_zero (S := L) (T := A) C₀ Mβ Mα)

/-- 概要：元Aへ制限した同じ実二因子源は、全正次数でホモロジーが消える。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem powerRootPrismMonicSourceCoefficient_homology_isZero_positive_of_unconditional (i : ℤ) (hi : 0 < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj
      (PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f).obj) :=
  (DerivedCategory.isLE_iff _ _).mp (powerRootPrismMonicSourceCoefficient_isLE_zero_of_unconditional W hW f) i hi

/-- 概要：同じaugmentationの終域である係数制限raw singleも非正次数である。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem powerRootPrismMonicSourceRawCoefficient_isLE_zero_of_unconditional :
    (PowerRootPrismMonicSourceRawCoefficientObject_of_unconditional W hW f).obj.IsLE 0 := by
  let e : (PowerRootPrismMonicSourceRawCoefficientObject_of_unconditional W hW f).obj ≅
      (DerivedCategory.singleFunctor (ModuleCat A) 0).obj
        ((ModuleCat.restrictScalars C₀).obj (PowerRootPrismMonicSourceRawModule_of_unconditional W hW f)) :=
    (derivedRestrictScalarsSingleIso C₀ 0).app (PowerRootPrismMonicSourceRawModule_of_unconditional W hW f)
  exact DerivedCategory.TStructure.t.isLE_of_iso e.symm 0

/-- 概要：元Aへ制限した標準augmentationそのものも、H0に同型を誘導する。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem powerRootPrismMonicSourceRawCoefficientAugmentation_h0_isIso_of_unconditional :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat A) 0).map
      (powerRootPrismMonicSourceRawCoefficientAugmentation_of_unconditional W hW f).hom) := by
  let η := (powerRootPrismMonicSourceRawAugmentation_of_unconditional W hW f).hom
  let H := DerivedCategory.homologyFunctor (ModuleCat A) 0
  let e := derivedRestrictScalarsHomologyIso C₀ 0
  have hf : IsIso ((DerivedCategory.homologyFunctor (ModuleCat L) 0).map η) :=
    powerRootPrismMonicSourceRawAugmentation_h0_isIso_of_unconditional W hW f
  have hn := e.hom.naturality η
  simp only [Functor.comp_map] at hn
  have he : IsIso (H.map ((derivedRestrictScalars C₀).map η) ≫ e.hom.app _) := by
    rw [hn]
    infer_instance
  change IsIso (H.map ((derivedRestrictScalars C₀).map η))
  exact IsIso.of_isIso_comp_right _ (e.hom.app _)

end SerrePositivity.BhattScholze.Andre
