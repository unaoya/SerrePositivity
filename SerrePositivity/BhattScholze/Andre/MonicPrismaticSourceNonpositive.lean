module

public import SerrePositivity.BhattScholze.Andre.MonicPrismaticRawSourceComparison
public import SerrePositivity.HomologicalAlgebra.DerivedTensorNonpositive

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
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "P" => MvPolynomial σ A
local notation "L" => RelativeFreeDeltaRing (R := P) σ
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "α" => deltaDivisionSourceMap (σ := σ) E (MvPolynomial.C d)
local notation "β" => deltaDivisionSourceEval E r
local notation "Mβ" => baseChangeScalarModule β
local notation "Mα" => baseChangeScalarModule α
local notation "X" => CategoryTheory.Functor.obj boundedAboveDerivedTensor
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)
local notation "C₀" => algebraMap A L

set_option maxHeartbeats 800000 in
-- 元の係数作用を保って具体的な非正射影テンソルモデルを照合するため。
/-- 概要：同じ元の実A対象は非正次数の対象であり、離散性や完備性は仮定しない。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem monicPrismaticSourceCoefficient_isLE_zero :
    (MonicPrismaticSourceCoefficientObject D d f).obj.IsLE 0 := by
  let Pβ := projectiveResolutionDerivedModel (projectiveResolution Mβ)
  let Pα := projectiveResolutionDerivedModel (projectiveResolution Mα)
  let K := cochainTensor Pβ.complex Pα.complex
  let KR : CochainComplex (ModuleCat A) ℤ :=
    ((ModuleCat.restrictScalars C₀).mapHomologicalComplex (.up ℤ)).obj K
  have hβ : Pβ.complex.IsStrictlyLE 0 := Pβ.bounded
  have hα : Pα.complex.IsStrictlyLE 0 := Pα.bounded
  have hK : K.IsStrictlyLE 0 := by
    simpa only [add_zero] using cochainTensor_isStrictlyLE Pβ.complex Pα.complex 0 0
  have hKR : KR.IsStrictlyLE 0 := by
    apply (CochainComplex.isStrictlyLE_iff _ _).mpr
    intro i hi
    change IsZero ((ModuleCat.restrictScalars C₀).obj (K.X i))
    exact (ModuleCat.restrictScalars C₀).map_isZero (K.isZero_of_isStrictlyLE 0 i hi)
  let e : (MonicPrismaticSourceCoefficientObject D d f).obj ≅ DerivedCategory.Q.obj KR :=
    (derivedRestrictScalars C₀).mapIso
        (boundedAboveDerivedTensorModelIso
          (boundedAboveDerivedSingleFunctor.obj Mβ)
          (boundedAboveDerivedSingleFunctor.obj Mα) Pβ Pα) ≪≫
      (derivedRestrictScalarsFactors C₀).app K
  exact DerivedCategory.TStructure.t.isLE_of_iso e.symm 0

/-- 概要：元Aへ制限した同じ実二因子源は、全正次数でホモロジーが消える。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem monicPrismaticSourceCoefficient_homology_isZero_positive (i : ℤ) (hi : 0 < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj
      (MonicPrismaticSourceCoefficientObject D d f).obj) :=
  (DerivedCategory.isLE_iff _ _).mp (monicPrismaticSourceCoefficient_isLE_zero D d f) i hi

/-- 概要：同じaugmentationの終域である係数制限raw singleも非正次数である。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem monicPrismaticSourceRawCoefficient_isLE_zero :
    (MonicPrismaticSourceRawCoefficientObject D d f).obj.IsLE 0 := by
  let e : (MonicPrismaticSourceRawCoefficientObject D d f).obj ≅
      (DerivedCategory.singleFunctor (ModuleCat A) 0).obj
        ((ModuleCat.restrictScalars C₀).obj (MonicPrismaticSourceRawModule D d f)) :=
    (derivedRestrictScalarsSingleIso C₀ 0).app (MonicPrismaticSourceRawModule D d f)
  exact DerivedCategory.TStructure.t.isLE_of_iso e.symm 0

/-- 概要：元Aへ制限した標準augmentationそのものも、H0に同型を誘導する。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem monicPrismaticSourceRawCoefficientAugmentation_h0_isIso :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat A) 0).map
      (monicPrismaticSourceRawCoefficientAugmentation D d f).hom) := by
  let η := (monicPrismaticSourceRawAugmentation D d f).hom
  let H := DerivedCategory.homologyFunctor (ModuleCat A) 0
  let e := derivedRestrictScalarsHomologyIso C₀ 0
  have hf : IsIso ((DerivedCategory.homologyFunctor (ModuleCat L) 0).map η) :=
    monicPrismaticSourceRawAugmentation_h0_isIso D d f
  have hn := e.hom.naturality η
  simp only [Functor.comp_map] at hn
  have he : IsIso (H.map ((derivedRestrictScalars C₀).map η) ≫ e.hom.app _) := by
    rw [hn]
    infer_instance
  change IsIso (H.map ((derivedRestrictScalars C₀).map η))
  exact IsIso.of_isIso_comp_right _ (e.hom.app _)

end SerrePositivity.BhattScholze.Andre
