module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.BaseChangeCharts
public import SerrePositivity.AlgebraicGeometry.BlowupFunctor
public import SerrePositivity.AlgebraicGeometry.ChartGluing
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
概要：KST §5 のアフィン blowup の基本開集合への局所化。
方針：係数局所化後のチャート写像の開埋め込み性を、標準被覆で大域化する。
規約：基底環の一元による局所化を扱う。
使われ方：一般スキーム上の blowup の貼り合わせ。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (I : Ideal R) (r : R) [hRS : IsLocalization.Away r S]

include hRS

set_option backward.isDefEq.respectTransparency false in
/--
概要：一元係数局所化による標準 blowup チャートの Spec の比較は開埋め込み。
方針：比較写像がチャート上の係数 r での局所化を実現することを使う。
規約：KST §5、像中心の対応するチャートを用いる。
使われ方：blowup 全体の局所化比較射の開埋め込み性。
-/
theorem chartBaseChangeSpec_isOpenImmersion (a : I) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (chartBaseChangeMap I (I.map (algebraMap R S)) (algebraMap R S) le_rfl a))) := by
  let F := chartBaseChangeMap I (I.map (algebraMap R S)) (algebraMap R S) le_rfl a
  let B := BlowupChartRing (I.map (algebraMap R S))
    (centerImageElement I _ (algebraMap R S) le_rfl a)
  let : Algebra (BlowupChartRing I a) B := F.toAlgebra
  have : IsLocalization.Away (chartBaseMap I a r) B := by
    apply (isLocalization_iff_isLocalizationMap _ _).mpr
    change (Submonoid.powers (chartBaseMap I a r)).IsLocalizationMap
      (chartBaseChangeMap I (I.map (algebraMap R S)) (algebraMap R S) le_rfl a)
    simpa only [Submonoid.map_powers] using
      chartBaseChangeMap_isLocalizationMap (S := S) I (Submonoid.powers r) a
  exact IsOpenImmersion.of_isLocalization (chartBaseMap I a r)

set_option backward.isDefEq.respectTransparency false in
/--
概要：一元係数局所化によるアフィン blowup の比較射は開埋め込み。
方針：標準チャートへの制限をチャート環の局所化の Spec と同定する。
規約：KST §5、有限生成性や Noether 性は不要。
使われ方：基本開集合への blowup の制限との同型。
-/
theorem affineBlowupBaseMap_isOpenImmersion :
    IsOpenImmersion (affineBlowupBaseMap I (algebraMap R S)) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun a : I => affineBlowupChart I a) (iSup_affineBlowupChart I)
  intro a
  have := chartBaseChangeSpec_isOpenImmersion (S := S) I r a
  apply isOpenImmersion_restrict_of_chart _
    (affineBlowupChart (I.map (algebraMap R S))
      (centerImageElement I _ (algebraMap R S) le_rfl a)) (affineBlowupChart I a)
    (affineBlowupBaseMap_preimage_chart I (algebraMap R S) a)
    (affineBlowupChartIso _ _) (affineBlowupChartIso I a)
    (Spec.map (CommRingCat.ofHom (chartBaseChangeMap I _ (algebraMap R S) le_rfl a)))
  exact affineBlowupBaseMap_chart I (algebraMap R S) a

set_option backward.isDefEq.respectTransparency false in
/--
概要：係数の一元局所化によるチャート比較の像は、係数 r の基本開集合。
方針：チャート比較写像の局所化条件から素スペクトルの像を計算する。
規約：KST §5、点集合の像を明示する。
使われ方：blowup 比較射の像と構造射の逆像を同定する。
-/
theorem chartBaseChangeSpec_range (a : I) :
    Set.range (Spec.map (CommRingCat.ofHom
      (chartBaseChangeMap I (I.map (algebraMap R S)) (algebraMap R S) le_rfl a))) =
        (PrimeSpectrum.basicOpen (chartBaseMap I a r)).carrier := by
  let F := chartBaseChangeMap I (I.map (algebraMap R S)) (algebraMap R S) le_rfl a
  let B := BlowupChartRing (I.map (algebraMap R S))
    (centerImageElement I _ (algebraMap R S) le_rfl a)
  let : Algebra (BlowupChartRing I a) B := F.toAlgebra
  have : IsLocalization.Away (chartBaseMap I a r) B := by
    apply (isLocalization_iff_isLocalizationMap _ _).mpr
    change (Submonoid.powers (chartBaseMap I a r)).IsLocalizationMap
      (chartBaseChangeMap I (I.map (algebraMap R S)) (algebraMap R S) le_rfl a)
    simpa only [Submonoid.map_powers] using
      chartBaseChangeMap_isLocalizationMap (S := S) I (Submonoid.powers r) a
  exact PrimeSpectrum.localization_away_comap_range B (chartBaseMap I a r)

set_option backward.isDefEq.respectTransparency false in
/--
概要：係数の一元局所化による blowup 比較射の像は D(r) の逆像全体。
方針：各標準チャートで局所化の像を計算し、チャート被覆を使う。
規約：KST §5、像はスキーム構造ではなく点集合として先に同定する。
使われ方：開埋め込みの像との同型による基本開集合上の blowup の同型。
-/
theorem affineBlowupBaseMap_range :
    Set.range (affineBlowupBaseMap I (algebraMap R S)) =
      (affineBlowupπ I ⁻¹ᵁ PrimeSpectrum.basicOpen r).carrier := by
  apply Set.Subset.antisymm
  · rintro _ ⟨y, rfl⟩
    change (affineBlowupBaseMap I (algebraMap R S) ≫ affineBlowupπ I) y ∈
      PrimeSpectrum.basicOpen r
    rw [affineBlowupBaseMap_base]
    change algebraMap R S r ∉ (affineBlowupπ (I.map (algebraMap R S)) y).asIdeal
    exact Ideal.notMem_of_isUnit _ (IsLocalization.Away.algebraMap_isUnit (S := S) r)
  · intro x hx
    let 𝒰 := affineBlowupChartCover I
    let a : I := 𝒰.idx x
    obtain ⟨z, hz⟩ := 𝒰.covers x
    change affineBlowupChartι I a z = x at hz
    have hz' : z ∈ PrimeSpectrum.basicOpen (chartBaseMap I a r) := by
      change (Spec.map (CommRingCat.ofHom (chartBaseMap I a))) z ∈ PrimeSpectrum.basicOpen r
      rw [← show affineBlowupChartι I a ≫ affineBlowupπ I =
        Spec.map (CommRingCat.ofHom (chartBaseMap I a)) from affineBlowupChartIso_inv_ι_π I a]
      change affineBlowupπ I (affineBlowupChartι I a z) ∈ PrimeSpectrum.basicOpen r
      rw [hz]
      exact hx
    change z ∈ (PrimeSpectrum.basicOpen (chartBaseMap I a r)).carrier at hz'
    rw [← chartBaseChangeSpec_range (S := S) I r a] at hz'
    obtain ⟨w, hw⟩ := hz'
    refine ⟨affineBlowupChartι (I.map (algebraMap R S))
      (centerImageElement I _ (algebraMap R S) le_rfl a) w, ?_⟩
    change (affineBlowupChartι _ _ ≫ affineBlowupBaseMap I (algebraMap R S)) w = x
    rw [affineBlowupBaseMap_chart]
    change affineBlowupChartι I a _ = x
    exact (congrArg (affineBlowupChartι I a) hw).trans hz

set_option backward.isDefEq.respectTransparency false in
/--
概要：係数環を r で局所化した中心の blowup は、元の blowup の D(r) 上の部分と同型。
方針：開埋め込みとなる比較射の像を D(r) の逆像と同定する。
規約：KST §5、通常の blowup の実際のスキーム同型。
使われ方：一般スキームのアフィン開集合間の blowup の貼り合わせ。
-/
def affineBlowupLocalizationIso : affineBlowup (I.map (algebraMap R S)) ≅
    (affineBlowupπ I ⁻¹ᵁ PrimeSpectrum.basicOpen r).toScheme := by
  have := affineBlowupBaseMap_isOpenImmersion (S := S) I r
  apply IsOpenImmersion.isoOfRangeEq (affineBlowupBaseMap I (algebraMap R S))
    (affineBlowupπ I ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι
  rw [affineBlowupBaseMap_range (S := S) I r]
  exact (Scheme.Opens.range_ι _).symm

/--
概要：係数局所化の blowup 同型と元の blowup への包含の合成は自然な比較射。
方針：像の一致から得た開部分スキームの同型の因子化公式を用いる。
規約：KST §5、実際の構造射と接続するための等式。
使われ方：アフィン開集合間の比較と三重交叉での両立性。
-/
@[reassoc] theorem affineBlowupLocalizationIso_hom_ι :
    (affineBlowupLocalizationIso (S := S) I r).hom ≫
      (affineBlowupπ I ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι =
        affineBlowupBaseMap I (algebraMap R S) := by
  have := affineBlowupBaseMap_isOpenImmersion (S := S) I r
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _
    ((affineBlowupBaseMap_range (S := S) I r).trans (Scheme.Opens.range_ι _).symm)

set_option backward.isDefEq.respectTransparency false in
/--
概要：局所化後の中心を別表示で同定しても blowup の中心比較射は開埋め込み。
方針：中心の等式で像中心の場合へ移送する。
規約：KST §5、係数写像は r における局所化。
使われ方：イデアル層のアフィン基本開集合への制限。
-/
theorem affineBlowupCenterMap_isOpenImmersion (J : Ideal S)
    (hJ : I.map (algebraMap R S) = J) :
    IsOpenImmersion (affineBlowupCenterMap I J (algebraMap R S) hJ) := by
  subst J
  exact affineBlowupBaseMap_isOpenImmersion I r

set_option backward.isDefEq.respectTransparency false in
/--
概要：局所化後の中心を同定した比較射の像も、基底の基本開集合の逆像。
方針：中心の等式で自然な基底比較射の像の計算へ帰着する。
規約：KST §5、像は点集合として述べる。
使われ方：局所 blowup モデル間の開包含の像を同定する。
-/
theorem affineBlowupCenterMap_range (J : Ideal S)
    (hJ : I.map (algebraMap R S) = J) :
    Set.range (affineBlowupCenterMap I J (algebraMap R S) hJ) =
      (affineBlowupπ I ⁻¹ᵁ PrimeSpectrum.basicOpen r).carrier := by
  subst J
  exact affineBlowupBaseMap_range I r

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
