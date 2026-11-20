module

public import SerrePositivity.AlgebraicGeometry.ChartFractions
public import SerrePositivity.AlgebraicGeometry.ChartGluing

/-!
概要：KST §5、Stacks 080Y の標準 blowup チャートの重なりの環論的モデル。
方針：二つの次数一元の積で斉次局所化し、比による通常の局所化と同定する。
規約：チャートの重なりは実際のファイバー積と環の Spec で扱う。
使われ方：中心の降下でチャートイデアルの局所化と斉次な分子を比較する。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open HomogeneousLocalization _root_.AlgebraicGeometry CategoryTheory Limits
variable {R : Type u} [CommRing R] (I : Ideal R) (a b : I)

/--
概要：二つの標準 blowup チャートの重なりを表す斉次局所化環。
方針：(a t)(b t) を可逆化した斉次局所化の零次部分を取る。
規約：KST §5、Stacks 080Y、基礎環の正則性は仮定しない。
使われ方：重なりのファイバー積と比による通常の局所化の同定。
-/
abbrev BlowupOverlapRing := Away (reesGrade I) (reesDegreeOne I a * reesDegreeOne I b)

/--
概要：第一の標準チャート環から重なりの環への準同型。
方針：Rees の第二の次数一元を追加で可逆化する斉次局所化写像を使う。
規約：KST §5、Stacks 080Y、向きは環の制限写像。
使われ方：チャートイデアルの重なりへの拡大。
-/
def chartOverlapFromLeft : BlowupChartRing I a →+* BlowupOverlapRing I a b :=
  awayMap (reesGrade I) (reesDegreeOne_mem I b) rfl

/--
概要：第二の標準チャート環から重なりの環への準同型。
方針：積の可換性で第一の次数一元を追加で可逆化する。
規約：KST §5、Stacks 080Y、重なり環の積の順序は a t、b t と固定する。
使われ方：二つのチャート上のイデアルの比較。
-/
def chartOverlapFromRight : BlowupChartRing I b →+* BlowupOverlapRing I a b :=
  awayMap (reesGrade I) (reesDegreeOne_mem I a) (mul_comm _ _)

/--
概要：二つの重なりへの制限は基礎環の係数上で一致する。
方針：斉次局所化の零次成分の写像の係数保存を使う。
規約：KST §5、Stacks 080Y、重なり環内の等式。
使われ方：同じ分子を二つのチャートから比較する。
-/
theorem chartOverlap_base (r : R) :
    chartOverlapFromLeft I a b (chartBaseMap I a r) =
      chartOverlapFromRight I a b (chartBaseMap I b r) := by
  simp only [chartOverlapFromLeft, chartOverlapFromRight, chartBaseMap,
    RingHom.comp_apply, awayMap_fromZeroRingHom]

/--
概要：二つの次数一元の斉次局所化の生成係数はチャートの比 b/a。
方針：両次数が一なので冪一を簡約する。
規約：KST §5、Stacks 080Y、実際の斉次分数同士の等式。
使われ方：重なりを比での通常の局所化とする。
-/
theorem chartRatio_eq_localizationElem : chartRatio I a b =
    Away.isLocalizationElem (reesDegreeOne_mem I a) (reesDegreeOne_mem I b) := by
  simp only [Away.isLocalizationElem, pow_one, chartRatio]

/--
概要：重なりの環は第一のチャート環で b/a を可逆化した局所化。
方針：斉次局所化の積に関する普遍性を使う。
規約：KST §5、Stacks 080Y、係数作用は構成済みの制限写像で与える。
使われ方：重なりでのイデアル所属から比の冪を払う。
-/
theorem chartOverlap_isLocalizationLeft :
    letI := (chartOverlapFromLeft I a b).toAlgebra
    IsLocalization.Away (chartRatio I a b) (BlowupOverlapRing I a b) := by
  let := (chartOverlapFromLeft I a b).toAlgebra
  rw [chartRatio_eq_localizationElem]
  exact Away.isLocalization_mul (reesDegreeOne_mem I a) (reesDegreeOne_mem I b) rfl
    (by decide)

/--
概要：重なりの環は第二のチャート環で a/b を可逆化した局所化でもある。
方針：斉次局所化の積の普遍性を逆の順序で適用する。
規約：KST §5、Stacks 080Y、係数作用は第二の制限写像を使う。
使われ方：イデアルの重なり上の一致を両側から判定する。
-/
theorem chartOverlap_isLocalizationRight :
    letI := (chartOverlapFromRight I a b).toAlgebra
    IsLocalization.Away (chartRatio I b a) (BlowupOverlapRing I a b) := by
  let := (chartOverlapFromRight I a b).toAlgebra
  rw [chartRatio_eq_localizationElem]
  exact Away.isLocalization_mul (reesDegreeOne_mem I b) (reesDegreeOne_mem I a)
    (mul_comm _ _) (by decide)

/--
概要：重なりの環と比 b/a による通常の局所化の実際の環同型。
方針：同じ元を可逆化する二つの局所化の普遍性を使う。
規約：KST §5、Stacks 080Y、向きは通常の局所化から斉次重なり環。
使われ方：局所化での等式・所属判定をチャートの重なりへ渡す。
-/
def chartOverlapLocalizationEquiv :
    Localization.Away (chartRatio I a b) ≃+* BlowupOverlapRing I a b := by
  let := (chartOverlapFromLeft I a b).toAlgebra
  have := chartOverlap_isLocalizationLeft I a b
  exact (IsLocalization.algEquiv (Submonoid.powers (chartRatio I a b))
    (Localization.Away (chartRatio I a b)) (BlowupOverlapRing I a b)).toRingEquiv

set_option backward.isDefEq.respectTransparency false in
/--
概要：標準チャートの重なりの実際のスキームは斉次重なり環の Spec。
方針：Proj の標準開集合のファイバー積の同型を使う。
規約：KST §5、Stacks 080Y、重なりの両射を保持する。
使われ方：チャートイデアル族の幾何学的な整合性。
-/
def affineBlowupChartOverlapIso :
    pullback (affineBlowupChartι I a) (affineBlowupChartι I b) ≅
      Spec (.of (BlowupOverlapRing I a b)) :=
  Proj.pullbackAwayιIso (reesGrade I) (reesDegreeOne_mem I a) (by decide)
    (reesDegreeOne_mem I b) (by decide) rfl

set_option backward.isDefEq.respectTransparency false in
/--
概要：重なりのスキーム同型の第一の射は環の制限写像の Spec。
方針：Proj の重なりの第一射の公式を使う。
規約：KST §5、Stacks 080Y、同型の逆方向を始域に置く。
使われ方：イデアルの重なり上の拡大の計算。
-/
@[reassoc] theorem affineBlowupChartOverlapIso_inv_fst :
    (affineBlowupChartOverlapIso I a b).inv ≫
      pullback.fst (affineBlowupChartι I a) (affineBlowupChartι I b) =
        Spec.map (CommRingCat.ofHom (chartOverlapFromLeft I a b)) := by
  exact Proj.pullbackAwayιIso_inv_fst ..

set_option backward.isDefEq.respectTransparency false in
/--
概要：重なりのスキーム同型の第二の射は第二の環制限写像の Spec。
方針：Proj の重なりの第二射の公式を使う。
規約：KST §5、Stacks 080Y、積の順序を保持する。
使われ方：幾何学的な重なりと両チャートイデアルの拡大の接続。
-/
@[reassoc] theorem affineBlowupChartOverlapIso_inv_snd :
    (affineBlowupChartOverlapIso I a b).inv ≫
      pullback.snd (affineBlowupChartι I a) (affineBlowupChartι I b) =
        Spec.map (CommRingCat.ofHom (chartOverlapFromRight I a b)) := by
  exact Proj.pullbackAwayιIso_inv_snd ..

set_option backward.isDefEq.respectTransparency false in
/--
概要：第二の標準チャートの第一のチャート内の逆像は比 b/a の基本開集合。
方針：Proj の標準チャートの逆像公式と次数一の比の同定を使う。
規約：KST §5、Stacks 080Y、通常の素スペクトルの基本開集合。
使われ方：有限チャート被覆上で分母を払って中心を降ろす。
-/
theorem affineBlowupChartι_preimage_chart :
    affineBlowupChartι I a ⁻¹ᵁ affineBlowupChart I b =
      PrimeSpectrum.basicOpen (chartRatio I a b) := by
  rw [chartRatio_eq_localizationElem]
  exact Proj.awayι_preimage_basicOpen (reesGrade I)
    (reesDegreeOne_mem I a) (by decide) (reesDegreeOne_mem I b) (by decide)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
