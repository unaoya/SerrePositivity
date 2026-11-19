module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.BlowupDensity
public import SerrePositivity.AlgebraicGeometry.SchemeBlowupCharts
public import SerrePositivity.AlgebraicGeometry.KernelLocality
public import SerrePositivity.AlgebraicGeometry.SchemeBlowupProper

/-!
概要：Stacks 081T の Noether 特殊形で用いる blowup の中心外開集合のスキーム論的稠密性。
方針：各標準チャートで正則係数の局所化の零核により、補開包含の核を検出する。
規約：位相的稠密性より強い、イデアル層としての核が零という条件を証明する。
使われ方：平坦基底変更での稠密性保存と、平坦化後の対角の比較。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
variable {X : Scheme.{u}} (I : X.IdealSheafData)

set_option backward.isDefEq.respectTransparency false in
/--
概要：Noether 基底の blowup の中心外開包含はスキーム論的に稠密。
方針：各標準チャートで正則な係数局所化を開包含の引き戻しへ因子化し、核を消す。
規約：Stacks 080Y Remark 38.30.1、081T。Noether 性は核の標的局所性の準コンパクト性に使う。
使われ方：strict transform の平坦化後の射を開埋め込みと判定する。
-/
instance blowup_centerComplement_isSchemeTheoreticallyDominant
    [_root_.AlgebraicGeometry.IsNoetherian X] :
    IsSchemeTheoreticallyDominant (blowupπ I ⁻¹ᵁ centerComplement I).ι := by
  let C := blowupπ I ⁻¹ᵁ centerComplement I
  have : QuasiCompact C.ι := inferInstance
  constructor
  apply ker_eq_bot_of_affineOpenCover_pullbacks C.ι (blowupAffineChartCover I)
  rintro ⟨U, a⟩
  let j := blowupChartι I U a
  let q := chartLocalizationι (I.ideal U) a
  let t : Spec (.of (BlowupChartAway (I.ideal U) a)) ⟶ C.toScheme :=
    IsOpenImmersion.lift C.ι (q ≫ j) (by
      rw [Scheme.Opens.range_ι]
      exact blowupChartLocalization_range I U a)
  let l : Spec (.of (BlowupChartAway (I.ideal U) a)) ⟶ pullback C.ι j :=
    pullback.lift t q (by simp [t])
  have hl : l ≫ pullback.snd C.ι j = q := by simp [l]
  change (pullback.snd C.ι j).ker = ⊥
  apply le_bot_iff.mp
  calc
    _ ≤ (l ≫ pullback.snd C.ι j).ker := Scheme.Hom.le_ker_comp _ _
    _ = q.ker := by rw [hl]
    _ = ⊥ := chartLocalizationι_ker_eq_bot (I.ideal U) a

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
