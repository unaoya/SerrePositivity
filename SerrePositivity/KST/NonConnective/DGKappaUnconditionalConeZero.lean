module
public import SerrePositivity.KST.NonConnective.DGKappaUnconditionalStageSupply
public import SerrePositivity.KST.NonConnective.DGKappaSplitCofiberSupply
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaClosedProjectiveOperations

/-!
概要：同じ D-8 無条件 cone の実零所属を消費し、同じ cone の連結 K・固定 K の消滅を得る。
方針：D の同じ代表系の零所属を既存の native 分裂 cofiber・swindle へ渡す。
規約：汎用 dg cofiber 判定は D-12 のまま。全 native 懸垂作用・fibration・共終性は別境界。
使われ方：K-7 c5・d3 の各実反復段で独立した I・P・Z を要求しない cone 零性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
local instance unconditionalConeSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)

/-- 概要：同じ無条件 cone の実代表系は元の実零加群を含む。
方針：同じ代表系の D 正本の零所属を代入する。
規約：同型代表への変更を使わず、元の moduleZero を保持する。
使われ方：同じ native 零関手と分裂四角形の実入力。 -/
theorem dgKappaUnconditionalZeroInput :
    DGKappaZeroInput R D (dgKappaSelectedConeInput R D κ hκ) :=
  dgKappaSelectedZeroInput R D κ hκ

/-- 概要：同じ無条件 cone の連結 BF K 頂点は実 Sp の零対象。
方針：実零所属と D-12 の分裂 cofiber 判定を同じ swindle へ代入する。
規約：I・Z・cofiber の存在を追加仮定に残さない。
使われ方：同じ cone の連結 fibration から構造射を作る際の消滅。 -/
theorem dgKappaUnconditionalConnectedK_isZeroVertex :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex
      (kOmegaSpectrum (presentedPerfectDGStableModel R
        (DGKappaCone R D (dgKappaSelectedConeInput R D κ hκ))))) :=
  dgKappaConnectedK_isZeroVertex R D (dgKappaSelectedConeInput R D κ hκ)
    (dgKappaUnconditionalZeroInput R D κ hκ)

/-- 概要：同じ無条件 cone の固定 dg K スペクトル頂点も実 Sp の零対象。
方針：同じ元の SOA 比較を使う既存の固定 K 消滅へ実零所属を代入する。
規約：固定 dgKInputK を変えない。使われ方：K-7 の同じ実 cone の非負次数 fiber 比較。 -/
theorem dgKappaUnconditionalFixedK_isZeroVertex :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R
      (dgKappaConeKInput R D (dgKappaSelectedConeInput R D κ hκ)))) :=
  dgKappaFixedK_isZeroVertex R D (dgKappaSelectedConeInput R D κ hκ)
    (dgKappaUnconditionalZeroInput R D κ hκ)

/-- 概要：無条件反復のすべての段で、同じ供給 cone の実零所属が得られる。
方針：各段の同じ厳密 dg 入力へ D の実代表系の零所属を適用する。
規約：段別の零所属の存在仮定を取らない。
使われ方：既存の実 BF 反復列への全段の Z 供給。 -/
theorem dgSuspensionUnconditionalIteration_zeroInput
    (A : PerfDGInput.{u, max (u + 1) v} R) (n : ℕ) :
    DGKappaZeroInput R (dgSuspensionUnconditionalIteration R κ hκ A n)
      (dgSuspensionIterationStage R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A n).cone :=
  dgKappaUnconditionalZeroInput R (dgSuspensionUnconditionalIteration R κ hκ A n) κ hκ

/-- 概要：無条件実反復の各段の同じ cone の固定 K は実 Sp の零対象。
方針：各段の同じ無条件 cone に既存の固定 K 消滅を代入する。
規約：反復懸垂の射作用・構造射の自然性はここから推論しない。
使われ方：K-7 c5・d3 の連結 fibration による全段の実構造辺。 -/
theorem dgSuspensionUnconditionalIteration_coneFixedK_isZeroVertex
    (A : PerfDGInput.{u, max (u + 1) v} R) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R
      (dgKappaConeKInput R (dgSuspensionUnconditionalIteration R κ hκ A n)
        (dgSuspensionIterationStage R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A n).cone))) :=
  dgKappaUnconditionalFixedK_isZeroVertex R (dgSuspensionUnconditionalIteration R κ hκ A n) κ hκ

end SerrePositivity.KST.NonConnective
