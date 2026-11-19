module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.SchemeExceptional

/-!
概要：KST §5 の一般の blowup の標準アフィンチャートの被覆。
方針：基底のアフィン局所モデルと、その次数一元による標準チャートを合わせる。
規約：添字はアフィン開集合と切断中心の元の組。
使われ方：スキーム論的稠密性と局所的なイデアルの計算。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {X : Scheme.{u}} (I : X.IdealSheafData)

set_option maxHeartbeats 800000 in
-- アフィン開集合と中心元を添字とする従属和の Spec の型の同一視が標準制限を超えるため。
set_option backward.isDefEq.respectTransparency false in
/--
概要：一般の blowup の各点はある標準アフィンチャートから来る。
方針：まず基底のアフィン局所モデルを選び、次に中心元のチャートを選ぶ。
規約：KST §5、中心の有限生成性は不要。
使われ方：全標準チャートを実際のアフィン開被覆として束ねる。
-/
theorem exists_blowupChartι (x : blowup I) :
    ∃ (p : Σ U : X.affineOpens, I.ideal U)
      (z : Spec (.of (BlowupChartRing (I.ideal p.1) p.2))), blowupChartι I p.1 p.2 z = x := by
  obtain ⟨U, y, hy⟩ := exists_blowupAffineι I x
  let 𝒰 := affineBlowupChartCover (I.ideal U)
  let a : I.ideal U := 𝒰.idx y
  obtain ⟨z, hz⟩ := 𝒰.covers y
  change affineBlowupChartι (I.ideal U) a z = y at hz
  exact ⟨⟨U, a⟩, z, (congrArg (blowupAffineι I U) hz).trans hy⟩

/--
概要：全標準チャートによる一般の blowup のアフィン開被覆。
方針：各点の標準チャートによる表示から被覆の添字を選ぶ。
規約：KST §5、被覆の各対象は実際の斉次局所化環の Spec。
使われ方：核イデアルのアフィン局所的な検証。
-/
def blowupAffineChartCover : (blowup I).AffineOpenCover where
  I₀ := Σ U : X.affineOpens, I.ideal U
  X p := CommRingCat.of (BlowupChartRing (I.ideal p.1) p.2)
  f p := blowupChartι I p.1 p.2
  idx x := (exists_blowupChartι I x).choose
  covers x := (exists_blowupChartι I x).choose_spec

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
