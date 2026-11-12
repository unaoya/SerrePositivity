module
public import SerrePositivity.KST.NonConnective.DGKappaSelectedConeInput
public import SerrePositivity.KST.NonConnective.DGKappaPerfectSupply

/-!
概要：D-8 の無条件 cone・Perf 実供給を、固定 κ の全厳密 dg 段入力へ代入する。
方針：同じ実代表系の cone を各入力で固定し、その同じ cone の P を既存の段供給へ渡す。
規約：全 native 懸垂作用・零所属・fibration・共終性の存在はここから推論しない。
使われ方：K-7 の反復懸垂で I・P の独立した存在入力を除く実入口。
-/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ)

/-- 概要：固定 κ の全厳密 dg 入力に同じ実 cone・Perf 対を供給する。
方針：D 正本の無条件 cone を既存の同じ cone の P 構成へ渡す。
規約：κ の非可算正則性だけを明示し、全入力射の作用は別境界に保つ。
使われ方：対象の全反復で独立した I・P 入力を要求しない段供給。 -/
def dgKappaUnconditionalStageProvider : DGSuspensionStageProvider.{u, v} R κ :=
  fun A => { cone := dgKappaSelectedConeInput R A κ hκ
             perfect := dgKappaSelectedPerfectInput R A κ hκ }

/-- 概要：供給された各段の cone は D の同じ実代表系そのもの。
方針：段供給の射影を計算する。
規約：別の小模型を選択しない。使われ方：同じ実核・商・swindle との照合。 -/
theorem dgKappaUnconditionalStageProvider_cone
    (A : PerfDGInput.{u, max (u + 1) v} R) :
    (dgKappaUnconditionalStageProvider.{u, v} R κ hκ A).cone =
      dgKappaSelectedConeInput R A κ hκ := rfl

/-- 概要：供給された P は同じ無条件 cone に対する D の実 Perf 比較。
方針：同じ cone への正本構成を展開する。
規約：比較・同値・包含を別の存在引数に残さない。
使われ方：反復懸垂の実 Perf 始点の回収。 -/
theorem dgKappaUnconditionalStageProvider_perfect
    (A : PerfDGInput.{u, max (u + 1) v} R) :
    (dgKappaUnconditionalStageProvider.{u, v} R κ hκ A).perfect =
      dgKappaSelectedPerfectInput R A κ hκ := rfl

/-- 採用した新 cone 正本を、D-S が同じ頂点として厳密回収する。 -/
theorem dgKappaUnconditionalStageProvider_cone_newInput
    (A : PerfDGInput.{u, max (u + 1) v} R) :
    (dgKappaUnconditionalStageProvider.{u, v} R κ hκ A).cone =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R A κ hκ := rfl

/-- 同じ新 cone に対する新 P 正本を厳密回収する。 -/
theorem dgKappaUnconditionalStageProvider_perfect_newInput
    (A : PerfDGInput.{u, max (u + 1) v} R) :
    (dgKappaUnconditionalStageProvider.{u, v} R κ hκ A).perfect =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput_unconditional' R A κ hκ := rfl

/-- 概要：元の同じ κ の全実懸垂対象を、I・P の存在仮定なしで反復する。
方針：実供給された同じ段入力を既存の反復へ代入する。
規約：構造射や全 native 入力作用の存在を対象の反復から推論しない。
使われ方：K-7 c4・c5・d の実構造射を接続する対象列。 -/
def dgSuspensionUnconditionalIteration
    (A : PerfDGInput.{u, max (u + 1) v} R) (n : ℕ) :
    PerfDGInput.{u, max (u + 1) v} R :=
  dgSuspensionIteration R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A n

/-- 概要：無条件実反復の初期対象は元の厳密 dg 入力。
方針：既存の同じ反復の零段を評価する。
規約：固定入力を保つ。使われ方：連結 K との比較の始点。 -/
theorem dgSuspensionUnconditionalIteration_zero
    (A : PerfDGInput.{u, max (u + 1) v} R) :
    dgSuspensionUnconditionalIteration R κ hκ A 0 = A := rfl

/-- 概要：無条件反復の次段は同じ D の実 cone を使った元の実懸垂。
方針：同じ段供給の cone 射影を反復の再帰式へ代入する。
規約：κ と実代表系を段別に変更しない。
使われ方：同じ cone 上の K 零性・実構造辺を各段へ接続する。 -/
theorem dgSuspensionUnconditionalIteration_succ
    (A : PerfDGInput.{u, max (u + 1) v} R) (n : ℕ) :
    dgSuspensionUnconditionalIteration R κ hκ A (n + 1) =
      dgKappaSuspensionKInput R (dgSuspensionUnconditionalIteration R κ hκ A n)
        (dgKappaSelectedConeInput R (dgSuspensionUnconditionalIteration R κ hκ A n) κ hκ) := rfl

end SerrePositivity.KST.NonConnective
