module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.SchemeBlowupAffine
public import SerrePositivity.AlgebraicGeometry.SubschemeAffinePullback
public import SerrePositivity.AlgebraicGeometry.Cartier

/-!
概要：KST §5 の一般スキーム上の blowup の例外閉部分スキーム。
方針：中心の閉部分スキームを引き戻し、標準チャート上で正則な単項方程式を計算する。
規約：中心の厚みを保った通常のファイバー積を用いる。
使われ方：例外因子の有効 Cartier 性と Stacks 081T の平坦化への入力。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
variable {X : Scheme.{u}} (I : X.IdealSheafData)

/--
概要：一般の blowup の例外閉部分スキーム。
方針：中心の閉部分スキームと blowup の構造射のファイバー積を取る。
規約：KST §5、導来例外因子とは区別する。
使われ方：古典的 blowup 正方形。
-/
def exceptional : Scheme := pullback (blowupπ I) I.subschemeι

/--
概要：一般の例外閉部分スキームの blowup への包含射。
方針：ファイバー積の第一射影を用いる。
規約：KST §5、中心の閉埋め込みの基底変更。
使われ方：例外因子の局所方程式と Cartier 性。
-/
def exceptionalι : exceptional I ⟶ blowup I := pullback.fst _ _

/--
概要：一般の例外閉部分スキームから中心への射。
方針：中心とのファイバー積の第二射影を用いる。
規約：KST §5、中心の厚みを保つ。
使われ方：古典的 blowup 正方形。
-/
def exceptionalToCenter : exceptional I ⟶ I.subscheme := pullback.snd _ _

/--
概要：例外閉部分スキーム、中心、blowup、基礎スキームの正方形は可換。
方針：ファイバー積の射影の交換式を用いる。
規約：KST §5、全て通常のスキーム射。
使われ方：K-L5・K-L6 へ渡す古典的 blowup 正方形の幾何学的入力。
-/
@[reassoc] theorem exceptional_square : exceptionalι I ≫ blowupπ I =
    exceptionalToCenter I ≫ I.subschemeι := pullback.condition

set_option backward.isDefEq.respectTransparency false in
/--
概要：一般の例外閉部分スキームの包含は閉埋め込み。
方針：中心の閉埋め込みの基底変更を用いる。
規約：KST §5、中心はイデアル層の実際の閉部分スキーム。
使われ方：有効 Cartier 因子の閉埋め込み条件。
-/
instance exceptionalι_isClosedImmersion : IsClosedImmersion (exceptionalι I) := by
  unfold exceptionalι
  infer_instance

/--
概要：アフィン局所モデルの標準チャートから一般の blowup への開包含。
方針：Rees Proj の標準チャート包含と局所モデルの標準射を合成する。
規約：KST §5、添字はアフィン開集合 U と中心 I(U) の元。
使われ方：一般の例外因子の局所方程式。
-/
def blowupChartι (U : X.affineOpens) (a : I.ideal U) :
    Spec (.of (BlowupChartRing (I.ideal U) a)) ⟶ blowup I :=
  affineBlowupChartι (I.ideal U) a ≫ blowupAffineι I U

set_option backward.isDefEq.respectTransparency false in
/--
概要：一般の blowup の標準チャート射は開埋め込み。
方針：二つの開埋め込みの合成を用いる。
規約：KST §5、チャートは実際の斉次局所化環の Spec。
使われ方：例外因子の局所モデル。
-/
instance blowupChartι_isOpenImmersion (U : X.affineOpens) (a : I.ideal U) :
    IsOpenImmersion (blowupChartι I U a) := by
  unfold blowupChartι
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
概要：一般の標準チャートの構造射は係数写像の Spec とアフィン開包含の合成。
方針：局所モデルの構造射の自然性とアフィンチャートの構造射の公式を使う。
規約：KST §5、基底 X への実際の射の等式。
使われ方：中心を引き戻してチャートの拡大イデアルの商を計算する。
-/
@[reassoc] theorem blowupChartι_π (U : X.affineOpens) (a : I.ideal U) :
    blowupChartι I U a ≫ blowupπ I =
      Spec.map (CommRingCat.ofHom (chartBaseMap (I.ideal U) a)) ≫ U.2.fromSpec := by
  unfold blowupChartι
  rw [Category.assoc, blowupAffineι_π]
  change affineBlowupChartι (I.ideal U) a ≫
      (affineBlowupπ (I.ideal U) ≫ U.2.fromSpec) = _
  rw [← Category.assoc]
  exact congrArg (fun z => z ≫ U.2.fromSpec)
    (show affineBlowupChartι (I.ideal U) a ≫ affineBlowupπ (I.ideal U) =
      Spec.map (CommRingCat.ofHom (chartBaseMap (I.ideal U) a)) from
        affineBlowupChartIso_inv_ι_π (I.ideal U) a)

set_option backward.isDefEq.respectTransparency false in
/--
概要：一般の例外閉部分スキームの標準チャートへの逆像は拡大イデアルの商の Spec。
方針：ファイバー積の貼り合わせ則と中心のアフィン商モデルを合成する。
規約：KST §5、商イデアルはチャート係数写像による I(U) の像。
使われ方：例外因子の有効 Cartier 性。
-/
def exceptionalChartIso (U : X.affineOpens) (a : I.ideal U) :
    pullback (exceptionalι I) (blowupChartι I U a) ≅
      Spec (.of (BlowupChartRing (I.ideal U) a ⧸ (I.ideal U).map (chartBaseMap (I.ideal U) a))) :=
  pullbackSymmetry _ _ ≪≫
    pullbackRightPullbackFstIso (blowupπ I) I.subschemeι (blowupChartι I U a) ≪≫
    pullback.congrHom (blowupChartι_π I U a) rfl ≪≫
    subschemeChartPullbackIso I U (BlowupChartRing (I.ideal U) a) (chartBaseMap (I.ideal U) a)

set_option backward.isDefEq.respectTransparency false in
/--
概要：例外因子のチャート同型はチャートへの包含を拡大イデアルの商写像の Spec に送る。
方針：各ファイバー積比較の射影との交換式を順に使う。
規約：KST §5、逆同型と第二射影の合成。
使われ方：局所方程式を実際の閉埋め込みの正則方程式へ接続する。
-/
@[reassoc] theorem exceptionalChartIso_inv_snd (U : X.affineOpens) (a : I.ideal U) :
    (exceptionalChartIso I U a).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk ((I.ideal U).map (chartBaseMap (I.ideal U) a)))) := by
  dsimp only [exceptionalChartIso, exceptionalι]
  simp only [Iso.trans_inv, Category.assoc, pullbackSymmetry_inv_comp_snd]
  erw [pullbackRightPullbackFstIso_inv_fst]
  rw [pullbackCongrHom_inv_fst]
  exact subschemeChartPullbackIso_inv_fst I U _ _

set_option backward.isDefEq.respectTransparency false in
/--
概要：一般の blowup の例外閉部分スキームは有効 Cartier 因子。
方針：標準チャートで拡大中心が正則な一元で生成されることを使う。
規約：KST §5、Stacks 01WQ Lemma 31.14.2。有限生成性・Noether 性は不要。
使われ方：通常の blowup の例外因子と平坦化の幾何学的入力。
-/
theorem exceptional_isEffectiveCartier : IsEffectiveCartierImmersion (exceptionalι I) := by
  refine ⟨inferInstance, ?_⟩
  intro x
  obtain ⟨U, y, hy⟩ := exists_blowupAffineι I x
  let 𝒰 := affineBlowupChartCover (I.ideal U)
  let a : I.ideal U := 𝒰.idx y
  obtain ⟨z, hz⟩ := 𝒰.covers y
  change affineBlowupChartι (I.ideal U) a z = y at hz
  refine ⟨CommRingCat.of (BlowupChartRing (I.ideal U) a), blowupChartι I U a,
    inferInstance, ?_, (I.ideal U).map (chartBaseMap (I.ideal U) a),
    chartBaseMap (I.ideal U) a a.1, chartBaseMap_mem_nonZeroDivisors (I.ideal U) a,
    chart_map_ideal_eq_span (I.ideal U) a, exceptionalChartIso I U a,
    exceptionalChartIso_inv_snd I U a⟩
  exact ⟨z, (congrArg (blowupAffineι I U) hz).trans hy⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
