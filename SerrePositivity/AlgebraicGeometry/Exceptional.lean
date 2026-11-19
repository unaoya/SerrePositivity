module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.QuotientPullback
public import SerrePositivity.AlgebraicGeometry.ChartAlgebra

/-!
概要：KST §5 の blowup の例外閉部分スキームを局所的な商として記述する。
方針：中心の逆像のファイバー積を標準チャートへ引き戻し、商の Spec と同定する。
規約：通常の blowup と導来 blowup の underlying scheme は区別する。
使われ方：例外閉部分スキームの有効 Cartier 性と Stacks 081T の入力。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits

variable {R : Type u} [CommRing R] (I : Ideal R)

/--
概要：標準チャートの Spec から blowup への開埋め込み。
方針：標準チャートの Spec 同型と開集合の包含を合成する。
規約：KST §5、添字は a ∈ I。
使われ方：例外閉部分スキームを引き戻す基準射。
-/
def affineBlowupChartι (a : I) : Spec (.of (BlowupChartRing I a)) ⟶ affineBlowup I :=
  Proj.awayι (reesGrade I) (reesDegreeOne I a) (reesDegreeOne_mem I a) (by decide)

set_option backward.isDefEq.respectTransparency false in
/--
概要：標準チャートの Spec の射は開埋め込み。
方針：Proj の標準開埋め込みの instance を使う。
規約：KST §5、チャート環は実際の斉次局所化。
使われ方：例外因子のアフィン局所モデル。
-/
instance affineBlowupChartι_isOpenImmersion (a : I) :
    IsOpenImmersion (affineBlowupChartι I a) := by
  unfold affineBlowupChartι
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
概要：例外閉部分スキームの標準チャートへの逆像は中心の拡大イデアルによる商の Spec。
方針：ファイバー積の貼り合わせ則とアフィン商の逆像同型を合成する。
規約：KST §5、商はチャートの係数写像の `Ideal.map` で定義する。
使われ方：チャート環の単項生成・非零因子性を実際の包含射に接続する。
-/
def affineExceptionalChartIso (a : I) :
    pullback (affineExceptionalι I) (affineBlowupChartι I a) ≅
      Spec (.of ((BlowupChartRing I a) ⧸ I.map (chartBaseMap I a))) := by
  letI : Algebra R (BlowupChartRing I a) := (chartBaseMap I a).toAlgebra
  exact pullbackSymmetry _ _ ≪≫
    pullbackRightPullbackFstIso (affineBlowupπ I) (affineCenterι I) (affineBlowupChartι I a) ≪≫
    pullback.congrHom (affineBlowupChartIso_inv_ι_π I a) rfl ≪≫
    specQuotientPullbackIso R (BlowupChartRing I a) I

set_option backward.isDefEq.respectTransparency false in
/--
概要：例外閉部分スキームのチャート同型はチャートへの包含を商写像に送る。
方針：各ファイバー積同型の射影との交換式を使う。
規約：KST §5、同型の逆方向と第二射影を合成する。
使われ方：例外閉部分スキームの局所方程式を確認する。
-/
@[reassoc] theorem affineExceptionalChartIso_inv_snd (a : I) :
    (affineExceptionalChartIso I a).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (chartBaseMap I a)))) := by
  let : Algebra R (BlowupChartRing I a) := (chartBaseMap I a).toAlgebra
  dsimp only [affineExceptionalChartIso, affineCenterι, affineExceptionalι]
  simp only [Iso.trans_inv, Category.assoc, pullbackSymmetry_inv_comp_snd]
  erw [pullbackRightPullbackFstIso_inv_fst]
  rw [pullback.congrHom_inv]
  simp only [pullback.map, Category.comp_id]
  erw [pullback.lift_fst]
  exact specQuotientPullbackIso_inv_fst R (BlowupChartRing I a) I

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
