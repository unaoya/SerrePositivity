module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import SerrePositivity.AlgebraicGeometry.PullbackComparison
public import SerrePositivity.AlgebraicGeometry.QuotientPullback

/-!
概要：KST §5 の中心の閉部分スキームのアフィン開集合への逆像。
方針：閉部分スキームの標準アフィン被覆と開埋め込みの像を比較する。
規約：実際のファイバー積を切断イデアルによる商の Spec と同定する。
使われ方：一般の blowup の例外因子をアフィン局所モデルへ移す。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
variable {X : Scheme.{u}} (I : X.IdealSheafData)

set_option backward.isDefEq.respectTransparency false in
/--
概要：中心のアフィン Spec への逆像は、切断環の中心イデアルによる商の Spec。
方針：ファイバー積の第一射影と閉部分スキームのアフィン被覆の開像が一致する。
規約：KST §5、中心の閉部分スキームのスキーム構造を保持する。
使われ方：例外因子のアフィン局所商モデル。
-/
def subschemeAffinePullbackIso (U : X.affineOpens) :
    pullback I.subschemeι U.2.fromSpec ≅ Spec (.of (Γ(X, U.1) ⧸ I.ideal U)) := by
  apply IsOpenImmersion.isoOfRangeEq (pullback.fst I.subschemeι U.2.fromSpec)
    (I.subschemeCover.f U)
  change ((pullback.fst I.subschemeι U.2.fromSpec).opensRange : Set I.subscheme) =
    ((I.subschemeCover.f U).opensRange : Set I.subscheme)
  apply congrArg TopologicalSpace.Opens.carrier
  rw [Scheme.Hom.opensRange_pullbackFst, U.2.opensRange_fromSpec,
    I.opensRange_subschemeCover_map]

set_option backward.isDefEq.respectTransparency false in
/--
概要：アフィン逆像同型の逆と第一射影の合成は閉部分スキームの標準アフィン被覆射。
方針：開像の一致から得た同型の因子化公式を用いる。
規約：KST §5、閉部分スキーム全体への射を同定する。
使われ方：商の Spec の包含射との交換式。
-/
@[reassoc] theorem subschemeAffinePullbackIso_inv_fst (U : X.affineOpens) :
    (subschemeAffinePullbackIso I U).inv ≫ pullback.fst _ _ = I.subschemeCover.f U := by
  dsimp only [subschemeAffinePullbackIso]
  exact IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
概要：アフィン逆像同型の逆と第二射影の合成は中心の商写像の Spec。
方針：アフィン開集合の開埋め込みを消去し、標準アフィン被覆の交換式を使う。
規約：KST §5、切断環の実際の商写像を用いる。
使われ方：blowup の例外因子の局所方程式。
-/
@[reassoc] theorem subschemeAffinePullbackIso_inv_snd (U : X.affineOpens) :
    (subschemeAffinePullbackIso I U).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))) := by
  apply (cancel_mono U.2.fromSpec).mp
  rw [Category.assoc, ← pullback.condition, subschemeAffinePullbackIso_inv_fst_assoc,
    I.subschemeCover_map_subschemeι]
  exact I.glueDataObjι_ι U

/--
概要：アフィン Spec から中心へのファイバー積を、基底の Spec を第一成分として商の Spec に同定する。
方針：二つの射の対称性とアフィン逆像同型を合成する。
規約：KST §5、第一射影が商写像に対応する向き。
使われ方：ファイバー積の貼り合わせ則で例外因子を比較する。
-/
def subschemeSpecPullbackIso (U : X.affineOpens) :
    pullback U.2.fromSpec I.subschemeι ≅ Spec (.of (Γ(X, U.1) ⧸ I.ideal U)) :=
  pullbackSymmetry _ _ ≪≫ subschemeAffinePullbackIso I U

set_option backward.isDefEq.respectTransparency false in
/--
概要：基底の Spec を第一成分とする中心の逆像同型は商の包含射を保存する。
方針：ファイバー積の対称性と既存の第二射影の公式を用いる。
規約：KST §5、逆同型と第一射影の合成。
使われ方：中心の局所商モデルによるファイバー積の置換。
-/
@[reassoc] theorem subschemeSpecPullbackIso_inv_fst (U : X.affineOpens) :
    (subschemeSpecPullbackIso I U).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))) := by
  simp only [subschemeSpecPullbackIso, Iso.trans_inv, Category.assoc,
    pullbackSymmetry_inv_comp_fst, subschemeAffinePullbackIso_inv_snd]

set_option backward.isDefEq.respectTransparency false in
/--
概要：アフィン開集合の切断環からの任意のアフィン射で中心を引き戻すと、拡大イデアルの商の Spec。
方針：中心のアフィン逆像同型をファイバー積に移し、アフィン商の逆像公式を使う。
規約：KST §5、係数写像は任意の環準同型。
使われ方：一般の blowup の標準チャート上での例外因子の方程式。
-/
def subschemeChartPullbackIso (U : X.affineOpens) (A : Type u) [CommRing A]
    (φ : Γ(X, U.1) →+* A) :
    pullback (Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec) I.subschemeι ≅
      Spec (.of (A ⧸ (I.ideal U).map φ)) := by
  let : Algebra Γ(X, U.1) A := φ.toAlgebra
  exact (pullbackRightPullbackFstIso U.2.fromSpec I.subschemeι
    (Spec.map (CommRingCat.ofHom φ))).symm ≪≫
      pullbackRightIso (Spec.map (CommRingCat.ofHom φ)) _ _ (subschemeSpecPullbackIso I U)
        (subschemeSpecPullbackIso_inv_fst I U) ≪≫
      specQuotientPullbackIso Γ(X, U.1) A (I.ideal U)

set_option backward.isDefEq.respectTransparency false in
/--
概要：任意のアフィン射による中心の逆像の比較は、拡大イデアルの商写像の Spec を保存する。
方針：各ファイバー積比較の第一射影の保存を順に適用する。
規約：KST §5、逆同型と第一射影の合成。
使われ方：例外因子の局所方程式を実際の閉埋め込みへ接続する。
-/
@[reassoc] theorem subschemeChartPullbackIso_inv_fst (U : X.affineOpens)
    (A : Type u) [CommRing A] (φ : Γ(X, U.1) →+* A) :
    (subschemeChartPullbackIso I U A φ).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((I.ideal U).map φ))) := by
  let : Algebra Γ(X, U.1) A := φ.toAlgebra
  dsimp only [subschemeChartPullbackIso]
  simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc, pullbackRightPullbackFstIso_hom_fst,
    pullbackRightIso_inv_fst]
  exact specQuotientPullbackIso_inv_fst Γ(X, U.1) A (I.ideal U)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
