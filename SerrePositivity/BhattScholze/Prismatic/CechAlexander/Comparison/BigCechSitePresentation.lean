module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.CechAlexanderCoproduct
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.CechAlexanderRingPresentation
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.BigCechFrameLift
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.BigCechFrameResidue

/-!
# 既存の大きい枠を site の Čech–Alexander 対象として読む

## 概要
BigCechTerm の剰余構造射と変数の持ち上げを再利用して、site 上の変数の普遍性を得る。

## 方針
既存の環射を prism の射にし、剰余の構造射との両立を変数で確認する。

## 規約
BS 著者版 Construction 4.17–4.18。各項の有界性と濃度は明示する。

## 使われ方
大きい Čech 対象の弱始性・余積。有限枠への比較や底変換は使わない。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.BhattScholze.Prismatic.BigCechTerm
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}
variable {Q : Poly (A ⧸ P.ideal)} {n : ℕ} {κ : Cardinal.{u}} (E : BigCechTerm P Q n)

/-- 大きい枠の包を、指定した濃度の site の対象として読む。 -/
@[expose] def siteObject (hb : IsBoundedPrism E.prism) (hs : Cardinal.mk E.carrier ≤ κ) :
    PrismOver P (polyCompletion P Q.n) κ where
  B := E.carrier
  Q := E.prism
  bounded := hb
  toHom := E.base
  sec := E.residueSection
  sec_comp := E.residueSection_comp
  small := hs

/-- 概要：大きい枠の包は変数の普遍性を持つ Čech–Alexander の項を与える。
方針：既存の剰余構造射と持ち上げをそのまま入力する。
規約：BS 著者版 Construction 4.17–4.18。
使われ方：一般の組み立てによる弱始性・標準余積・交代余面複体。 -/
@[expose] def sitePresentation (hb : IsBoundedPrism E.prism) (hs : Cardinal.mk E.carrier ≤ κ) :
    CechAlexanderPresentation (P := P) (R := polyCompletion P Q.n) (κ := κ) n :=
  CechAlexanderPresentation.ofRingLift (E.siteObject hb hs) E.variableImage
    (fun s => (E.residueSection_variable s).symm)
    (fun D v hv => E.existsUnique_liftVariables D.Q D.toHom D.sec D.sec_comp v hv)

end SerrePositivity.BhattScholze.Prismatic.BigCechTerm
