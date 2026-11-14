module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.CechAlexanderEnvelopeLift
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.CechAlexanderRingPresentation
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.CechAlexanderCoproduct

/-!
# HasEnvelopes からの Čech–Alexander 対象

## 概要
原典の包絡の存在仮定から site の余単体的対象、弱始性、標準余積を構成する。

## 方針
包絡の変数像の普遍性を共通の Presentation に移し、その組み立てを使う。

## 規約
BS 著者版 Construction 4.17–4.18。一般の包絡の存在や Tot の計算は主張しない。

## 使われ方
任意の HasEnvelopes の族から得る古典的な Čech データと交代余面複体。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.BhattScholze.Prismatic
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (R : Type u) [CommRing R] [Algebra (A ⧸ P.ideal) R]

namespace CechEnvelopeTerm
variable {P R} {n : ℕ} (E : CechEnvelopeTerm P R n)

/-- 選択した一般の包絡を site の対象として読む。 -/
@[expose] def siteObject (κ : Cardinal.{u}) (hκ : cutoff A R ≤ κ) : PrismOver P R κ where
  B := E.carrier
  Q := E.prism
  bounded := E.bounded
  toHom := E.base
  sec := E.residueSection
  sec_comp := E.residueSection_comp
  small := E.small.trans hκ

/-- 概要：一般の包絡から site の変数の普遍性を得る。
方針：一般の包絡の一意な δ 環射を共通の ofRingLift に入力する。
規約：BS 著者版 Construction 4.17。使われ方：HasEnvelopes からの組み立て。 -/
@[expose] def sitePresentation (κ : Cardinal.{u}) (hκ : cutoff A R ≤ κ) :
    CechAlexanderPresentation (P := P) (R := R) (κ := κ) n :=
  CechAlexanderPresentation.ofRingLift (E.siteObject κ hκ) E.variableImage
    (fun s => (E.residueSection_variable s).symm)
    (fun D v hv => E.existsUnique_liftVariables D.Q D.toHom D.sec D.sec_comp v hv)

end CechEnvelopeTerm

variable (h : HasEnvelopes P R) (κ : Cardinal.{u}) (hκ : cutoff A R ≤ κ)

/-- 概要：HasEnvelopes から選んだ Čech–Alexander の各項。
方針：原典の導来閉包の包絡を選び、指定した cutoff の site へ入れる。
規約：BS 著者版 Construction 4.18。使われ方：余単体的対象の各項。 -/
@[expose] def cechAlexanderObj (n : ℕ) : PrismOver P R κ := (HasEnvelopes.term P R h n).siteObject κ hκ

/-- 概要：HasEnvelopes から作る site の余単体的 Čech–Alexander 対象。
方針：単体射を変数の添字の写像として一意に延長する。
規約：BS 著者版 Construction 4.18。使われ方：交代余面複体と Čech データ。 -/
@[expose] def cechAlexander : CosimplicialObject (PrismOver P R κ) :=
  CechAlexanderPresentation.cosimplicial (fun n => (HasEnvelopes.term P R h n).sitePresentation κ hκ)

/-- 概要：零次の Čech–Alexander 対象は環の向きで弱始対象。
方針：標的の剰余への全射で全ての変数を持ち上げる。
規約：BS 著者版 Construction 4.17。使われ方：Čech による計算の入力。 -/
theorem cechAlexanderObj_weaklyInitial :
    CategoryTheory.IsWeaklyInitial (cechAlexanderObj P R h κ hκ 0) :=
  ((HasEnvelopes.term P R h 0).sitePresentation κ hκ).weaklyInitial

/-- 概要：標準頂点は n 次項を零次の n+1 個の余積にする。
方針：一般の変数の普遍性による余積の組み立てを使う。
規約：BS 著者版 Construction 4.17。使われ方：site 側の Čech 積の錐。 -/
def cechAlexander_isCoproduct (n : ℕ) :
    IsColimit (Cofan.mk ((cechAlexander P R h κ hκ).obj ⦋n⦌)
      (fun i : Fin (n + 1) => (cechAlexander P R h κ hκ).map
        (SimplexCategory.const ⦋0⦌ ⦋n⦌ i))) :=
  CechAlexanderPresentation.isCoproduct (fun n => (HasEnvelopes.term P R h n).sitePresentation κ hκ) n

/-- 概要：大きい site 上の実際の Čech 脈体のデータ。
方針：標準頂点の余積を反対圏で積として読む。
規約：BS 著者版 Construction 4.18。小さい模型への移送や ∞ 圏は使わない。
使われ方：site の古典的な Čech データ。 -/
def cechAlexanderNerve : CategoryTheory.CechNerveData
    (Opposite.op (cechAlexanderObj P R h κ hκ 0)) :=
  CategoryTheory.CechNerveData.ofCoproducts (cechAlexander P R h κ hκ)
    (cechAlexander_isCoproduct P R h κ hκ)

end SerrePositivity.BhattScholze.Prismatic

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Construction 4.17" (partial := special) "BS-W17 H3（11-11）：HasEnvelopes からの C^• の組み立て、標準余積、弱始性（site では弱終）、交代余面複体は本体。存在を供給するのは多項式の場合（D21）。C^• が Δ を計算すること（G10）は drafts ／ 11-12 夜更新（§4 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.cechAlexanderObj
attribute [cite BS19 "Construction 4.17" (partial := special) "BS-W17 H3（11-11）：HasEnvelopes からの C^• の組み立て、標準余積、弱始性（site では弱終）、交代余面複体は本体。存在を供給するのは多項式の場合（D21）。C^• が Δ を計算すること（G10）は drafts ／ 11-12 夜更新（§4 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.cechAlexanderObj_weaklyInitial
