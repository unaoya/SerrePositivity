module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.BigCechSiteAlexander
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.CechAlexanderAssembly
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.CechAlexanderBounds
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.BigCechAffineEnvelope

/-!
# 有限完備多項式上の大きい Čech 対象

## 概要
既存の affineBigCechTerm に有界性と cutoff の評価を付け、実際の site の Čech 対象を得る。

## 方針
包絡の存在・有界性は既存の宣言を再利用し、全ての元を変数とする濃度の評価を接続する。

## 規約
BS 著者版 Construction 4.18、D21。任意の剰余環の包絡の存在は主張しない。

## 使われ方
有限完備多項式の場合の HasEnvelopes と弱始対象の供給。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.BhattScholze.Prismatic
open CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (hP : IsBoundedPrism P) (Q : Poly (A ⧸ P.ideal))

/-- 既存の大きい affine 枠の各項は指定された cutoff に収まる。 -/
theorem affineBigCechTerm_small (n : ℕ) {κ : Cardinal.{u}}
    (hκ : cutoff A (polyCompletion P Q.n) ≤ κ) :
    Cardinal.mk (affineBigCechTerm P Q n hP).carrier ≤ κ :=
  (completedFreeDelta_cechIndex_mk_le_cutoff P (polyCompletion P Q.n) n).trans hκ

include hP in
/-- 概要：有限完備多項式には原典の導来閉包の包絡の有界な族が存在する。
方針：既存の affineBigCechTerm を再利用し、閉包の包絡の同値と濃度の評価を使う。
規約：BS 著者版 Construction 4.18、D21。有限個の多項式変数の場合。
使われ方：一般の HasEnvelopes による組み立てへ実在する族を供給する。 -/
theorem hasEnvelopes_of_finitePolynomial : HasEnvelopes P (polyCompletion P Q.n) := by
  intro n
  let E := affineBigCechTerm P Q n hP
  refine ⟨E.carrier, inferInstance, E.prism, E.unit, ?_,
    affineBigCechTerm_bounded P Q n hP, affineBigCechTerm_small P hP Q n le_rfl⟩
  exact (IsPrismaticEnvelope.of_closure P _ _ _ (cechRawKernel P (polyCompletion P Q.n) n)
    (generator_mem_cechRawKernel P (polyCompletion P Q.n) n) E.prism E.unit).mp E.isEnvelope

/-- 概要：既存の大きい affine 枠の site 上の Čech–Alexander 対象。
方針：既存の族とその有界性・濃度を一般の大きい枠の構成へ入力する。
規約：BS 著者版 Construction 4.18。使われ方：弱始性・標準余積と実際の環射の比較。 -/
def affineBigCechSiteAlexander (κ : Cardinal.{u}) (hκ : cutoff A (polyCompletion P Q.n) ≤ κ) :
    CosimplicialObject (PrismOver P (polyCompletion P Q.n) κ) :=
  bigCechSiteAlexander (fun n => affineBigCechTerm P Q n hP)
    (fun n => affineBigCechTerm_bounded P Q n hP) (fun n => affineBigCechTerm_small P hP Q n hκ)

end SerrePositivity.BhattScholze.Prismatic
