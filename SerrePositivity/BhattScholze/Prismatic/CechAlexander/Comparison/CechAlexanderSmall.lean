module
public import SerrePositivity.BhattScholze.Prismatic.Site.PrismOverSmall


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.CategoryTheory.CechNerveTransport
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.CechAlexanderAssembly

/-!
# 小さい prismatic site の Čech–Alexander データ

## 概要
HasEnvelopes で作った余単体的対象を、小さい site の積と弱終対象として読む。

## 方針
一般の圏同値による移送を、既に証明した標準余積と弱始性へ適用する。

## 規約
BS 著者版 Construction 4.17–4.18。∞ 圏の層条件や Tot の比較は使わない。

## 使われ方
後の Čech による計算のための、小さい通常の site の入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.BhattScholze.Prismatic
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (R : Type u) [CommRing R] [Algebra (A ⧸ P.ideal) R] (κ : Cardinal.{u})

/-- 概要：標準余積を持つ任意の site の余単体的対象を小さい Čech データへ送る。
方針：圏同値による標準余積の移送を使う。
規約：BS 著者版 Construction 4.18。使われ方：大きい模型と小さい模型に共通する移送。 -/
def smallCechNerveOfCoproducts (X : CosimplicialObject (PrismOver P R κ))
    (hc : ∀ n : ℕ, IsColimit (Cofan.mk (X.obj ⦋n⦌)
      (fun i : Fin (n + 1) => X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)))) :
    CategoryTheory.CechNerveData
      (Opposite.op ((equivSmallModel (PrismOver P R κ)).functor.obj (X.obj ⦋0⦌))) :=
  CategoryTheory.CechNerveData.ofCoproductsSmall X hc

variable (h : HasEnvelopes P R) (hκ : cutoff A R ≤ κ)

/-- 概要：HasEnvelopes から作る零次の対象の、小さい site の Čech データ。
方針：実際の標準頂点の余積を smallCechNerveOfCoproducts へ渡す。
規約：BS 著者版 Construction 4.18。使われ方：小さい site の Čech 脈体の入力。 -/
def cechNerveData : CategoryTheory.CechNerveData
    (Opposite.op ((equivSmallModel (PrismOver P R κ)).functor.obj
      (cechAlexanderObj P R h κ hκ 0))) :=
  smallCechNerveOfCoproducts P R κ (cechAlexander P R h κ hκ)
    (cechAlexander_isCoproduct P R h κ hκ)

/-- 概要：小さい site の Čech 対象の零次は弱終対象。
方針：環の向きの弱始性を圏同値と反対圏で移す。
規約：BS 著者版 Construction 4.17。使われ方：後の Čech 計算の古典的な入力。 -/
theorem cechSmall_weaklyTerminal : CategoryTheory.IsWeaklyTerminal
    (Opposite.op ((equivSmallModel (PrismOver P R κ)).functor.obj
      (cechAlexanderObj P R h κ hκ 0))) :=
  CategoryTheory.CechNerveData.weaklyTerminal_small (cechAlexanderObj_weaklyInitial P R h κ hκ)

end SerrePositivity.BhattScholze.Prismatic

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Construction 4.17" (partial := special) "BS-W17 H3（11-11）：HasEnvelopes からの C^• の組み立て、標準余積、弱始性（site では弱終）、交代余面複体は本体。存在を供給するのは多項式の場合（D21）。C^• が Δ を計算すること（G10）は drafts ／ 11-12 夜更新（§4 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.cechSmall_weaklyTerminal
