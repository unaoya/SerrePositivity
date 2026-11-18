import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§1 Introduction" =>
%%%
number := false
tag := "bm18-1"
%%%

BM18 §1 の項目と、本体の宣言との対応。本文は対応表（`research/bm18-coverage`）の照合の理由で、原典の本文の写しではない。

:::definition "bm18_1_1"
*定義 1.1*　v 位相と v 被覆。対応表の状態：一部（component）。

原典 PDF p.2, y=447.9。忠実平坦な付値環拡大によるスキームの射の v 被覆判定と、アフィン有限族の定義を持つ。全スキーム上の Grothendieck 位相の被覆族までの定義は見出していない。

宣言：`SerrePositivity.AlgebraicGeometry.IsSchemeVCover`、`SerrePositivity.AlgebraicGeometry.IsAffineVCoverFamily`

外の文献：RydhII、VHomology

:::

:::definition "bm18_eq_1" (uses := "bm18_1_1")
*式 (1)*　v 被覆の付値持ち上げ。対応表の状態：一部（special）。

原典 PDF p.2, y=513.6。一射の v 被覆に対する付値環拡大と持ち上げの可換性を合成等式で表している。

宣言：`SerrePositivity.AlgebraicGeometry.IsSchemeVCover`

:::

:::definition "bm18_1_2" (uses := "bm18_eq_1, bm18_1_1, bm18_2_19, bm18_2_6")
*定義 1.2*　arc 位相と arc 被覆。対応表の状態：一部（special）。

原典 PDF p.3, y=125.2。アフィンの射と有限アフィン族を rank ≤ 1 の付値環で判定する。一般の qcqs スキームの射および全スキーム上の arc 位相は型に含まれない。

宣言：`SerrePositivity.AlgebraicGeometry.ArcRouteB.IsArcHom`、`SerrePositivity.AlgebraicGeometry.ArcRouteB.IsArcCoverFamilyCharP`、`SerrePositivity.AlgebraicGeometry.ArcRouteB.isArcHom_pi_iff`

外の文献：Pic、Rydh、RydhII

:::

:::proposition "bm18_1_3" (uses := "bm18_2_9")
*例 1.3*　階数二の付値環の arc 被覆。対応表の状態：なし。

原典 PDF p.3, y=278.8。arc-cover・valuation・descent・excisionの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bm18_1_4" (uses := "bm18_1_5")
*注意 1.4*　qcqs スキームへの制限。対応表の状態：なし。

原典 PDF p.3, y=420.4。arc-cover・valuation・descent・excisionの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：SAG

:::

:::definition "bm18_1_5"
*定義 1.5*　∞ 圏値関手の降下。対応表の状態：なし。

原典 PDF p.4, y=96.3。arc-cover・valuation・descent・excisionの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：SAG

:::

:::proposition "bm18_1_6" (uses := "bm18_1_3")
*例 1.6*　サイトの導来コホモロジー。対応表の状態：なし。

原典 PDF p.4, y=246.2。arc-cover・valuation・descent・excisionの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：HK18

:::

:::theorem "bm18_1_7" (uses := "bm18_4_1, bm18_5_2")
*定理 1.7*　arc 降下の判定条件。対応表の状態：なし。

原典 PDF p.4, y=392.7。原典の finitary D(ℤ) 値関手の一般の判定は本体・Mathlib で確認できなかった。計画下の drafts/A6/ArcSheafProperty.lean:179 の affine・coconnective 版には sorry がある。G-A6-1 の構造層への適用は 4.8 を参照。

外の文献：Stacks 049J

:::

:::theorem "bm18_1_8" (uses := "bm18_5_13, bm18_5_4")
*定理 1.8*　エタールコホモロジーと構成可能層。対応表の状態：なし。

原典 PDF p.5, y=96.3。arc-cover・valuation・descent・excisionの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：BS17

:::

:::theorem "bm18_1_9" (uses := "bm18_5_16")
*定理 1.9*　完全複体の arc 降下。対応表の状態：なし。

原典 PDF p.5, y=183.3。arc-cover・valuation・descent・excisionの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::theorem "bm18_1_10" (uses := "bm18_5_17")
*定理 1.10*　完全スキームの arc 被覆の特徴づけ。対応表の状態：なし。

原典 PDF p.5, y=234.4。arc-cover・valuation・descent・excisionの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Stacks 00WP

:::

:::definition "bm18_1_11" (uses := "bm18_eq_2")
*定義 1.11*　excision datum。対応表の状態：なし。

原典 PDF p.5, y=357.2。arc-cover・valuation・descent・excisionの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Cortinas、GHexc、LT、Milnor、SW

:::

:::definition "bm18_eq_2" (uses := "bm18_1_11")
*式 (2)*　excision datum の Milnor 正方形。対応表の状態：なし。

原典 PDF p.5, y=400.9。arc-cover・valuation・descent・excisionの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::theorem "bm18_1_12" (uses := "bm18_4_1, bm18_4_25")
*定理 1.12*　arc 層の excision。対応表の状態：なし。

原典 PDF p.5, y=549.4。arc-cover・valuation・descent・excisionの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bm18_1_13" (uses := "bm18_1_12, bm18_1_3, bm18_2_7")
*注意 1.13*　v 層に対する excision の反例。対応表の状態：なし。

原典 PDF p.5, y=581.0。arc-cover・valuation・descent・excisionの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::definition "bm18_1_14" (uses := "bm18_eq_3")
*定義 1.14*　形式的貼り合わせのデータ。対応表の状態：なし。

原典 PDF p.6, y=138.9。arc-cover・valuation・descent・excisionの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Stacks 05E5

:::

:::definition "bm18_eq_3" (uses := "bm18_1_14")
*式 (3)*　形式的貼り合わせの正方形。対応表の状態：なし。

原典 PDF p.6, y=181.0。arc-cover・valuation・descent・excisionの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::theorem "bm18_1_15" (uses := "bm18_6_4, bm18_6_7")
*定理 1.15*　arc 層の形式的貼り合わせ。対応表の状態：なし。

原典 PDF p.6, y=337.2。arc-cover・valuation・descent・excisionの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bm18_1_16" (uses := "bm18_1_12, bm18_1_13, bm18_1_15, bm18_6_3, bm18_6_8")
*注意 1.16*　v 層での形式的貼り合わせの反例。対応表の状態：なし。

原典 PDF p.6, y=367.8。arc-cover・valuation・descent・excisionの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::corollary "bm18_1_17" (uses := "bm18_1_11, bm18_1_14")
*系 1.17*　torsion 係数の excision と形式的貼り合わせ。対応表の状態：なし。

原典 PDF p.6, y=453.0。arc-cover・valuation・descent・excisionの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::corollary "bm18_1_18" (uses := "bm18_6_10, bm18_6_17")
*系 1.18*　Hensel 対上のエタールコホモロジー。対応表の状態：なし。

原典 PDF p.6, y=526.2。arc-cover・valuation・descent・excisionの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Fujiwara、Gabber、HansenArtin、Huber、HuberBook

:::

:::theorem "bm18_1_19" (uses := "bm18_7_3")
*定理 1.19*　アフィノイドの Artin–Grothendieck 消滅。対応表の状態：なし。

原典 PDF p.7, y=257.4。arc-cover・valuation・descent・excisionの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：BourbakiCA、EGAIV、HansenArtin、Stacks 0018、Stacks 00IA、Stacks 00M9、Stacks 08YF、Stacks 0ASF

:::

