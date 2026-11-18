import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed.Basic
import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed.Etale

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§5 Examples of arc-sheaves" =>
%%%
number := false
tag := "bm18-5"
%%%

BM18 §5 の項目と、本体の宣言との対応。本文は対応表（`research/bm18-coverage`）の照合の理由で、原典の本文の写しではない。

:::lemma_ "bm18_5_1" (uses := "bm18_eq_10")
*補題 5.1*　and · finitary · functor · qcqs · satisfies。対応表の状態：なし。

原典 PDF p.37, y=270.3。étale・constructible・de Rham・perfect complex・arc-coverの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::definition "bm18_eq_10" (uses := "bm18_5_1")
*式 (10)*　エタール局所での降下比較。対応表の状態：なし。

原典 PDF p.37, y=353.5。étale・constructible・de Rham・perfect complex・arc-coverの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bm18_5_2" (uses := "bm18_3_4, bm18_3_8, bm18_5_1")
*命題 5.2*　torsion · sheaf · the · qcqs · functor。対応表の状態：なし。

原典 PDF p.37, y=453.9。étale・constructible・de Rham・perfect complex・arc-coverの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Rydh 3.12、SGA4

:::

:::lemma_ "bm18_5_3" (lean := "SerrePositivity.IsAbsolutelyIntegrallyClosed.henselianLocalRing, SerrePositivity.IsAbsolutelyIntegrallyClosed.residue_isAlgClosed")
*補題 5.3*　絶対整閉付値環の狭義 Hensel 性。対応表の状態：本体にある。

原典 PDF p.38, y=144.2。付値環の局所性を使い、絶対整閉局所環の Hensel 性と剰余体の代数閉性を合わせて狭義 Hensel 性を得る。

:::

:::theorem "bm18_5_4" (uses := "bm18_1_18, bm18_4_1, bm18_5_2")
*定理 5.4*　arc-descent for étale cohomology。対応表の状態：なし。

原典 PDF p.38, y=204.0。étale・constructible・de Rham・perfect complex・arc-coverの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Gabber、Gabberpair、Huber

:::

:::proposition "bm18_5_5" (uses := "bm18_eq_11, bm18_4_1, bm18_5_1, bm18_5_4")
*注意 5.5*　Excision from rigidity。対応表の状態：なし。

原典 PDF p.39, y=126.8。étale・constructible・de Rham・perfect complex・arc-coverの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Gabberpair、RydhII

:::

:::definition "bm18_eq_11" (uses := "bm18_5_5")
*式 (11)*　エタール剛性を使う excision 正方形。対応表の状態：なし。

原典 PDF p.39, y=188.4。étale・constructible・de Rham・perfect complex・arc-coverの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::theorem "bm18_5_6"
*定理 5.6*　rydh · ryd · the · three · functors。対応表の状態：なし。

原典 PDF p.39, y=419.1。étale・constructible・de Rham・perfect complex・arc-coverの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Mil80、RydhII、SGA4

:::

:::proposition "bm18_5_7" (uses := "bm18_2_22, bm18_4_1, bm18_5_3, bm18_5_4, bm18_5_6")
*命題 5.7*　absolutely · integrally · closed · valuation · quasi-compact。対応表の状態：なし。

原典 PDF p.39, y=538.5。étale・constructible・de Rham・perfect complex・arc-coverの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Rydh、Stacks 081C、Stacks 0EZN

:::

:::definition "bm18_5_8"
*記法 5.8*　Constructible sheaves。対応表の状態：なし。

原典 PDF p.41, y=138.3。étale・constructible・de Rham・perfect complex・arc-coverの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bm18_5_9"
*注意 5.9*　field · product · fields · the · preceding。対応表の状態：なし。

原典 PDF p.41, y=216.4。étale・constructible・de Rham・perfect complex・arc-coverの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Stacks 09C0

:::

:::proposition "bm18_5_10"
*命題 5.10*　the · functor · cons · finitary · more。対応表の状態：なし。

原典 PDF p.41, y=282.3。étale・constructible・de Rham・perfect complex・arc-coverの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Stacks 095M、Stacks 09YU

:::

:::proposition "bm18_5_11" (uses := "bm18_eq_12, bm18_3_8, bm18_5_10")
*命題 5.11*　the · functor · cons · generally · for。対応表の状態：なし。

原典 PDF p.41, y=542.4。étale・constructible・de Rham・perfect complex・arc-coverの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：BS17、Deligne90、HA、HTT、LaszloOlsson1、Rydh 3.12、SGA4

:::

:::definition "bm18_eq_12" (uses := "bm18_5_11")
*式 (12)*　構成可能な複体の Čech 降下比較。対応表の状態：なし。

原典 PDF p.42, y=186.0。étale・constructible・de Rham・perfect complex・arc-coverの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bm18_5_12" (uses := "bm18_5_7")
*命題 5.12*　absolutely · integrally · closed · valuation · finite。対応表の状態：なし。

原典 PDF p.42, y=483.3。étale・constructible・de Rham・perfect complex・arc-coverの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::theorem "bm18_5_13" (uses := "bm18_2_22, bm18_4_1, bm18_5_10, bm18_5_11, bm18_5_12")
*定理 5.13*　arc-descent for constructible sheaves。対応表の状態：なし。

原典 PDF p.42, y=616.5。étale・constructible・de Rham・perfect complex・arc-coverの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：HJ14

:::

:::theorem "bm18_5_14" (uses := "bm18_eq_13, bm18_eq_5, bm18_3_8, bm18_4_1")
*定理 5.14*　the · functor · qcqs · arc-sheaf。対応表の状態：なし。

原典 PDF p.43, y=518.0。étale・constructible・de Rham・perfect complex・arc-coverの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：HJ14、HK18、Zar40、dJ96

:::

:::definition "bm18_eq_13" (uses := "bm18_5_14")
*式 (13)*　微分形式の区間正方形。対応表の状態：なし。

原典 PDF p.44, y=132.6。étale・constructible・de Rham・perfect complex・arc-coverの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::corollary "bm18_5_15" (uses := "bm18_5_14")
*系 5.15*　the · construction · defines · arc-sheaf。対応表の状態：なし。

原典 PDF p.44, y=275.7。étale・constructible・de Rham・perfect complex・arc-coverの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：BS17

:::

:::theorem "bm18_5_16" (uses := "bm18_eq_14, bm18_4_1, bm18_4_2, bm18_5_11")
*定理 5.16*　arc-hyperdescent for perfect complexes on perfect schemes。対応表の状態：なし。

原典 PDF p.44, y=354.2。étale・constructible・de Rham・perfect complex・arc-coverの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：BS17、MathewGalois、Stacks 00WP

:::

:::definition "bm18_eq_14" (uses := "bm18_5_16")
*式 (14)*　完全複体の excision 正方形。対応表の状態：なし。

原典 PDF p.44, y=529.3。étale・constructible・de Rham・perfect complex・arc-coverの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::theorem "bm18_5_17" (uses := "bm18_3_30, bm18_5_16")
*定理 5.17*　Universally effective epimorphisms of perfect schemes。対応表の状態：一部（special）。

原典 PDF p.45, y=190.6。完全アフィンの arc 被覆について、Čech 複体の次数零の完全性から環の等化子が得られ、アフィンな試験対象への射についての降下を与える。任意の qcqs 代数空間への射、ならびに普遍有効エピから arc 被覆への逆向きは含まない。

宣言：`SerrePositivity.AlgebraicGeometry.ArcRouteB.cechExact_of_arcHom_perfect`

外の文献：B、RNoeth

:::

:::proposition "bm18_5_18" (uses := "bm18_eq_15")
*注意 5.18*　the · canonical · topology · qcqs · perfect。対応表の状態：なし。

原典 PDF p.46, y=96.3。étale・constructible・de Rham・perfect complex・arc-coverの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Stacks 0EUE

:::

