import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§6 Construction of line bundles: geometric approach" =>
%%%
number := false
tag := "bs17-6"
%%%

BS17 §6 の項目と、本体の宣言との対応。本文は対応表（`research/bs17-coverage`）の照合の理由で、原典の本文の写しではない。

:::proposition "bs17_6_1" (uses := "bs17_3_8")
*命題 6.1*　proper · surjective · perfectly · finitely · presented。対応表の状態：なし。

原典 PDF p.20, y=531.0。line bundle・valuation・ultraproduct・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::lemma_ "bs17_6_2"
*補題 6.2*　qcqs · v-cover · each · connected · component。対応表の状態：なし。

原典 PDF p.21, y=139.9。line bundle・valuation・ultraproduct・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：BS19、BourbakiCA、KruckmanStoneCech、Stacks 092F、Stacks 092G

:::

:::lemma_ "bs17_6_3" (uses := "bs17_3_18")
*補題 6.3*　perfect · valuation · with · ordered · abelian。対応表の状態：一部（component）。

原典 PDF p.22, y=74.4。局所化・素イデアル商・剰余体による加法群の短完全列を与える。一般の完全 V スキームと任意の準連接複体に対する導来大域切断の三角は含まない。

宣言：`SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationRing_milnorSquare_perfect`

:::

:::lemma_ "bs17_6_4"
*補題 6.4*　perfect · valuation · specv · proper · perfectly。対応表の状態：なし。

原典 PDF p.22, y=505.6。line bundle・valuation・ultraproduct・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bs17_6_5" (uses := "bs17_6_1, bs17_6_12, bs17_6_3")
*注意 6.5*　the · more · generally · replacing · condition。対応表の状態：なし。

原典 PDF p.22, y=551.2。line bundle・valuation・ultraproduct・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::lemma_ "bs17_6_6"
*補題 6.6*　and · non-zero · divisor · complex。対応表の状態：なし。

原典 PDF p.23, y=234.4。line bundle・valuation・ultraproduct・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bs17_6_7" (uses := "bs17_3_18, bs17_6_4")
*注意 6.7*　for · perfect · valuation · exist · complexes。対応表の状態：なし。

原典 PDF p.23, y=273.7。line bundle・valuation・ultraproduct・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::theorem "bs17_6_8" (uses := "bs17_6_1, bs17_6_2, bs17_6_4")
*定理 6.8*　proper · perfectly · finitely · presented · perf。対応表の状態：なし。

原典 PDF p.23, y=554.7。line bundle・valuation・ultraproduct・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::lemma_ "bs17_6_9" (uses := "bs17_3_13, bs17_3_18, bs17_6_2, bs17_6_3")
*補題 6.9*　proper · surjective · perfectly · finitely · presented。対応表の状態：なし。

原典 PDF p.24, y=74.4。line bundle・valuation・ultraproduct・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：MehtaRamanathan

:::

:::corollary "bs17_6_10" (uses := "bs17_3_8, bs17_6_9")
*系 6.10*　proper · perfectly · finitely · presented · perfect。対応表の状態：なし。

原典 PDF p.24, y=439.1。line bundle・valuation・ultraproduct・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::lemma_ "bs17_6_11" (uses := "bs17_5_7, bs17_6_1, bs17_6_8, bs17_6_9")
*補題 6.11*　perfect · field · and · finite · length。対応表の状態：なし。

原典 PDF p.24, y=583.7。line bundle・valuation・ultraproduct・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bs17_6_12" (uses := "bs17_6_8")
*注意 6.12*　the · period · this · paper · was。対応表の状態：なし。

原典 PDF p.25, y=401.7。line bundle・valuation・ultraproduct・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::theorem "bs17_6_13" (uses := "bs17_4_1, bs17_6_4, bs17_6_8")
*定理 6.13*　proper · surjective · perfectly · finitely · presented。対応表の状態：なし。

原典 PDF p.25, y=472.7。line bundle・valuation・ultraproduct・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：BoschGuentzerRemmert、RG71

:::

:::lemma_ "bs17_6_14"
*補題 6.14*　complete · nonarchimedean · field · spherically · and。対応表の状態：なし。

原典 PDF p.26, y=362.7。line bundle・valuation・ultraproduct・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：ZhuMixedCharGeomSatake

:::

