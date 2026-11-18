import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§B Absolute weak normalization" =>
%%%
number := false
tag := "rydh-B"
%%%

Rydh §B の項目と、本体の宣言との対応。本文は対応表（`research/rydh-coverage`）の照合の理由で、原典の本文の写しではない。

:::definition "rydh_B_1"
*定義 B.1*　絶対弱正規と絶対弱正規化。対応表の状態：一部（special）。

原典 PDF p.38, y=237.6。完全標数 p の環 A と被約環 B に対するアフィン普遍同相では環準同型が全単射になる。絶対弱正規性の判定のアフィン完全環の場合で、一般の被約スキーム・代数空間の定義や正規化の構成までは含まない。

宣言：`SerrePositivity.CommutativeAlgebra.isUniversalHomeomorphism_bijective_of_perfect_reduced`

:::

:::proposition "rydh_B_2" (uses := "rydh_3_8")
*Properties B.2*　絶対弱正規スキームの性質。対応表の状態：なし。

原典 PDF p.38, y=360.8。weak normalization・universal homeomorphism・subintegral・reducedの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：olivier\_sem\_samuel-2

:::

:::definition "rydh_B_3"
*定義 B.3*　弱 subintegral 拡大とその閉包。対応表の状態：一部（component）。

原典 PDF p.38, y=558.9。環射の整性・素点での全単射性・剰余体の純非分離性により Spec の普遍同相を表す。単射を入力にすれば weakly subintegral な拡大の条件に対応する。最大のそのような部分拡大の構成は含まない。

宣言：`SerrePositivity.CommutativeAlgebra.IsUniversalHomeomorphism`

外の文献：egaIV

:::

:::proposition "rydh_B_4"
*Properties B.4*　弱 subintegral 閉包の性質。対応表の状態：なし。

原典 PDF p.38, y=738.7。weak normalization・universal homeomorphism・subintegral・reducedの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：egaIV

:::

:::lemma_ "rydh_B_5"
*補題 B.5*　テンソル積による弱 subintegral 閉包の判定。対応表の状態：なし。

原典 PDF p.39, y=272.7。weak normalization・universal homeomorphism・subintegral・reducedの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：egaI\_NE、manaresi

:::

:::proposition "rydh_B_6" (uses := "rydh_3_9, rydh_B_5")
*命題 B.6*　局所化・エタール底変換での閉包。対応表の状態：なし。

原典 PDF p.39, y=431.6。weak normalization・universal homeomorphism・subintegral・reducedの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：egaIV

:::

:::definition "rydh_B_7"
*定義 B.7*　射に関する弱正規化。対応表の状態：なし。

原典 PDF p.40, y=266.8。weak normalization・universal homeomorphism・subintegral・reducedの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "rydh_B_8"
*注意 B.8*　整域・被約環の弱正規性。対応表の状態：なし。

原典 PDF p.40, y=340.3。weak normalization・universal homeomorphism・subintegral・reducedの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

