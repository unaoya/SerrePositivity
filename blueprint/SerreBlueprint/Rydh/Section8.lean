import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§8 The h-topology" =>
%%%
number := false
tag := "rydh-8"
%%%

Rydh §8 の項目と、本体の宣言との対応。本文は対応表（`research/rydh-coverage`）の照合の理由で、原典の本文の写しではない。

:::definition "rydh_8_1"
*定義 8.1*　h 位相と qfh 位相。対応表の状態：なし。

原典 PDF p.31, y=119.0。h-topology・étale・sheaf・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "rydh_8_2"
*注意 8.2*　qcqs スキームへの制限。対応表の状態：なし。

原典 PDF p.31, y=238.0。h-topology・étale・sheaf・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "rydh_8_3"
*注意 8.3*　h 被覆を生成する射。対応表の状態：なし。

原典 PDF p.31, y=285.4。h-topology・étale・sheaf・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：egaIV、voevodsky\_homology

:::

:::theorem "rydh_8_4" (uses := "rydh_3_11, rydh_3_12")
*定理 8.4*　h 被覆と qfh 被覆の細分。対応表の状態：なし。

原典 PDF p.31, y=406.9。h-topology・étale・sheaf・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：milne\_etale\_coh、sga3、voevodsky\_homology

:::

:::definition "rydh_8_5"
*定義 8.5*　前層の局所一致による商。対応表の状態：なし。

原典 PDF p.31, y=699.3。h-topology・étale・sheaf・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "rydh_8_6"
*注意 8.6*　分離化から層化への移行。対応表の状態：なし。

原典 PDF p.32, y=233.2。h-topology・étale・sheaf・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：artin\_groth\_top

:::

:::definition "rydh_8_7"
*定義 8.7*　可表現前層の分離化と層化。対応表の状態：なし。

原典 PDF p.32, y=295.8。h-topology・étale・sheaf・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::lemma_ "rydh_8_8" (uses := "rydh_7_2")
*補題 8.8*　被約試験スキーム上の分離化。対応表の状態：なし。

原典 PDF p.32, y=373.4。h-topology・étale・sheaf・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：voevodsky\_homology

:::

:::lemma_ "rydh_8_9" (uses := "rydh_7_2")
*補題 8.9*　分離化と被約化上の射の像。対応表の状態：なし。

原典 PDF p.32, y=452.5。h-topology・étale・sheaf・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：egaIV

:::

:::proposition "rydh_8_10"
*注意 8.10*　分離化と全ての被約化上の射の差。対応表の状態：なし。

原典 PDF p.32, y=725.7。h-topology・étale・sheaf・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：voevodsky\_homology

:::

:::proposition "rydh_8_11" (uses := "rydh_8_9")
*命題 8.11*　有限型代数空間の層化の余極限表示。対応表の状態：なし。

原典 PDF p.33, y=153.3。h-topology・étale・sheaf・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::definition "rydh_8_12" (uses := "rydh_8_11, rydh_8_8")
*定義 8.12*　被覆上での切断の実現。対応表の状態：なし。

原典 PDF p.33, y=361.4。h-topology・étale・sheaf・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::lemma_ "rydh_8_13"
*補題 8.13*　エタール被覆で実現された切断の降下。対応表の状態：なし。

原典 PDF p.33, y=502.6。h-topology・étale・sheaf・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：voevodsky\_homology

:::

:::proposition "rydh_8_14" (uses := "rydh_7_4, rydh_8_13, rydh_8_9")
*命題 8.14*　切断を実現する細分。対応表の状態：なし。

原典 PDF p.33, y=594.9。h-topology・étale・sheaf・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::corollary "rydh_8_15" (uses := "rydh_8_14")
*系 8.15*　有限表示代数空間への適用。対応表の状態：なし。

原典 PDF p.33, y=725.7。h-topology・étale・sheaf・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::theorem "rydh_8_16" (uses := "rydh_8_11, rydh_8_15")
*定理 8.16*　h 層化と絶対弱正規化。対応表の状態：なし。

原典 PDF p.34, y=198.4。h-topology・étale・sheaf・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "rydh_8_17" (uses := "rydh_3_14, rydh_5_14, rydh_5_16, rydh_8_11, rydh_8_14, rydh_8_15, rydh_8_16, rydh_8_4, rydh_8_9, rydh_A_13, rydh_A_2, rydh_A_4, rydh_A_7")
*注意 8.17*　非 Noether の場合の位相の変形。対応表の状態：なし。

原典 PDF p.34, y=408.8。h-topology・étale・sheaf・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

