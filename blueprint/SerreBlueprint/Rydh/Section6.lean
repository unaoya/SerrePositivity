import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§6 Passage to the limit" =>
%%%
number := false
tag := "rydh-6"
%%%

Rydh §6 の項目と、本体の宣言との対応。本文は対応表（`research/rydh-coverage`）の照合の理由で、原典の本文の写しではない。

:::definition "rydh_6_1"
*記法 6.1*　アフィン遷移射の逆系。対応表の状態：なし。

原典 PDF p.25, y=625.9。filtered・limit・descent・finite presentationの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：egaIV

:::

:::proposition "rydh_6_2" (uses := "rydh_2_1, rydh_6_1")
*命題 6.2*　逆極限と subtrusive 性。対応表の状態：なし。

原典 PDF p.25, y=725.7。filtered・limit・descent・finite presentationの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：picavet\_submersion

:::

:::corollary "rydh_6_3" (uses := "rydh_2_4, rydh_6_2")
*系 6.3*　有限次元アフィン空間への底変換での判定。対応表の状態：なし。

原典 PDF p.26, y=425.1。filtered・limit・descent・finite presentationの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::theorem "rydh_6_4" (uses := "rydh_2_4, rydh_3_10, rydh_6_1")
*定理 6.4*　普遍 subtrusive 性の有限段への降下。対応表の状態：なし。

原典 PDF p.26, y=592.6。filtered・limit・descent・finite presentationの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：egaIV

:::

:::corollary "rydh_6_5" (uses := "rydh_4_3")
*系 6.5*　アフィン基底での有限段判定。対応表の状態：なし。

原典 PDF p.27, y=153.3。filtered・limit・descent・finite presentationの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::theorem "rydh_6_6" (uses := "rydh_3_10, rydh_6_1")
*定理 6.6*　普遍開性の有限段への降下。対応表の状態：なし。

原典 PDF p.27, y=323.2。filtered・limit・descent・finite presentationの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：egaIV、laumon

:::

