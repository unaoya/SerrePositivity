import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§A Étale morphisms and henselian pairs" =>
%%%
number := false
tag := "rydh-A"
%%%

Rydh §A の項目と、本体の宣言との対応。本文は対応表（`research/rydh-coverage`）の照合の理由で、原典の本文の写しではない。

:::proposition "rydh_A_1"
*命題 A.1*　分離エタール射の可表現性。対応表の状態：なし。

原典 PDF p.34, y=725.7。henselian・étale・algebraic space・properの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：knutson\_alg\_spaces

:::

:::proposition "rydh_A_2" (uses := "rydh_A_1")
*命題 A.2*　対角・切断・普遍単射での開埋め込み。対応表の状態：一部（component）。

原典 PDF p.35, y=119.0。エタール射は局所有限型かつ形式的不分岐なので、スキームの場合には (i) の対角射が開埋め込みになり、底変換で (ii) の切断も開埋め込みになる。代数空間の一般性を含まない。

宣言：`AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal`

:::

:::corollary "rydh_A_3" (uses := "rydh_A_2")
*系 A.3*　エタール空間への射のグラフ。対応表の状態：なし。

原典 PDF p.35, y=262.6。henselian・étale・algebraic space・properの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "rydh_A_4" (uses := "rydh_A_3")
*命題 A.4*　nilimmersion によるエタール圏の不変性。対応表の状態：なし。

原典 PDF p.35, y=352.3。henselian・étale・algebraic space・properの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：egaIV

:::

:::proposition "rydh_A_5"
*命題 A.5*　完備局所固有スキームの開閉集合。対応表の状態：なし。

原典 PDF p.35, y=551.6。henselian・étale・algebraic space・properの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：egaIII

:::

:::theorem "rydh_A_6" (uses := "rydh_A_4")
*定理 A.6*　完備局所固有スキームの有限エタール圏。対応表の状態：なし。

原典 PDF p.35, y=628.3。henselian・étale・algebraic space・properの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：egaIII、egaIV

:::

:::proposition "rydh_A_7"
*命題 A.7*　閉部分とエタール層の切断。対応表の状態：なし。

原典 PDF p.36, y=187.6。henselian・étale・algebraic space・properの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：artin\_theoremes\_de\_repr、milne\_etale\_coh、sga4

:::

:::proposition "rydh_A_8" (uses := "rydh_A_2")
*注意 A.8*　espace étalé の局所分離性。対応表の状態：なし。

原典 PDF p.37, y=205.2。henselian・étale・algebraic space・properの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "rydh_A_9" (uses := "rydh_A_7")
*注意 A.9*　閉部分への制限の判定。対応表の状態：なし。

原典 PDF p.37, y=265.5。henselian・étale・algebraic space・properの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：egaIV、raynaud\_hensel\_rings、sga4

:::

:::definition "rydh_A_10" (uses := "rydh_A_5, rydh_A_6, rydh_A_7")
*定義 A.10*　Hensel 対の定義。対応表の状態：なし。

原典 PDF p.37, y=351.7。henselian・étale・algebraic space・properの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::theorem "rydh_A_11" (uses := "rydh_A_5")
*定理 A.11*　完備局所基底の固有スキームの Hensel 性。対応表の状態：なし。

原典 PDF p.37, y=427.8。henselian・étale・algebraic space・properの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "rydh_A_12"
*命題 A.12*　Hensel 局所基底での開閉集合。対応表の状態：なし。

原典 PDF p.37, y=503.8。henselian・étale・algebraic space・properの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：artin\_alg\_approximation、egaIV、sga4、spivakovsky\_popescus\_theorem、swan\_popescus\_theorem

:::

:::theorem "rydh_A_13" (uses := "rydh_5_22")
*定理 A.13*　Hensel 局所基底における固有底変換。対応表の状態：なし。

原典 PDF p.37, y=644.7。henselian・étale・algebraic space・properの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：and-bom、artin\_theoremes\_de\_repr、egaIV、manaresi、sga4、yanagihara\_1

:::

