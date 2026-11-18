import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§5 Effective descent of étale morphisms" =>
%%%
number := false
tag := "rydh-5"
%%%

Rydh §5 の項目と、本体の宣言との対応。本文は対応表（`research/rydh-coverage`）の照合の理由で、原典の本文の写しではない。

:::definition "rydh_5_1" (uses := "rydh_A_1")
*記法 5.1*　エタール射のファイバー圏。対応表の状態：なし。

原典 PDF p.17, y=699.8。étale・descent・finite étale・algebraic spaceの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "rydh_5_2" (uses := "rydh_5_11, rydh_A_7")
*注意 5.2*　基底圏の選択。対応表の状態：なし。

原典 PDF p.18, y=288.8。étale・descent・finite étale・algebraic spaceの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "rydh_5_3" (uses := "rydh_A_3")
*命題 5.3*　普遍 submersion に沿うエタール射の降下。対応表の状態：なし。

原典 PDF p.18, y=388.4。étale・descent・finite étale・algebraic spaceの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：sga1

:::

:::proposition "rydh_5_4" (uses := "rydh_1_7")
*命題 5.4*　エタール射の性質の降下。対応表の状態：なし。

原典 PDF p.18, y=556.0。étale・descent・finite étale・algebraic spaceの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：egaIV

:::

:::proposition "rydh_5_5"
*Exposition 5.5*　エタール射の降下データ。対応表の状態：なし。

原典 PDF p.18, y=686.8。étale・descent・finite étale・algebraic spaceの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "rydh_5_6"
*命題 5.6*　降下射の合成と反映。対応表の状態：なし。

原典 PDF p.19, y=422.0。étale・descent・finite étale・algebraic spaceの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：giraud\_descente

:::

:::proposition "rydh_5_7"
*命題 5.7*　普遍降下による有効性の判定。対応表の状態：なし。

原典 PDF p.19, y=482.4。étale・descent・finite étale・algebraic spaceの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：giraud\_descente

:::

:::proposition "rydh_5_8" (uses := "rydh_5_3, rydh_5_6")
*命題 5.8*　逆極限に沿う普遍降下。対応表の状態：なし。

原典 PDF p.19, y=582.8。étale・descent・finite étale・algebraic spaceの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：egaIV

:::

:::proposition "rydh_5_9"
*命題 5.9*　逆極限での有効降下。対応表の状態：なし。

原典 PDF p.20, y=153.3。étale・descent・finite étale・algebraic spaceの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：egaIV、sga1

:::

:::proposition "rydh_5_10"
*命題 5.10*　忠実平坦準コンパクト射の有効降下。対応表の状態：なし。

原典 PDF p.20, y=400.6。étale・descent・finite étale・algebraic spaceの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：sga1

:::

:::proposition "rydh_5_11"
*命題 5.11*　忠実平坦局所有限表示射の有効降下。対応表の状態：なし。

原典 PDF p.20, y=448.0。étale・descent・finite étale・algebraic spaceの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：laumon

:::

:::proposition "rydh_5_12" (uses := "rydh_5_10, rydh_5_11, rydh_5_7, rydh_5_9")
*命題 5.12*　局所エタール持ち上げと降下。対応表の状態：なし。

原典 PDF p.20, y=501.3。étale・descent・finite étale・algebraic spaceの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "rydh_5_13" (uses := "rydh_5_11, rydh_5_9")
*注意 5.13*　Popescu による平滑近似と降下。対応表の状態：なし。

原典 PDF p.21, y=168.1。étale・descent・finite étale・algebraic spaceの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：spivakovsky\_popescus\_theorem、swan\_popescus\_theorem

:::

:::proposition "rydh_5_14" (uses := "rydh_5_10, rydh_5_12, rydh_A_6")
*命題 5.14*　固有全射に沿う有限エタール降下。対応表の状態：なし。

原典 PDF p.21, y=228.3。étale・descent・finite étale・algebraic spaceの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：sga1

:::

:::corollary "rydh_5_15" (uses := "rydh_5_12, rydh_5_14, rydh_5_16")
*系 5.15*　固有全射に沿う分離準コンパクトエタール降下。対応表の状態：なし。

原典 PDF p.21, y=435.9。étale・descent・finite étale・algebraic spaceの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：egaIII

:::

:::corollary "rydh_5_16" (uses := "rydh_5_12, rydh_5_15, rydh_A_12, rydh_A_7")
*系 5.16*　固有全射に沿う準コンパクトエタール降下。対応表の状態：なし。

原典 PDF p.22, y=217.8。étale・descent・finite étale・algebraic spaceの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::theorem "rydh_5_17" (uses := "rydh_3_10, rydh_5_11, rydh_5_16, rydh_5_6, rydh_5_8")
*定理 5.17*　普遍 subtrusive 射に沿う有効エタール降下。対応表の状態：なし。

原典 PDF p.22, y=586.9。étale・descent・finite étale・algebraic spaceの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：sga1

:::

:::corollary "rydh_5_18"
*系 5.18*　Noether 基底上の普遍 submersion の場合。対応表の状態：なし。

原典 PDF p.23, y=119.0。étale・descent・finite étale・algebraic spaceの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::theorem "rydh_5_19" (uses := "rydh_2_5, rydh_3_12, rydh_5_12, rydh_5_17, rydh_5_6")
*定理 5.19*　普遍開全射・普遍閉全射の有効降下。対応表の状態：なし。

原典 PDF p.23, y=169.2。étale・descent・finite étale・algebraic spaceの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：egaIV

:::

:::proposition "rydh_5_20"
*例 5.20*　エタール同値関係の商の例。対応表の状態：なし。

原典 PDF p.24, y=282.9。étale・descent・finite étale・algebraic spaceの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：knutson\_alg\_spaces、sga1

:::

:::theorem "rydh_5_21" (uses := "rydh_5_17, rydh_5_19, rydh_A_4")
*定理 5.21*　普遍同相によるエタール圏の同値。対応表の状態：なし。

原典 PDF p.24, y=423.8。étale・descent・finite étale・algebraic spaceの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::corollary "rydh_5_22" (uses := "rydh_5_21")
*系 5.22*　分離普遍同相の可表現性と整性。対応表の状態：なし。

原典 PDF p.24, y=725.7。étale・descent・finite étale・algebraic spaceの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：egaIV

:::

:::proposition "rydh_5_23" (uses := "rydh_5_21, rydh_5_22")
*注意 5.23*　非分離普遍同相での失敗。対応表の状態：なし。

原典 PDF p.25, y=205.2。étale・descent・finite étale・algebraic spaceの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "rydh_5_24"
*例 5.24*　閉埋め込みに沿う押し出し。対応表の状態：なし。

原典 PDF p.25, y=239.6。étale・descent・finite étale・algebraic spaceの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：ferrand\_conducteur

:::

:::proposition "rydh_5_25" (uses := "rydh_2_1, rydh_2_4")
*問い 5.25*　普遍 submersion での有効降下の問い。対応表の状態：なし。

原典 PDF p.25, y=471.6。étale・descent・finite étale・algebraic spaceの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：egaIV

:::

