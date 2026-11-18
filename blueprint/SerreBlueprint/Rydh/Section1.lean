import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§1 Topologies" =>
%%%
number := false
tag := "rydh-1"
%%%

Rydh §1 の項目と、本体の宣言との対応。本文は対応表（`research/rydh-coverage`）の照合の理由で、原典の本文の写しではない。

:::proposition "rydh_1_1"
*命題 1.1*　pro-constructible 集合のアフィン像表示。対応表の状態：なし。

原典 PDF p.4, y=552.4。constructible・spectral・specialization・topologyの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：egaI\_NE

:::

:::proposition "rydh_1_2"
*命題 1.2*　構成可能位相での連続性・開閉性。対応表の状態：なし。

原典 PDF p.4, y=667.4。constructible・spectral・specialization・topologyの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：egaI\_NE

:::

:::proposition "rydh_1_3"
*注意 1.3*　素スペクトルの特殊化順序。対応表の状態：Mathlib にある。

原典 PDF p.5, y=347.8。素イデアルの包含順序と specializes の同値。原典の点の ≤ は Lean の specializes の向きと逆で、極大な点は極小素イデアルになる。

宣言：`PrimeSpectrum.le_iff_specializes`

:::

:::proposition "rydh_1_4"
*命題 1.4*　構成可能集合の内部・閉包。対応表の状態：なし。

原典 PDF p.5, y=421.2。constructible・spectral・specialization・topologyの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：egaI\_NE

:::

:::corollary "rydh_1_5" (uses := "rydh_1_4")
*系 1.5*　構成可能位相と特殊化位相による開閉判定。対応表の状態：なし。

原典 PDF p.5, y=494.4。constructible・spectral・specialization・topologyの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "rydh_1_6" (uses := "rydh_1_2")
*命題 1.6*　構成可能位相での submersion。対応表の状態：なし。

原典 PDF p.6, y=119.0。constructible・spectral・specialization・topologyの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "rydh_1_7" (uses := "rydh_1_2")
*命題 1.7*　submersion に沿う性質の降下。対応表の状態：なし。

原典 PDF p.6, y=292.6。constructible・spectral・specialization・topologyの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：egaIV、egaI\_NE

:::

:::proposition "rydh_1_8" (uses := "rydh_1_1, rydh_1_7")
*注意 1.8*　代数空間の submersion。対応表の状態：なし。

原典 PDF p.6, y=622.0。constructible・spectral・specialization・topologyの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：RG71、knutson\_alg\_spaces、laumon

:::

