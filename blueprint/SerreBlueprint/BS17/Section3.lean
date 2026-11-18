import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.CommutativeAlgebra.PerfectTorIndependence.Basic

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§3 Perfect schemes" =>
%%%
number := false
tag := "bs17-3"
%%%

BS17 §3 の項目と、本体の宣言との対応。本文は対応表（`research/bs17-coverage`）の照合の理由で、原典の本文の写しではない。

:::definition "bs17_3_1"
*定義 3.1*　完全スキームと完全化。対応表の状態：一部（special）。

原典 PDF p.10, y=307.2。標数 p の環の Frobenius 余極限の完全性と降下写像を与える。Spec の双対でアフィン完全化に相当する。一般のスキームの逆極限は含まない。

宣言：`SerrePositivity.AlgebraicGeometry.ArcRouteB.frobeniusDirectLimit_perfectRing`、`SerrePositivity.AlgebraicGeometry.ArcRouteB.frobeniusDirectLimitDesc`

:::

:::definition "bs17_3_2"
*定義 3.2*　perf · the · category · perfect · qcqs。対応表の状態：なし。

原典 PDF p.10, y=361.1。Frobenius・perfection・perfect ring・Torの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bs17_3_3"
*注意 3.3*　avoid · set-theoretic · issues · the · defining。対応表の状態：なし。

原典 PDF p.10, y=394.6。Frobenius・perfection・perfect ring・Torの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::lemma_ "bs17_3_4" (uses := "bs17_6_2")
*補題 3.4*　not · necessarily · qcqs · over · the。対応表の状態：なし。

原典 PDF p.10, y=475.0。Frobenius・perfection・perfect ring・Torの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：TT

:::

:::lemma_ "bs17_3_5"
*補題 3.5*　for · any · qcqs · pullback · along。対応表の状態：なし。

原典 PDF p.11, y=334.2。Frobenius・perfection・perfect ring・Torの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Stacks 01PR

:::

:::lemma_ "bs17_3_6" (uses := "bs17_3_4")
*補題 3.6*　and · line · bundle · ample · only。対応表の状態：なし。

原典 PDF p.11, y=446.1。Frobenius・perfection・perfect ring・Torの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Stacks 04DY

:::

:::theorem "bs17_3_7"
*定理 3.7*　any · with · perfection · perf · equivalence。対応表の状態：なし。

原典 PDF p.11, y=577.0。Frobenius・perfection・perfect ring・Torの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::lemma_ "bs17_3_8"
*補題 3.8*　普遍同相と完全化。対応表の状態：一部（special）。

原典 PDF p.11, y=629.1。アフィンの普遍同相な環の射について、完全環での全単射と Frobenius 余極限上の同型を与える。一般のスキームへの貼り合わせと完全化後の同型からの逆向きは、この二つの型に含まれない。

宣言：`SerrePositivity.CommutativeAlgebra.isUniversalHomeomorphism_bijective_of_perfect_reduced`、`SerrePositivity.AlgebraicGeometry.frobeniusDirectLimitUniversalHomeomorphismEquiv`

外の文献：Stacks 04DC、Yanagihara

:::

:::proposition "bs17_3_9" (uses := "bs17_3_8, bs17_4_1, bs17_6_2")
*注意 3.9*　the · context · this · paper · different。対応表の状態：なし。

原典 PDF p.12, y=145.8。Frobenius・perfection・perfect ring・Torの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::definition "bs17_3_10"
*定義 3.10*　perfect · the · perfectly · finitely · presented。対応表の状態：なし。

原典 PDF p.12, y=275.8。Frobenius・perfection・perfect ring・Torの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bs17_3_11"
*命題 3.11*　perf · the · conditions · are · covering。対応表の状態：なし。

原典 PDF p.12, y=341.1。Frobenius・perfection・perfect ring・Torの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：EGAIV

:::

:::proposition "bs17_3_12"
*命題 3.12*　cofiltered · inverse · system · perf · with。対応表の状態：なし。

原典 PDF p.12, y=652.8。Frobenius・perfection・perfect ring・Torの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：EGAIV、ZhuMixedCharGeomSatake

:::

:::proposition "bs17_3_13" (uses := "bs17_3_11, bs17_3_12, bs17_3_8")
*命題 3.13*　perfectly · finitely · presented · perf · any。対応表の状態：なし。

原典 PDF p.13, y=204.6。Frobenius・perfection・perfect ring・Torの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：TT

:::

:::definition "bs17_3_14"
*定義 3.14*　perfectly · finitely · presented · perf · proper。対応表の状態：なし。

原典 PDF p.13, y=598.9。Frobenius・perfection・perfect ring・Torの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::corollary "bs17_3_15" (uses := "bs17_3_4")
*系 3.15*　perfectly · finitely · presented · perf · with。対応表の状態：なし。

原典 PDF p.13, y=632.4。Frobenius・perfection・perfect ring・Torの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::lemma_ "bs17_3_16" (lean := "SerrePositivity.tor_vanishing_of_perfect") (uses := "bs17_11_6")
*補題 3.16*　完全環上の正次数 Tor の消滅。対応表の状態：本体にある。

原典 PDF p.14, y=74.4。同じ素標数 p の完全環 A と完全 A-代数 B、C に対して、すべての正次数の Tor を零対象とする。

:::

:::proposition "bs17_3_17" (uses := "bs17_11_31, bs17_3_16")
*注意 3.17*　the · shows · any · quotient · perfect。対応表の状態：なし。

原典 PDF p.14, y=514.8。Frobenius・perfection・perfect ring・Torの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::lemma_ "bs17_3_18" (uses := "bs17_3_16")
*補題 3.18*　pullback · diagram · perf · for · any。対応表の状態：なし。

原典 PDF p.14, y=581.5。Frobenius・perfection・perfect ring・Torの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

