import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.LengthAlgebra.Flat
import SerrePositivity.Paper.Section3.LengthComputation
import SerrePositivity.Paper.Section3.NormComparison

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§3 Rational descent with closed supports" =>
%%%
number := false
tag := "paper-3"
%%%

本論文 §3 の項目と、本体の宣言との対応。本文は対応表（`research/paper-coverage`）の照合の理由で、論文の本文の写しではない。

:::theorem "paper_3_1" (uses := "paper_eq_3_1, paper_eq_3_2, paper_eq_3_5, paper_eq_3_6, paper_eq_3_7, paper_eq_3_8, paper_3_3")
**定理 3.1**　任意の連結結合係数を持つ台つき有理降下。対応表の状態：未証明の入力に依存。

原典 PDF p.10 / layout L502。本体の入力は離散H=A、局所基底とパラメータ台についてのK0の正整数倍持ち上げで、直接sorryを持つ。原典の任意の連結結合Hと有理Kスペクトルの同値は未構成なので、入力界面としてのみ対応する。

宣言：`SerrePositivity.theorem_3_1_K0`

外の文献：BGT 8.1、BGT 8.7、BGT 9.3、BGT 9.8、Goodwillie Main Theorem、LT 3.10、LT 3.12、LT 3.9、LT A.2、LT Appendix B、LT B.2、LT B.3、TT 5.2.2、TT 5.2.3、TT 5.2.4、TT 7.4

:::

:::definition "paper_eq_3_1" (uses := "paper_eq_3_2, paper_eq_3_6, paper_eq_3_7, paper_eq_3_8, paper_3_3")
**式 (3.1)**　台つき有理KスペクトルのGalois降下。対応表の状態：なし。

原典 PDF p.10 / layout L509。連結非可換係数H、support、rationalizationとhomotopy fixed pointsのスペクトル同値の宣言はない。離散K0入力で代用しない。

:::

:::definition "paper_eq_3_2" (uses := "paper_eq_3_1, paper_eq_3_6")
**式 (3.2)**　台つき有理K0のG不変部分への全射。対応表の状態：未証明の入力に依存。

原典 PDF p.10 / layout L514。離散・局所・パラメータ台の場合の正整数倍の持ち上げを直接sorryで置く。原典の任意Hに対する全射全体にはまだ達しない。

宣言：`SerrePositivity.theorem_3_1_K0`

:::

# §3.1 The truncating invariant and its supports

%%%
number := false
tag := "paper-3-1"
%%%

:::definition "paper_eq_3_3"
**式 (3.3)**　pを反転して消える有理K理論のfiber E。対応表の状態：なし。

原典 PDF p.11 / layout L540。任意の導来Z\_(p)代数Uに対するスペクトルfiber E(U)の定義を確認できない。

:::

:::definition "paper_eq_3_4"
**式 (3.4)**　Eとinfinitesimal K理論のfiberとの同値。対応表の状態：なし。

原典 PDF p.11 / layout L544。負巡回ホモロジーとcharacter squareから得るfiber比較の同値は未構成。

:::

:::definition "paper_eq_3_5"
**式 (3.5)**　閉台を取る係数付きfiber L。対応表の状態：なし。

原典 PDF p.11 / layout L556。scheme上の係数付きスペクトルの開補集合restrictionのfiberとしてLを構成する宣言はない。

:::

:::definition "paper_eq_3_6" (uses := "paper_eq_3_5")
**式 (3.6)**　Lと実際の台つきperfect K理論との同定。対応表の状態：なし。

原典 PDF p.11 / layout L564。係数付きperfect localizationを使う有理Kスペクトルの同定はない。中心的台の判定だけでは同じ主張にならない。

外の文献：BGT 8.1、BGT 8.7、BGT 9.3、BGT 9.8、LT 3.12、LT B.2、TT 5.2.2、TT 5.2.3、TT 5.2.4、TT 7.4

:::

# §3.2 Descent for finite surjections

%%%
number := false
tag := "paper-3-2"
%%%

:::lemma_ "paper_3_2"
**補題 3.2**　有限忠実平坦被覆に沿う普遍Čech降下。対応表の状態：なし。

原典 PDF p.12 / layout L587。任意の係数付き有理支持KスペクトルLについて、有限平坦transfer・trivialization・自然なretract・Čech totalizationを組み合わせる主張は確認できない。有限群和のK0計算だけでは同じ型にならない。

:::

:::lemma_ "paper_3_3" (uses := "paper_3_2")
**補題 3.3**　有限全射に沿う通常のČech降下。対応表の状態：なし。

原典 PDF p.12 / layout L609。cdh sheafと有限忠実平坦Čech降下から、flattening blowupと次元帰納で全有限全射の降下を得るLのスペクトル値定理は未構成。KSTの幾何学補助や層の一般論だけを対応宣言とはしない。

外の文献：Stacks 0815

:::

# §3.3 The geometric orbit argument

%%%
number := false
tag := "paper-3-3"
%%%

:::definition "paper_eq_3_7" (uses := "paper_eq_3_1, paper_eq_3_6, paper_eq_3_8, paper_3_3")
**式 (3.7)**　幾何的軌道議論の自然な固定点比較。対応表の状態：なし。

原典 PDF p.13 / layout L647。任意の有限型S-scheme Yに自然なL(Y)→L(X×Y)\^hGのスペクトル比較と同値を確認できない。

:::

:::definition "paper_eq_3_8" (uses := "paper_eq_3_7")
**式 (3.8)**　推移的置換作用の有理homotopy固定点。対応表の状態：なし。

原典 PDF p.13 / layout L689。非有界有理スペクトルの置換作用のhomotopy fixed pointsの同値を確認できない。群和の数値平均とは別である。

:::

# §3.4 Comparison of ordinary and normalized Euler lengths

%%%
number := false
tag := "paper-3-4"
%%%

:::definition "paper_eq_3_9" (lean := "SerrePositivity.lemma_3_4") (uses := "paper_2_5, paper_2_6")
**式 (3.9)**　比較に仮定する基底Koszul長と商長。対応表の状態：本体にある。

原典 PDF p.14 / layout L725。ここは独立の存在定理ではなくSection3.4の長さ仮定。lemma\_3\_4のhzero・hquotに同じ全冪の仮定が現れる。Theorem2.5からの供給は別項目で扱う。

:::

:::lemma_ "paper_3_4" (lean := "SerrePositivity.lemma_3_4, SerrePositivity.normalizedLength_tor_of_isWeaklyRegular") (uses := "paper_eq_3_9")
**補題 3.4**　有限長加群の通常長と正規化Tor長。対応表の状態：本体にある。

原典 PDF p.14 / layout L730。(3.9)のKoszul長条件から、任意有限長Vの高次Tor長零とdegree0のr倍公式、有限性を導く。弱正則列による一般のTor長計算へ帰着しており、降下入力は使わない。

:::

:::definition "paper_eq_3_10" (lean := "SerrePositivity.lemma_3_4") (uses := "paper_eq_3_9")
**式 (3.10)**　有限長加群に対するTor長のr倍公式。対応表の状態：本体にある。

原典 PDF p.14 / layout L733。Lemma3.4と同じ二つの結論。

:::

:::lemma_ "paper_3_5" (uses := "paper_eq_3_11, paper_eq_3_12, paper_eq_3_13, paper_eq_3_14, paper_eq_3_9, paper_3_1, paper_3_4")
**補題 3.5**　通常のEuler評価とnorm和の比較。対応表の状態：未証明の入力に依存。

原典 PDF p.15 / layout L748。有限性・加法性および基底からの引戻しでの比較は別々に証明されている。一般の不変K0類・norm和へ広げるlemma\_3\_5cはtheorem\_3\_1\_K0のsorryに依存する。原典の二つの評価を個々の共役について等しいとはしていない。

宣言：`SerrePositivity.lemma_3_5a`、`SerrePositivity.lemma_3_5b`、`SerrePositivity.lemma_3_5c`、`SerrePositivity.theorem_3_1_K0`

:::

:::definition "paper_eq_3_11" (uses := "paper_eq_3_13, paper_eq_3_14, paper_3_1")
**式 (3.11)**　共役Euler評価のnorm和の一致。対応表の状態：未証明の入力に依存。

原典 PDF p.15 / layout L761。有理不変類の持ち上げを通常K0降下入力に依存して証明する。

宣言：`SerrePositivity.lemma_3_5c`

:::

:::definition "paper_eq_3_12" (uses := "paper_eq_3_9")
**式 (3.12)**　零ホモトピーのKoszul cone分裂。対応表の状態：なし。

原典 PDF p.15 / layout L777。有限Koszulテンソルのshiftと二項係数への分裂は周辺のKoszul計算で用いられるが、任意の支持perfect T複体Pと任意Cについてこの表示の同型を一つの対応宣言として未同定。

:::

:::definition "paper_eq_3_13" (lean := "SerrePositivity.lemma_3_5b_lam") (uses := "paper_3_4")
**式 (3.13)**　基底から来る正規化Euler評価。対応表の状態：本体にある。

原典 PDF p.15 / layout L793。C評価の値をrankA(T)×普通の基底Euler値として返す。

:::

:::definition "paper_eq_3_14" (lean := "SerrePositivity.lemma_3_5b_ord") (uses := "paper_eq_3_13")
**式 (3.14)**　基底から来る通常Euler評価。対応表の状態：本体にある。

原典 PDF p.15 / layout L810。普通T評価について同じrank倍公式を与える。

:::

:::proposition "paper_3_6"
**注意 3.6**　長さのG不変性を要求しないという注意。対応表の状態：一部。

原典 PDF p.16 / layout L823。定理の型はlambdaのG不変性を仮定せずnorm和だけを比較する。この注意の論理的内容は読み取れるが、個々の評価が不変でない具体例や独立の否定命題は宣言していない。比較自体は入力依存。

宣言：`SerrePositivity.lemma_3_5c`

:::

