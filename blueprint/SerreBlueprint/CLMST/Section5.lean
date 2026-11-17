import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§5 BCM-regularity via perfectoid signature" =>
%%%
number := false
tag := "clmst-5"
%%%

CLMST（Cai–Lee–Ma–Schwede–Tucker, arXiv 2209.04046v4）§5 の項目と、本体の宣言との対応。本文は対応表（`research/clmst-coverage`）の照合の理由で、論文の本文の写しではない。

# §5.1 BCM-regular rings

%%%
number := false
tag := "clmst-5-1"
%%%

:::definition "clmst_5_1_1"
**定義 5.1.1**　弱 BCM 正則性と Q Gorenstein BCM 正則性。対応表の状態：なし。

原典 PDF p.44; layout L2420。原典の「弱 BCM 正則性と Q Gorenstein BCM 正則性」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

:::

:::proposition "clmst_5_1_2"
**注意 5.1.2**　正標数の弱 F 正則性との一致。対応表の状態：なし。

原典 PDF p.44; layout L2424。原典の「正標数の弱 F 正則性との一致」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

外の文献：Hoc07 Theorem on page 250、Hoc94 Theorem 11.1

:::

:::definition "clmst_5_1_3"
**定義 5.1.3**　因子対の BCM 正則性。対応表の状態：なし。

原典 PDF p.44; layout L2429。原典の「因子対の BCM 正則性」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

外の文献：MS21 Definition 6.9、MS21 Theorem 6.12 and Proposition 6.14、MST+22 Lemma 7.1、Tak04

:::

:::proposition "clmst_5_1_4" (uses := "clmst_5_1_1, clmst_5_1_3")
**注意 5.1.4**　balanced BCM 代数と極大イデアル完備化への帰着。対応表の状態：なし。

原典 PDF p.44; layout L2454。原典の「balanced BCM 代数と極大イデアル完備化への帰着」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

:::

:::lemma_ "clmst_5_1_5" (uses := "clmst_4_0_1")
**補題 5.1.5**　Galois 共役のテンソル積と共通 BCM 代数。対応表の状態：なし。

原典 PDF p.45; layout L2466。原典の「Galois 共役のテンソル積と共通 BCM 代数」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

外の文献：MS21 Proposition 5.7、MS21 Theorem 4.9

:::

:::lemma_ "clmst_5_1_6" (uses := "clmst_2_4_3, clmst_2_4_5, clmst_2_4_9, clmst_2_5_1, clmst_2_5_3, clmst_4_0_1, clmst_5_1_5")
**補題 5.1.6**　p 冪捩れ加群の消滅部分加群の比較と有限生成時の一致。対応表の状態：なし。

原典 PDF p.45; layout L2533。原典の「p 冪捩れ加群の消滅部分加群の比較と有限生成時の一致」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

外の文献：MS21 Theorem 4.9、MS21 Theorem A∞ c+ is a map 4.9

:::

:::proposition "clmst_5_1_7" (uses := "clmst_eq_5_1_7_1, clmst_4_0_1, clmst_5_1_6")
**命題 5.1.7**　純性を与える小さい元の存在の同値。対応表の状態：なし。

原典 PDF p.47; layout L2643。原典の「純性を与える小さい元の存在の同値」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

:::

:::definition "clmst_eq_5_1_7_1" (uses := "clmst_5_1_6")
**式 (5.1.7.1)**　入射包の almost 消滅部分加群が零になる条件。対応表の状態：なし。

原典 PDF p.47; layout L2658。原典の「入射包の almost 消滅部分加群が零になる条件」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

:::

# §5.2 BCM regularity and perfectoid signature

%%%
number := false
tag := "clmst-5-2"
%%%

:::proposition "clmst_5_2_1" (uses := "clmst_2_5_3, clmst_4_0_1, clmst_4_0_13")
**命題 5.2.1**　BCM 正則な因子対なら signature が正。対応表の状態：なし。

原典 PDF p.48; layout L2679。原典の「BCM 正則な因子対なら signature が正」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

:::

:::proposition "clmst_5_2_2" (uses := "clmst_4_0_1, clmst_4_0_10, clmst_5_1_7")
**命題 5.2.2**　正の signature から根による一様な純性。対応表の状態：なし。

原典 PDF p.48; layout L2722。原典の「正の signature から根による一様な純性」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

:::

:::proposition "clmst_5_2_3" (uses := "clmst_2_4_3, clmst_4_0_1, clmst_5_1_6")
**命題 5.2.3**　有限正規拡大のトレース条件による BCM 正則性。対応表の状態：なし。

原典 PDF p.49; layout L2739。原典の「有限正規拡大のトレース条件による BCM 正則性」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

:::

:::proposition "clmst_5_2_4" (uses := "clmst_5_2_1, clmst_5_2_2")
**注意 5.2.4**　正標数の F signature 正値性の別証明。対応表の状態：なし。

原典 PDF p.49; layout L2779。原典の「正標数の F signature 正値性の別証明」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

外の文献：AL03、HL02、MST+22、PT18、Pol22、SS10

:::

:::proposition "clmst_5_2_5" (uses := "clmst_2_5_1, clmst_4_0_1, clmst_4_0_10, clmst_4_0_13, clmst_5_1_6")
**命題 5.2.5**　HK 重複度の一致・BCM 閉包・extended plus closure の同値。対応表の状態：なし。

原典 PDF p.50; layout L2794。原典の「HK 重複度の一致・BCM 閉包・extended plus closure の同値」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

外の文献：HM21 Lemma 2.4.3, it follows that g u ∈ IR Lemma 3.1

:::

# §5.3 Strong BCM-regularity

%%%
number := false
tag := "clmst-5-3"
%%%

:::definition "clmst_5_3_1" (uses := "clmst_4_0_13, clmst_5_2_1, clmst_5_2_2")
**定義 5.3.1**　四種類の強 BCM 正則性。対応表の状態：なし。

原典 PDF p.51; layout L2848。原典の「四種類の強 BCM 正則性」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

外の文献：HH91、SS10

:::

:::definition "clmst_eq_5_3_1_1" (uses := "clmst_4_0_13, clmst_5_2_1, clmst_5_2_2")
**式 (5.3.1.1)**　BCM 正則性の諸概念と splinter の含意列。対応表の状態：なし。

原典 PDF p.51; layout L2869。原典の「BCM 正則性の諸概念と splinter の含意列」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

:::

:::proposition "clmst_5_3_2" (uses := "clmst_5_1_7")
**Example 5.3.2**　BCM 正則性の超曲面・klt 対・直和因子の例。対応表の状態：なし。

原典 PDF p.51; layout L2888。原典の「BCM 正則性の超曲面・klt 対・直和因子の例」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

外の文献：BMP+23 Corollary 7.16、MST+22 Example 7.8、MST+22 Theorem 7.11

:::

:::definition "clmst_5_3_3"
**定義 5.3.3**　モノイドの単元群と群完備化。対応表の状態：一部。

原典 PDF p.52; layout L2908。Mathlib の可換モノイドの群完備化を局所化として確認（加法版は to\_additive）。原典の M\* の集合と Mgp の両記号のうち群完備化側のみを採用し、モノイドを明示的に可換に限る。強凸・正規性など次項の条件は含まない。

宣言：`Algebra.GrothendieckGroup`

:::

:::definition "clmst_5_3_4"
**定義 5.3.4**　強凸・整・飽和・正規・full モノイド。対応表の状態：なし。

原典 PDF p.52; layout L2910。原典の「強凸・整・飽和・正規・full モノイド」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

:::

:::proposition "clmst_5_3_5" (uses := "clmst_5_2_1")
**命題 5.3.5**　Witt モノイド環の超曲面の BCM 正則性。対応表の状態：なし。

原典 PDF p.52; layout L2936。原典の「Witt モノイド環の超曲面の BCM 正則性」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

外の文献：Bli04、Ful93、GR22、Hoc72、Kol13、MST+22 Subsection 2.1、MST+22 Theorem 4.1、MST+22 Theorem A.5、Mus05、Rob22

:::

# §5.4 BCM-rational rings and perfectoid rational and relative rational signatures

%%%
number := false
tag := "clmst-5-4"
%%%

:::definition "clmst_5_4_1"
**定義 5.4.1**　BCM 有理性。対応表の状態：なし。

原典 PDF p.54; layout L3026。原典の「BCM 有理性」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

:::

:::definition "clmst_5_4_2" (uses := "clmst_4_0_1")
**定義 5.4.2**　perfectoid 有理・相対有理 signature の定義。対応表の状態：なし。

原典 PDF p.54; layout L3031。原典の「perfectoid 有理・相対有理 signature の定義」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

外の文献：MS21

:::

:::proposition "clmst_5_4_3" (uses := "clmst_4_0_1, clmst_5_2_5")
**命題 5.4.3**　非 Cohen–Macaulay 環での有理 signature の消滅。対応表の状態：なし。

原典 PDF p.55; layout L3052。原典の「非 Cohen–Macaulay 環での有理 signature の消滅」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

外の文献：CHL99 Corollary 2.4、MQS20 Theorem 9

:::

:::lemma_ "clmst_5_4_4" (uses := "clmst_2_2_6, clmst_4_0_1")
**補題 5.4.4**　socle へ移す HK 長さ差の比の評価。対応表の状態：なし。

原典 PDF p.55; layout L3067。原典の「socle へ移す HK 長さ差の比の評価」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

外の文献：ST24 Proposition 3.5

:::

:::proposition "clmst_5_4_5" (uses := "clmst_4_0_1, clmst_5_4_4")
**命題 5.4.5**　有理 signature の socle 上の下限表示。対応表の状態：なし。

原典 PDF p.56; layout L3137。原典の「有理 signature の socle 上の下限表示」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

:::

:::corollary "clmst_5_4_6" (uses := "clmst_4_0_1, clmst_4_0_23, clmst_5_4_5")
**系 5.4.6**　三種の signature と Cohen–Macaulay type の比較。対応表の状態：なし。

原典 PDF p.56; layout L3169。原典の「三種の signature と Cohen–Macaulay type の比較」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

:::

:::proposition "clmst_5_4_7" (uses := "clmst_4_0_1, clmst_4_0_18, clmst_4_0_20, clmst_4_1_1, clmst_5_4_3")
**命題 5.4.7**　相対有理 signature の上界と正則性。対応表の状態：なし。

原典 PDF p.57; layout L3195。原典の「相対有理 signature の上界と正則性」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

外の文献：BH93 Corollary 4.7.11

:::

:::lemma_ "clmst_5_4_8" (uses := "clmst_4_0_1, clmst_4_0_10, clmst_4_0_5")
**補題 5.4.8**　HK 長さ差の局所コホモロジー像による表示。対応表の状態：なし。

原典 PDF p.57; layout L3216。原典の「HK 長さ差の局所コホモロジー像による表示」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

:::

:::proposition "clmst_5_4_9" (uses := "clmst_4_0_1, clmst_5_4_3, clmst_5_4_5, clmst_5_4_8")
**命題 5.4.9**　固定パラメータと局所コホモロジーによる下限表示。対応表の状態：なし。

原典 PDF p.57; layout L3242。原典の「固定パラメータと局所コホモロジーによる下限表示」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

:::

:::theorem "clmst_5_4_10" (uses := "clmst_2_5_3")
**定理 5.4.10**　BCM 有理環の小付値元による局所コホモロジーの単射性。対応表の状態：なし。

原典 PDF p.59; layout L3326。原典の「BCM 有理環の小付値元による局所コホモロジーの単射性」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

:::

:::theorem "clmst_5_4_11" (uses := "clmst_4_0_1, clmst_4_0_11, clmst_4_0_12, clmst_5_2_5, clmst_5_4_10, clmst_5_4_3, clmst_5_4_6, clmst_5_4_9")
**定理 5.4.11**　BCM 有理性と二種の有理 signature の正値性。対応表の状態：なし。

原典 PDF p.59; layout L3358。原典の「BCM 有理性と二種の有理 signature の正値性」に対応する定義または主張を持つ宣言を確認できない。 正規化長さ・局所コホモロジー・Witt 環の一般補助があっても、BCM 代数や signature の該当条件を構成したことにはならない。

:::

