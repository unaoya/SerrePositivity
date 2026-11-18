import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "§6 Transformation rules under finite maps" =>
%%%
number := false
tag := "clmst-6"
%%%

CLMST §6 の項目と、本体の宣言との対応。本文は対応表（`research/clmst-coverage`）の照合の理由で、原典の本文の写しではない。

:::theorem "clmst_6_0_1" (uses := "clmst_eq_6_0_1_1, clmst_eq_6_0_2_2, clmst_2_4_3, clmst_2_4_5, clmst_4_0_1, clmst_4_0_16, clmst_6_1_1, clmst_6_1_4, clmst_6_2_1, clmst_6_2_2")
*定理 6.0.1*　有限準エタール分裂拡大の signature 変換則。対応表の状態：なし。

原典 PDF p.61; layout L3437。原典の「有限準エタール分裂拡大の signature 変換則」に対応する定義または主張を持つ宣言を確認できない。 本体の almost Tor・同種性と有限自由比較は補助であり、この項目の一様 almost 自由性・非分裂イデアル・signature の結論を代替しない。

外の文献：BJNnB19、BS19 Proposition 8.13、CR22、CRST18、HL02、JS22、Stacks Tag 0BMB、VK12、XZ21

:::

:::proposition "clmst_6_0_2" (uses := "clmst_eq_6_0_2_2, clmst_2_2_6")
*注意 6.0.2*　剰余体拡大と基底別の正規化長さの尺度。対応表の状態：なし。

原典 PDF p.61; layout L3445。原典の「剰余体拡大と基底別の正規化長さの尺度」に対応する定義または主張を持つ宣言を確認できない。 本体の almost Tor・同種性と有限自由比較は補助であり、この項目の一様 almost 自由性・非分裂イデアル・signature の結論を代替しない。

外の文献：BS19 Proposition 8.5

:::

:::definition "clmst_eq_6_0_2_1"
*式 (6.0.2.1)*　剰余体拡大の前後の S\_perfd の同型。対応表の状態：なし。

原典 PDF p.61; layout L3459。原典の「剰余体拡大の前後の S\_perfd の同型」に対応する定義または主張を持つ宣言を確認できない。 本体の almost Tor・同種性と有限自由比較は補助であり、この項目の一様 almost 自由性・非分裂イデアル・signature の結論を代替しない。

外の文献：BS19 Proposition 8.5

:::

:::definition "clmst_eq_6_0_2_2" (uses := "clmst_2_2_6")
*式 (6.0.2.2)*　剰余体次数による正規化長さの尺度変換。対応表の状態：なし。

原典 PDF p.61; layout L3470。原典の「剰余体次数による正規化長さの尺度変換」に対応する定義または主張を持つ宣言を確認できない。 本体の almost Tor・同種性と有限自由比較は補助であり、この項目の一様 almost 自由性・非分裂イデアル・signature の結論を代替しない。

:::

:::corollary "clmst_6_0_3" (uses := "clmst_eq_6_0_2_1, clmst_eq_6_0_2_2, clmst_2_4_5, clmst_4_0_1, clmst_6_0_1, clmst_6_2_2")
*系 6.0.3*　有限エタール拡大での perfectoid 不変量の不変性。対応表の状態：なし。

原典 PDF p.61; layout L3493。原典の「有限エタール拡大での perfectoid 不変量の不変性」に対応する定義または主張を持つ宣言を確認できない。 本体の almost Tor・同種性と有限自由比較は補助であり、この項目の一様 almost 自由性・非分裂イデアル・signature の結論を代替しない。

:::

:::corollary "clmst_6_0_4" (uses := "clmst_4_0_1, clmst_4_0_14, clmst_4_0_17, clmst_4_0_18, clmst_4_0_23, clmst_4_0_8, clmst_6_0_3")
*系 6.0.4*　S2・重複度 2 の環での二不変量の和。対応表の状態：なし。

原典 PDF p.62; layout L3531。原典の「S2・重複度 2 の環での二不変量の和」に対応する定義または主張を持つ宣言を確認できない。 本体の almost Tor・同種性と有限自由比較は補助であり、この項目の一様 almost 自由性・非分裂イデアル・signature の結論を代替しない。

外の文献：And18a Page 72 (2)、BH93 Corollary 4.7.11、HS06 Proposition 8.3.7 and Corollary 8.3.9、Ike97

:::

:::definition "clmst_eq_6_0_1_1" (uses := "clmst_2_4_5, clmst_4_0_1, clmst_6_1_1, clmst_6_1_4, clmst_6_2_2")
*式 (6.0.1.1)*　有限自由近似写像の像と p 冪根による被覆。対応表の状態：なし。

原典 PDF p.68; layout L3897。原典の「有限自由近似写像の像と p 冪根による被覆」に対応する定義または主張を持つ宣言を確認できない。 本体の almost Tor・同種性と有限自由比較は補助であり、この項目の一様 almost 自由性・非分裂イデアル・signature の結論を代替しない。

:::

# §6.1 Almost projective and almost finite free modules

%%%
number := false
tag := "clmst-6-1"
%%%

:::lemma_ "clmst_6_1_1"
*補題 6.1.1*　almost 射影加群からの射のスカラー倍の lift。対応表の状態：なし。

原典 PDF p.63; layout L3589。原典の「almost 射影加群からの射のスカラー倍の lift」に対応する定義または主張を持つ宣言を確認できない。 本体の almost Tor・同種性と有限自由比較は補助であり、この項目の一様 almost 自由性・非分裂イデアル・signature の結論を代替しない。

:::

:::lemma_ "clmst_6_1_2"
*補題 6.1.2*　almost 有限生成射影加群の有限自由近似。対応表の状態：なし。

原典 PDF p.64; layout L3605。原典の「almost 有限生成射影加群の有限自由近似」に対応する定義または主張を持つ宣言を確認できない。 本体の almost Tor・同種性と有限自由比較は補助であり、この項目の一様 almost 自由性・非分裂イデアル・signature の結論を代替しない。

外の文献：GR03 Lemma 2.4.15

:::

:::definition "clmst_6_1_3" (uses := "clmst_6_1_2")
*定義 6.1.3*　almost 有限自由性と一様階数。対応表の状態：なし。

原典 PDF p.64; layout L3610。原典の「almost 有限自由性と一様階数」に対応する定義または主張を持つ宣言を確認できない。 本体の almost Tor・同種性と有限自由比較は補助であり、この項目の一様 almost 自由性・非分裂イデアル・signature の結論を代替しない。

:::

:::lemma_ "clmst_6_1_4"
*補題 6.1.4*　完全環の有限エタール開集合から一様 almost 射影性。対応表の状態：なし。

原典 PDF p.64; layout L3620。原典の「完全環の有限エタール開集合から一様 almost 射影性」に対応する定義または主張を持つ宣言を確認できない。 本体の almost Tor・同種性と有限自由比較は補助であり、この項目の一様 almost 自由性・非分裂イデアル・signature の結論を代替しない。

外の文献：Bou98 64 Chapter 5, Proposition 17、GR03 Proof of Claim 3.5.33、GR03 Proposition 4.3.27、Sch12 Proposition 5.23

:::

:::corollary "clmst_6_1_5" (uses := "clmst_6_1_4")
*系 6.1.5*　perfectoid 環の mod p の一様 almost 有限自由性。対応表の状態：なし。

原典 PDF p.65; layout L3701。原典の「perfectoid 環の mod p の一様 almost 有限自由性」に対応する定義または主張を持つ宣言を確認できない。 本体の almost Tor・同種性と有限自由比較は補助であり、この項目の一様 almost 自由性・非分裂イデアル・signature の結論を代替しない。

外の文献：Sch12 Theorem 5.25、Sch12 Theorem 7.9

:::

# §6.2 Transformation rule: the quasi-étale case

%%%
number := false
tag := "clmst-6-2"
%%%

:::lemma_ "clmst_6_2_1"
*補題 6.2.1*　mod 根イデアルでの根の lift の正規化長さ。対応表の状態：なし。

原典 PDF p.66; layout L3727。原典の「mod 根イデアルでの根の lift の正規化長さ」に対応する定義または主張を持つ宣言を確認できない。 本体の almost Tor・同種性と有限自由比較は補助であり、この項目の一様 almost 自由性・非分裂イデアル・signature の結論を代替しない。

:::

:::lemma_ "clmst_6_2_2" (uses := "clmst_2_1_1, clmst_2_1_4, clmst_2_4_9, clmst_4_0_1, clmst_4_0_7, clmst_6_0_1")
*補題 6.2.2*　Hom 生成元条件と非分裂イデアルの移送。対応表の状態：なし。

原典 PDF p.66; layout L3753。原典の「Hom 生成元条件と非分裂イデアルの移送」に対応する定義または主張を持つ宣言を確認できない。 本体の almost Tor・同種性と有限自由比較は補助であり、この項目の一様 almost 自由性・非分裂イデアル・signature の結論を代替しない。

外の文献：Kun86 Appendix F.17(a)、Stacks Tag 0BMB

:::

# §6.3 Transformation rule: a more general case

%%%
number := false
tag := "clmst-6-3"
%%%

:::proposition "clmst_6_3_1" (uses := "clmst_eq_6_0_1_1, clmst_eq_6_0_2_2, clmst_eq_6_3_1_1, clmst_2_4_3, clmst_2_4_5, clmst_4_0_1, clmst_4_0_16, clmst_6_0_1, clmst_6_1_1, clmst_6_1_4, clmst_6_2_2")
*命題 6.3.1*　一般の有限拡大に対する適合パラメータと変換則。対応表の状態：なし。

原典 PDF p.69; layout L3946。原典の「一般の有限拡大に対する適合パラメータと変換則」に対応する定義または主張を持つ宣言を確認できない。 本体の almost Tor・同種性と有限自由比較は補助であり、この項目の一様 almost 自由性・非分裂イデアル・signature の結論を代替しない。

外の文献：Sch12 Theorem 5.25

:::

:::definition "clmst_eq_6_3_1_1" (uses := "clmst_eq_6_0_1_1, clmst_6_1_1, clmst_6_1_4, clmst_6_2_2")
*式 (6.3.1.1)*　一般変換則の有限自由近似の像の被覆。対応表の状態：なし。

原典 PDF p.71; layout L4038。原典の「一般変換則の有限自由近似の像の被覆」に対応する定義または主張を持つ宣言を確認できない。 本体の almost Tor・同種性と有限自由比較は補助であり、この項目の一様 almost 自由性・非分裂イデアル・signature の結論を代替しない。

:::

:::corollary "clmst_6_3_2" (uses := "clmst_4_1_1, clmst_6_0_1, clmst_6_0_4, clmst_6_3_1")
*系 6.3.2*　二次元 Gorenstein 有理特異点の ADE 計算。対応表の状態：なし。

原典 PDF p.72; layout L4083。原典の「二次元 Gorenstein 有理特異点の ADE 計算」に対応する定義または主張を持つ宣言を確認できない。 本体の almost Tor・同種性と有限自由比較は補助であり、この項目の一様 almost 自由性・非分裂イデアル・signature の結論を代替しない。

外の文献：CRMP+21 Lemma 4.1、CRMP+21 Proposition 4.4、CRMP+21 Propositions 4.7, 4.9, 4.11、CRMP+21 Section 4

:::

