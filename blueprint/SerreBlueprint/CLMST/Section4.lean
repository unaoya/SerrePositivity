import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.CLMST.Algebra
import SerrePositivity.CLMST.AllModuleTorVanishing
import SerrePositivity.CLMST.CyclicLengthBound
import SerrePositivity.CLMST.KoszulAnnihilation
import SerrePositivity.CLMST.ParameterPowerLength
import SerrePositivity.CLMST.ParameterQuotientLength

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "§4 Perfectoid signature and perfectoid Hilbert-Kunz multiplicity" =>
%%%
number := false
tag := "clmst-4"
%%%

CLMST §4 の項目と、本体の宣言との対応。本文は対応表（`research/clmst-coverage`）の照合の理由で、原典の本文の写しではない。

:::definition "clmst_4_0_1" (lean := "SerrePositivity.CLMST.RPerfd") (uses := "clmst_2_4_2")
*記法 4.0.1*　Noether–Cohen 正規化・根の塔・R\_perfd の設定。対応表の状態：未証明の入力に依存。

*主張*　混標数 $`(0,p)` の完備ネーター局所整域 $`R` の完全剰余体を $`k` とし、$`(p,x_2,\ldots,x_d)` をパラメータ系にとる。有限な正則基底 $`A=W(k)[[x_2,\ldots,x_d]]` と根の塔の完備化 $`A_\infty` から $`R^{A_\infty}_{\mathrm{perfd}}=(R\otimes_A A_\infty)_{\mathrm{perfd}}` とおき、$`A_\infty` と絶対整閉包の $`p` 進完備化の間の環として扱う。$`A\to R` が有限エタールになる開集合を定める非零元 $`g` を選び、$`A_\infty\to(A_\infty/g)_{\mathrm{perfd}}` の核を almost の基準にする。

原典 PDF p.26; layout L1410。混標数の有限基底 A⊆R、完備根の塔、(A\_infty⊗\_A R)\_perfd の透明な別名を確認。完全剰余体・Witt 冪級数表示は使用定理の引数で保持する。標準 perfectoid 化の存在は E3 sorry 入力に依存する。テンソル積の左右の順は可換交換で対応。

外の文献：BS19 Section 10、BS19 Theorem 10.11、GR03 2.1.1

:::

:::proposition "clmst_4_0_2"
*注意 4.0.2*　R\_perfd の基底とパラメータの選択への依存。対応表の状態：なし。

原典 PDF p.27; layout L1432。原典の「R\_perfd の基底とパラメータの選択への依存」を同じ仮定・結論で述べる宣言を確認できない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

:::

:::theorem "clmst_4_0_3" (lean := "SerrePositivity.CLMST.perfectoidIdeal_allModule_tor_annihilated") (uses := "clmst_2_4_3, clmst_2_4_9, clmst_4_0_1")
*定理 4.0.3*　R\_perfd の全加群 almost 平坦性と忠実性。対応表の状態：一部（part）。

*主張*　記法 4.0.1 の下で、任意の $`A` 加群と $`R^{A_\infty}_{\mathrm{perfd}}` の正次数の Tor は $`(g)_{\mathrm{perfd}}` で消える。また非零 $`A` 加群との通常テンソルは $`(g)_{\mathrm{perfd}}` では消えない。

原典 PDF p.27; layout L1439。(a) の全 A 加群・全正次数 Tor の零化を、p 冪捩れ試験の零化 hTor と完備 almost 零加群の拡大閉性 hExt を明示的に受け取る形で確認。原典の設定だけから両入力を供給する入口でも (b) の非零加群に対する忠実性でもない。

外の文献：And18a、BS19 Proposition 10.2、Stacks Tag 091U、Stacks Tag 0ARD、Stacks Tag 0CQE

:::

:::corollary "clmst_4_0_4" (lean := "SerrePositivity.CLMST.corollary_4_0_4") (uses := "clmst_4_0_1, clmst_4_0_3")
*系 4.0.4*　局所コホモロジーと全有限段パラメータ Koszul の零化。対応表の状態：未証明の入力に依存。

*主張*　記法 4.0.1 の下で、$`R^{A_\infty}_{\mathrm{perfd}}` の極大イデアル台の局所コホモロジーは $`i<d` で $`(g)_{\mathrm{perfd}}` により消される。従って、任意の有限段 $`A_n\otimes_A R` のパラメータ系について、その環上の係数を $`R^{A_\infty}_{\mathrm{perfd}}` にした Koszul ホモロジーも正次数では同じイデアルで消される。

原典 PDF p.28; layout L1509。原典の混標数・完全剰余体・Witt 基底・非零 g の外のエタール性を保持し、i\<d の局所コホモロジーと全有限段・任意パラメータ系の正 Koszul ホモロジーの両方を零化する。hperf は別途構成できるが、RPerfd の存在は E3 sorry 入力に依存する。

外の文献：Hoc02、Shi11 Lemma 4.2

:::

:::proposition "clmst_4_0_5" (uses := "clmst_4_0_1, clmst_4_0_4")
*注意 4.0.5*　パラメータ商から最上局所コホモロジーへの almost 単射性。対応表の状態：なし。

原典 PDF p.29; layout L1546。任意パラメータの各冪商から最上局所コホモロジーへの標準写像の almost 単射性をまとめる宣言は未確認。Corollary 4.0.4 の Koszul 零化だけでは、この写像の核と直接極限での単射性の同定まで実装したことにはならない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

外の文献：BHM24 Theorem 3.4 (i)

:::

:::definition "clmst_4_0_6" (uses := "clmst_4_0_1, clmst_4_0_2")
*定義 4.0.6*　R\_perfd の非分裂イデアル I\_infty。対応表の状態：なし。

原典 PDF p.29; layout L1579。原典の「R\_perfd の非分裂イデアル I\_infty」を同じ仮定・結論で述べる宣言を確認できない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

:::

:::lemma_ "clmst_4_0_7" (uses := "clmst_2_1_1, clmst_4_0_1, clmst_4_0_5")
*補題 4.0.7*　I\_infty のイデアル性と入射包による表示。対応表の状態：なし。

原典 PDF p.29; layout L1592。原典の「I\_infty のイデアル性と入射包による表示」を同じ仮定・結論で述べる宣言を確認できない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

:::

:::definition "clmst_4_0_8" (uses := "clmst_4_0_1")
*定義 4.0.8*　perfectoid signature と perfectoid HK 重複度。対応表の状態：なし。

原典 PDF p.30; layout L1620。原典の「perfectoid signature と perfectoid HK 重複度」を同じ仮定・結論で述べる宣言を確認できない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

:::

:::proposition "clmst_4_0_9" (uses := "clmst_2_1_3")
*例 4.0.9*　非分岐正則環で不変量が 1 になる例。対応表の状態：なし。

原典 PDF p.30; layout L1630。原典の「非分岐正則環で不変量が 1 になる例」を同じ仮定・結論で述べる宣言を確認できない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

:::

:::proposition "clmst_4_0_10" (lean := "SerrePositivity.CLMST.completedLength_eq_of_perfectoid_mod_almost_iso") (uses := "clmst_eq_4_0_10_1, clmst_2_2_6, clmst_2_4_3, clmst_4_0_1")
*命題 4.0.10*　almost 同型に対する正規化長さの不変性。対応表の状態：未証明の入力に依存。

*主張*　記法 4.0.1 の $`(g)_{\mathrm{perfd}}` に関する almost 圏で二つの $`\mathfrak m_A` 冪ねじれ $`A_\infty` 加群が同型なら、それらの正規化長は等しい。

原典 PDF p.30; layout L1645。原典と同じ混標数 Witt 基底、非零 g、および両加群の一様 m 冪捩れを持つ。共通 p\^N 零化の構成は exists\_common\_completedTower\_p\_pow\_annihilates で補い、mod p\^N の局所化圏の同型から長さ一致を得る。巡回商の評価に用いる商 perfectoid 化の存在に E3 sorry 入力が残る。

外の文献：Fal02 Appendix 2、Mon83 Lemma 1.1

:::

:::definition "clmst_eq_4_0_10_1" (lean := "SerrePositivity.CLMST.exists_stage_root_mem_sup_perfectoidIdeal_of_surjective") (uses := "clmst_2_4_1")
*式 (4.0.10.1)*　mod p 冪根での g の根と perfectoid イデアル。対応表の状態：一部（part）。

*主張*　$`n>0` について $`A_\infty/(p^{1/p^n})` の $`n` 回 Frobenius で $`g\bmod p` に対応する元は、同じ商で $`(g)_{\mathrm{perfd}}` の像に属する。

原典 PDF p.31; layout L1677。原典の Frobenius 図式からの根の所属を、完備根の塔の有限段の代表元で表す。商 perfectoid 化写像の全射性を明示入力としており、原典の式単独より追加入力がある。 perfectoid 化を用いる箇所には E3 sorry 入力への依存が残る。

:::

:::definition "clmst_4_0_11"
*定義 4.0.11*　m 進付値と v almost zero の定義。対応表の状態：なし。

原典 PDF p.31; layout L1709。原典の「m 進付値と v almost zero の定義」を同じ仮定・結論で述べる宣言を確認できない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

:::

:::proposition "clmst_4_0_12"
*注意 4.0.12*　付値の完備絶対整閉包への延長。対応表の状態：なし。

原典 PDF p.32; layout L1715。原典の「付値の完備絶対整閉包への延長」を同じ仮定・結論で述べる宣言を確認できない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

外の文献：Hei22 Lemma 1.3、Hei22 Proposition 1.6

:::

:::lemma_ "clmst_4_0_13" (uses := "clmst_2_2_4")
*補題 4.0.13*　正規化長さ零なら v almost zero。対応表の状態：なし。

原典 PDF p.32; layout L1737。原典の「正規化長さ零なら v almost zero」を同じ仮定・結論で述べる宣言を確認できない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

外の文献：Shi07 Proposition 2.15

:::

:::proposition "clmst_4_0_14" (lean := "SerrePositivity.CLMST.proposition_4_0_14, SerrePositivity.CLMST.base_maximalIdeal_quotient_length_eq_rank") (uses := "clmst_eq_4_0_15_1, clmst_eq_4_0_15_2, clmst_eq_4_0_15_3, clmst_eq_4_0_15_4, clmst_eq_4_0_15_5, clmst_2_2_6, clmst_2_4_7, clmst_4_0_1, clmst_4_0_10, clmst_4_0_15, clmst_4_0_4")
*命題 4.0.14*　全有限段パラメータ商の長さ・重複度公式。対応表の状態：未証明の入力に依存。

*主張*　記法 4.0.1 の下で、有限段 $`A_n\otimes_A R` の任意のパラメータ系 $`y` による $`R^{A_\infty}_{\mathrm{perfd}}` の商の正規化長は、$`e(y,A_n\otimes_A R)/p^{nd}` である。特に $`\mathfrak m_A` による商の長さは $`e(\mathfrak m_A,R)=\operatorname{rank}_A R` である。

原典 PDF p.32; layout L1748。任意有限段 n と任意のパラメータ系 y に対して、長さ=e(y,A\_n⊗R)/p\^(nd) を保持し、基底極大イデアル商の階数公式もある。原典の混標数・完全剰余体の設定を Witt 表示などで明示化したもの。証明本文の直接 sorry はないが RPerfd の存在の E3 sorry 入力に依存する。

外の文献：BH93 Corollary 1.6.13 (a)、BH93 Theorem 4.7.6、BHM24 Theorem 3.4 (c)

:::

:::lemma_ "clmst_4_0_15" (lean := "SerrePositivity.CLMST.completedTensor_stage_parameter_last_pow_length") (uses := "clmst_2_2_6, clmst_4_0_10, clmst_4_0_4")
*主張 4.0.15*　最後のパラメータの冪と商の長さ。対応表の状態：未証明の入力に依存。

*主張*　命題 4.0.14 のパラメータ系 $`y` の最後の元を $`y_d^D`（$`D\ge1`）に替えると、そのパラメータ商の正規化長は元の商の正規化長の $`D` 倍となる。

原典 PDF p.33; layout L1772。任意有限段のパラメータ系について最後の元を D 乗すると長さが D 倍になる。原典の補助 Claim と同じ範囲であり、D を一つに固定していない。RPerfd の存在の E3 sorry 入力に依存する。

:::

:::definition "clmst_eq_4_0_15_1" (lean := "SerrePositivity.CLMST.perfectoidizationCokernel_restricted_koszul_shortExact") (uses := "clmst_2_2_6, clmst_2_4_7, clmst_4_0_10, clmst_4_0_4")
*式 (4.0.15.1)*　perfectoid 比較の余核の Koszul 長完全列。対応表の状態：一部（part）。

*主張*　$`S=R^{A_\infty}_{\mathrm{perfd}}` とし、$`A_\infty\otimes_A R\to S` の余核を $`C` とする。この短完全列に対する $`y` の Koszul ホモロジー長完全列は、各次数で基底変換環・$`S`・$`C` の順につなぎ、次数零では $`H_0(y,C)\to0` で終わる。

原典 PDF p.33; layout L1800。原典の比較余核短完全列に Koszul を適用する短完全複体列を構成。原典の表示はそれから得る長完全ホモロジー列で、表示全体を一つの宣言として同定したものではない。 perfectoid 化を用いる箇所には E3 sorry 入力への依存が残る。

:::

:::definition "clmst_eq_4_0_15_2" (lean := "SerrePositivity.CLMST.completedTensor_stage_source_homology_length") (uses := "clmst_eq_4_0_15_1, clmst_2_2_1, clmst_2_2_6, clmst_4_0_10, clmst_4_0_4")
*式 (4.0.15.2)*　余核と有限段の正 Koszul 長さの一致と有限性。対応表の状態：一部（part）。

*主張*　(4.0.15.1) の設定で、$`i\ge1` について $`H_{i+1}(y,C)` の正規化長は $`H_i(y,A_\infty\otimes_A R)` の長さに等しい。後者は有限段の $`H_i(y,A_n\otimes_A R)` を $`A_\infty` に底変換しても計算でき、その値は有限である。

原典 PDF p.33; layout L1807。有限段の源のホモロジー長さの p\^(nd) 正規化公式を確認。原典の余核 H\_(i+1) との等号および全 i≥1 の有限性の連結全体はこの宣言に含まない。 perfectoid 化を用いる箇所には E3 sorry 入力への依存が残る。

:::

:::definition "clmst_eq_4_0_15_3" (lean := "SerrePositivity.CLMST.completedTensor_stage_cokernel_negative_length_ne_top") (uses := "clmst_eq_4_0_15_1, clmst_2_2_6, clmst_4_0_10")
*式 (4.0.15.3)*　余核の H1 の長さの上界。対応表の状態：一部（part）。

*主張*　(4.0.15.1) の余核 $`C` に対し、$`\lambda_\infty H_1(y,C)\le\lambda_\infty H_0(y,A_\infty\otimes_A R)<\infty` である。

原典 PDF p.33; layout L1809。余核の負 cochain 次数の長さ有限性を、零化冪と最後のパラメータの所属を入力として得る。原典の H1 の長さが源 H0 以下という具体的不等式そのものまでは確認していない。 perfectoid 化を用いる箇所には E3 sorry 入力への依存が残る。

外の文献：BH93 Corollary 1.6.13 (a)、BHM24 Theorem 3.4 (c)

:::

:::definition "clmst_eq_4_0_15_4" (uses := "clmst_eq_4_0_15_1, clmst_2_2_6")
*式 (4.0.15.4)*　Koszul H0 と余核 H1 の長さの加法公式。対応表の状態：なし。

原典 PDF p.33; layout L1812。四つの H0/H1 の正規化長さの加法等式を直接述べる宣言は未確認。completedTensor\_stage\_euler\_comparison は全次数の Euler 集約の等式であり、この四項公式にそのまま対応づけない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

外の文献：BH93 Corollary 1.6.13 (a)、BHM24 Theorem 3.4 (c)

:::

:::definition "clmst_eq_4_0_15_5" (uses := "clmst_eq_4_0_15_2, clmst_eq_4_0_15_3")
*式 (4.0.15.5)*　最後のパラメータの乗法による Koszul 長完全列。対応表の状態：なし。

原典 PDF p.33; layout L1819。原典の「最後のパラメータの乗法による Koszul 長完全列」を同じ仮定・結論で述べる宣言を確認できない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

外の文献：BHM24 Theorem 3.4 (c)

:::

:::proposition "clmst_4_0_16" (lean := "SerrePositivity.CLMST.base_maximalIdeal_quotient_length_eq_rank") (uses := "clmst_4_0_1, clmst_4_0_10, clmst_4_0_14, clmst_4_0_3")
*命題 4.0.16*　基底の有限生成準素イデアル商の階数公式。対応表の状態：一部（special）。

*主張*　記法 4.0.1 の下で、$`\mathfrak m_A` のある冪を含む有限生成イデアル $`J\subset A_\infty` に対し、$`R^{A_\infty}_{\mathrm{perfd}}` の $`J` による商の正規化長は $`\lambda_\infty(A_\infty/J)` に $`\operatorname{rank}_A R` を掛けた値である。

原典 PDF p.34; layout L1870。J=m\_A A\_infty の商に対する長さ=rank\_A R の場合は確認。原典は m\_A の冪を含む任意の有限生成 J⊆A\_infty に対する倍率公式であり、J を基底の極大イデアルに狭めている。E3 sorry 入力への依存も残る。

:::

:::lemma_ "clmst_4_0_17"
*補題 4.0.17*　有限剰余体上でパラメータによる reduction を得る拡大。対応表の状態：なし。

原典 PDF p.35; layout L1902。原典の「有限剰余体上でパラメータによる reduction を得る拡大」を同じ仮定・結論で述べる宣言を確認できない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

外の文献：HS06 Proposition 8.2.4

:::

:::corollary "clmst_4_0_18" (lean := "SerrePositivity.CLMST.parameter_quotient_length") (uses := "clmst_4_0_1, clmst_4_0_14, clmst_4_0_17, clmst_6_0_3")
*系 4.0.18*　perfectoid HK 重複度の Hilbert–Samuel 上界とパラメータでの等号。対応表の状態：一部（special）。

*主張*　記法 4.0.1 の下で、任意の $`\mathfrak m`-準素イデアル $`I\subseteq R` の perfectoid Hilbert–Kunz 重複度は Hilbert–Samuel 重複度以下であり、パラメータ系が $`I` を生成するときは等しい。

原典 PDF p.36; layout L1941。I がパラメータで生成される場合の長さ=e(I,R) を確認。原典の任意 m 準素 I に対する上界、およびこの上界に至る有限剰余体の拡大の議論全体は未確認。E3 sorry 入力への依存も残る。

:::

:::proposition "clmst_4_0_19" (uses := "clmst_4_0_1")
*問い 4.0.19*　perfectoid HK 重複度の e(I)/d! 下界の問い。対応表の状態：なし。

原典 PDF p.36; layout L1972。原典で問われる任意 m 準素 I の下界 e(I)/d! ≤ e\_perfd(I) を予想として定義する、または証明する宣言は未確認。パラメータ生成 I の等号だけを一般の問いの解答とは数えない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

:::

:::proposition "clmst_4_0_20" (uses := "clmst_eq_4_0_20_2, clmst_4_0_1, clmst_4_0_14, clmst_4_0_3")
*命題 4.0.20*　perfectoid HK 重複度の下界 1 と等号の必要条件。対応表の状態：なし。

原典 PDF p.37; layout L1981。原典の「perfectoid HK 重複度の下界 1 と等号の必要条件」を同じ仮定・結論で述べる宣言を確認できない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

外の文献：BH93 Corollary 4.7.9、MQS20 Definition 8、MQS20 Theorem 9

:::

:::definition "clmst_eq_4_0_20_1"
*式 (4.0.20.1)*　limit closure からの組成列。対応表の状態：なし。

原典 PDF p.37; layout L1994。原典の「limit closure からの組成列」を同じ仮定・結論で述べる宣言を確認できない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

外の文献：BH93 Corollary 4.7.9、MQS20 Definition 8、MQS20 Theorem 9

:::

:::definition "clmst_eq_4_0_20_2" (uses := "clmst_4_0_4")
*式 (4.0.20.2)*　limit closure の R\_perfd 上での colon 包含。対応表の状態：なし。

原典 PDF p.37; layout L2009。原典の「limit closure の R\_perfd 上での colon 包含」を同じ仮定・結論で述べる宣言を確認できない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

:::

:::lemma_ "clmst_4_0_21" (uses := "clmst_4_0_1")
*補題 4.0.21*　イデアル商の長さ差と生成元数による評価。対応表の状態：なし。

原典 PDF p.37; layout L2034。原典の「イデアル商の長さ差と生成元数による評価」を同じ仮定・結論で述べる宣言を確認できない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

:::

:::proposition "clmst_4_0_22" (uses := "clmst_4_0_1, clmst_4_0_14, clmst_4_0_21")
*命題 4.0.22*　perfectoid signature と HK 重複度の基本不等式。対応表の状態：なし。

原典 PDF p.38; layout L2070。原典の「perfectoid signature と HK 重複度の基本不等式」を同じ仮定・結論で述べる宣言を確認できない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

:::

:::proposition "clmst_4_0_23" (uses := "clmst_2_1_2, clmst_2_2_6, clmst_4_0_1, clmst_4_0_21, clmst_4_0_7")
*命題 4.0.23*　近似 Gorenstein 系による signature の上限表示。対応表の状態：なし。

原典 PDF p.38; layout L2083。原典の「近似 Gorenstein 系による signature の上限表示」を同じ仮定・結論で述べる宣言を確認できない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

:::

# §4.1 Characterization of regular local rings

%%%
number := false
tag := "clmst-4-1"
%%%

:::theorem "clmst_4_1_1" (uses := "clmst_4_0_1, clmst_4_0_3, clmst_4_1_3, clmst_4_1_4, clmst_4_1_5")
*定理 4.1.1*　almost 平坦性・二不変量による正則性の特徴づけ。対応表の状態：なし。

原典 PDF p.39; layout L2150。原典の「almost 平坦性・二不変量による正則性の特徴づけ」を同じ仮定・結論で述べる宣言を確認できない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

外の文献：BIM19 Theorem 5.2

:::

:::lemma_ "clmst_4_1_2" (uses := "clmst_eq_4_1_2_1, clmst_4_0_14")
*補題 4.1.2*　R\_perfd と剰余体の全高次 Tor の長さ零から正則性。対応表の状態：なし。

原典 PDF p.39; layout L2163。原典の「R\_perfd と剰余体の全高次 Tor の長さ零から正則性」を同じ仮定・結論で述べる宣言を確認できない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

外の文献：BIM19 Theorem 5.2、BIM19 Theorem 5.2 Claim 5

:::

:::definition "clmst_eq_4_1_2_1"
*式 (4.1.2.1)*　Tor の長さと自由分解の長さの比較。対応表の状態：なし。

原典 PDF p.40; layout L2169。原典の「Tor の長さと自由分解の長さの比較」を同じ仮定・結論で述べる宣言を確認できない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

外の文献：BIM19 Theorem 5.2

:::

:::proposition "clmst_4_1_3" (uses := "clmst_4_0_1, clmst_4_0_10, clmst_4_0_20, clmst_4_0_3, clmst_4_1_2")
*命題 4.1.3*　R\_perfd の almost 平坦性・忠実性による正則性。対応表の状態：なし。

原典 PDF p.40; layout L2197。原典の「R\_perfd の almost 平坦性・忠実性による正則性」を同じ仮定・結論で述べる宣言を確認できない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

外の文献：BIM19 Theorem 5.2

:::

:::proposition "clmst_4_1_4" (uses := "clmst_eq_4_0_20_1, clmst_eq_4_0_20_2, clmst_4_0_1, clmst_4_0_10, clmst_4_0_14, clmst_4_0_20, clmst_4_0_4, clmst_4_1_2, clmst_4_1_3")
*命題 4.1.4*　perfectoid HK 重複度 1 による正則性。対応表の状態：なし。

原典 PDF p.41; layout L2240。原典の「perfectoid HK 重複度 1 による正則性」を同じ仮定・結論で述べる宣言を確認できない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

外の文献：CN03 Theorem 3.1、MQS20 Theorem 9

:::

:::corollary "clmst_4_1_5" (uses := "clmst_2_1_3, clmst_4_0_1, clmst_4_0_14, clmst_4_0_20, clmst_4_0_21, clmst_4_0_7, clmst_4_1_3, clmst_4_1_4")
*系 4.1.5*　perfectoid signature 1 による正則性。対応表の状態：なし。

原典 PDF p.42; layout L2335。原典の「perfectoid signature 1 による正則性」を同じ仮定・結論で述べる宣言を確認できない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

:::

:::proposition "clmst_4_1_6" (uses := "clmst_4_0_1, clmst_4_0_14, clmst_4_0_8")
*注意 4.1.6*　R\_perfd を絶対整閉包内の像で置き換えることへの反例。対応表の状態：なし。

原典 PDF p.43; layout L2358。原典の Z\_p→Z\_p\[p\^(1/p)\] の例で、R\_perfd の絶対整閉包内の像を使うと長さが 1/p、正しい R\_perfd では 1 となる反例を実現する宣言は未確認。RPerfd の別名や一般の根の塔だけではこの例の二つの値を計算したことにならない。 RPerfd やパラメータ商の長さ公式だけでは、該当する不変量・付値・純性を含む項目全体を得ない。

外の文献：Hei22

:::

