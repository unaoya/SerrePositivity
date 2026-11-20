-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.Inputs.Descent
import SerrePositivity.LengthAlgebra.Flat
import SerrePositivity.Paper.Section3.LengthComputation
import SerrePositivity.Paper.Section3.NormComparison

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "§3 Rational descent with closed supports" =>
%%%
number := false
tag := "paper-3"
%%%

本論文 §3 の項目と、本体の宣言との対応。各項目の頭は対応表（`research/paper-coverage`）の照合の理由、その下は解説から移した本文（あるものだけ）。

*解説 §5 perfect 複体での評価*

この節では、§3 の一般論の第一の実現として、評価元を perfect 複体の三角圏、評価先を §4 の商にとる。扱うのは任意の可換環上の perfect 複体と、Koszul 有限な長さ付き代数についての一般論である。論文に固有の対象（有限拡大 $`T` のランク、Galois 群、降下の引用）は使わない。それらを入れて論文の Lemma 3.5 を導くのは §7 である。

- §3 の結論　／　この実現で確かめる入力　／　場所　／　得られる結論
- Euler 評価（命題 3.4）　／　台と Koszul 有限性から Euler 有限性（定義 3.3）。シフト・長完全列・有界性　／　§5.1　／　Euler 有限性は命題 5.3、5.6。$`K_0` 上の準同型は系 5.4、5.7
- 共役和の比較（命題 3.6）　／　(a) 係数変更との両立（命題 5.5）、$`K(z)` が剰余体の分解であることと $`e_\lambda(z;C)` の値。(b) 降下は仮定として受け取る　／　§5.2　／　命題 5.8、定理 5.9
- 反復錐による消滅（補題 3.11）　／　台の条件（定義 3.8）：零ホモトピー。Koszul 振幅の条件（定義 3.9）：自由振幅と正次数の Koszul 長さ零　／　§5.3　／　補題 5.10
- 第零次の下界（補題 3.12）　／　極小性による全射　／　§5.3　／　補題 5.11

§5.4 では $`\lambda`-平坦な代数でこれらの入力がそろうことを、§5.5 では消滅の適用としてパラメータ商（Lemma 5.3）を述べる。

:::theorem "paper_3_1" (lean := "SerrePositivity.theorem_3_1_K0") (uses := "paper_eq_3_1, paper_eq_3_2, paper_eq_3_5, paper_eq_3_6, paper_eq_3_7, paper_eq_3_8, paper_3_3, ext_BGT_8_1, ext_BGT_8_7, ext_BGT_9_3, ext_BGT_9_8, ext_Goodwillie_Main_Theorem, ext_LT_3_10, ext_LT_3_12, ext_LT_3_9, ext_LT_A_2, ext_LT_Appendix_B, ext_LT_B_2, ext_LT_B_3, ext_TT_5_2_2, ext_TT_5_2_3, ext_TT_5_2_4, ext_TT_7_4")
**定理 3.1**　任意の連結結合係数を持つ台つき有理降下。対応表の状態：未証明の入力に依存。

*主張*　$`A` を有限 Krull 次元の可換ネーター $`\mathbf Z_{(p)}` 代数、$`J\supseteq(p)` をイデアル、$`H` を中心的 $`A` 作用をもつ連結結合 $`A` 代数とする。有限可換 $`A` 代数 $`T` が $`A` 上の有限群 $`G` 作用をもち、$`\operatorname{Spec}T\to\operatorname{Spec}A` が全射で各幾何ファイバー上の作用が推移的なら、引き戻しは台 $`V(J)` つき有理 K 理論 $`K^J(H)_{\mathbf Q}\simeq(K^J(H\otimes_A^{\mathbf L}T)_{\mathbf Q})^{hG}` を与える。従って有理 $`K_0^J` から上の $`G` 不変部分への写像は全射となる。

原典 PDF p.10 / layout L502。本体の入力は離散H=A、局所基底とパラメータ台についてのK0の正整数倍持ち上げで、直接sorryを持つ。原典の任意の連結結合Hと有理Kスペクトルの同値は未構成なので、入力界面としてのみ対応する。

*解説 §7.1 Lemma 3.5*

*定理 7.3（Theorem 3.1、引用）*

$`A` を有限次元ネーター $`\mathbb{Z}_{(p)}` 代数、$`J\ni p`、$`H` を連結な dg $`A` 代数とする。$`T` が $`A` 上有限で $`\operatorname{Spec} T\to\operatorname{Spec} A` が全射、有限群 $`G` が幾何ファイバーに推移的に作用するなら、

$$`K^J(H)_\mathbb{Q} \simeq \bigl(K^J(H\otimes^L_A T)_\mathbb{Q}\bigr)^{hG}.`

特に $`K_0^J(H)_\mathbb{Q} \to (K_0^J(H\otimes^L_A T)_\mathbb{Q})^G` は全射。

§5 では $`H = A` として使う（$`\mathcal{K}_A = \operatorname{Perf}^J(A)`）。§6 では補題 7.7 の $`H` を使う。正則局所環で剰余標数が $`p` なら「有限次元ネーター $`\mathbb{Z}_{(p)}` 代数」は自動的に満たされる。

証明の流れ（形式化は未）：$`J` で台をつけた有理 K 理論は truncating になり（Goodwillie）、係数つきで cdh 降下をもつ（Land–Tamme）。有限忠実平坦被覆では転送で降下し、爆発による平坦化で一般の有限全射に延ばし、切断の $`G` 移動で不変部分を同定する。$`\operatorname{Spec} T\to\operatorname{Spec} A` は一般に cdh 被覆ではなく、この定理は cdh 降下と有限平坦降下から組み立てた h 型の降下である。構造の詳しい整理は付録 E にある。

*Lean:* \`theorem\_3\_1\_K0\`（$`H = A` の場合のみ、引用）。

外の文献：BGT 8.1、BGT 8.7、BGT 9.3、BGT 9.8、Goodwillie Main Theorem、LT 3.10、LT 3.12、LT 3.9、LT A.2、LT Appendix B、LT B.2、LT B.3、TT 5.2.2、TT 5.2.3、TT 5.2.4、TT 7.4

:::

:::definition "paper_eq_3_1" (uses := "paper_eq_3_2, paper_eq_3_6, paper_eq_3_7, paper_eq_3_8, paper_3_3")
**式 (3.1)**　台つき有理KスペクトルのGalois降下。対応表の状態：なし。

原典 PDF p.10 / layout L509。連結非可換係数H、support、rationalizationとhomotopy fixed pointsのスペクトル同値の宣言はない。離散K0入力で代用しない。

:::

:::definition "paper_eq_3_2" (lean := "SerrePositivity.theorem_3_1_K0") (uses := "paper_eq_3_1, paper_eq_3_6")
**式 (3.2)**　台つき有理K0のG不変部分への全射。対応表の状態：未証明の入力に依存。

*主張*　定理 3.1 の有限全射と幾何ファイバー上の推移的な有限群作用の下で、引き戻しは $`K_0^J(H)\otimes\mathbf Q\longrightarrow(K_0^J(H\otimes_A^{\mathbf L}T)\otimes\mathbf Q)^G` を全射にする。

原典 PDF p.10 / layout L514。離散・局所・パラメータ台の場合の正整数倍の持ち上げを直接sorryで置く。原典の任意Hに対する全射全体にはまだ達しない。

*解説 §3.2 共役和の比較*

*補題 3.5（共役和の形式的補題）*

有理化した $`f` が $`G` 不変部分へ全射であれば、分母と捩れを払うことでこの整数倍の条件が得られる。

*解説 §7.1 Lemma 3.5*

*系 7.4（降下の $`K_0` での形）*

定理 7.3 の仮定のもとで、$`G` 不変な $`y\in K_0^J(H\otimes^L_AT)` には、正の整数 $`n` と $`x\in K_0^J(H)` があって $`ny` は $`x` の像に等しい。これは命題 3.6 の (b) である。

*証明*

有理化した写像が不変部分へ全射なので、$`y\otimes1` の原像 $`x'\otimes(1/m)` をとる。$`my-f(x')` は有理化すると零なので捩れであり、その位数を掛けて分母と捩れを払う。

*Lean:* $`H=A` の場合は \`theorem\_3\_1\_K0\`、§6 の $`H`（補題 7.7）の場合は \`Section4.supportedRankK0\_descent\`。いずれもこの整数倍の形で引用している。

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

:::definition "paper_eq_3_6" (uses := "paper_eq_3_5, ext_BGT_8_1, ext_BGT_8_7, ext_BGT_9_3, ext_BGT_9_8, ext_LT_3_12, ext_LT_B_2, ext_TT_5_2_2, ext_TT_5_2_3, ext_TT_5_2_4, ext_TT_7_4")
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

:::lemma_ "paper_3_3" (uses := "paper_3_2, ext_Stacks_0815")
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

*主張*　完備正則局所基底 $`A` の正則パラメータ $`z` と、同じ剰余体をもつ有限局所整域拡大 $`T` に対する長さ代数 $`C` に課す条件は、各 $`v\ge1` について $`\lambda H_i(z^v;C)=0`（$`i>0`）および $`\lambda(C/(z^v)C)=v^e\operatorname{rank}_A T` である。

原典 PDF p.14 / layout L725。ここは独立の存在定理ではなくSection3.4の長さ仮定。lemma\_3\_4のhzero・hquotに同じ全冪の仮定が現れる。Theorem2.5からの供給は別項目で扱う。

*解説 §4.3 Koszul 有限性と $`\lambda`-平坦性*

*定義 4.8（Koszul 有限性）*

長さ付き $`A` 代数 $`(C,\lambda)` が $`z` に関して Koszul 有限であるとは、全ての $`v\ge1` と $`0\le j\le e` について $`\lambda H_j(z^v;C)<\infty` となることをいう。このとき

$$`e_\lambda(z;C)=\sum_{j=0}^e(-1)^j\lambda H_j(z;C)\in\mathbb{R}`

を Koszul Euler 特性、または $`\lambda`-重複度と呼ぶ。この一般性では、その正値性は仮定しない。

以下この小節の残りでは、$`A` を正則局所環、$`z` をその正則パラメータ系とする。

*系 4.11*

$`z_1,\dots,z_e` を $`A` の正則パラメータ系とする。$`(C,\lambda)` が $`\lambda`-平坦でランク $`r` なら、全ての $`v\ge 1` で

$$`\lambda H_i(z_1^v,\dots,z_e^v; C) = 0 \quad (i>0), \qquad \lambda\bigl(C/(z^v)C\bigr) = v^e\cdot r.`

逆に $`v=1` でこれが成り立てば $`(C,\lambda)` は $`\lambda`-平坦でランク $`r` である。特に定義 4.9 の条件は元論文の (3.9) と同値。

*証明*

$`z` は正則列なので $`z^v` も正則列で、Koszul 複体 $`K(z^v)` は $`A/(z^v)` の自由分解である。よって $`H_i(z^v;C) = \operatorname{Tor}_i^A(A/(z^v),C)` で、$`\operatorname{length}_A A/(z^v) = v^e`。定義を $`V = A/(z^v)` に適用する。逆は $`K(z)` が $`k` の分解であることと補題 4.10 から。

*Lean:* \`LengthAlgebra.Flat\` で証明済み。\`flat\_rank\_iff\_koszul\` が一乗での同値を、\`quotient\_length\_powers\_of\_flat\` が全ての正の冪の値を与える。列の冪の正則性と商の長さ $`v^e` は \`RegularSequencePowers\`・\`RegularSequenceLength\` で証明し、重複度の未証明公式は使わない。正則列であることを明示的な入力とする。

*注意 4.12（仮定の形と形式化の境界）*

共通理論では、全ての正の冪についての Koszul 有限性、正次数の Koszul ホモロジーの長さ零、$`v=1` での Koszul Euler 特性の値を別々に指定する。有限性だけで Euler 評価を構成し、消滅と値の計算はそれぞれ必要な定理にだけ加えるためである。

定義 4.9 の $`\lambda`-平坦性と有限ランクからこれらの入力を供給する接続も形式化した。\`LengthAlgebra.Flat\` が \`KoszulFinite\`、高次の長さ零、Koszul Euler 特性 $`e_\lambda=r` をそれぞれ導く。\`LengthAlgebra.CohenMacaulay\` は任意のパラメータ系についての $`\lambda`-CM 条件から同じ入力を供給する。一般の共通定理ではこれらを独立に受け取り、平坦性をもたない通常の長さによる Euler 評価も引き続き扱う。

*$`\lambda`-平坦性の意味*

$`\lambda`-平坦性は、有限長 $`A` 加群について $`q\operatorname{Tor}_i^A(V,C)=0`（$`i>0`）と同値であり、$`V\mapsto q(V\otimes_A C)` を完全関手にする。$`C` 自体は冪ねじれとは限らないので、商圏の中の対象 $`qC` の平坦性とは述べない。$`\lambda`-平坦性だけでは $`\lambda(C/zC)` の有限性は出ず、有限ランクの条件と合わせて初めて、系 4.11 から上の表の三つの条件がそろう。$`\lambda`-CM 性を正則部分環 $`A\subseteq D` 上で使うには、$`D` が $`A` 上有限で、そのパラメータ系が $`D` のパラメータ系にもなる条件を使う（命題 4.15）。

*例 4.13*

普通の評価は $`(T,\operatorname{length}_T)`、正規化側は $`(C,\lambda)` という二つの例である。$`T` がネーターで $`T/(z)T` が有限長なら、$`H_j(z^v;T)` は有限生成で $`(z^v)` により消されるので、$`(T,\operatorname{length}_T)` は Koszul 有限である。この有限性には CM 性を使わない。例えば本文の有限局所代数 $`T` が CM でなければ、普通の長さで測る高次の Koszul ホモロジーが残り、$`\lambda`-平坦性は満たさない。したがって普通の側にも Euler 評価はあるが、消滅まで結論することはできない。

*解説 §5.2 この実現での比較定理*

*命題 5.8（基底から来る類での評価）*

$`z'` が $`A` の別のパラメータ系、またはその各元の正の冪からなる列であれば、$`K(z')` は $`A/(z')` の分解である。上の公式を $`Q=K(z')` に使うと

$$`e_\lambda(z';C)=\operatorname{length}_A(A/(z'))\,e_\lambda(z;C)`

も得られる。左辺の各長さの有限性は命題 5.3 により確かめられる。

:::

:::lemma_ "paper_3_4" (lean := "SerrePositivity.lemma_3_4, SerrePositivity.normalizedLength_tor_of_isWeaklyRegular") (uses := "paper_eq_3_9")
**補題 3.4**　有限長加群の通常長と正規化Tor長。対応表の状態：本体にある。

*主張*　§3.4 の有限局所拡大・長さの設定と式 (3.9) の下で、任意の有限長 $`A` 加群 $`V` の $`C` との正次数 Tor の長さは零、テンソル積の長さは $`\operatorname{rank}_A T` と $`\operatorname{length}_A V` の積であり、すべて有限である。

原典 PDF p.14 / layout L730。(3.9)のKoszul長条件から、任意有限長Vの高次Tor長零とdegree0のr倍公式、有限性を導く。弱正則列による一般のTor長計算へ帰着しており、降下入力は使わない。

*解説 §4.3 Koszul 有限性と $`\lambda`-平坦性*

*補題 4.10（判定法）（Lemma 3.4）*

$`(C,\lambda)` を長さ付き $`A` 代数とする。

- (a) $`(C,\lambda)` が $`\lambda`-平坦であることと、全ての $`i>0` で $`\lambda\operatorname{Tor}_i^A(k,C) = 0` であることは同値。

- (b) $`(C,\lambda)` が $`\lambda`-平坦のとき、ランク $`r` であることと $`\lambda(k\otimes_A C) = r` は同値。

*証明*

どちらも $`V = k` の場合が必要条件。逆は組成列の長さの帰納法で、$`0\to V'\to V\to V''\to 0` の Tor の長完全列から、$`i>0` では $`\lambda\operatorname{Tor}_i(V)\le\lambda\operatorname{Tor}_i(V')+\lambda\operatorname{Tor}_i(V'')=0`、$`i=0` では $`\lambda\operatorname{Tor}_1(V'')=0` より $`\lambda(V\otimes C)=\lambda(V'\otimes C)+\lambda(V''\otimes C)`。

この証明は $`\lambda` の加法性と非負性しか使わない。$`A` の完備性も、次節の $`T` の性質も使わない。

*Lean:* \`IntersectionMultiplicity.NormalizedTor\` の剰余体判定と有限長加群の公式は、任意の局所環上で証明済み。ランクは任意の有限な非負実数でよい。零次 Tor と通常のテンソル積の対応も確認した。既存の \`lemma\_3\_4\` は証明済みの正則パラメータを通してこの一般論に接続する。

:::

:::definition "paper_eq_3_10" (lean := "SerrePositivity.lemma_3_4") (uses := "paper_eq_3_9")
**式 (3.10)**　有限長加群に対するTor長のr倍公式。対応表の状態：本体にある。

*主張*　式 (3.9) の仮定の下で有限長 $`A` 加群 $`V` に対して、$`\lambda\operatorname{Tor}_i^A(V,C)=0`（$`i>0`）かつ $`\lambda(V\otimes_A C)=r\operatorname{length}_A V` となる。ここで $`r=\operatorname{rank}_A T` である。

原典 PDF p.14 / layout L733。Lemma3.4と同じ二つの結論。

*解説 §4.3 Koszul 有限性と $`\lambda`-平坦性*

*定義 4.9（$`\lambda`-平坦性とランク）*

$`(A,\mathfrak{m}_A,k)` を正則局所環、$`z` をその正則パラメータ系とし、$`(C,\lambda)` を長さ付き $`A` 代数とする（$`\sqrt{(z)}=\mathfrak{m}_A` なので、定義域は $`\mathfrak{m}_A C`-冪ねじれ加群である）。

$`V` を有限長 $`A` 加群（普通の長さで $`\operatorname{length}_A V<\infty`）とすると、$`\mathfrak{m}_A^N V = 0`（$`N = \operatorname{length}_A V`）なので、$`\operatorname{Tor}_i^A(V,C)` は $`\mathfrak{m}_A^N` で、したがって $`(\mathfrak{m}_A C)^N` で消され、$`\lambda` の定義域に入る。特に $`V = k` のとき $`\mathfrak{m}_A` で消される。そこで

- 全ての有限長 $`A` 加群 $`V` と $`i>0` で $`\lambda\operatorname{Tor}_i^A(V,C) = 0` のとき、$`(C,\lambda)` は \*\*$`\lambda`-平坦\*\*であるという。

- 実数 $`r\ge 0` について、全ての有限長 $`A` 加群 $`V` で $`\lambda(V\otimes_A C) = r\cdot\operatorname{length}_A V` のとき、$`(C,\lambda)` は\*\*ランク $`r`\*\* であるという。

正則局所環上の有限生成加群 $`M` が「$`\operatorname{Tor}_i(k,M) = 0`（$`i>0`）なら自由」となることの $`\lambda` 版で、$`C` は「$`\lambda` の目で Cohen–Macaulay」である（正則局所環上では巨大 CM 代数は平坦）。次の補題により $`V = k` で判定でき、元論文の条件 (3.9) とも同値になる（系 4.11）。形式化ではこの条件を構造体に束ねず、各定理の仮定として直接書く。具体例の構成は §8 で行う。

:::

:::lemma_ "paper_3_5" (lean := "SerrePositivity.lemma_3_5a, SerrePositivity.lemma_3_5b, SerrePositivity.lemma_3_5c, SerrePositivity.theorem_3_1_K0") (uses := "paper_eq_3_11, paper_eq_3_12, paper_eq_3_13, paper_eq_3_14, paper_eq_3_9, paper_3_1, paper_3_4")
**補題 3.5**　通常のEuler評価とnorm和の比較。対応表の状態：未証明の入力に依存。

*主張*　§3.4 の基底と長さの条件の下で、$`T` に作用する有限群 $`G` が $`\operatorname{Spec}T\to\operatorname{Spec}A` の各幾何ファイバーで推移的とする。閉点に台をもつ完全 $`T` 複体の通常および長さ $`\lambda` による Euler 評価は有限で、$`K_0` 上の準同型を与え、各 $`G` 共役和で一致する。さらに基底からの像と任意の $`G` 不変有理類でも一致する。

原典 PDF p.15 / layout L748。有限性・加法性および基底からの引戻しでの比較は別々に証明されている。一般の不変K0類・norm和へ広げるlemma\_3\_5cはtheorem\_3\_1\_K0のsorryに依存する。原典の二つの評価を個々の共役について等しいとはしていない。

*解説 §3.1 長さ付きアーベル圏と Euler 評価*

*定義 3.1（長さ付きアーベル圏）*

アーベル圏 $`\mathcal{A}` と、同型不変な関数 $`\ell\colon\mathrm{Ob}\,\mathcal{A}\to[0,\infty]` で、$`\ell(0)=0`、短完全列で加法的、$`\ell(X)=0\Rightarrow X\cong0` となるものの組を長さ付きアーベル圏という。$`\ell` は組成列の長さである必要はない。

*定義 3.2（ホモロジー的関手）*

$`\mathcal{K}` を三角圏、$`\mathcal{A}` をアーベル圏とする。加法的関手の族 $`H_i\colon\mathcal{K}\to\mathcal{A}`（$`i\in\mathbb{Z}`）がシフトの同型 $`H_i(X[j])\cong H_{i-j}(X)` を備え、完全三角 $`X\to Y\to Z\to X[1]` から長完全列

$$`\cdots\to H_i(X)\to H_i(Y)\to H_i(Z)\to H_{i-1}(X)\to\cdots`

を与えるとき、$`H_*` を*ホモロジー的関手*と呼ぶ。

*定義 3.3（Euler 有限）*

$`(\mathcal{A},\ell)` を長さ付きアーベル圏とする。ホモロジー的関手 $`H_*\colon\mathcal{K}\to\mathcal{A}` が *Euler 有限*であるとは、$`\mathcal{K}` の各対象 $`X` について次の二つが成り立つことをいう。

- (i) *有界性*：有限個の $`i` を除いて $`H_i(X)=0`。

- (ii) *長さの有限性*：全ての $`i` で $`\ell(H_iX)<\infty`。

このとき交代和 $`\chi(X)=\sum_i(-1)^i\ell(H_iX)` は実数として定まる。

*命題 3.4（Euler 評価）*

$`H_*\colon\mathcal{K}\to\mathcal{A}` を Euler 有限なホモロジー的関手とする。このとき

$$`\chi(X)=\sum_i(-1)^i\ell(H_iX)`

は完全三角で加法的で、準同型 $`K_0(\mathcal{K})\to\mathbb{R}` を定める。

*証明*

長完全列を各射の像による短完全列に分ける。像の長さも有限であり、非零項は有限個なので、交代和をとると像の長さが相殺して $`\chi(Y)=\chi(X)+\chi(Z)` を得る。同型不変性と合わせて $`K_0` に降りる。この証明では長さの忠実性は使わない。

*Lean:* \`CategoryTheory.ExactSequenceEuler\`、\`HomologicalEuler\`、\`TriangulatedK0\`（証明済み）。

実装の長完全列の定理はさらに一般的で、零対象で零となる同型不変・短完全列に加法的な実数値評価だけを使う。対象ごとの有界性があれば、非負性も忠実性も不要である。拡大実数値の $`\lambda` からこの定理へ移る際には、先に有限長さの部分圏へ制限する。

*解説 §3.2 共役和の比較*

*命題 3.6（Euler 評価の共役和比較）*

二つの実現では、(a) をどちらも「基底から来る類での評価は、基底上の共通の評価の定数倍」という形で確かめる。その形で述べ直しておく。

*系 3.7（基底公式つきの共役和比較）*

命題 3.6 の設定で、準同型 $`\chi_A\colon K\to\mathbb{R}` と実数 $`e_1,e_2` があって

$$`\chi_1\circ f=e_1\,\chi_A,\qquad \chi_2\circ f=e_2\,\chi_A`

とする（*基底公式*）。$`e_1=e_2` で、(b) の降下が成り立てば、全ての $`x\in K_0(\mathcal{K})` について

$$`\sum_{g\in G}\chi_1(g\cdot x)=\sum_{g\in G}\chi_2(g\cdot x).`

*証明*

基底公式と $`e_1=e_2` から (a) が従う。

二つの実現では、$`\chi_A` を基底 $`A` 上の普通の Euler 評価、$`e_i` を Koszul Euler 特性 $`e_{\lambda_i}(z;C_i)` にとり、基底公式を命題 5.8、6.7 で示す。

*Lean:* \`GroupTheory.ConjugateSum\` の \`conjSum\_eq\_of\_base\_formula\`（群論の形）と、\`CategoryTheory.EulerComparison\` の \`homologicalEulerK0\_pullback\_conjSum\_eq\_of\_base\_formula\`（二つの Euler 評価を準同型 $`u_1`、$`u_2` で引き戻した形。二つの実現では $`u_i` は係数変更が誘導する $`K_0` の写像）。二つの実現の比較定理（\`perfectEuler\_conjSum\_eq\`、\`symmetricPaperEuler\_conjSum\_eq\`）はこの定理の適用である（いずれも証明済み）。

*解説 §5.1 設定と評価関手*

*設定*

$`A` を可換環、$`z` をその元の有限列、$`T` を可換 $`A` 代数、$`C` を $`T` 代数とし、$`(C,\lambda)` を $`z` に関して Koszul 有限な長さ付き $`A` 代数とする（定義 4.3、4.8）。§5.2 の基底公式では、さらに $`A` が正則局所環で $`z` が正則パラメータ系であることを仮定する。$`S\in\{A,T\}` に対し

$$`\mathcal{K}_S = \operatorname{Perf}_{(z)}(S)`

とおく。ホモロジーの台が $`V((z)S)` に入る perfect $`S` 複体の三角圏で、$`S` が局所で $`\sqrt{(z)S}` が極大イデアルなら、閉点に台をもつ perfect 複体の三角圏である。perfect 複体は有限射影項の有界複体で計算する。
係数拡大 $`-\otimes_A T\colon\mathcal{K}_A\to\mathcal{K}_T` がある。$`P\in\mathcal{K}_T` に対して

$$`\chi_{\mathrm{ord}}(P) = \sum_i (-1)^i \operatorname{length}_T H_i(P),\qquad \chi_C(P) = \sum_i (-1)^i \lambda\, H_i(P\otimes_T C)`

とおく（$`S = A`、$`C = A`、$`\lambda = \operatorname{length}` のときの $`\chi_{\mathrm{ord}}` を $`\chi_A` と書く）。
普通の長さの評価 $`\chi_{\mathrm{ord}}` には、$`T` がネーターで $`T/(z)T` が有限長であることを仮定する（例 4.13）。$`\lambda`-平坦性、ランク、$`T` の有限性や局所性はこの節の一般論では使わない。

*評価先*

普通の側の評価先は有限長 $`T` 加群の圏である。正規化側は、有限な $`\lambda`-長さをもつ冪ねじれ $`C` 加群を、長さ零の加群で割った Serre 商 $`\mathcal A_\lambda^{\mathrm{fin}}` とし、$`H_i^C(P)=q_{\mathrm{fin}}H_i(P\otimes_T C)` とする。商の長さは忠実で、元の $`\lambda` と一致する（§4.2）。

*命題 5.3（有限性とホモロジー的関手）*

$`(C,\lambda)` を Koszul 有限とし、$`S\to C` を $`A` 代数の準同型とする。このとき

$$`H_i^C(P)=q_{\mathrm{fin}}H_i(P\otimes_S^LC) \quad(P\in\operatorname{Perf}_{(z)}(S))`

は長さ付きアーベル圏 $`\mathcal{A}_\lambda^{\mathrm{fin}}` に値をとる Euler 有限なホモロジー的関手である。

*証明*

補題 5.1 により全ての $`z_j^v` が $`P` 上で零ホモトピックとなる共通の $`v\ge1` を選べる。係数拡大後の $`P\otimes_S C` でも同じ作用が零なので、ホモロジーは $`(z)C`-冪ねじれである。$`P` の各項は有限射影なので有限自由加群の直和因子であり、補題 5.2 と Koszul 有限性から $`\lambda H_i(P\otimes_S C)<\infty` を得る（長さの有限性）。

係数拡大は導来圏で完全三角を保ち、ホモロジーの長完全列は全て有限な冪ねじれ加群に入るので、完全な $`q_{\mathrm{fin}}` を適用できる。これによりホモロジー的関手を得る。perfect 複体は有界なので、非零の次数は有限個であり（有界性）、上の評価とあわせて Euler 有限性を得る。

この命題では $`S` の局所性、ネーター性、$`A` 上の有限性や平坦性を使わない。

*系 5.4（Euler 評価）*

命題 5.3 の設定で、

$$`\chi_C(P)=\sum_i(-1)^i\lambda H_i(P\otimes_S^LC)`

は準同型 $`K_0(\operatorname{Perf}_{(z)}(S))\to\mathbb{R}` を定める。

*証明*

命題 5.3 により命題 3.4 の仮定がそろう。

大きな商の有限部分を評価先にした場合も、命題 4.7 の同値により同じ Euler 評価となる。

*Lean:* \`LengthAlgebra.PerfectHomology\`、\`PerfectBaseChange\`、\`PerfectHomologyComparison\`。実装は、より一般の有限生成イデアル $`J` と $`J\subseteq\sqrt{(z)C}` を入力にとる。本文の $`J=(z)C` ではこの条件は自動的に満たされる。

*命題 5.5（係数変更との両立）*

$`S\to S'\to C` を $`A` 代数の準同型とし、$`(C,\lambda)` を Koszul 有限とする。$`P\in\operatorname{Perf}_{(z)}(S)` について $`P\otimes_S^LS'\in\operatorname{Perf}_{(z)}(S')` で、

$$`\chi_C(P\otimes_S^LS')=\chi_C(P).`

つまり、係数拡大 $`K_0(\operatorname{Perf}_{(z)}(S))\to K_0(\operatorname{Perf}_{(z)}(S'))` と系 5.4 の二つの Euler 評価は可換である。

*証明*

係数拡大した複体でも $`z_j^v` の作用は零ホモトピックなので、補題 5.1 により台は $`V((z)S')` に入る。導来テンソルの結合律 $`(P\otimes_S^LS')\otimes_{S'}^LC\cong P\otimes_S^LC` から、各ホモロジーの長さが一致する。

*Lean:* \`LengthAlgebra.PerfectBaseChange\`。\`perfectBaseChangeEulerK0\` は評価をこの係数拡大と合成して定義し、\`perfectBaseChangeEulerK0\_comp\` が両立を与える（証明済み）。

*命題 5.6（Lemma 3.5a の前半）*

$`T` がネーターで $`T/(z)T` が有限長とする。$`P\in\mathcal{K}_T` について、有限長 $`T` 加群の圏に値をとる $`H_i(P)` と、$`\mathcal{A}_\lambda^{\mathrm{fin}}` に値をとる $`H_i^C(P)` は、ともに Euler 有限なホモロジー的関手である。

*証明*

正規化側は命題 5.3（$`S=T`）である。普通の側では、台から共通の $`v` を選んで全ての $`z_j^v` の零ホモトピーを得て、補題 5.2 を $`S=C=T`、$`\lambda=\operatorname{length}_T` で使う（$`M_v<\infty` は例 4.13）。複体は有界で、ホモロジーの長完全列とシフト同型はそのまま有限長加群の圏に入る。

*系 5.7（Lemma 3.5a）*

$`\chi_{\mathrm{ord}}`、$`\chi_C` は準同型

$$`\chi_{\mathrm{ord}},\ \chi_C\colon K_0(\mathcal{K}_T)\to\mathbb{R}`

を定める。

*証明*

命題 5.6 により、命題 3.4 を二つの評価に適用できる。

*Lean:* \`lemma\_3\_5a\`、\`lemma\_3\_5a\_lam\_finite\`（証明済み）。

*解説 §7 論文の状況での命題*

- $`A` は正則局所環、$`z` はその正則パラメータ系。

- $`T` は $`A` 上有限な局所整域で剰余体が $`A` と同じもの、$`r=\operatorname{rank}_A T`。

- $`(C,\lambda)` は $`\lambda`-平坦でランク $`r` の長さ付き $`A` 代数で、$`C` は $`T` 代数、$`A\to T\to C` は可換（§4.3）。

- 共役和については、$`A` の剰余標数が $`p>0`、有限群 $`G` が $`T` に $`A` 上で作用して幾何ファイバーに推移的、$`\operatorname{Spec} T\to\operatorname{Spec} A` は全射。

比較定理の入力のうち、(a) は二つの Koszul Euler 特性がともに $`r` であることから、(b) は有理 K 理論の降下（定理 7.3、引用）から得る。正規化側の $`e_\lambda(z;C)=r` は系 4.11 で、普通の側は次の補題である。

*補題 7.1（Koszul Euler 特性の階数公式）*

$`A` を次元 $`e` の正則局所環、$`z` を正則パラメータ系、$`T` を $`A` 上有限な局所代数で剰余体が $`A` と同じものとする。このとき

$$`e_{\operatorname{length}_T}(z;T)=\sum_j(-1)^j\operatorname{length}_T H_j(z;T)=\operatorname{rank}_A T.`

*証明*

$`K(z)` は $`k` の自由分解なので $`H_j(z;T)=\operatorname{Tor}_j^A(k,T)` である。$`T` の $`A` 上の有限自由分解をとり、$`k` とテンソルして Euler 特性を二通りに数えると、交代階数 $`\operatorname{rank}_AT` になる。剰余体が同じなので $`T` 上と $`A` 上の長さは一致する。

*Lean:* \`koszulEulerChar\_eq\_finrank\`。一般の Euler–Poincaré 公式から導出され、正則パラメータが正則列であることの引用に依存する。

*解説 §7.1 Lemma 3.5*

以下の命題 7.2、7.5 は、$`(C_1,\lambda_1)=(T,\operatorname{length}_T)` と $`(C_2,\lambda_2)=(C,\lambda)` をとった場合である。$`T` の局所性と剰余体の一致は、普通の側の $`e_{\operatorname{length}_T}(z;T)=r` の計算で使い、比較定理そのものには使わない。

*命題 7.2（Lemma 3.5b、命題 5.8 の系）*

$`Q\in\mathcal{K}_A` について

$$`\chi_{\mathrm{ord}}(Q\otimes_A T) \;=\; r\cdot\chi_A(Q) \;=\; \chi_C(Q\otimes_A T).`

*証明*

正規化側は系 5.12 (a) である。普通の側は、命題 5.8 を $`(T,\operatorname{length}_T)` に適用し、補題 7.1 の $`e_{\operatorname{length}_T}(z;T)=r` を入れる。

*Lean:* \`lemma\_3\_5b\`、生成は \`K0.exists\_eq\_zsmul\_koszul\`、\`K0.hom\_ext\_koszul\`（証明済み。\`lemma\_3\_5b\_ord\_of\_koszul\`、\`lemma\_3\_5b\_lam\_of\_koszul\` は一般の基底公式の適用）。

:::

:::definition "paper_eq_3_11" (lean := "SerrePositivity.lemma_3_5c") (uses := "paper_eq_3_13, paper_eq_3_14, paper_3_1")
**式 (3.11)**　共役Euler評価のnorm和の一致。対応表の状態：未証明の入力に依存。

*主張*　補題 3.5 の仮定の下で、閉点に台をもつ完全 $`T` 複体 $`P` について、$`\sum_{g\in G}\chi_T(g^*P)=\sum_{g\in G}\chi_C(g^*P)` が成り立つ。

原典 PDF p.15 / layout L761。有理不変類の持ち上げを通常K0降下入力に依存して証明する。

*解説 §3.2 共役和の比較*

*補題 3.5（共役和の形式的補題）*

$`f\colon K\to K'` をアーベル群の準同型、有限群 $`G` が $`K'` に群自己同型として作用しているとし、$`\varphi,\psi\colon K'\to\mathbb{R}` を準同型とする。$`\varphi\circ f = \psi\circ f` とし、全ての $`G` 不変な $`y\in K'` について、ある正の整数 $`n` と $`a\in K` で $`ny=f(a)` となるとする。このとき、全ての $`x\in K'` について

$$`\sum_{g\in G}\varphi(g\cdot x) \;=\; \sum_{g\in G}\psi(g\cdot x).`

*証明*

$`\sum_g g\cdot x` は $`G` 不変なので、ある正の整数 $`m` で $`m\sum_g g\cdot x` は $`f` の像に入る。そこで $`\varphi` と $`\psi` は一致するので、$`m` で割ればよい。

*Lean:* \`GroupTheory.ConjugateSum\` の \`conjSum\_eq\`（証明済み）。

この補題を命題 3.4 の二つの Euler 評価に適用したものが、二つの実現で使う比較定理である。

*命題 3.6（Euler 評価の共役和比較）*

$`\mathcal{K}` を三角圏とし、$`H^{(1)}_*`、$`H^{(2)}_*` をそれぞれ長さ付きアーベル圏 $`(\mathcal{A}_1,\ell_1)`、$`(\mathcal{A}_2,\ell_2)` に値をとる Euler 有限なホモロジー的関手、$`\chi_1,\chi_2\colon K_0(\mathcal{K})\to\mathbb{R}` を命題 3.4 の Euler 評価とする。アーベル群 $`K` からの準同型 $`f\colon K\to K_0(\mathcal{K})` と、有限群 $`G` の $`K_0(\mathcal{K})` への作用が次をみたすとする。

- (a) *基底から来る類での一致*：$`\chi_1\circ f=\chi_2\circ f`。

- (b) *不変類の降下*：全ての $`G` 不変な $`y\in K_0(\mathcal{K})` について、ある正の整数 $`n` と $`a\in K` で $`ny=f(a)`。

このとき全ての $`x\in K_0(\mathcal{K})` について

$$`\sum_{g\in G}\chi_1(g\cdot x)=\sum_{g\in G}\chi_2(g\cdot x).`

*証明*

補題 3.5 を $`\varphi=\chi_1`、$`\psi=\chi_2` に適用する。

*解説 §5.2 この実現での比較定理*

*定理 5.9（二つの長さ付き代数のノルム比較）*

$`A` を正則局所環、$`z` を正則パラメータ系、$`T` を可換 $`A` 代数とする。有限群 $`G` が $`K_0(\operatorname{Perf}_{(z)}(T))` に群自己同型として作用し、その不変類の正の整数倍が係数拡大

$$`f\colon K_0(\operatorname{Perf}_{\mathfrak{m}}(A))\longrightarrow K_0(\operatorname{Perf}_{(z)}(T))`

の像に入るとする。$`T` 代数 $`C_1,C_2` とそれぞれの長さ関数 $`\lambda_1,\lambda_2` が Koszul 有限で、

$$`e_{\lambda_1}(z;C_1)=e_{\lambda_2}(z;C_2)`

なら、任意の $`y\in K_0(\operatorname{Perf}_{(z)}(T))` について

$$`\sum_{g\in G}\chi_{C_1}(g\cdot y)=\sum_{g\in G}\chi_{C_2}(g\cdot y).`

*証明*

系 5.4 により、二つの評価は $`K_0` 上の Euler 評価である。命題 5.5 と命題 5.8 により、$`\chi_{C_i}\circ f=e_{\lambda_i}(z;C_i)\,\chi_A` である（基底公式）。系 3.7 を適用する。

*Lean:* \`LengthAlgebra.Comparison\` の \`perfectEuler\_conjSum\_eq\`（Koszul 分解と整数倍の降下を明示的に受け取り、証明済み）。証明は系 3.7 の \`homologicalEulerK0\_pullback\_conjSum\_eq\_of\_base\_formula\` に、係数変更の合成 \`perfectBaseChangeEulerK0\_comp\` と基底公式 \`perfectBaseChangeEulerK0\_eq\_koszulEuler\_mul\` を渡すだけである。

$`T` 上の群作用が $`A` を固定すれば、ひねり $`P\mapsto P^g` がこの $`K_0` 作用を与える。有限射影版での作用、係数変更との両立、有限自由モデルとの同変な比較は \`PerfectComplex.K0Functoriality\` で構成されている。局所環 $`T` では旧モデルの降下入力も移せる。

幾何的な適用では、剰余標数 $`p>0`、$`T` の有限性、幾何ファイバーへの推移的作用と $`\operatorname{Spec} T\to\operatorname{Spec} A` の全射性から、定理 7.3 の引用で降下を供給する。これは上の条件付き比較とは別の段階である。

*解説 §5.4 $`\lambda`-平坦な代数での適用*

*系 5.12（$`\lambda`-平坦な代数での比較・消滅・下界）*

- (b) *比較*：Koszul 有限なもう一つの長さ付き代数 $`(C',\lambda')` で $`e_{\lambda'}(z;C')=r` なら、定理 5.9 の降下のもとで共役和が一致する。

*解説 §7.1 Lemma 3.5*

*命題 7.5（Lemma 3.5c）*

さらに $`A` の剰余標数が $`p`、有限群 $`G` が $`T` に $`A` 上で作用して幾何ファイバーに推移的、$`\operatorname{Spec} T\to\operatorname{Spec} A` が全射とする。$`P\in\mathcal{K}_T` と、$`g` でひねった $`P^g = P\otimes_{T,g} T` について

$$`\sum_{g\in G} \chi_{\mathrm{ord}}(P^g) \;=\; \sum_{g\in G} \chi_C(P^g).`

*証明*

系 5.12 (b) を $`(C',\lambda')=(T,\operatorname{length}_T)` に適用する。$`e_{\operatorname{length}_T}(z;T)=r` は補題 7.1 による。$`G` の $`K_0(\mathcal{K}_T)` への作用はひねり $`P\mapsto P^g` による。降下（命題 3.6 の (b)）は、剰余標数 $`p`、推移性、全射性のもとで系 7.4（$`H=A`）による。

*Lean:* \`lemma\_3\_5c\`（引用を除いて証明済み）。証明はこの形である：定理 5.9（\`perfectEuler\_conjSum\_eq\`）を係数環 $`A\to T`、$`T\to T`（通常の長さ）、$`T\to C`（$`\lambda`）に適用する。二つの Koszul Euler 特性が $`\operatorname{rank}_AT` で一致すること（補題 7.1、\`koszulEulerChar\_eq\_finrank\`）と、旧来の有限自由モデル（\`K0Supported\`）で述べられた降下の引用 \`theorem\_3\_1\_K0\` を有限射影 $`K_0` へ移したもの（\`perfectK0\_descent\_of\_free\`）を渡し、結論を \`freeToPerfectK0\` で旧モデルの値 \`chiOrd\`、\`chiLam\` に戻す。

:::

:::definition "paper_eq_3_12" (uses := "paper_eq_3_9")
**式 (3.12)**　零ホモトピーのKoszul cone分裂。対応表の状態：なし。

原典 PDF p.15 / layout L777。有限Koszulテンソルのshiftと二項係数への分裂は周辺のKoszul計算で用いられるが、任意の支持perfect T複体Pと任意Cについてこの表示の同型を一つの対応宣言として未同定。

*解説 §3.3 スカラーの反復錐*

*前提*

この小節では次を仮定する。

- $`A` は可換環、$`z=(z_1,\dots,z_e)` はその元の有限列で、$`z^v=(z_1^v,\dots,z_e^v)` と書く。$`e=\dim A` や $`A` の正則性は要らない。

- $`\mathcal{K}` は $`A` 線形な三角圏で、シフトも $`A` 線形である。したがって $`a\in A` と対象 $`X` についてスカラー倍 $`a\operatorname{id}_X` が定まり、その錐がとれる。

- $`H_*\colon\mathcal{K}\to\mathcal{A}` はホモロジー的関手（定義 3.2）である。補題 3.10、3.11 は長さを使わず、補題 3.12 だけが長さ $`\ell` を使う。

$`v\ge1` に対し $`z_j^v` のスカラー作用の錐を順にとった対象を $`K_v\otimes X` と書く。抽象三角圏でこの記法は反復錐を表し、テンソル積の存在を仮定しない。

*定義 3.8（$`z` に台をもつ）*

対象 $`X` が\*\*指数 $`v` で $`z` に台をもつ\*\*とは、全ての $`j` で $`z_j^v\operatorname{id}_X=0` となることをいう。ある $`v\ge1` でそうなるとき、単に \*\*$`z` に台をもつ\*\*という。

ここで零なのは三角圏の射としての作用で、ホモロジー上の零作用より強い。perfect 複体では、この条件はホモロジーの幾何学的な台が $`V((z))` に入ることと同値になる（補題 5.1）。

*定義 3.9（Koszul 振幅）*

$`m\ge0` とする。対象 $`X` の\*\*指数 $`v` の Koszul 振幅が $`[0,m]` に入る\*\*とは、$`n\notin[0,m]` で $`H_n(K_v\otimes X)=0` となることをいう。

*使う場所*

補題 3.11、3.12 は、比較（命題 7.5、定理 7.9）には使わない。§5.3 と §6.4 で、perfect 複体と列の圏について台の条件（定義 3.8）、Koszul 振幅の条件（定義 3.9）と第零次の全射を確かめて適用する。その結果を §5.5 の次数の上界と、§9 の正値性（補題 9.6）で使う。

*補題 3.10（零作用と分裂）*

$`X` が指数 $`v` で $`z` に台をもつなら

$$`K_v\otimes X\cong\bigoplus_{j=0}^eX[j]^{\oplus\binom ej},\qquad H_n(K_v\otimes X)\cong\bigoplus_{j=0}^eH_{n-j}(X)^{\oplus\binom ej}. \tag{3.1}`

*証明*

零射 $`Y\to Y` の錐は $`Y\oplus Y[1]` と同型である。残りのスカラーもその直和成分上で零なので、シフトの線形性を使って繰り返す。二項係数で成分をまとめ、$`H_*` の加法性を使う。

ここで零なのは三角圏の射としての作用である。ホモロジー上の零作用だけではこの分裂は得られない。

*Lean:* \`CategoryTheory.IteratedCone\` の \`iteratedZeroCone\_iso\` は二項直和の反復として分裂を構成する。実装ではこの再帰表示を使い、二項係数の長さ公式、以下の消滅、第零次同型と下界を証明している。式 （3.1） はその数学的な表示である。

*解説 §5.1 設定と評価関手*

*補題 5.1（幾何学的な台とスカラーの零作用）*

任意の可換環 $`S` 上の有界有限射影複体 $`P` について、次は同値である。

- (i) 全ての $`H_i(P)` の台が $`V((z)S)` に入る。

- (ii) ある $`v\ge1` で全ての $`z_j^v` の作用が $`P` 上で零ホモトピックである。

これらは全ホモロジーが共通の $`(z)S` の冪で消されることとも同値である。$`S` のネーター性やホモロジーの有限生成性は不要である。

*証明*

(ii) なら $`z_j^v` が全ホモロジーを消す。有限列なので $`(z)S` の十分大きな冪も全ホモロジーを消し、(i) を得る。

逆に一つのスカラー $`x=z_j` を固定し、cochain 次数の上から順に恒等射の成分を消す。より上の成分を消した鎖写像の次の成分はサイクルへ写る。そのホモロジーへの像は有限生成な項からの像なので有限生成であり、台が $`V(x)` に入ることから $`x` のある冪で消える。項の射影性により境界への持ち上げを選べるので、その冪を掛けた鎖写像の成分をホモトピーで一段消せる。有界性により有限回で零射となる。有限個の $`j` について指数をそろえれば (ii) を得る。ホモロジー全体が有限生成だとは使っていない。

*Lean:* \`HomologicalAlgebra.SupportNullHomotopy\`、\`PerfectComplex.Support\`、\`HomotopyCategory\`（任意の可換環上で証明済み）。

*補題 5.2（Koszul 上界）*

$`S` を可換 $`A` 代数、$`C` を $`S` 代数とする。$`P` を有限射影項の有界な $`S` 複体とし、各項 $`P_k` が $`S^{r_k}` の直和因子であるとする。ある $`v` で全ての $`z_j^v` が $`P` 上ホモトピー的に $`0` なら、

$$`M_v = \sum_j \lambda H_j(z^v; C)`

とおいて、全ての $`i` で

$$`\lambda H_i(P\otimes_S C) \;\le\; \Bigl(\sum_k r_k\Bigr)\cdot M_v.`

$`C = S`、$`\lambda = \operatorname{length}_S` としても成り立つ。

*証明*

零ホモトピーにより、$`P\otimes_S C` は $`K(z^v)\otimes P\otimes_S C` の直和因子になる。後者を $`P` の項による愚直なフィルトレーションで分解すると、各段は $`K(z^v;C)\otimes_S P_k` のシフトである。$`P_k` は $`S^{r_k}` の直和因子なので、そのホモロジーは $`K(z^v;C)^{\oplus r_k}` のホモロジーの直和因子で、長さは $`r_k M_v` 以下である。長完全列と $`\lambda` の劣加法性から上界が出る。

Koszul 有限性から $`M_v<\infty` である（$`\lambda`-平坦でランク $`r` なら、系 4.11 より $`M_v = v^e r`）。普通の長さの側でも、$`T` はネーターで $`H_j(z^v;T)` は $`(z^v)` で消される有限生成加群なので $`M_v<\infty`。この補題は §6 で列に一様に適用する。

*Lean:* \`PerfectComplex.KoszulLengthBounds\` の \`lambdaHomology\_koszulComplexOn\_le\_sum\_of\_retracts\`（直和因子版の上界）と \`lambdaHomology\_le\_of\_retract\`。有限射影項の有限性への適用は \`PerfectComplex.ProjectiveBounds\` の \`lambdaHomology\_supported\_projective\_ne\_top\`（証明済み）。

:::

:::definition "paper_eq_3_13" (lean := "SerrePositivity.lemma_3_5b_lam") (uses := "paper_3_4")
**式 (3.13)**　基底から来る正規化Euler評価。対応表の状態：本体にある。

*主張*　補題 3.5 の設定で、閉点に台をもつ完全 $`A` 複体 $`Q` を $`T` へ導来底変換すると、長さ $`\lambda` による評価は $`\chi_C(Q\otimes_A^{\mathbf L}T)=r\sum_j(-1)^j\operatorname{length}_A H_j(Q)` である。

原典 PDF p.15 / layout L793。C評価の値をrankA(T)×普通の基底Euler値として返す。

*解説 §5.2 この実現での比較定理*

*命題 5.8（基底から来る類での評価）*

$`A` を正則局所環、$`z` を正則パラメータ系とし、$`(C,\lambda)` を Koszul 有限とする。$`Q\in\operatorname{Perf}_{\mathfrak{m}}(A)` について

$$`\chi_C(Q)=e_\lambda(z;C)\,\chi_A(Q).`

ここで $`\chi_C(Q)` は $`Q\otimes_A^LC` のホモロジーによる評価である。

*証明*

正則局所環上では各有限長加群が perfect である。切り詰めの三角とホモロジーの組成列を用いると

$$`[Q]=\sum_i(-1)^i\operatorname{length}_A H_i(Q)\,[k]=\chi_A(Q)[k].`

$`K(z)` は $`k` の自由分解だから $`[k]=[K(z)]`、$`\chi_A(K(z))=1` である。両辺の評価は準同型で、$`K(z)` 上の左辺は $`e_\lambda(z;C)` なので結論する。Lean では有限自由モデルの Koszul 生成定理を、局所環上の $`K_0` 比較同型を通して有限射影モデルへ移す。

*Lean:* \`LengthAlgebra.KoszulFormula\`。一般の基底公式は \`IsKoszulResolution z\` を明示的に受け取り、保留した降下を呼ばず、正則パラメータの一般定理もこの条件付き証明には不要。

*解説 §5.4 $`\lambda`-平坦な代数での適用*

*系 5.12（$`\lambda`-平坦な代数での比較・消滅・下界）*

$`A` を正則局所環、$`z` をその正則パラメータ系、$`T` を可換 $`A` 代数、$`(C,\lambda)` を $`\lambda`-平坦でランク $`r` の長さ付き $`A` 代数で $`C` が $`T` 代数のものとする。

- (a) *基底公式*：$`Q\in\operatorname{Perf}_{\mathfrak{m}}(A)` について $`\chi_C(Q\otimes_AT)=r\cdot\chi_A(Q)`。

:::

:::definition "paper_eq_3_14" (lean := "SerrePositivity.lemma_3_5b_ord") (uses := "paper_eq_3_13")
**式 (3.14)**　基底から来る通常Euler評価。対応表の状態：本体にある。

*主張*　同じ $`Q` の $`T` への導来底変換の通常 Euler 評価は、$`\chi_T(Q\otimes_A^{\mathbf L}T)=r\sum_j(-1)^j\operatorname{length}_A H_j(Q)` である。

原典 PDF p.15 / layout L810。普通T評価について同じrank倍公式を与える。

:::

:::proposition "paper_3_6" (lean := "SerrePositivity.lemma_3_5c")
**注意 3.6**　長さのG不変性を要求しないという注意。対応表の状態：一部。

*主張*　ノルム比較は長さ $`\lambda` の $`G` 不変性を仮定しない。保証される等式は共役類の和に対するものであり、各共役の評価は個別に一致するとは限らない。

原典 PDF p.16 / layout L823。定理の型はlambdaのG不変性を仮定せずnorm和だけを比較する。この注意の論理的内容は読み取れるが、個々の評価が不変でない具体例や独立の否定命題は宣言していない。比較自体は入力依存。

*解説 §3.2 共役和の比較*

*命題 3.6（Euler 評価の共役和比較）*

二つの評価先を同じ圏に同定する必要はなく、$`H^{(i)}_*` の $`G` 同変性や長さの $`G` 不変性も要らない。群作用は評価元の $`K_0` に置けばよい。二つの実現では、(a) を基底の Koszul 分解から（命題 5.8）、(b) を有理 K 理論の降下から（定理 7.3）供給する。

*Lean:* \`CategoryTheory.EulerComparison\` の \`homologicalEulerK0\_conjSum\_eq\`（証明済み）。

*解説 §5.2 この実現での比較定理*

*定理 5.9（二つの長さ付き代数のノルム比較）*

二つの評価先 $`\mathcal{A}_{\lambda_1}^{\mathrm{fin}}` と $`\mathcal{A}_{\lambda_2}^{\mathrm{fin}}` を同じ圏に同定する必要はない。共通なのは評価元の $`K_0` と、最終的な実数値の Euler 評価である。$`T` が局所でない場合、$`\operatorname{Perf}_{(z)}(T)` の台は閉ファイバー $`V(\mathfrak{m}_AT)` であり、一つの閉点に限らない。

*解説 §7.1 Lemma 3.5*

仮定の使われ方を補足する。元論文は $`A` を完備としているが、完備性はどこでも使わない（完備性が効くのは §9 で正規化基底をとる段階である）。$`A` の剰余標数 $`p` と $`G` の作用・推移性は降下（定理 7.3）にだけ要る。$`T` が整域であることは $`r` の定義と $`\operatorname{Spec} T\to\operatorname{Spec} A` の全射性に、剰余体の一致は普通の側の長さの比較（補題 7.1）にだけ使う。$`\lambda` については加法性と非負性、および Koszul 条件（有限性は全ての $`v`、値は $`v=1`）だけを使う。また結論は共役の和についての等式であり、個々の $`P` について $`\chi_{\mathrm{ord}}(P)=\chi_C(P)` を主張しない（元論文 Remark 3.6）。このため $`D` 側と $`E` 側の長さ付き代数を独立に選べ、$`\lambda` の $`G` 不変性も要らない。

:::

