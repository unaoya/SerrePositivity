import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.Asymptotic.Completed
import SerrePositivity.Asymptotic.RankQuotient
import SerrePositivity.Paper.Section3.LengthComputation
import SerrePositivity.Paper.Section4.LengthHypotheses
import SerrePositivity.Paper.Section4.RankQuotient

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§4 Supported asymptotic complexes" =>
%%%
number := false
tag := "paper-4"
%%%

本論文 §4 の項目と、本体の宣言との対応。各項目の頭は対応表（`research/paper-coverage`）の照合の理由、その下は解説から移した本文（あるものだけ）。

*解説 §6 ランク無視の圏での評価*

この節では、§3 の一般論の第二の実現として、評価元をランク無視の圏 $`P_S^J`、評価先を加群列の Serre 商にとる。§5 と同じく一般論であり、論文の Theorem 4.7 は §7 で導く。この実現で新たに必要なのは、支持つき局所化、冪等完備化へのホモロジー関手の延長、一様代表による計算である。

- §3 の結論　／　この実現で確かめる入力（§5 との違い）　／　場所　／　得られる結論
- Euler 評価（命題 3.4）　／　共通の台の指数と長さ $`O(s_n)`。局所化と直和因子への延長　／　§6.2　／　Euler 有限性は命題 6.4。$`K_0` 上の準同型は系 6.5
- 共役和の比較（命題 3.6）　／　(a) 係数変更との両立（命題 6.6）と、全対象の一様代表で各段の基底公式を極限へ移すこと。(b) 降下は仮定として受け取る　／　§6.3　／　命題 6.7、定理 6.9
- 反復錐による消滅（補題 3.11）　／　商での零作用と、Koszul を掛けた列の振幅　／　§6.4　／　補題 6.11
- 第零次の下界（補題 3.12）　／　全射の列と正規化極限　／　§6.4　／　補題 6.12

§6.5 では、有限近似列（定義 4.18）からランク無視の圏の対象を作る。§6.6 は $`\lambda`-平坦な代数での適用である。

設定は §5 と同じとする。原論文の適用では $`A` の優秀性も仮定するが、以下の構成自体は優秀性も完備性も使わない。

*解説 §6.1 圏*

*定義 6.1（ランク無視の圏）*

正の整数の列 $`s_n` と非単項超フィルター $`\mathcal{U}` を固定する。$`S = A, T` について

- $`D_S`：ランク $`O(s_n)` の自由 $`S` 加群の列からなる、共通の有界な次数範囲の複体の列のホモトピー圏

- $`N_S`：ランク $`o(s_n)` の列が生成する thick 部分圏

- $`P_S = (D_S/N_S)^\natural`：Verdier 商の冪等完備化

- $`P_S^J`：ある $`v` で全ての $`z_j^v` が恒等射を消す対象（商をとった後で消えればよい）

:::definition "paper_eq_4_1" (lean := "SerrePositivity.Section4.koszulFinite_of_lengthAlgebra_values, SerrePositivity.Section4.quotient_length_of_lengthAlgebra_values") (uses := "paper_2_5")
**式 (4.1)**　漸近比較で仮定する長さ公式。対応表の状態：本体にある。

原典 PDF p.16 / layout L844。Section4の仮定の表現とそこから使う有限性・商長を形式化する。長さ代数の存在自体の証明と混同しない。

:::

# §4.1 The rank quotient and its support condition

%%%
number := false
tag := "paper-4-1"
%%%

:::proposition "paper_4_1"
**注意 4.1**　生のホモロジー長がランク商へ降りない反例。対応表の状態：なし。

原典 PDF p.17 / layout L877。DVRのT/(z\^n)のrank-one分解列で、rank-smallなのに生の正規化H0長が1となる反例を一括で述べる宣言を確認できない。一般のrank-small商の定義だけではこの反例に対応しない。

*解説 §6.1 圏*

*注意 6.2（Remark 4.1）*

生のホモロジーの長さは商と両立しない。DVR 上で $`s_n = n` とし、$`T/(z^n)` のランク 1 の分解の列をとると、これは $`N_T` に入る（$`P_T` で $`0`）が、$`H_0` の長さの $`s_n` に対する比は $`1`。一様に台をもたないことが原因で、Koszul とテンソルした後の長さは $`0` になる（$`v` を固定すると $`H_i(z^v;T/(z^n))` の長さは $`v` 以下で $`n` によらず有界）。問題が起きるのは、商をとる前に一様に台をもたない対象だけである。一様に台をもつ列では、分裂 $`K_v\otimes F\simeq\bigoplus_jF[j]^{\binom ej}` により生のホモロジーが Koszul とテンソルしたホモロジーの直和成分になるので、生の長さも商と両立する。そこで長さは一様に台をもつ持ち上げの上で先に定義し、商と冪等完備化に延ばす（命題 6.3、§6.2）。§9 で使う切り詰めた分解の列は、切り詰めの誤差のために商をとった後で初めて台をもつので、まさにこの状況が起こりうる対象である。

:::

# §4.2 The supported subquotient

%%%
number := false
tag := "paper-4-2"
%%%

:::lemma_ "paper_4_2" (lean := "SerrePositivity.Asymptotic.supportedRankQuotientInclusion, SerrePositivity.Asymptotic.paperSupportedRankEquivalence")
**補題 4.2**　台つき部分商の充満忠実性と冪等完備化。対応表の状態：本体にある。

原典 PDF p.17 / layout L889。台つき部分商からランク商への標準関手のFull・Faithful・三角性のinstanceと、支持つきKaroubi包の同値を確認した。有限ランク誤差の商の後に現れる支持と、lift上の一様支持を区別する。

*解説 §6.1 圏*

*定義 6.1（ランク無視の圏）*

$`D_S` の対象 $`F = (F_n)` が*一様に台をもつ*とは、$`n` によらない $`v` があって、全ての $`z_j^v` が全ての $`F_n` 上でホモトピー的に $`0` になること。ホモトピー自体は段ごとに選んでよく、その係数の有界性は要らない。

$`P\in\operatorname{Perf}_{\mathfrak{m}}(S)` に $`(P^{\oplus s_n})_n` を対応させる関手 $`\iota\colon\operatorname{Perf}_{\mathfrak{m}}(S)\to P_S^J` がある。

*Lean:* \`Asymptotic.FreeSequence\`、\`RankQuotient\`、\`SupportedKaroubi\`、\`PaperRankQuotient\`、\`SequenceSupport\`（圏の構成と比較同値は証明済み）。本文は計算モデルの記法で書いた。原論文の完備化と商の順序の圏との線形三角同値も構成されている。$`\iota` の記法による有限版の埋め込みと (c) の式は、ここでは数学的な説明として述べる。

*命題 6.3（Lemma 4.2）*

$`P_S^J` の対象は全て、一様に台をもつ $`D_S` の対象の像の直和因子である。ただし射影子は商をとる前の鎖写像に持ち上がるとは限らない。

*証明*

商の対象で零作用するスカラーの Koszul 複体を掛けると、その対象は反復錐の直和因子になる。Koszul を掛けた列は一様に台をもつ。冪等完備化の対象も、もとの商の対象の直和因子であることを合わせる。

*Lean:* \`Asymptotic.SupportedKaroubi\`、\`PaperRankQuotient\`（支持つきの比較同値と直和因子による表示を構成済み）。

:::

# §4.3 Nonnegative homology lengths

%%%
number := false
tag := "paper-4-3"
%%%

:::proposition "paper_4_3" (lean := "SerrePositivity.Asymptotic.paperRankHomology, SerrePositivity.Asymptotic.completedRankHomology_isHomological, SerrePositivity.Asymptotic.paperRankBetti_nonneg, SerrePositivity.Asymptotic.paperRankBetti_hasFiniteSupport, SerrePositivity.Asymptotic.paperRankEulerK0, SerrePositivity.Asymptotic.paperBaseChangeHomology, SerrePositivity.Asymptotic.paperBaseChangeHomology_isHomological, SerrePositivity.Asymptotic.paperBaseChangeBetti_nonneg, SerrePositivity.Asymptotic.paperBaseChangeBetti_hasFiniteSupport, SerrePositivity.Asymptotic.paperBaseChangeEulerK0") (uses := "paper_eq_4_1, paper_eq_4_2, paper_eq_4_3, paper_4_1, paper_4_2, ext_BalmerSchlichting_1_10, ext_BalmerSchlichting_1_12")
**命題 4.3**　長さのSerre商へのホモロジー関手とEuler評価。対応表の状態：本体にある。

原典 PDF p.18 / layout L937。現在はLengthSerreQuotientへの各次数の関手とIsHomological、非負・有限supportのBetti長、K0のEuler準同型がある。ordinary長とbase-change長に適用し、Karoubi包の全支持対象を扱う。旧表の数値部分のみというpartial判定は維持しない。添字はcochainのq=-iへ読み替える。

*解説 §4.2 評価先：長さ付きアーベル圏の構成*

$`(C,\lambda)` を長さ付き $`A` 代数とし、$`J=(z)C` とする。

*補題 4.4*

$`J`-冪ねじれ $`C` 加群の圏 $`\mathcal{T}_J(C)` はアーベル圏である。その中の

$$`\mathcal{N}_\lambda=\{M\mid\lambda(M)=0\},\qquad \mathcal{T}_J^{\mathrm{fin}}(C)=\{M\mid\lambda(M)<\infty\}`

は Serre 部分圏である。$`\mathrm{fin}` は $`\lambda` の有限性で、有限生成性や通常の有限長性を意味しない。

*証明*

冪ねじれ加群は部分加群・商で閉じ、$`J^aM'=0`、$`J^bM''=0` ならその拡大 $`M` は $`J^{a+b}` で消される。したがって加群の圏の Serre 部分圏をなし、包含は完全である。短完全列で $`\lambda(M)=\lambda(M')+\lambda(M'')` なので、非負性から長さ $`0` と有限性のそれぞれについて Serre 条件が従う。

*定義 4.5*

Serre 商と完全な商関手を

$$`\mathcal{A}_\lambda=\mathcal{T}_J(C)/\mathcal{N}_\lambda,\qquad q\colon\mathcal{T}_J(C)\to\mathcal{A}_\lambda`

と書く。有限な長さの部分だけの商を $`\mathcal{A}_\lambda^{\mathrm{fin}}=\mathcal{T}_J^{\mathrm{fin}}(C)/\mathcal{N}_\lambda`、その商関手を $`q_{\mathrm{fin}}` と書く。圏の構成には宇宙を固定し、必要に応じてより大きい宇宙を使う。

*命題 4.6*

$`\lambda` は商上の同型不変・短完全列に加法的な長さ $`\ell_\lambda` に降り、

$$`\ell_\lambda(qM)=\lambda(M),\qquad \ell_\lambda(X)=0\iff X\cong0`

となる。有限な商では長さは $`[0,\infty)` 値である。

*証明*

核と余核が長さ $`0` の射 $`f\colon M\to N` は、像を介する短完全列により $`\lambda(M)=\lambda(\operatorname{im}f)=\lambda(N)` を満たす。無限値の引き算は使わない。Serre 商の分数表示と、商で可逆となる射の核・余核の判定から、商で同型な対象の長さは等しい。商の短完全列は代表元を取り替えて元の圏の短完全列の像として表せるので、加法性も降りる。最後に $`qM\cong0\iff M\in\mathcal{N}_\lambda` より忠実性が従う。有限な商でも同じ議論を使う。

*命題 4.7（有限な商と大きな商の有限部分）*

包含から誘導される関手は、長さを保つ完全な同値

$$`\mathcal A_\lambda^{\mathrm{fin}}\simeq \{X\in\mathcal A_\lambda\mid\ell_\lambda(X)<\infty\}`

を与える。この同値は元の加群からの二つの商関手と自然に両立する。

*証明*

大きな商の射を分数で表すとき、逆にする射は長さを保つ。両端が有限長さなら必要な中間対象も有限長さとなるので、有限な商からの関手は充満忠実である。商の対象は元の加群で表され、その長さは代表元の長さだから、本質的像は有限長さの対象全体になる。包含・商関手の完全性と長さの計算から残りが従う。

$`q` を複体の各項に適用できるのは、その各項が $`\mathcal{T}_J(C)` に入る場合だけである。一般の $`K(z;C)` はこの条件を満たさない。以下では加群の圏でホモロジーを計算し、その冪ねじれと有限性を確かめてから商関手で送る。

これで $`(\mathcal{A}_\lambda^{\mathrm{fin}},\ell_\lambda)` は定義 3.1 の長さ付きアーベル圏である。§5、§6 のホモロジー的関手はここに値をとる。

*解説 §6.2 評価関手*

$`s_n>0` と非単項超フィルター $`\mathcal{U}` を固定する。共通の $`J` の冪で消え、各段の $`\lambda(M_n)` が有限で、$`\lambda(M_n)=O(s_n)` となる加群列の圏は、部分商・拡大で閉じるアーベル圏である。正規化超極限

$$`L(M)=\lim_\mathcal{U}\lambda(M_n)/s_n`

は有限・非負・同型不変で短完全列に加法的である。$`L=0` の列で割った Serre 商を $`\mathcal{A}_{\lambda,s,\mathcal{U}}` と書く。命題 4.6 と同じ証明で忠実な有限値の長さが入る。

一様に台をもつ自由複体列に Koszul 上界を各段で適用すると、ホモロジー列の長さは $`O(s_n)` となる。ランク $`o(s_n)` の一様に台をもつ列なら正規化長さは零になる。ただし一般のランクの小さい複体列の生のホモロジーをそのまま評価できるわけではない（§6 の Remark 4.1）。支持つきランク商 $`P_T^J` 上の関手は、次の四段階で構成する。

1. 一様に台をもつ代表元で、共通の冪ねじれ条件と長さ $`O(s_n)` を示す。

2. 支持部分の局所化で逆にする射を、列の Serre 商の同型に送る。

3. シフト・長完全列と両立して関手を降下させ、冪等元の像によって直和因子へ延長する。

4. 一様に台をもつ列の像では、延長した関手を元のホモロジー列で計算できることを示す。

この接続と有界性を構成すると Euler 有限性が成り立ち、命題 3.4 が使える。評価先の Serre 商だけでは (2)–(4) は得られないが、これらも実装済みである。

*Lean:* \`Asymptotic.SequenceHomologyLocalization\`、\`CompletedHomology\`、\`RankHomologyShiftNatural\`、\`CompletedRankEvaluation\`、\`PaperBaseChangeEvaluation\`。

*命題 6.4（Euler 有限なホモロジー的関手）（Prop 4.3 (a)(b)、命題 5.6 の対応物）*

$`(C,\lambda)` を Koszul 有限とする。一様に台をもつ $`F = (F_n)` に対し

$$`b_i^{\mathrm{ord}}(F) = \lim_\mathcal{U} \frac{\operatorname{length} H_i(F_n)}{s_n},\qquad b_i^{C}(F) = \lim_\mathcal{U} \frac{\lambda H_i(F_n\otimes_T C)}{s_n}`

とおくと、これらは有限で、$`F\in N_T` なら $`0` である。上の四段階により、$`H_i^{\mathrm{ord}}`、$`H_i^C` は $`P_T^J` の全ての対象 $`X` に延び、それぞれ有限長 $`T` 加群の列の商と $`\mathcal{A}_{\lambda,s,\mathcal{U}}` に値をとる Euler 有限なホモロジー的関手になる。一様に台をもつ列の像では、その長さは $`b_i^{\mathrm{ord}}(F)`、$`b_i^C(F)` である。

*証明*

有限性：共通の $`v` について補題 5.2 を各段に適用する。これによりホモロジー列は共通の冪で消され、長さは $`O(s_n)` となる。一様に台をもつ小ランク列では正規化長さが零になる。

延長：評価先は、有限な長さ $`O(s_n)` の冪ねじれ加群列を

$$`L(M)=\lim_\mathcal{U}\lambda(M_n)/s_n=0`

の列で割った Serre 商である。通常の $`o(s_n)` はこの零条件の十分条件である。支持部分の局所化の分母を同型に送ることを確かめてホモロジー関手を降下させ、評価先で射影子の像をとって冪等完備化へ延長する。シフト同型、長完全列、対象ごとの有界性もこの延長と両立するので、Euler 有限なホモロジー的関手になる。一般の小ランク列の生のホモロジーが零だとは仮定しない。

*Lean:* \`Asymptotic.SequenceHomologyBounds\`、\`SequenceHomologyLocalization\`、\`CompletedHomology\`、\`RankHomologyShiftNatural\`、\`CompletedRankEvaluation\`、\`PaperBaseChangeEvaluation\`（Koszul 有限性を入力として証明済み）。

この証明で構成するのは、(i) ホモロジー列が評価先に入ること、(ii) 支持つき局所化の分母を同型に送ること、(iii) 直和因子への延長の完全性、(iv) シフトとの自然な同型と有界性、(v) 一様支持の代表での計算公式、である。これらはそれぞれ独立に証明して接続している。任意の小ランク列の生のホモロジーが零となると仮定するものではない。

*系 6.5（Euler 評価）（Prop 4.3 (b)）*

$`\chi_{\mathrm{ord}}=\sum_i(-1)^ib_i^{\mathrm{ord}}`、$`\chi_C=\sum_i(-1)^ib_i^C` は準同型 $`K_0(P_T^J)\to\mathbb{R}` を定める。

*証明*

命題 6.4 により命題 3.4 を適用できる。

*Lean:* Euler の準同型は共通の \`homologicalEulerK0\` の引き戻しで定義する（\`paperRankEulerK0\`、\`paperBaseChangeEulerK0\`）。

有限版との関係（Prop 4.3 (c)）：$`P\in\operatorname{Perf}_{\mathfrak{m}}(T)` について $`H_i(P^{\oplus s_n})=H_i(P)^{\oplus s_n}` なので正規化した長さは定数で、関手 $`\iota` を通すと $`\chi_{\mathrm{ord}}(\iota P)=\chi_{\mathrm{ord}}(P)`、$`\chi_C(\iota P)=\chi_C(P)` となる。これは数学的な説明で、Lean では $`\iota` の独立した入口は置いていない。

*命題 6.6（係数変更との両立）*

$`A\to S\to S'\to C` を $`A` 代数の準同型とし、$`(C,\lambda)` を Koszul 有限とする。$`X\in P_S^J` について、係数拡大 $`X\otimes_SS'` は $`P_{S'}^J` に入り、

$$`\chi_C(X\otimes_SS')=\chi_C(X).`

つまり、係数拡大 $`K_0(P_S^J)\to K_0(P_{S'}^J)` と系 6.5 の Euler 評価は可換である。

*証明*

一様に台をもつ代表の各段で命題 5.5 を使い、正規化極限をとる。直和因子への延長とも両立する。

*Lean:* Lean では、係数変更後の評価 \`paperBaseChangeEulerK0\` を評価と係数拡大 \`paperSupportedChangeRing\` の合成として定義する。二段階の係数拡大との同定は \`Paper.Section4.SymmetricComparison\` の \`paperBaseChangeEulerK0\_eq\_koszulEuler\_mul\` の中で行う。

外の文献：BalmerSchlichting 1.10、BalmerSchlichting 1.12

:::

:::definition "paper_eq_4_2" (lean := "SerrePositivity.Asymptotic.paperRankBetti_koszul_formula, SerrePositivity.Asymptotic.paperBaseChangeBetti_koszul_formula, SerrePositivity.Asymptotic.paperBaseChangeBetti_koszul_tensor_formula") (uses := "paper_eq_4_3, paper_4_1")
**式 (4.2)**　商内支持からのKoszul–Betti二項係数公式。対応表の状態：本体にある。

原典 PDF p.18 / layout L956。厳密有界自由列の像が商内でsupportedであればよく、元の列の一様支持を追加仮定しない。ordinaryとbase-change lengthの両方へ適用する。原典のLaurent多項式を各係数の等式で与える。

*解説 §6.4 消滅と下界：補題 3.11、3.12 の適用*

*補題 6.10（Koszul の多項式恒等式）（Prop 4.3 (d)、(4.2)）*

$`F` を有界な自由列で、その像 $`X` が $`P_T^J` に入るものとし、$`z^v` が $`X` に $`0` で作用するとする（$`F` 自体は一様に台をもたなくてよい）。$`e` を列 $`z` の長さ、$`K_v = K(z^v;A)` として、どちらの評価についても

$$`(1+t)^e\sum_i b_i(X)\,t^i \;=\; \sum_i t^i\,\lim_\mathcal{U}\frac{\lambda H_i(K_v\otimes_A F_n\otimes_T C)}{s_n}`

（普通の長さの側は $`C = T`、$`\lambda = \operatorname{length}`）。

*証明*

商での零作用から補題 3.10 の分裂を適用し、長さをとると左辺の二項係数が得られる。一方、$`K_v\otimes F` は一様に台をもつので、命題 6.4 の計算公式により右辺となる。元の $`F` の一様支持は使わない。

*Lean:* \`Asymptotic.PaperBaseChangeEvaluation\` の \`paperBaseChangeBetti\_koszul\_formula\`、\`paperBaseChangeBetti\_koszul\_tensor\_formula\`（証明済み）。

:::

:::definition "paper_eq_4_3" (uses := "paper_eq_4_1")
**式 (4.3)**　支持liftのKoszulテンソルのshift分裂。対応表の状態：なし。

原典 PDF p.18 / layout L971。Koszul同型を数値Betti公式へ移す道具はあるが、ここに書かれた全bounded sequenceの同型そのものの宣言を特定していない。対応しない数値公式で置換しない。

:::

# §4.4 Scalar extension and nonlifting idempotents

%%%
number := false
tag := "paper-4-4"
%%%

:::lemma_ "paper_4_4" (lean := "SerrePositivity.lemma_3_4") (uses := "paper_3_4")
**補題 4.4**　有限長基底加群に対する係数Tor長。対応表の状態：本体にある。

原典 PDF p.19 / layout L1023。同じ(4.1)の長さ仮定の下で、Lemma3.4を再利用する型である。原典同様、Cの平坦性やlambdaの忠実性を仮定せず、高次Torは長さ零として扱う。

:::

:::proposition "paper_4_5" (uses := "paper_eq_4_4, paper_eq_4_5, paper_eq_4_6, paper_4_2, paper_4_4")
**命題 4.5**　冪等直和因子を含む基底変換Euler比較。対応表の状態：一部。

原典 PDF p.20 / layout L1037。Karoubi包の全K0類で正規化Euler評価の基底変換公式を直接確認した。原典のchi\_A・通常T評価・C評価の三項同一視のうち通常T評価側までを一つの対応として検収していないためpartialとする。

*解説 §6.3 この実現での比較定理*

*命題 6.7（ランク無視版の基底公式、命題 5.8 の対応物）*

$`A` を正則局所環、$`z` を正則パラメータ系、$`(C,\lambda)` を Koszul 有限な長さ付き $`A` 代数とする。$`X\in P_A^J` について

$$`\chi_C(X\otimes_A C)=e_\lambda(z;C)\,\chi_A(X).`

*証明*

$`K(z)` が剰余体の自由分解であることから、$`A` 側の支持つきランク商に有界な t 構造を構成し、冪等完備性を得る。これにより $`X` は一様に台をもつ共通有界な自由複体列 $`F` で表される。単に直和因子であることから評価の一致を推論するのではなく、全対象をこの形で計算できることを使う。

各 $`F_n` に命題 5.8 を適用し、$`s_n` で割って超極限をとる。共通の有界な次数範囲と Koszul 上界により、有限 Euler 和と極限を交換できる。ここでは $`K_0(P_A^J)` の Koszul 一元生成は使わない。

*Lean:* \`Paper.Section4.PaperK0Comparison\` の \`koszulPaperEulerK0\_changeRing\`（基底の Koszul 分解を明示して証明済み）。全対象の一様代表は \`UniformRepresentative\`、冪等完備性は \`supportedRank\_isIdempotentComplete\_of\_koszul\`。

*注意 6.8（正則な基底側の構造）*

上の証明の背景を述べる。正則な $`A` 側では、一様に台をもつ対象のなす部分圏に各段のホモロジーから定まる有界な t 構造が入り、その heart は共通の冪で消され長さ $`O(s_n)` の有限 $`A` 加群の列の圏である。有限長加群 $`M` は次数 $`0,\dots,e`、各項の階数が $`\binom ej\operatorname{length}(M)` 以下の自由分解をもつ（$`k` の Koszul 分解と組成列に沿う Horseshoe 補題）ので、ランクの小ささとホモロジーの長さの小ささが一致し、ランク $`o(s_n)` の部分で割った Verdier 商にも有界な t 構造が降りる。有界な t 構造をもつ三角圏は冪等完備なので、$`P_A^J` の全ての対象は一様に台をもつ自由複体の列で表される。固定した持ち上げ $`F` 上の商の冪等元が $`F` 上の鎖写像に持ち上がるとは主張していない（別の持ち上げを選ぶ）。さらに heart の $`\mathfrak{m}_A` 進フィルトレーションから $`K_0` が計算でき、$`O(s_n)`、$`o(s_n)` の整数列の群を $`G_s`、$`g_s` とすると $`K_0(P_A^J)\cong G_s/g_s` で、一様に台をもつ $`F` の類は $`(\sum_i(-1)^i\operatorname{length} H_i(F_n))_n` の剰余類に対応する。この同型で $`\chi_A` は $`[c]\mapsto\lim_\mathcal{U} c_n/s_n` であり単射ではない（$`\mathcal{U}` に入らない無限集合の指示列が核に入る）。$`s_n\to\infty` なら $`G_s/g_s\cong\ell^\infty(\mathbb{N},\mathbb{R})/c_0(\mathbb{N},\mathbb{R})` である。$`K_0` のこの計算は形式化していない。

この t 構造の議論は $`T` 側には移せない。$`T` が正則でなければ剰余体の有限自由分解がなく、ホモロジーへの切り詰めが有界自由複体の列の圏を出るからである。$`T` 側では冪等完備化と、直和因子への関手の延長（命題 6.4）が本当に必要になる。また「通常の極限で $`o(s_n)`」と「正規化超極限で $`0`」は区別しなければならない。t 構造で割る heart は前者を使い、評価先の Serre 商は後者を使う。

*解説 §6.6 $`\lambda`-平坦な代数での適用*

*系 6.14（$`\lambda`-平坦な代数での比較・消滅・下界）*

系 5.12 と同じ設定で、次が成り立つ。

- (a) *基底公式*：$`X\in P_A^J` について $`\chi_C(X\otimes_AT)=r\cdot\chi_A(X)`。

*解説 §7.2 Theorem 4.7*

*命題 7.6（Prop 4.5、命題 7.2 の対応物）*

$`X\in P_A^J` について

$$`\chi_{\mathrm{ord}}(X\otimes_A T) \;=\; r\cdot\chi_A(X) \;=\; \chi_C(X\otimes_A T).`

*証明*

正規化側は系 6.14 (a) である。普通の側は、命題 6.7 を $`(T,\operatorname{length}_T)` に適用し、補題 7.1 を入れる。

*Lean:* \`Paper.Section4.UniformRepresentative\`、\`PaperK0Comparison\`。明示した Koszul 分解からの一般係数公式は証明済み。正則局所環からその分解を供給する適用は正則パラメータの引用に依存する。

宣言：`SerrePositivity.Section4.paperBaseChangeEulerK0_eq_koszulEuler_mul`、`SerrePositivity.Section4.ordinaryPaperEulerK0`、`SerrePositivity.Section4.koszulPaperEulerK0_changeRing`

:::

:::definition "paper_eq_4_4"
**式 (4.4)**　有限tensor spectral sequenceのE1項。対応表の状態：なし。

原典 PDF p.20 / layout L1062。双複体からのfunctorialなspectral sequenceのこのE1ページを表示する宣言は未同定。Euler恒等式だけではこの項目を埋めない。

:::

:::definition "paper_eq_4_5" (uses := "paper_eq_4_6")
**式 (4.5)**　普通Euler評価に現れるr倍有限和。対応表の状態：一部。

原典 PDF p.20 / layout L1085。Koszul Euler数を係数とするK0での比較はあるが、原典のidempotent aの像V\_bの通常長の有限和をこの形で計算する表示は未検収。

宣言：`SerrePositivity.Section4.koszulPaperEulerK0_changeRing`

:::

:::definition "paper_eq_4_6" (uses := "paper_eq_4_5, paper_4_4")
**式 (4.6)**　有限hyper-Tor spectral sequence。対応表の状態：なし。

原典 PDF p.21 / layout L1096。一般の支持summand YとCについてのfunctorialなhyper-Tor spectral sequenceの宣言は未確認。Lemma4.6とは別項目として扱う。

:::

# §4.5 Connective coefficients and the norm comparison

%%%
number := false
tag := "paper-4-5"
%%%

:::lemma_ "paper_4_6" (uses := "paper_3_1, ext_Drinfeld_3_1, ext_Drinfeld_3_4, ext_LT_3_12")
**補題 4.6**　連結結合係数Hによる両ランク商のMorita表示。対応表の状態：なし。

原典 PDF p.21 / layout L1123。任意のNoether基底で生成元のendomorphism dg algebraが連結となり、P\_A≃Perf(H)、P\_T≃Perf(H⊗\^L T)を中心的局所化と両立させる一組の同値は確認できない。KSTの特定dg商やsupportedRankK0\_descentはこの同値を構成していない。

*解説 §7.2 Theorem 4.7*

*補題 7.7（Lemma 4.6）*

連結な dg $`A` 代数 $`H` で、$`P_A\simeq\operatorname{Perf}(H)`、$`P_T\simeq\operatorname{Perf}(H\otimes^L_A T)` となるものがある。$`H` は行列環の積 $`\prod_n M_{s_n}(A)` のランクの小さい部分による DG 商の、生成元の自己準同型として得られる。

*Lean:* dg 表示そのものは未。定理 7.9 に必要な一般係数の降下への接続を含む帰結を、\`Section4.supportedRankK0\_descent\` として引用している。

*注意 7.8*

何らかの $`H` があること自体は一般論である：生成元を一つもつ冪等完備な安定圏はその自己準同型代数の $`\operatorname{Perf}` に同値であり（Schwede–Shipley）、Verdier 商は生成元の像で生成される。商と $`-\otimes_AT` の可換性も一般論（Land–Tamme Lemma 3.12、Drinfeld Prop. 1.6.3）である。定理 7.3 を使うために本当に要るのは、次の二点を満たす $`H` であり、これはこの構成に固有の事情に依る。

- *連結性*：一般には成り立たない。たとえば $`\operatorname{Perf}(\mathbb P^1)` の生成元 $`\mathcal O\oplus\mathcal O(2)` の自己準同型代数は $`\operatorname{Ext}^1(\mathcal O(2),\mathcal O)=H^1(\mathbb P^1,\mathcal O(-2))\neq0` を含む。ここでは元の圏も潰す部分圏も次数 $`0` の自由列で生成され、Drinfeld の商で加わる射は元の射と次数 $`+1` の収縮ホモトピーの交互の合成だけなので、Hom 複体は非負次数に集中する。元論文も「選んだ生成元についての主張」と断っている。定理 7.3 は連結な係数を要求する（その入力 Land–Tamme Thm. B.3 が連結係数の主張）。

外の文献：Drinfeld 3.1、Drinfeld 3.4、LT 3.12

:::

:::definition "paper_eq_4_7" (uses := "ext_Drinfeld_3_1, ext_Drinfeld_3_4")
**式 (4.7)**　endomorphism代数の積と導来基底変換。対応表の状態：なし。

原典 PDF p.21 / layout L1142。B\_A=∏M\_(s\_n)(A)のflatnessと有限表示TによるB\_A⊗\^L T≃B\_Tの同値を、この生成元表示と一緒に構成する宣言は未確認。

*解説 §7.2 Theorem 4.7*

*注意 7.8*

- *商をとる前の底変換*：$`\prod_nM_{s_n}(A)\otimes_AT=\prod_nM_{s_n}(T)` は無限積とテンソル積の交換であり、$`T` が有限表示であることと、$`A` がネーターで $`\prod_nM_{s_n}(A)` が $`A` 平坦であることに依る。§6 で底のネーター性が効くのはここである。

外の文献：Drinfeld 3.1、Drinfeld 3.4

:::

:::theorem "paper_4_7" (uses := "paper_eq_4_1, paper_3_1, paper_4_5, paper_4_6")
**定理 4.7**　漸近Euler評価の共役norm和の比較。対応表の状態：未証明の入力に依存。

原典 PDF p.22 / layout L1171。全支持対象上の共役和の等式の型はあるが、supportedRankK0\_descentが直接sorryを持つ。Lemma4.6を構成してTheorem3.1を実際に適用したものとはせず、別の入力界面として記録する。

*解説 §6.3 この実現での比較定理*

*定理 6.9（ランク無視版のノルム比較、定理 5.9 の対応物）*

$`A` を正則局所環、$`z` を正則パラメータ系、$`T` を可換 $`A` 代数とする。有限群 $`G` が $`K_0(P_T^J)` に群自己同型として作用し、その不変類の正の整数倍が係数拡大 $`f\colon K_0(P_A^J)\to K_0(P_T^J)` の像に入るとする。$`T` 代数 $`C_1,C_2` とそれぞれの長さ関数 $`\lambda_1,\lambda_2` が Koszul 有限で $`e_{\lambda_1}(z;C_1)=e_{\lambda_2}(z;C_2)` なら、任意の $`y\in K_0(P_T^J)` について

$$`\sum_{g\in G}\chi_{C_1}(g\cdot y)=\sum_{g\in G}\chi_{C_2}(g\cdot y).`

*証明*

系 6.5 により、二つの評価は $`K_0` 上の Euler 評価である。命題 6.6 と命題 6.7 により $`\chi_{C_i}\circ f=e_{\lambda_i}(z;C_i)\,\chi_A` である（基底公式）。ここで二段階の係数変更 $`A\to T\to C_i` と直接の $`A\to C_i` の自然な同定を使う。系 3.7 を適用する。二つの列の評価先を同じ圏にする必要はない。

*Lean:* \`Paper.Section4.SymmetricComparison\` の \`symmetricPaperEuler\_conjSum\_eq\`（二つの Koszul Euler 特性の一致と降下を引数にして証明済み）。証明は系 3.7 の \`homologicalEulerK0\_pullback\_conjSum\_eq\_of\_base\_formula\` に、二段階の係数変更を一段に直した基底公式 \`paperBaseChangeEulerK0\_eq\_koszulEuler\_mul\` を渡すだけである。

*解説 §6.6 $`\lambda`-平坦な代数での適用*

*系 6.14（$`\lambda`-平坦な代数での比較・消滅・下界）*

- (b) *比較*：Koszul 有限なもう一つの長さ付き代数 $`(C',\lambda')` で $`e_{\lambda'}(z;C')=r` なら、定理 6.9 の降下のもとで共役和が一致する。

*解説 §7.2 Theorem 4.7*

以下は $`(C_1,\lambda_1)=(T,\operatorname{length}_T)`、$`(C_2,\lambda_2)=(C,\lambda)` の場合である。幾何的条件から不変類を降下させる議論は、上の比較定理とは別の入力である。

*定理 7.9（Theorem 4.7、命題 7.5 の対応物）*

命題 7.5 と同じ仮定のもと、$`X\in P_T^J` について

$$`\sum_{g\in G} \chi_{\mathrm{ord}}(X^g) \;=\; \sum_{g\in G} \chi_C(X^g).`

*証明*

系 6.14 (b) を $`(C',\lambda')=(T,\operatorname{length}_T)` に適用する。$`e_{\operatorname{length}_T}(z;T)=r` は補題 7.1 による。降下は、系 7.4 を補題 7.7 の $`H` について使って得る（引用）。

*Lean:* \`symmetricPaperEuler\_conjSum\_eq\` は二つの Koszul Euler 特性の一致と降下を引数にして証明済み。\`Section4.theorem\_4\_7\_K0\` はその系であり、\`supportedRankK0\_descent\` と正則パラメータの引用への依存は残る。

宣言：`SerrePositivity.Section4.theorem_4_7`、`SerrePositivity.Section4.theorem_4_7_K0`、`SerrePositivity.Section4.supportedRankK0_descent`

:::

