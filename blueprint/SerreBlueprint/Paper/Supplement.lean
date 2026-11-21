-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option maxHeartbeats 2000000

#doc (Manual) "補足" =>
%%%
number := false
tag := "paper-supplement"
%%%

本論文の項目に対応しない文章（主張と帰着、証明の方針、先行研究との関係、検討の記録など）。解説から移した原稿（`research/paper-coverage/notes/supplement/`）で、原稿に「未確認」「精密ではない」とある議論は、その断り書きのまま載せる。

# はじめに

%%%
number := false
tag := "paper-supplement-01-introduction"
%%%

この文書は、プレプリント \*Positivity of Serre's Intersection Multiplicity\*
（OpenAI、2026-09-23。openai/math のファミリー 193、コミット \`adc7f124\`）
の証明を、Lean 4 による形式化
unaoya/SerrePositivity
で得た理解に基づいて整理し直した解説である。

この解説では、証明を次のように整理して述べる。

- Euler 評価、反復錐による消滅、第零次の下界、群作用による共役和比較を共通定理としてまとめる（§3）。評価先は長さ付き代数から作る（§4）。

- perfect 複体（§5）とランク無視の圏（§6）をその二つの実現とする。各節では具体的な圏と関手を作り、共通定理の仮定を確認して適用する。どちらも一般論であり、論文に固有の仮定を入れて論文の命題を導くのは §7 である。

- 長さの有限性、Koszul ホモロジーの消滅、比較に必要な降下を別々の入力とする。$`\lambda`-平坦性・$`\lambda`-CM 性（§4）は、それらを供給する十分条件として述べる。

- 具体的な代数の構成（§8）と核の場合への適用（§9）は別に述べる。

*表記*

命題の番号はこの解説の通し番号で、元論文の番号を括弧で併記する。

宣言名は名前空間 \`SerrePositivity\` を省略して書く。解説の定式化が Lean と異なる箇所は、その場で注意し、付録 A.4 にまとめる。

# 主張と帰着

%%%
number := false
tag := "paper-supplement-02-statement-and-reduction"
%%%

*定理 1.2（核の場合）*

*帰着（Lemma 5.1）*

消滅定理はここと補題 9.2（Lemma 5.2）の2か所で使う。

*注意 1.3（消滅定理の証明：巡回 Adams 作用素）*

元論文は消滅定理を引用するが、形式化では Gillet–Soulé の Adams 作用素の方法で証明した。Chow 群・局所 Chern 指標・Riemann–Roch は使わない。$`R` を次元 $`d` の正則局所環とし、閉集合 $`Z\subseteq\operatorname{Spec} R` に台をもつ有界な有限射影複体の Grothendieck 群を $`K_0^Z(R)` と書く。テンソル積がカップ積 $`K_0^Y\times K_0^Z\to K_0^{Y\cap Z}` を与え、$`\chi(M,N)` は分解の類 $`[F_M]\in K_0^{\operatorname{Supp} M}`、$`[F_N]\in K_0^{\operatorname{Supp} N}` の積の Euler 標数である。

1. *巡回 Adams 作用素。* 素数 $`p` と、$`1/p` と $`1` の原始 $`p` 乗根 $`\zeta` を含む係数体 $`E` をとる。巡回群 $`C_p` はテンソル冪 $`X^{\otimes p}` に Koszul 符号つきで作用する。その $`\zeta^j` 固有部分を使い $`\psi^p[X]=\sum_j\zeta^j[(X^{\otimes p})^{(\zeta^j)}]` と定める。これは (A1) 加法的、(A2) カップ積と乗法的、(A3) 平坦な底変換と可換、(A4) 長さ $`1` の Koszul 複体で $`\psi^p[K(a)]=p\,[K(a)]` を満たす。加法性は、射影複体の擬同型がホモトピー同値であることと、短完全列の次数ごとの分裂から得る（混合項は $`C_p` が自由に作用するので寄与しない）。

2. *重みの評価。* $`Z` の余次元が $`c` なら、$`K_0^Z(R)_E` 上の $`\psi^p` の固有値は $`p^c,\dots,p^d` に限る。高さ $`c` の生成点全体で半局所化し、台つき局所化の完全列（$`K_0^Z\cong G_0^Z` との比較から証明）と Koszul 複体による生成を使って、余次元についての下降帰納法で示す。閉点では $`K_0^{\{\mathfrak{m}\}}(R)_E\cong E` が純粋に重み $`d` である。

3. *結論。* 正則局所環では $`\operatorname{ht}P=d-\dim R/P` なので、$`[F_M]` は重み $`\ge d-\dim M`、$`[F_N]` は重み $`\ge d-\dim N` の部分にある。(A2) により積の重みは $`\ge 2d-\dim M-\dim N>d` となるが、積は閉点に台をもち重み $`d` しかないので零。よって $`\chi(M,N)=0`。

素数は、剰余標数が $`2` でなければ $`p=2`（$`\zeta=-1` なので係数拡大は不要）、剰余標数が $`2` なら $`p=3` とし、$`1` の原始 $`3` 乗根を添加した平坦局所拡大の上で同じ議論を行う。拡大で正則性・台の次元・$`\chi` が保たれることも証明している。原典は Gillet–Soulé、巡回 Adams 作用素の構成と公理の証明は Brown–Miller–Thompson–Walker（\*Cyclic Adams operations\*, arXiv:1601.05072）による。

*Lean:* \`IntersectionMultiplicity.AdamsVanishingAll\` の \`intersectionVanishing\_of\_adams\`。剰余標数 $`2` 以外は \`intersectionVanishing\_of\_residue\_two\_ne\_zero\`（\`KTheory.Adams.CyclicTwo\`）、剰余標数 $`2` は \`intersectionVanishing\_of\_residue\_two\_eq\_zero\`（\`KTheory.Adams.CyclicThree\`）。作用素の公理の束は \`Adams.LocalizationAdamsFamily\`、重みの評価は \`KTheory.Adams.SemilocalPureWeight\`、カップ積の消滅は \`KTheory.Adams.CupVanishing\`。

*先行結果と位置づけ*

等標数と不分岐の場合（完備 DVR 上の冪級数環を含む）は Serre による。Roberts、Gillet–Soulé は $`\dim M+\dim N<\dim R` での消滅を、Gabber は一般の非負性を示した。正値性の部分的な結果として、Skalit（2 次元正則局所環上 essentially smooth な場合）、KC–Soto Levins（Serre の持ち上げ条件をみたす加群）、Bhatt–Hochster–Ma（両方の商整域に lim Cohen–Macaulay 列があれば正、付録 B.2）がある。元論文の新しい部分は剰余標数 $`p>0` の混標数の場合で、不分岐も分岐も一様に扱う。等標数は Lemma 5.1 で Serre を引用するだけで、別証明はしていない（形式化では、主定理が使う剰余標数零の場合を対角線論法で証明した。付録 A.1）。元論文の脚注 1 には、同じ主張（素イデアル商の形）が 2025 年 12 月に公開ポストされていることが記録されている。

*系（この解説では扱わない）*

元論文は定理 1.1 から二つの系を導く。分岐する混標数の正則局所環で $`\sqrt{P+Q}=\mathfrak{m}`、$`\operatorname{ht}P+\operatorname{ht}Q=\dim R` なら、$`r\ge1` で $`P\cap Q^{(r)}\subseteq\mathfrak{m}^{r+1}`（Kurano–Roberts の「正値性から記号的冪へ」の定理の適用）。また strict transform の交点についての不等式 $`\chi_A(A/P,A/Q)\ge e(A/P)\,e(A/Q)`（Corollary 1.2、Skalit の爆発公式に正値性を入れたもの）。どちらも定理 1.1 の帰結であり、形式化の対象にしていない。

# 証明の方針

%%%
number := false
tag := "paper-supplement-03-proof-strategy"
%%%

*アイデア：古典的な Cohen–Macaulay の場合*

$`D` と $`E` がどちらも Cohen–Macaulay なら、高次の Tor が消えて $`\chi^R(D,E) = \operatorname{length}(D\otimes_R E) > 0` となる。論文は本物の CM 加群の代わりに、長さ関数 $`\lambda` の目で CM な巨大代数 $`C_D`、$`C_E`（\*\*$`\lambda`-CM 代数\*\*、定義 4.14）を使い、次の古典的事実の $`\lambda` 版で高次の項を消す。

- $`D` 側：CM 加群の射影次元は低い（Auslander–Buchsbaum の公式）。$`\lambda` 版は補題 5.14。

- $`E` 側：巨大 CM 代数とテンソルすると、短い有限自由複体の高次ホモロジーが消える（Hochster による新交叉定理の議論）。$`\lambda` 版は補題 5.10 と補題 6.11。

- 残る $`0` 次の項が正であることは、巨大 CM 代数の非自明性 $`\mathfrak{m} B\ne B` の $`\lambda` 版（系 8.7）による。

*基底と Galois 閉包：2段階の準備*

$`D` は正則でないので、比較を直接示せる場所（命題 7.2：$`K_0` が Koszul 複体で生成される）としても、$`\lambda`-平坦性を定義する場所（定義 4.9）としても使えない。そこで次の2段階の準備をする。

1. 正則な基底をとる（本論文 Lemma 2.2 の原稿）

2. *Galois にする*：比べたい複体は $`D` 上にあって $`A_D` からは来ないので、その類を $`A_D` に戻す必要がある。戻す手段は定理 7.3（有理 K 理論の降下）で、幾何ファイバーに推移的に作用する群が要る。$`D/A_D` は Galois とは限らないので、$`\operatorname{Frac}(D)/\operatorname{Frac}(A_D)` の Galois 閉包における $`A_D` の整閉包 $`D'` に上げ、Galois 群 $`G_D` を得る。1段目で分離性を課したのはこのためである。代わりに $`\chi^R(D,E)` が $`\chi^R(D',E')` に変わり、ランクの因子 $`a_D = \operatorname{rank}_D D'` がつく。

$`E` についても同様に $`A_E`、$`E'`、$`G_E`、$`a_E = \operatorname{rank}_E E'` をとる（詳細は §9）。

*記号*

$`\sigma\in G_D` に対し、$`C_D` に $`R\to D'\xrightarrow{\sigma}D'\to C_D` で $`R` 作用を入れたものを $`C_D^\sigma` と書く。$`C_E^\gamma`（$`\gamma\in G_E`）も同様。

*2回の置き換え*

$`\chi` を変えずに $`D` と $`E` を1つずつ置き換える。個々の値はひねりで変わりうるが、Galois 共役の和をとると変わらない。

置き換え 1（本論文の式 (5.3) の原稿）

*置き換え 2*（$`E'\to C_E`、式 （9.1））．ランク無視の圏でのノルム比較（§6）により、各 $`\sigma` について

$$`|G_E|\, \sum_i (-1)^i\, \lambda_D \operatorname{Tor}_i^R(C_D^\sigma, E') \;=\; \sum_{\gamma\in G_E} \chi_{\lambda_E}\bigl(\text{$C_D^\sigma$ の有限近似} \otimes C_E^\gamma\bigr). \tag{2.2}`

右辺の各項は、$`C_D^\sigma` を有限長加群の列で近似し、その分解を $`\gamma` でひねって $`C_E` とテンソルした複体の列について、$`\lambda_E` で測った Euler 特性を列の大きさ $`s_n` で割って超極限をとったものである（§9）。直観的には「$`C_D^\sigma` と $`C_E^\gamma` の Tor を、$`\lambda_D` と $`\lambda_E` の両方で測った Euler 特性」である。

*正値性*（補題 9.6）．両側が CM もどきなので、（2.2） の右辺の各項は $`0` 次の項だけになり、正。したがって

$$`|G_D|\, a_D a_E\, \chi^R(D,E) \;=\; \frac{1}{|G_E|}\sum_{\sigma\in G_D}\sum_{\gamma\in G_E} \chi_{\lambda_E}\bigl(\text{$C_D^\sigma$ の有限近似} \otimes C_E^\gamma\bigr) \;>\; 0.`

*ノルム比較の型*

2回の置き換えは同じ型の議論である。右の因子 $`T` を $`C_T` に置き換えるため、左の因子の自由分解と $`T` のテンソルとして「閉点に台をもつ対象」$`X` を作り、

- 普通の長さで測ると元の $`\chi`（Galois でひねっても変わらない）

- $`X\otimes C_T` を $`\lambda` で測ると置き換えた量（ひねりで変わりうる）

の2つが、共役の和の上で一致する。一致の理由は「正則な基底 $`A` から来る類では一致する」と「共役の和は有理的に $`A` から来る（定理 7.3、有理 K 理論の降下）」の組み合わせ。

- 　／　置き換え 1　／　置き換え 2
- 左の因子　／　$`E'`　／　$`C_D^\sigma`
- 置き換えるもの　／　$`D' \to C_D`　／　$`E' \to C_E`
- 対象 $`X`　／　$`E'` の有限自由分解 $`\otimes\, D'`　／　$`C_D^\sigma` の有限近似の切り詰めた分解 $`\otimes\, E'` の列
- 対象が住む圏　／　$`\operatorname{Perf}_{\mathfrak{m}}(D')`　／　$`P_{E'}^J`（ランク無視の圏）
- 比較定理　／　命題 7.5　／　定理 7.9

置き換え 2 で左の因子 $`C_D^\sigma` が有限加群でないために、有限近似と「ランク $`o(s_n)` を無視する圏」が必要になる。これが論文 §4 の存在理由である。

*証明の骨格*

以下では、二つの置き換えと正値性に共通する四つの道具を先に抽象的に述べ（§3）、評価先を長さ付き代数から作る（§4）。その上で、評価元を perfect 複体とランク無視の圏にとった二つの実現を一般論として作る（§5、§6）。ここまでが一般論である。そこに論文の状況（有限拡大のランク、Galois 群、降下の引用、$`\lambda`-平坦性・$`\lambda`-CM 性）を入れて論文の命題を導き（§7）、具体的な長さ付き代数（§8）を経て核の場合を示す（§9）。

- 共通の道具（§3）　／　実現（§5 / §6）　／　論文の状況（§7）　／　核の場合（§9）
- Euler 評価　／　系 5.7 / 系 6.5　／　　／　
- 共役和の比較　／　定理 5.9 / 定理 6.9　／　命題 7.5（Lemma 3.5c） / 定理 7.9（Thm 4.7）　／　補題 9.2（置き換え 1） / 命題 9.5（置き換え 2）
- 反復錐による消滅　／　補題 5.10、5.14 / 補題 6.11　／　命題 7.10（Lemma 5.3）　／　補題 9.3
- 第零次の下界　／　補題 5.11 / 補題 6.12　／　命題 7.11（Lemma 5.6）　／　補題 9.6

# 長さ付き代数（解説 §4 の補足）

%%%
number := false
tag := "paper-supplement-04-length-algebra"
%%%

*解説 §4.1 長さ関数と長さ付き代数*

*例 4.2*

*Lean:* \`NormalizedLength\`（\`PerfectComplex.NormalizedLength\`）、普通の長さは \`NormalizedLength.ordinary\`（$`J = \bot`）。Lean の名前は元論文に合わせて「正規化長さ」のまま（付録 A.4）。

*定義 4.3（長さ付き代数）*

$`A` を可換環、$`z=(z_1,\dots,z_e)` をその元の有限列とし、$`z^v=(z_1^v,\dots,z_e^v)` と書く。\*\*長さ付き $`A` 代数\*\*とは、可換 $`A` 代数 $`C` と、$`J=(z)C` のある冪で加群全体が消される $`C` 加群の上の長さ関数 $`\lambda` の組 $`(C,\lambda)` のことである。

$`A` がネーター局所環で $`\sqrt{(z)}=\mathfrak{m}_A` なら、$`(z)C`-冪ねじれと $`\mathfrak{m}_A C`-冪ねじれは同じ条件である。実際、$`\mathfrak{m}_A` のある冪が $`(z)` に入り、この包含を $`C` に移せばよい。§4.2 と定義 4.8 では $`A` のネーター性は仮定せず、有限列 $`z` を固定して使う。

*解説 §4.2 評価先：長さ付きアーベル圏の構成*

*命題 4.7（有限な商と大きな商の有限部分）*

*Lean:* \`LengthAlgebra.FiniteQuotientEquivalence\` の \`finiteQuotientEquivalence\`。ホモロジー、零対象、Euler 数と $`K_0` 評価への接続は \`PerfectHomologyComparison\`。

# perfect 複体での評価（解説 §5 の補足）

%%%
number := false
tag := "paper-supplement-05-perfect-complexes"
%%%

*解説 §5.1 設定と評価関手*

*設定*

*Lean:* 評価元は \`SupportedPerfectHomotopy\`、評価は \`LengthAlgebra.perfectEulerK0\`。局所環上で \`K0Supported\` と同型になり、\`chiOrdHom\`・\`chiLamHom\_of\_finite\` との一致は \`LengthAlgebra.EulerCompatibility\`。

*解説 §5.3 消滅と下界：補題 3.11、3.12 の適用*

ここでは、補題 3.11 の仮定（台の条件と Koszul 振幅の条件）と、補題 3.12 の全射を perfect 複体について確かめ、補題 5.10、5.11 を得る。$`z` に台をもつことは、ホモロジーの幾何学的な台の条件と補題 5.1 から、Koszul 振幅の条件は次の段落の項によるフィルトレーションから、全射は極小性から出る。

$`P` が $`0` 次から $`m` 次に有限射影項をもつなら、$`K_v\otimes P\otimes C` の項によるフィルトレーションの各段は、$`K(z^v;C)` の有限直和のシフトの直和因子である。正次数の Koszul ホモロジーが商で零であれば、各段はその項の次数だけに集中し、長完全列から Koszul 振幅の条件が出る。台の条件は台の条件と補題 5.1 から出るので、補題 3.11 が使える。

一方、$`S=T` が局所環で $`P` の $`0` 次の項が $`T^{\oplus\beta_0}`、$`d_1` の成分が $`\mathfrak{m}_T` に入れば

$$`H_0(P\otimes C)\twoheadrightarrow(C/\mathfrak{m}_T C)^{\oplus\beta_0}.`

この全射と長さの単調性は $`\lambda`-平坦性を使わない。$`\lambda`-平坦性による高次の消滅と組み合わせて初めて、$`m=e` のとき Euler 評価の下界になる。

*補題 5.10（新交叉型の消滅）*

$`e` を列 $`z` の長さとし、全ての $`v\ge1` と $`j>0` で $`\lambda H_j(z^v;C)=0` とする。$`P\in\mathcal{K}_T` が $`0` 次から $`m` 次に有限射影な項をもつ複体で表されるなら、

$$`\lambda H_i(P\otimes_T C) = 0 \qquad (i > m - e).`

特に $`m = e` なら $`\chi_C(P) = \lambda H_0(P\otimes_T C)`。

*証明*

台から $`z_j^v` の零ホモトピーを選び、台の条件を得る。$`P` の項によるフィルトレーションの各段は $`K(z^v;C)` の有限直和のシフトである。正次数の Koszul ホモロジーの長さは零なので、評価先では各段のホモロジーはその項の次数に集中する。長完全列から $`H_n^C(K_v\otimes P)=0`（$`n\notin[0,m]`）、すなわち Koszul 振幅の条件が従う。あとは共通の補題 3.11 により零対象としての消滅を得て、その長さをとればよい。

$`A` が正則局所環、$`z` が正則パラメータ系で $`(C,\lambda)` が $`\lambda`-平坦なら、$`e=\dim A` で、Koszul ホモロジーの仮定は系 4.11 から出る。この補題は §5.5 で $`(A,z,T)=(R,x,R)` として使う。そこでは列の長さ $`e=h` と $`\dim R` が異なるので、$`e` を列の長さとして述べておく。

古典的には、$`B` を巨大 CM 代数、$`F` を長さ $`m` で有限長ホモロジーの有限自由複体とすると、同じ議論で $`H_i(F\otimes B) = 0`（$`i>m-e`）となる。$`m = e` で $`\mathfrak{m} B\ne B` と合わせると、Hochster による新交叉定理の証明になる（cf. Iyengar–Ma–Schwede–Walker, \*Maximal Cohen–Macaulay complexes and their uses\*, Thm. 2.4 とその前後）。

*Lean:* \`LengthAlgebra.PerfectVanishing\` の \`lambdaHomology\_projective\_vanishing\`（Koszul 消滅を入力として$`e` は列の長さで、有限射影項でも成立し、消滅自体は Koszul 有限性を使わない）。

*補題 5.11（$`0` 次の下界）*

補題 5.10 の $`P` の $`0` 次の項を $`T^{\oplus\beta_0}` とし、$`P` が $`1` 次で極小（$`d_1` の成分が $`\mathfrak{m}_T` に入る）とする。このとき

$$`\lambda H_0(P\otimes_T C) \;\ge\; \beta_0\cdot\lambda(C/\mathfrak{m}_T C).`

*証明*

$`H_0(P\otimes C) = C^{\oplus\beta_0}/\operatorname{im}(d_1\otimes C)` は極小性により $`(C/\mathfrak{m}_T C)^{\oplus\beta_0}` に全射する。

*Lean:* \`LengthAlgebra.PerfectMinimalLowerBound\`（極小性から全射を構成し、共通下界を適用）。

普通の評価についても準同型と共役和の比較はあるが、この消滅の入力は一般には満たさない。

*解説 §5.4 $`\lambda`-平坦な代数での適用*

*系 5.12（$`\lambda`-平坦な代数での比較・消滅・下界）*

- (c) *消滅と下界*：補題 5.10、5.11 が成り立つ。

*証明*

系 4.11 により Koszul 有限性、正次数の Koszul ホモロジーの長さ零、$`e_\lambda(z;C)=r` が得られる。(a) は命題 5.8、(b) は定理 5.9、(c) は補題 5.10、5.11 にこれらを入れたものである。

$`\lambda`-CM 代数についても、命題 4.15 を通して同じである。

*Lean:* \`LengthAlgebra.FlatRealization\` の \`perfectEuler\_conjSum\_eq\_of\_flat\`、\`lambdaHomology\_projective\_vanishing\_of\_flat\`、\`perfectEuler\_minimal\_lower\_bound\_of\_flat\`（基底の Koszul 分解と降下を明示した形）。

# ランク無視の圏での評価（解説 §6 の補足）

%%%
number := false
tag := "paper-supplement-06-rank-negligible-category"
%%%

*解説 §6.2 評価関手*

段ごとの長さ $`0` は正規化超極限の長さ $`0` を含意するが、逆は成り立たない。「段ごとに商をとり、次に列の商をとる」という説明を圏同値として使うには、射の分数表示の持ち上げと一様な制御を確かめる必要がある。ここではその同値を使わず、元の加群列から直接 Serre 商を作る。

# 先行研究との関係

%%%
number := false
tag := "paper-supplement-07-prior-work"
%%%

この付録では、§3、§4 の枠組み（長さ関数、長さ $`0` の加群による Serre 商、長さ付きアーベル圏に値をとるホモロジー的評価）から、二つの先行研究がどう見えるかを整理する。一つは Cai–Lee–Ma–Schwede–Tucker（以下 CLMST、arXiv:2209.04046v4、Invent. Math. 244 (2026)）で、もう一つは Bhatt–Hochster–Ma（以下 BHM、arXiv:2410.18372、J. Reine Angew. Math. 835 (2026)）である。番号は CLMST は arXiv v4、BHM は arXiv v1 による（BHM の §6 の番号が Crelle 版でも同じかは未確認）。

以下では、評価の係数（CM な対象）を次の三つの型に分けて呼ぶ。

- 型 (i)：有限生成加群と普通の長さ（評価先は有限長加群の圏）。

- 型 (ii)：巨大代数と長さ関数 $`\lambda`（評価先は $`\mathcal{A}_\lambda`）。CLMST の perfectoid 化や $`D_{\mathrm{perf}}` がこれに当たる。

- 型 (iii)：有限加群の列と正規化した長さ $`\lim_\mathcal{U}\ell(\cdot)/s_n`（評価先は §6.2 の列の Serre 商）。

*解説 §B.1 CLMST：入力の層*

CLMST は、混標数の完備局所整域 $`R` と、その中の正則な基底 $`A = W(k)[[x_2,\dots,x_d]]` について、perfectoid 化 $`C = R^{A_\infty}_{\mathrm{perfd}} = (R\otimes_A A_\infty)_{\mathrm{perfd}}` を調べている（Notation 4.0.1）。解説で使うのは次の結果である。

- *Def. 2.2.1、Prop. 2.2.3、2.2.6*：Faltings の正規化長さ $`\lambda_\infty` を、$`A_\infty^{nc}` 上の $`\mathfrak{m}_A`-冪ねじれ加群の上に3段階（有限表示、有限生成、一般）で定義する。短完全列で加法的で、推移写像が単射（または全射で値が有限）の有向余極限と交換する。

- *Thm. 4.0.3*：$`C` は $`A` 上 $`g`-almost flat で、$`g`-almost faithful。

- *Cor. 4.0.4*：$`A_n\otimes_A R` の任意のパラメータ系 $`\bar y` について、$`H_i(\bar y; C)`（$`i>0`）は $`(g)_{\mathrm{perfd}}` で消える（almost CM）。

- *Prop. 4.0.10*：almost で同型な加群は $`\lambda_\infty` が等しく、特に almost zero な加群は $`\lambda_\infty = 0`。CLMST はこれを「almost 加群に正規化長さが定義できる」と解釈している。逆は一般に成り立たず、$`\lambda_\infty = 0` からは $`v`-almost zero しか出ない（Lemma 4.0.13、Shimomoto）。

- *Prop. 4.0.14*：$`\lambda_\infty(C/\bar yC) = p^{-nd}\,e(\bar y; A_n\otimes_A R)`。特に $`\lambda_\infty(C/\mathfrak{m}_A C) = \operatorname{rank}_A R`。

- *Cor. 4.0.18*：perfectoid Hilbert–Kunz 重複度 $`e_{\mathrm{perfd}}(I) = \lambda_\infty(C/IC)` は $`e(I)` 以下で、$`I` がパラメータイデアルなら等号。

CLMST には、複体の Euler 特性、$`K_0`、Dutta 重複度、lim CM 列は現れない。

*概念の対応*

- この解説　／　CLMST　／　関係
- 長さ関数 $`\lambda`（定義 4.1）　／　正規化長さ $`\lambda_\infty`（Def. 2.2.1）　／　$`\lambda_\infty` はその一例
- 長さ $`0` の加群による Serre 商 $`\mathcal{A}_\lambda`（定義 4.5）　／　almost 加群の圏と、その上の正規化長さ（Prop. 4.0.10）　／　商は「加群 $`\to` almost 加群 $`\to\mathcal{A}_\lambda`」と続く。後半の包含は真（Lemma 4.0.13）
- 長さ付きアーベル圏（定義 3.1）　／　なし　／　CLMST は長さが almost 加群に降りることまで。忠実な長さをもつアーベル圏としての扱いと、ホモロジー的評価はこの解説の視点
- $`\lambda`-平坦（定義 4.9）　／　almost flat（Thm. 4.0.3）　／　almost flat と Prop. 4.0.10 から $`\lambda`-平坦
- $`\lambda`-CM（定義 4.14）　／　almost CM（Cor. 4.0.4）　／　almost CM と Prop. 4.0.10 から $`\lambda`-CM。定理 8.5 の混標数の場合はこの合成
- ランク、$`\lambda(C/xC) = e`　／　Prop. 4.0.14、Cor. 4.0.18　／　そのまま対応
- 弱い $`\lambda`-CM（$`\lambda`-重複度 $`=` $`0` 次の長さ）　／　パラメータイデアルで $`e_{\mathrm{perfd}} = e`（Cor. 4.0.18）　／　同じ現象
- 複体の評価、$`K_0` 上の準同型、$`e_\lambda` 公式、対称なノルム比較（命題 5.3、5.8、定理 5.9）　／　なし　／　元論文 §3–§4 をこの解説で抽象化した層

*まとめ*

CLMST が与えるのは「$`\lambda`-CM で、パラメータ商の長さが重複度に等しい長さ付き代数が存在する」という*入力の層*であり、そこへ至る論法（almost で消えるなら $`\lambda` でも消える）も Prop. 4.0.10 に書かれている。長さ付きアーベル圏に値をとるホモロジー的評価と、その上の比較の一般論は、先行研究に対応するものが見当たらない。

*解説 §B.2 BHM：lim CM 列*

*BHM がやっていること*

BHM は、正則局所環 $`T` 上の正値性を、両側の商整域 $`R = T/P`、$`S = T/Q` の「極限で CM な有限加群の列」に帰着する。

- *lim CM 列*（Def. 1.1、4.2）：有限生成 $`R` 加群の列 $`(M_n)` で、あるパラメータ系 $`x` について $`\ell H_i(x;M_n) = o(\nu(M_n))`（$`i\ge1`）となるもの。$`\nu` は極小生成元数。パラメータ系の取り方によらず（Thm. 4.6）、$`R` が整域なら $`\nu` を階数に替えてもよい（Thm. 4.17）。

- *弱い lim CM*（§4.1）：$`\chi_1(x;M_n) = o(\nu(M_n))`。lim CM なら弱い lim CM（Prop. 4.8）。弱い lim CM なら $`\lim\ell H_0(x;M_n)/\operatorname{rank} M_n = e(x;R)`（Lemma 4.16）。

- *存在*（Thm. 5.4）：標数 $`p` で $`R` が F-有限なら $`\{F^e_*R\}` は lim CM。混標数での存在は限定的。

- *正値性*（Thm. 6.1）：$`R`、$`S` がともに lim CM 列 $`(M_n)`、$`(N_n)` をもてば、$`\chi(R,S) = \lim\ell(M_n\otimes N_n)/(\operatorname{rank} M_n\cdot\operatorname{rank} N_n)\ge1`。

Thm. 6.1 の証明は3段である。

1. 消滅定理と双加法性により、各 $`n` で厳密に $`\chi(M_n,N_n) = \operatorname{rank} M_n\cdot\operatorname{rank} N_n\cdot\chi(R,S)`。

2. 両側のパラメータ系の Koszul 複体を同時に使う多重 Tor の評価で、$`i\ge1` の $`\ell\operatorname{Tor}_i(M_n,N_n)` は $`o(\operatorname{rank} M_n\cdot\operatorname{rank} N_n)`。

3. $`\ell(M_n\otimes N_n)\ge\nu(M_n)\nu(N_n)\ge\operatorname{rank} M_n\cdot\operatorname{rank} N_n`（Rem. 6.2）。

Galois 拡大や K 理論の降下は現れない。

*lim CM と $`\lambda`-CM*

1. \*\*lim CM は列の圏での $`\lambda`-CM である。\*\* §6.2 の列の Serre 商で、長さを $`L((V_n)) = \lim_\mathcal{U}\ell(V_n)/\nu(M_n)` とおく。lim CM は $`L(H_i(x;M_n)) = 0`（$`i\ge1`）、すなわち列 $`(M_n)` がこの圏で $`\lambda`-CM であることに当たり、全ての非単項超フィルターについて成り立つことと同値である。

  - パラメータ商の長さの有限性は自動的である（$`\nu\le\ell H_0\le\ell(R/x)\,\nu`、BHM Rem. 4.13）。

  - $`\nu` で正規化すると $`L((M_n/\mathfrak{m} M_n)) = 1` で、非自明性も自動的である。BHM で正値性が $`\nu\ge\operatorname{rank}` から出るのはこのためである。

  - 弱い lim CM は弱い $`\lambda`-CM（$`\lambda`-重複度 $`=` $`0` 次の長さ）に当たる。$`\lambda`-重複度は Serre の公式から自動的に $`\operatorname{rank}\cdot e(x;R)` で、BHM Lemma 4.16 はこの形である。

1. BHM の対象は代数ではなく加群の列だが、3 の一般論は $`C` の代数構造をほとんど使わないので、この違いは問題にならない。

2. \*\*標数 $`p` では同じものの二つの見方である。\*\* 列として $`\{F^e_*R\}` は lim CM（BHM Thm. 5.4）、極限として $`R_{\mathrm{perf}}` と $`\lambda_\infty` は $`\lambda`-CM（Roberts の Frobenius ホモロジー定理、定理 8.5 の標数 $`p` の場合）。正規化は BHM が $`\nu`、$`\lambda_\infty` が $`p^{ed}` で、比は Hilbert–Kunz 重複度のような定数である（BHM Lemma 5.3）。

3. *混標数では二つの見方が分かれる。* $`\lambda`-CM 代数（型 (ii)）を lim CM 列（型 (iii)）に降ろすには、$`\lambda` が $`D` 上有限な段で計算できる必要がある。Ishiro–Shimomoto（arXiv:2509.06527、Thm. 3.17）は、$`D` 上の perfectoid tower があればその段が lim CM 列になることを示した。CLMST の $`\lambda`-CM 代数は正則な基底 $`A` の塔で $`\lambda` を測るので、$`D` 上の lim CM 列には直接は降りない。

4. *列の使い方が逆である。* BHM では列は係数（CM な対象）の側にあり、評価されるのは単一の有限加群どうしの Tor である。元論文の §6 では CM な対象は単一の $`\lambda`-CM 代数 $`C_E` で、列は評価される自由複体の側にある。§6.2 の列の Serre 商は、どちらの使い方も同じ形で扱える。元論文の有限近似で作る有限長 $`B` 加群の列 $`M_n` は $`D` 上の lim CM 列ではなく、$`C_D` の $`\lambda`-CM 性をパラメータ商で $`B` に移したもの（$`\lambda` の意味で射影次元 $`\le l`、補題 5.14）を列の側に映したものである。

*正値性の二つの証明の対比*

- 　／　BHM Thm. 6.1　／　元論文
- CM な対象　／　両側の lim CM 列（有限加群、型 (iii)）　／　両側の $`\lambda`-CM 代数（有限でない、型 (ii)）
- 存在　／　混標数では未知　／　CLMST により無条件
- $`\chi(D,E)` との比較　／　消滅定理だけで厳密に階数倍　／　有理 K 理論の降下（定理 5.9）と Galois 閉包、ランク無視の圏
- 高次の消滅　／　両側の Koszul を同時に使う多重 Tor　／　$`D` 側の $`\lambda` 版 Auslander–Buchsbaum と $`E` 側の新交叉型の消滅
- 正値性　／　$`\nu\ge\operatorname{rank}`　／　非自明性（系 8.7）と生成元数の下界

CM な対象が有限加群なら、普通の長さで測れるので、二つの評価が基底から来る類で一致すること（定理 5.9 の仮定）は消滅定理から自動的に出る。巨大代数ではそうならないので、元論文は降下で補う。この意味で、元論文の主定理は「BHM Thm. 6.1 の $`\lambda`-CM 代数版」と読める。BHM では入力（両側の lim CM 列）の存在が混標数で未知であるのに対し、元論文の入力（両側の $`\lambda`-CM 代数）は CLMST により存在し、代償として比較に降下とランク無視の圏が要る。

*確かめていないこと*

- BHM Thm. 4.6（パラメータ系への非依存性）の $`\lambda`-CM 版が一般の $`\lambda` で成り立つか。BHM の証明は有限加群の長さの評価を使う。解説では「任意のパラメータ系」を定義に入れているので影響はない。

- lim CM 列から巨大 CM 加群が出ること（BHM §9、Dietz 閉包）の $`\lambda`-CM 版。

- BHM §6 の番号が Crelle 版でも同じか。

*解説 §B.3 Lech の論文*

元論文と同日に、同じ方法を使う論文が二つ公開されている。OpenAI, \*Lech's multiplicity conjecture\* と、OpenAI, \*A Complete Local Domain without a Small Cohen–Macaulay Module\*（いずれも 2026-09-23、openai/math の \`preprints/\` 以下）である。前者も長さ付き代数とその Serre 商という同じ枠組みを使い、有限加群の列（Ma の弱い lim Ulrich 列）の代わりに $`\lambda`-CM 代数と短い複体の一様な評価を使う。これらとの関係は、Lech の論文の解説（\`exposition/ja/lech-ja.tex\`、PDF は同じ場所）の「Serre の論文との関係」の節にまとめた。

# 拡大すると高次の項が消える理由（直感的な説明）

%%%
number := false
tag := "paper-supplement-08-vanishing-at-scale"
%%%

この付録は、定理 8.5 の $`\lambda`-CM 性がなぜ成り立つのかを、直感的な水準で説明する。議論はまだ精密ではなく、確かめていない主張を含む。精密化すべき点は最後にまとめる。

*解説 §C.1 何が消え、何が残るのか*

$`D = R/P`、$`E = R/Q` は一般には CM でなく、$`\operatorname{Tor}_i^R(D,E)`（$`i>0`）が残りうる。そのため、$`\chi(D,E)` の各項を見ても正値性はわからない。元論文の証明は、この状況を次の二つに分けて扱う。

1. *残る部分*：Euler 特性。$`D`、$`E` を $`\lambda`-CM 代数 $`C_D`、$`C_E` に拡大して $`\lambda` で測ると、Euler 特性はランク倍 $`r_D r_E\,\chi(D,E)` になる。$`C_D` は $`R` 上有限でないので、この等式に K 理論の降下と有限近似（§5–§6）が要る。

2. *消える部分*：拡大した側の高次ホモロジー。$`C_D`、$`C_E` が $`\lambda`-CM なので、新交叉型の消滅（補題 5.10）と $`\lambda` 版 Auslander–Buchsbaum（補題 5.14）により、正の次数のホモロジーは $`\lambda` が $`0` になる。$`0` 次の項は非自明性（系 8.7）から正である。

消えるのは「$`\lambda` で測ると $`0`」という意味であり、群として $`0` になるわけではない。また、元の $`\operatorname{Tor}_i^R(D,E)` が消えるわけでもない。元の側に戻すのは Euler 特性という不変量だけである。

以下では、2 の前提である「拡大すると $`\lambda`-CM になる」ことを三つの見方で説明する。

*解説 §C.2 見方 1：CM でないことは、正則な基底の上で平坦でないこと*

$`A` を $`D` の中の正則な基底（Cohen–Gabber）とし、$`D` は $`A` 上有限とする。

- Auslander–Buchsbaum により、$`D` が CM であることと、$`D` が $`A` 上自由であることは同値である。

- $`A` のパラメータ系 $`t` について $`H_i(t;D) = \operatorname{Tor}^A_i(A/t, D)` なので、高次 Koszul ホモロジーは $`D` が $`A` 上平坦でない度合いを測っている。

したがって、拡大の目標は「$`D` を $`A` の塔の上でほぼ平坦にすること」と言い換えられる。CLMST の Thm. 4.0.3（$`C` は $`A` 上 $`g`-almost flat）はまさにこの形の主張である。補題 5.14 は、この見方を $`\lambda` の側で逆向きに使ったもの（$`\lambda`-CM なら $`\lambda` の意味で平坦）と読める。

*解説 §C.3 見方 2：欠陥は低次元にあり、主要項に比べて小さい*

標数 $`p` では、増大度の比較として理解できる。例として Macaulay の曲線

$$`D = k[[s^4, s^3t, st^3, t^4]]`

を考える。$`\dim D = 2`、$`\operatorname{depth} D = 1` で、$`H^1_\mathfrak{m}(D)\cong k` である。

- パラメータ系 $`z` を $`q` 乗すると、主要項は $`\ell(D/z^{[q]})\approx q^2 e(z;D)` と $`q^2` の速さで増える。

- 一方、高次の項 $`\ell H_1(z^{[q]};D)` は $`q` によらず有界である（一般化 CM 環で、局所コホモロジー $`H^1_\mathfrak{m}(D)` の長さで抑えられる。この例での計算は未確認）。

- $`D^{1/q}` の段で $`\lambda = \ell/q^h` と正規化すると、主要項は $`e(z;D)` に収束し、欠陥は $`O(q^{-2})\to 0` となる。

一般の場合も、Roberts の Frobenius ホモロジー定理 $`\ell H_i(z^{[q]};D) = o(q^h)`（$`i>0`）が同じことを言っている。CM でない欠陥はパラメータを深くしても主要項ほど速くは増えない。$`D^{1/q}` に移ることは「パラメータを深くして体積で割る」操作であり、$`\lambda` はこの割り算を極限まで済ませた量である。この意味で、$`D_{\mathrm{perf}}` の $`\lambda`-CM 性は $`\{F^e_*D\}` が lim CM 列であること（BHM Thm. 5.4、§B.2）の極限版である。

ここで効いているのは $`D` のすべての元の $`q` 乗根をとること（$`D^{1/q}`）であって、基底 $`A` のパラメータの $`q` 乗根を足すこと（$`D\otimes_A A^{1/q}`）ではない。後者は平坦な基底変換で、それだけでは欠陥は減らない（§C.8）。

*解説 §C.4 見方 2 の補足：ホモロジーの次数ごとの増大度*

見方 2 で起きていることを、次数ごとに分けて書く。以下は標数 $`p` の話である。

*固定したパラメータが、塔の上では深い冪になる*

$`D^{1/q}` は Frobenius によって環として $`D` と同型であり、この同型で $`D` の元 $`z` は $`z^q` に対応する。言い換えると、$`D^{1/q}` のパラメータ系 $`z^{1/q}` から見れば、最初に固定したパラメータ系 $`z` は $`q` 乗という深い冪である。したがって

$$`\lambda H_i(z; D^{1/q}) = q^{-h}\,\ell_D H_i(z^{[q]}; D)`

であり、$`\lambda` を計算することは「同じ形の環で、パラメータ系をどんどん深い冪にして Koszul ホモロジーの長さを測り、体積 $`q^h` で割る」ことである。基底の塔 $`A^{1/q}` でも同じで、$`A` のパラメータ $`t_j` は $`A^{1/q}` の上では $`(t_j^{1/q})^q` である。

*次数ごとの増大度*

- 次数　／　対応する局所コホモロジー　／　$`\ell_D H_i(z^{[q]};D)` の増大度　／　$`q^{-h}` で割ると
- $`i = 0`　／　$`H^h_\mathfrak{m}(D)`（最上次。双対は次元 $`h`）　／　$`\approx e(z;D)\,q^h`　／　$`e(z;D)`
- $`i\ge 1`　／　$`H^{h-i}_\mathfrak{m}(D)`（最上次より下。双対は次元 $`\le h-i`）　／　$`o(q^h)`（Roberts）。目安は $`O(q^{h-i})`（未確認）　／　$`0`

表の「対応する局所コホモロジー」は次の意味である。Koszul 複体は自己双対で $`H_i(z;D)\cong H^{h-i}(z;D)` であり、$`H^j_\mathfrak{m}(D) = \varinjlim_t H^j(z^t;D)` である。したがって、パラメータを深くしたときの $`H_i(z^t;D)` は $`H^{h-i}_\mathfrak{m}(D)` を近似している。局所双対により、$`H^j_\mathfrak{m}(D)` の Matlis 双対の次元は $`j` 以下である。

- $`i = 0` の項は最上次の $`H^h_\mathfrak{m}(D)` に対応し、$`D` の次元 $`h` をそのまま感じる。だから $`q^h` の速さで増える。

- $`i\ge 1` の項は、それより下の $`H^{h-i}_\mathfrak{m}(D)` に対応する。これは「次元 $`h-i` 以下のもの」で、パラメータの $`q` 乗で切り取ると、目安として $`q^{h-i}` 程度にしか増えない。次数が上がるほど増大度は小さくなる。

CM であることは $`H^j_\mathfrak{m}(D) = 0`（$`j<h`）、つまり最上次以外の局所コホモロジーが消えることだった。正規化した長さ $`\lambda` で見ることは、最上次（次元 $`h`）だけを残し、それより下を無視することに当たる。だから $`\lambda` で見ると「CM のように振る舞う」。

Macaulay の曲線（$`h = 2`）では、$`H^1_\mathfrak{m}(D)\cong k` は有限長（双対の次元 $`0`）なので、$`\ell H_1(z^{[q]};D)` は有界である。これは目安 $`O(q^{h-1}) = O(q)` よりさらに小さい。

*混標数では仕組みが違う*

混標数で塔の段 $`A_n\otimes_A D` に移るだけなら、これは平坦な基底変換なので、$`\ell H_i(z;A_n\otimes_A D)` と体積 $`p^{nh}` は同じ割合で増え、正規化した欠陥は減らない（§C.8）。混標数では、増大度の差ではなく、perfectoid 化による分岐の希釈（見方 3）が欠陥を消している。上の次数ごとの描像は、そのままでは標数 $`p` の話である。

*解説 §C.5 平坦でない場所と Frobenius：Koszul、局所コホモロジー、$`W` の関係*

この小節では、見方 1（平坦性）と見方 2（増大度）を一つの描像にまとめ、Koszul 複体による見方、局所コホモロジーによる見方、平坦でない場所 $`W` による見方がどう対応するかを書く。標数 $`p` で、$`A\subseteq D` を正則な基底、$`t` を $`A` の正則パラメータ系、$`r = \operatorname{rank}_A D` とする。剰余体は perfect とする。

*何で割っているのか*

これまで「体積で割る」と書いたが、正確には次のとおりである。$`F^n_*A = A^{1/q}` は $`A` 上ランク $`q^h` の自由加群である（Kunz）。$`D^{1/q} = F^n_*D` を $`A` 加群として見て、その Betti 数

$$`\beta_i^A(F^n_*D) = \ell\,\operatorname{Tor}_i^A(k, F^n_*D) = \ell\,H_i(t; D^{1/q}) = \ell\,H_i(t^{[q]}; D)`

を、$`F^n_*A` のランク $`q^h` を単位として測る。$`\lambda` はこの正規化の極限である。

- $`i = 0`：$`\beta_0^A(F^n_*D)/q^h = \ell(D/t^{[q]}D)/q^h\to e(t;D) = r`。

- $`i\ge 1`：$`\beta_i^A(F^n_*D)/q^h\to 0`（Roberts）。

つまり $`F^n_*D` は、$`A` 上で「ランク $`r q^h` の自由加群に、相対的に小さい誤差を加えたもの」に近づいていく。これが $`\lambda`-平坦でランク $`r`（定義 4.9）の中身であり、BHM の言葉では $`\{F^n_*D\}` が $`A` 上の lim CM 列であることに当たる。

*基底の根と、全ての元の根の違い*

- 基底の根だけを足すと、$`A` 加群として $`D\otimes_A A^{1/q}\cong D^{\oplus q^h}` である。主要項も欠陥も同じく $`q^h` 倍になるので、比は変わらない。

- 全ての元の根をとる $`F^n_*` は、各部分をその次元に応じて拡大する。次元 $`w` の素イデアル $`\mathfrak{p}` について、$`F^n_*(A/\mathfrak{p})` の $`A/\mathfrak{p}` 上の階数は $`q^w` である（剰余体が perfect なので、超越次数 $`w` の体の $`q` 乗根拡大の次数は $`q^w`）。

$`F^n_*` は次元 $`h` の部分を $`q^h` 倍に、次元 $`w<h` の部分を $`q^w` 倍にする。欠陥がより低い次元にあれば、ランク $`q^h` を単位として測ったときに消えていく。

*平坦でない場所 $`W` と、その層別*

$`D` は $`A` 上有限なので、$`A` 上の有限な自由分解をもつ。$`E^c = \operatorname{Ext}^c_A(D,A)` とおく。

- $`D_\mathfrak{p}` が $`A_\mathfrak{p}` 上自由であることと、全ての $`c>0` で $`E^c_\mathfrak{p} = 0` であることは同値である。したがって平坦でない場所は $`W = \bigcup_{c>0}\operatorname{Supp}E^c` で、Auslander–Buchsbaum によりこれは $`D` が CM でない場所の像である。

- $`E^c_\mathfrak{p}\neq0` なら $`\operatorname{pd}D_\mathfrak{p}\ge c` で、$`\operatorname{pd}D_\mathfrak{p}\le\operatorname{ht}\mathfrak{p}` なので $`\operatorname{ht}\mathfrak{p}\ge c` である。よって $`\dim\operatorname{Supp}E^c\le h-c`。$`c` は「平坦でない度合いの次数」で、次数が高いほど小さい場所に住む。

- $`D` は整域なので生成点で平坦であり、$`\dim W<h` である。$`D` が $`S_2`（例えば正規）なら、高さ $`2` 以下の素イデアルで CM なので、$`\dim W\le h-3` である。

*局所コホモロジーとの関係*

正則な $`A` 上の局所双対により、$`j<h` について

$$`H^j_\mathfrak{m}(D)^\vee\cong\operatorname{Ext}_A^{h-j}(D,A) = E^{h-j}`

である（$`\mathfrak{m}`-冪ねじれは $`\mathfrak{m}_A`-冪ねじれと同じなので、$`H^j_\mathfrak{m}(D) = H^j_{\mathfrak{m}_A}(D)`）。つまり、$`j<h` の局所コホモロジーは、次数 $`c = h-j` の平坦でない部分 $`E^c` の Matlis 双対である。§C.4 の $`K^j` は $`E^{h-j}` のことで、$`\dim K^j\le j` は上の $`\dim\operatorname{Supp}E^c\le h-c` と同じ主張である。CM であること（$`H^j_\mathfrak{m}(D) = 0`、$`j<h`）と、$`A` 上自由であること（$`E^c = 0`、$`c>0`）が同値であることも、この対応から読める。

*Koszul 複体との関係*

$`K(t;A)` は $`k` の自由分解なので、$`H_i(t;D) = \operatorname{Tor}^A_i(k,D)` は閉点での平坦性の判定である。Auslander–Buchsbaum により、$`H_i(t;D)\neq0` となる最大の $`i` は $`h-\operatorname{depth}D` で、これは $`0` でない最小の局所コホモロジー $`H^{\operatorname{depth}D}_\mathfrak{m}(D)` に対応する。より一般に、有限長加群 $`V` について $`\operatorname{Tor}_i^A(V,D)^\vee\cong\operatorname{Ext}^i_A(D,V^\vee)` を $`\mathbf{R}\!\operatorname{Hom}_A(D,A)\otimes^{\mathbf{L}}_A V^\vee` で計算すると、スペクトル系列

$$`\operatorname{Tor}^A_{c-i}(E^c, V^\vee)\ \Longrightarrow\ \operatorname{Tor}_i^A(V,D)^\vee`

が得られる。$`V = A/t^{[q]}`（Gorenstein なので $`V^\vee\cong V`）とすると

$$`H_{c-i}(t^{[q]};E^c)\ \Longrightarrow\ H_i(t^{[q]};D)^\vee \qquad (c\ge i)`

で、§C.4 のスペクトル系列は、この形で書くと $`W` の層別と直接つながる。Koszul の次数 $`i` に寄与するのは $`c\ge i` の $`E^c` だけ、すなわち次元 $`h-i` 以下の場所に住む欠陥だけである。「Koszul の次数が上がるほど、効く欠陥の住む場所が小さくなる」というのが、次数と増大度の対応の正体である。

Koszul 複体を深い冪 $`t^{[q]}` にとることは、局所コホモロジー（$`H^j_\mathfrak{m}(D) = \varinjlim_t H^j(t^t;D)`、$`H_i(t;D)\cong H^{h-i}(t;D)`）に近づくことでもある。元論文は局所コホモロジーを表に出さず Koszul 複体で計算しているが、上のスペクトル系列は、Koszul 複体の計算が実質的に「$`E^c` を箱 $`A/t^{[q]}` で切り取った量」を数えていることを示している。

*三つの見方の対応*

- 見方　／　欠陥を表すもの　／　$`F^n_*`（$`D^{1/q}`）での振る舞い
- Koszul 複体　／　$`H_i(t;D) = \operatorname{Tor}^A_i(k,D)`（$`i\ge1`）　／　$`H_i(t^{[q]};D) = \beta_i^A(F^n_*D)`
- 平坦でない場所　／　$`E^c = \operatorname{Ext}^c_A(D,A)`（$`c\ge1`）、台は $`W`、$`\dim\le h-c`　／　次元の分だけ拡大：おおよそ $`q^{\dim E^c}` 倍
- 局所コホモロジー　／　$`H^j_\mathfrak{m}(D) = (E^{h-j})^\vee`（$`j<h`）　／　Frobenius 作用で同じく拡大
- 対応　／　次数 $`i` に効くのは $`c\ge i`、すなわち $`j\le h-i`　／　増大度は目安 $`q^{h-i}`、正規化すると $`O(q^{-i})`

*まとめ*

1. 平坦なら高次の Koszul ホモロジーは消える。

2. $`D` は平坦ではないが、平坦でない部分 $`E^c` は低次元の場所 $`W` にあり、次数 $`c` が高いほど小さい場所にある。$`E^c` の双対が局所コホモロジーである。

3. $`F^n_*` は各部分をその次元の分だけ拡大するので、平坦な主要部分（次元 $`h`）に比べて $`E^c` は相対的に小さくなる。

4. $`F^n_*A` のランク $`q^h` を単位として測ると、$`F^n_*D` はランク $`r` の自由加群に近づく。Koszul の次数 $`i` の欠陥は次元 $`h-i` 以下の部分から来るので、$`O(q^{-i})` で消える。

基底の根だけを足すこと（$`D\otimes_A A^{1/q}`）では全体が一様に $`q^h` 倍になるだけで、何も起きない（§C.8）。

*$`W` は小さくならない*

冪根をとっても、平坦でない場所 $`W` そのものは変わらない。

- $`D^{1/q}` は環として $`D` と同型で、Frobenius は $`\operatorname{Spec}` の上で同相なので、$`D^{1/q}` が CM でない場所は $`D` と同じである。$`F^n_*D` は $`A` 上有限なので、Auslander–Buchsbaum により $`A` 上平坦でない場所も同じ $`W` である。

- 極限の $`D_{\mathrm{perf}}` も、$`W` の点では平坦にならない。$`\lambda`-平坦は本当の平坦ではない（$`\lambda` で $`0` でも群として $`0` ではない、と同じこと）。

変わるのは場所ではなく相対的な大きさだけである。平坦な主要部分は $`q^h` 倍、$`W` の上の欠陥は $`q^{\dim W}` 倍程度にしかならないので、ランク $`q^h` を単位として測ると欠陥の割合が $`0` に近づく。測度論で言えば、正方形の中の曲線は空でなくても面積 $`0` である、という状況に近い。$`\lambda` は「次元 $`h` の大きさ」を測る量で、Frobenius の塔はその測り方を有限段で近似している。

*確かめていないこと*

- 「$`F^n_*` が次元 $`w` の部分をおおよそ $`q^w` 倍にする」ことを、高次の Tor（Betti 数）について正確な評価にすること。$`0` 次（生成元数）は Hilbert–Samuel から出るが、高次は §C.4 のステップ 2 と同じ問題である。

- スペクトル系列の添字の正確な形（CM の場合と一般化 CM の場合で整合することは確認した）。

- 混標数で perfectoid 化が $`p` を法として $`F_*` の役をする（tilt）とき、同じ描像がどこまで成り立つか。

*解説 §C.6 定理 2.5 の証明との対応*

ここまでの直感的な議論は、元論文 Theorem 2.5（定理 8.5）の標数 $`p` の場合の証明に当たる。証明の各ステップと対応を並べる。設定は次のとおり。基底は Lemma 2.2 の $`A = k[[t_1,\dots,t_h]]\subseteq D`（有限、生成的に分離的、剰余体は同じ）、塔は $`A_n = A^{1/q}`、$`\Lambda = \varinjlim A_n`。長さは Lemma 2.3 の $`\lambda_\infty` で、有限段の $`A_n` 加群 $`V_n` について $`\lambda_\infty(V_n\otimes\Lambda) = p^{-nh}\,\ell_{A_n}(V_n)`（(2.2)）。$`p^{nh}` は $`A_n` の $`A` 上の階数である。

- 　／　証明のステップ　／　直感的な議論との対応
- (1)　／　$`C_D = D_{\mathrm{perf}}`。$`B_q = \Lambda\otimes_{A^{1/q}}D^{1/q}` は $`C_D` に入り（生成的分離性による線形無関性）、$`q` とともに増えて $`C_D` に至る　／　「全ての元の根」は $`D^{1/q}` の部分。$`B_q` は $`(A^{1/q}\subset D^{1/q})\cong(A\subset D)` を $`\Lambda` へ平坦に基底変換したもので、「基底の根」は測るための土台としてだけ入る
- (2)　／　有限段の公式 $`\lambda_\infty(B_q/HB_q) = q^{-h}\,\ell_D(D/H^{[q]})`　／　ランク $`q^h` を単位にする（(2.2) の $`p^{-nh}`）。Frobenius 同型 $`D^{1/q}\cong D` で、固定した $`H` が $`H^{[q]}`（深い冪）に移る
- (3)　／　トレースの分母 $`g`（$`A[1/g]\to D[1/g]` が有限エタール）による制御 (2.7)：$`g^{1/q}C_D\subseteq B_q`。$`B_q/H\to C_D/H` の核は $`g^{1/q}` で消され、$`\lambda\le q^{-h}\ell(D/(H^{[q]},g)) = O(q^{-1})`　／　分岐から来る誤差。$`V(g)`（次元 $`h-1`）に住むので $`q^{h-1}` でしか増えない。「$`F_*` は次元の分だけ拡大する」原理が論文中で明示的に（Hilbert–Samuel として）使われている箇所。$`W\subseteq V(g)`（エタールなら平坦）
- (4)　／　Hilbert–Kunz の極限と Lemma 2.4 から (2.8)：$`\lambda(C_D/HC_D) = e_{\mathrm{HK}}(H,D)`　／　$`0` 次の主要項（$`\beta_0/q^h` の極限）
- (5)　／　パラメータ系 $`z` について $`\lambda_\infty H_i(z;B_q) = q^{-h}\ell_D H_i(z^{[q]};D)`。Roberts により $`i>0` で $`0` に近づく　／　CM でないことから来る誤差。高次 Koszul $`=` 高次 Betti 数で、$`W` 上の $`E^c` から来る（§C.5）。論文は $`o(q^h)` だけを使い、次数ごとの速さ、$`W`、局所コホモロジーは表に出さない
- (6)　／　$`H_i(z;C_D) = \varinjlim H_i(z;B_q)`。共通の消去イデアル $`(z)` があるので、Lemma 2.4（$`\lambda(V_a)\to0` なら余極限の $`\lambda` は $`0`。単射性は不要）から (2.4)　／　「$`W` は消えないが $`\lambda` では $`0`」の正確な形。有限段で比が $`0` に近づくことを、極限での $`\lambda = 0` に変える
- (7)　／　Koszul の Euler 特性 $`\sum(-1)^i\ell H_i(z^{[q]};D) = q^h e` と (2.8) から (2.5)。$`e((t),D) = \operatorname{rank}_A D` から (2.6)　／　$`F^n_*D` が「ランク $`r q^h` の自由加群」に近づくことの $`r` の部分

*読み取れること*

1. 誤差は二種類あり、どちらも有限段で数えている。分岐から来る誤差（ステップ (3)）は $`V(g)` の次元による $`O(q^{-1})` で、論文に明示されている。CM でないことから来る誤差（ステップ (5)）は Roberts の $`o(q^h)` に任されている。

2. トレースの制御が要るのは $`0` 次だけである。一般の $`H` で $`\lambda(C_D/HC_D)` の値を正確に出すには、有限段から極限への写像の核を抑える必要がある。高次は $`0` になることだけ言えばよいので、Lemma 2.4 により単射性なしで済む。

3. $`W`、$`E^c`、局所コホモロジー、次数ごとの速さは論文に出てこない。これらは Roberts の定理の中身を開いたときの描像で、論文の証明はそれらを使わずに完結している。

混標数では、論文はステップ (1)–(7) を CLMST の Cor. 4.0.4、Prop. 4.0.10、4.0.14 でまとめて置き換えている（定理 8.5）。

*解説 §C.7 見方 3：混標数では分岐が薄まる（almost purity）*

混標数には Frobenius がないので、見方 2 の代わりに次の仕組みが働く。

- $`A[1/g]\to D[1/g]` が有限エタールとなる $`g\neq0` をとる。$`g` の外では $`D` は $`A` 上平坦であり、平坦でない部分は分岐の場所 $`V(g)` に集中している。

- パラメータの $`p` 冪根をすべて添加した塔 $`A_\infty` への基底変換 $`D\otimes_A A_\infty` は平坦なので、それだけでは平坦でない度合いは変わらない。効くのはその後の perfectoid 化で、これは $`D/p` 上の Frobenius を全射にする操作、つまり「$`D` のすべての元の、$`p` を法とした $`p` 乗根を足す」ことに当たる。これによって分岐は $`g^{1/p^n}` 程度にまで薄まる（almost purity）。原型は、$`\mathbb{Q}_p` に $`p` の冪根を添加していくと分岐がほぼ消える、という Tate の現象である。

- その結果、平坦でない部分は「任意の $`n` について $`g^{1/p^n}` で消える」大きさに押し込められる。これが almost zero である（CLMST Cor. 4.0.4）。群としては残りうるが、体積を測る $`\lambda` では $`0` になる（CLMST Prop. 4.0.10）。

*解説 §C.8 冪根の次数が剰余標数と一致することの意味*

見方 2、3 で添加する冪根の次数は、剰余標数 $`p` と一致していなければならない。理由を以下に述べる。

*トレースによる分裂*

$`D` を正規整域、$`D'` をその次数 $`d` の有限拡大とする。$`d` が $`D` で可逆なら、$`(1/d)\operatorname{Tr}\colon D'\to D` は $`D` 線形な分裂を与えるので、$`H^i_\mathfrak{m}(D)` は $`H^i_\mathfrak{m}(D')` の直和因子になる。したがって、次数が $`p` と素な拡大では、CM でない欠陥は群として必ず残る。

- 剰余標数 $`0` では全ての有限拡大がこれに当たる。このため $`R^+` は（次元 $`3` 以上で）CM にならない。

- 欠陥を群として消せる可能性があるのは、次数が $`p` で割り切れる拡大だけである。Bhatt による $`R^+` の CM 性や perfectoid 化の almost CM 性は、この分裂が壊れることを利用している。

*平坦な基底変換は正規化した欠陥を変えない*

$`\lambda` で測る場合も、$`p` と素な冪根は役に立たない。$`\ell\neq p` とし、$`A_n = A[t^{1/\ell^n}]` とおくと、$`A_n` は $`A` 上自由で、$`D\otimes_A A_n` は $`D` の平坦な基底変換である。$`A_n` 上で平坦でない度合いは $`D` と同じで、Koszul ホモロジーの長さもランクも同じ割合 $`\ell^{nh}` 倍になるので、正規化した欠陥は減らない。同じことは $`p` 冪根でも、基底 $`A` のパラメータに根を足すだけなら成り立つ。

*すべての元の根をとれるのは $`p` のときだけ*

効いているのは $`D` のすべての元の根をとる操作である。

- 標数 $`p` では $`D^{1/q}` がそれに当たり、$`D\otimes_A A^{1/q}\to D^{1/q}`（相対 Frobenius）は基底変換ではない。環として $`D^{1/q}\cong D` なので、Koszul ホモロジーは $`H_i(z^{[q]};D)` になり、Roberts の定理が使える。

- これは $`x\mapsto x^p` が環準同型であることによる。$`x\mapsto x^\ell`（$`\ell\neq p`）は加法的でないので、すべての元の $`\ell` 乗根を添加するとランクを制御できない巨大な環になる。

- 混標数でも、perfectoid 化は $`D/p` 上の Frobenius を全射にする操作で、$`x\mapsto x^p` が環準同型になるのは $`p` を法としたときだけである。したがって $`p` は剰余標数でなければならない。塔 $`A_\infty` でも、$`t_1 = p` そのものの冪根 $`p^{1/p^n}` を添加している。

*分岐の言葉で*

馴分岐（$`p` と素な部分）は、$`\ell` 冪根を添加すれば Abhyankar の補題で厳密に消える。しかしそのとき起きているのは平坦な基底変換で、CM でない欠陥には効かない。野生分岐（$`p` の部分）は $`p` 冪根を添加しても厳密には消えず、almost にしか消えない（Tate、Faltings）。それでも、欠陥を $`\lambda` で見えなくする仕組みはこれしかない。剰余標数 $`0` の場合を直接示せず、正標数に帰着するしかないのも同じ理由による（Lech の論文 §7 の帰着はその例である）。

*解説 §C.9 まとめと、他の構成との関係*

元の $`D` で高次の項が生きているのは、$`D` が正則な基底の上で平坦でないからである。その欠陥は低次元の場所や分岐の場所に集中している。基底に冪根を足す（平坦な基底変換）だけではこの欠陥は変わらないが、Frobenius や perfectoid 化で $`D` のすべての元の $`p` 乗根をとると、主要項だけが大きくなり、体積で正規化すれば欠陥は見えなくなる。標数 $`p` では見方 2（増大度）が、混標数では見方 3（分岐の希釈）が、同じ結論を与える。

この説明からわかるように、perfectoid 化が担っているのは次の二つを同時に満たすことである。

- *CM 性*：欠陥を $`\lambda` で見えなくする（見方 3）。

- *大きさの有限性*：$`C` は $`A_\infty` 上でほぼランク $`r` なので、$`\lambda(C/zC) = e` が有限である。$`R^+` のような本物の巨大 CM 代数は $`A_\infty` 上で無限ランクなので、$`\lambda(R^+/zR^+)` が無限大になり、そのままでは使えない。

原理的には、この二つを満たす長さ付き代数なら perfectoid である必要はない。$`D`、$`E` が小さな CM 加群をもてば、型 (i) の議論（Hochster）で済み、K 理論の降下は不要になる。しかし一般の $`D` について混標数でこれを供給する方法は、現在のところ perfectoid 化しか知られていないと思われる。perfectoid 化は常に存在する（Bhatt–Scholze）が、$`R` 上有限ではない。元論文の後半（K 理論の降下、Galois 閉包、ランク無視の圏、有限近似）は、この「有限でない」ことの帰結である。

*解説 §C.10 精密化すべき点*

- 見方 1 は $`A` のパラメータ系についての説明である。$`\lambda`-CM（定義 4.14）は $`D` の任意のパラメータ系を要求する。$`A` 上の（almost）平坦性から $`D` の任意のパラメータ系の消滅が出る仕組みを確認する（CLMST Cor. 4.0.4 は $`A_n\otimes_A D` の任意のパラメータ系を扱う）。

- 見方 2 の例で $`\ell H_1(z^{[q]};D)` が有界であることを計算で確かめる。一般化 CM 環での評価の正確な形を文献で確認する。

- 標数 $`p` で、$`H_i(z;D_{\mathrm{perf}})`（$`i>0`）が群として $`0` でない例があるか。almost zero になるか（混標数と同じ形か）を確認する。

- 見方 3 の almost purity の正確な主張（どの塔の上で、どのイデアルについて almost か）と、CLMST Thm. 4.0.3 の証明の中での使われ方を確認する。Tate の例は比喩として正確な形に直す。

- §C.8 のトレースによる分裂の議論は群としての消滅についてのもので、正規化した欠陥については平坦な基底変換の議論しかしていない。$`p` と素な次数の、基底変換でない有限拡大の列で正規化した欠陥が $`0` に近づかないことは確かめていない。Abhyankar の補題の適用（どの環で、どの分岐因子について）も正確な形にする。

- 「混標数で一般の $`D` に $`\lambda`-CM 代数を供給する方法は perfectoid 化しかない」という主張は、文献調査に基づくものではない。

- §C.4 の目安 $`\ell H_i(z^{[q]};D) = O(q^{h-i})` は確かめていない。$`H_i(z^t;D)` と $`H^{h-i}_\mathfrak{m}(D)` の関係（推移写像の像と核）を正確に追い、文献（Frobenius 関手と有限長ホモロジーの複体の増大度の評価）を確認する。混標数の perfectoid 化について、次数ごとの描像に当たるものがあるかも確認する。

# $`\lambda`-平坦を主役にした整理の検討

%%%
number := false
tag := "paper-supplement-09-lambda-flatness"
%%%

この付録では、$`\lambda`-CM の代わりに $`\lambda`-平坦（almost flat の対応物）を基本の概念にして議論を整理できるかを検討する。結論を先に書くと、本文のほとんどの箇所は $`\lambda`-平坦だけで足り、$`\lambda`-CM が必要なのは $`D` 側のパラメータ商の一箇所だけである。そこを $`\lambda`-平坦から導けるかは未解決である。

*解説 §D.1 現状の定義*

- $`\lambda`-平坦（定義 4.9）：正則な基底 $`A` の上で、全ての有限長 $`A` 加群 $`V` と $`i>0` について $`\lambda\operatorname{Tor}_i^A(V,C)=0`。$`k` で判定でき（補題 4.10）、正則パラメータ系の条件と同値である（系 4.11）。

- $`\lambda`-CM（定義 4.14）：$`D` の任意のパラメータ系 $`x` について $`\lambda H_i(x;C)=0`（$`i>0`）。

- $`\lambda`-CM なら、$`D` 上有限な正則部分環 $`A` の上で $`\lambda`-平坦である（命題 4.15）。逆は示していない。

$`\lambda`-平坦は、有限長 $`A` 加群の圏から Serre 商 $`\mathcal{A}_\lambda` への関手 $`V\mapsto q(V\otimes_A C)` が完全関手になることと同じである（§4.3「\$\\lambda\$-平坦性の意味」）。ランク $`r` は $`\lambda\circ q(-\otimes_A C) = r\cdot\ell_A` という条件である。3 の一般論（$`K_0` への準同型、Euler 特性の比較）が使うのは、ほぼこの完全関手の性質だけである。CLMST の対応する結果は almost flat（Thm. 4.0.3）で、almost flat と Prop. 4.0.10 から $`\lambda`-平坦が出る（§B.1）。

古典的な対応は次のとおりである。

- 有限生成加群 $`M` が CM であることと、$`M` が正則な基底 $`A` の上で自由であることは同値である（Auslander–Buchsbaum）。CM 性は深さで決まり、パラメータ系の取り方によらない。

- 巨大加群では、正則な基底の上で平坦であることと、基底から来るパラメータ系が正則列であることは同値である。しかし任意のパラメータ系について正則列になる（balanced）とは限らず、balanced にするには完備化が要る（Bartijn–Strooker、Griffith。文献の主張の正確な形は未確認）。

$`\lambda`-平坦と $`\lambda`-CM の差は、後者の「基底によらない」部分にある。

*解説 §D.2 本文でどちらの条件を使っているか*

- 使う場所　／　必要な条件
- §5 の比較、§6 のランク無視の圏　／　$`A` 上の $`\lambda`-平坦とランク $`r`
- 新交叉型の消滅（補題 5.10、補題 6.11。$`E` 側）　／　$`A_E` 上の $`\lambda`-平坦（$`A_E` のパラメータ系だけを使う）
- パラメータ商と次数の上界（補題 5.14 とその修正版、§5.5。$`D` 側）　／　\*\*$`\lambda`-CM\*\*：$`R` の元 $`x` で像が $`D` のパラメータ系になるものについて、全ての $`v` で $`\lambda H_q(x^v;C)=0`（$`q>0`）

$`D` 側で使う $`x` は $`R` から来るもので、正則な基底 $`A_D` の元とは限らない。$`\lambda`-平坦だけでは足りないのはここだけである。補題 5.14 と §5.5 では $`R` 上の分解の長さを使い、$`B=R/(x)` の正則性は仮定しない。$`D` 側に必要なのは、ここでも $`x` とその冪に対する Koszul 消滅である。

*解説 §D.3 隙間を埋める方法の候補*

1. \*\*$`x` を含むように基底を選ぶ。\*\* 等標数なら $`k[[x]]\subseteq D` は正則で、$`D` はその上で有限である。しかし構成には生成的な分離性（Cohen–Gabber、補題 8.4）が要り、混標数では $`p` を基底のパラメータに含める必要がある。任意の $`x` では使えない。

2. \*\*「ある $`A` の上で $`\lambda`-平坦なら $`\lambda`-CM」を補題として示す。\*\* 有限加群なら自明だが、巨大加群の古典版では完備化が要る。一方、CLMST は almost flat の定理（Thm. 4.0.3）の系として almost CM（Cor. 4.0.4、$`A_n\otimes_A D` の任意のパラメータ系）を出している。この論法が $`\lambda` に移るなら、$`\lambda`-平坦を主役にできる。

3. \*\*$`\lambda`-CM を「$`\lambda`-平坦と、パラメータ系への非依存性」として定義し直す。\*\* 古典版の「CM $`\Leftrightarrow` 正則な基底の上で自由」との対応が最も見えやすい形である。ただし 2 を示さない限り、仮定を言い換えているだけである。

*解説 §D.4 CM は絶対的、平坦は相対的*

CM は相対的な概念ではない。有限加群 $`M` について depth $`M = \dim M` という条件で、$`R\to D` が有限な局所準同型なら深さも次元も $`R` 上と $`D` 上で同じなので、「$`R` 上 CM」「$`D` 上 CM」「$`A` 上 CM」は全て同じ意味である。一方、平坦（自由）や射影次元は、どの環の上で見るかによる相対的な概念である。

$`D` が正則局所環 $`S` の上で有限なら、Auslander–Buchsbaum により $`\operatorname{pd}_S D = \dim S - \operatorname{depth}D\ge\dim S-\dim D` で、等号は $`D` が CM であることと同値である。一つの絶対的な性質が、基底によって次のように見える。

- 基底 $`S`　／　$`\dim S`　／　CM の現れ方
- $`A`（$`D` の中の正則な基底）　／　$`h`　／　$`\operatorname{pd}_A D = 0`、すなわち $`A` 上自由（平坦）
- $`R`（$`D = R/P`）　／　$`d>h`　／　$`\operatorname{pd}_R D = d-h`（perfect）、すなわち $`R` 上の Tor を計算する複体が短い

$`D` は $`R` の商なので $`R` 上で平坦になることはなく、Serre の Euler 特性で問題になるのは $`R` 上の射影次元である。

欠陥の層も $`D` に内在的で、基底によって添字がずれるだけである。正則な $`A` と $`R` の上の局所双対から

$$`H^j_\mathfrak{m}(D)^\vee\cong\operatorname{Ext}^{h-j}_A(D,A)\cong\operatorname{Ext}^{d-j}_R(D,R),\qquad\text{すなわち}\quad \operatorname{Ext}^c_A(D,A)\cong\operatorname{Ext}^{c+(d-h)}_R(D,R)`

となる。§C.5 の $`E^c` は、$`R` の側から見れば $`d-h` を超える次数の Ext であり、平坦でない場所 $`W`（CM でない場所）も同じである。

$`\lambda` 版では、この絶対性が自動的には成り立たない。$`C_D` は $`D` 上有限でないからである。巨大加群の古典版でも、巨大 CM 加群はもともと「あるパラメータ系が正則列になる」という相対的な定義で、任意のパラメータ系について正則列になる（balanced）には完備化が要る。$`\lambda`-CM（定義 4.14）は balanced に当たる絶対的な条件として定義し、$`\lambda`-平坦（定義 4.9）は基底 $`A` に相対的な条件である。有限加群なら両者は同値だが、有限でない対象では「相対的な条件から絶対的な条件が出るか」が問題として残る。これが上の隙間の正体である。

*解説 §D.5 なぜ両側を取り替えるのか*

「$`\lambda`-CM が必要なのは $`D` 側だけ」というのは、両側の CM 性の強さが違うという意味であり、$`E` 側に CM 的な性質が要らないという意味ではない。

*古典版での役割分担*

$`D`、$`E` がともに CM なら $`\operatorname{Tor}^R_i(D,E) = 0`（$`i>0`）である。この議論は二つに分かれる。

1. \*\*$`D` が CM なら複体が短い。\*\* $`D` の $`R` 上の自由分解 $`G` は長さ $`\operatorname{pd}_R D = d-h = l` で、$`\operatorname{Tor}^R(D,E)` は長さ $`l = \dim E` の複体 $`G\otimes E` のホモロジーである。

2. \*\*$`E` が CM なら短い複体の高次が消える。\*\* $`G\otimes E` は $`E` 上の長さ $`\dim E` の有限自由複体で、ホモロジーは有限長である。$`E` が CM なら、Peskine–Szpiro の acyclicity lemma（新交叉型の議論）により正の次数のホモロジーは消える。

$`D` が CM でなければ複体の長さが $`\dim E` を超え、新交叉型の議論は何も言わない。$`E` が CM でなければ、短い複体でも高次が消える保証はない（新交叉定理は「長さが $`\dim` 以上でなければホモロジーは $`0` にならない」という下からの評価で、消滅は $`E` の深さから来る）。二つの $`l` が噛み合うのは $`h+l = d` による。BHM Thm. 6.1 が両側に lim CM 列を要求するのも同じ理由である。

*片側の平坦性で Tor が消えるのはいつか*

片側が平坦なら Tor は消えるが、それは平坦性が Tor を計算する環の上で成り立つときに限る。$`D`、$`E` は $`R` の商なので $`R` 上で平坦にはならず、手元にあるのは別の環 $`A_D` の上の平坦性である。それを $`R` 上の情報に翻訳すると「$`R` 上の Tor の複体が短い」ことしか出ない（§D.4 の表）。

片側が最良でも消えない例：$`D = R/(x_1,\dots,x_l)`（$`x` は $`R` 正則列で $`l = d-h`、$`E` の上でパラメータ系になるもの）とする。$`D` は完全交叉で CM（正則にもできる）だが、$`\operatorname{Tor}^R_i(D,E) = H_i(x;E)` であり、$`E` が CM でなければ高次の Koszul ホモロジーは消えない。この例では $`\chi = e(x;E) > 0` なので正値性は重複度として別の理由で成り立つが、「高次を消して $`0` 次だけ残す」方法は片側だけでは動かない。

*元論文での対応*

- 　／　古典版　／　元論文
- $`D` 側　／　$`\operatorname{pd}_R D = d-h`　／　$`\lambda` 版 Auslander–Buchsbaum（補題 5.14、修正版は §5.5）：$`i>d-h` で $`\lambda\operatorname{Tor}^R_i(C_D,L) = 0`。$`R` から来る $`x` を使うので $`D` に内在的な $`\lambda`-CM が要る
- $`E` 側　／　$`E` が CM なら長さ $`l` の複体は acyclic　／　$`C_E` が $`A_E` 上 $`\lambda`-平坦なら新交叉型の消滅（補題 5.10、補題 6.11）。$`A_E` のパラメータで測れる形に持っていけるので、基底に相対的な $`\lambda`-平坦で足りる

片側の平坦性だけで Tor を消す使い方も元論文にある。それは Tor が基底 $`A` の上で計算される場面で、$`\lambda`-平坦の定義そのもの（有限長 $`A` 加群 $`V` について $`\lambda\operatorname{Tor}^A_i(V,C) = 0`）や、§5 の perfect 複体での比較とランクの計算がそうである。$`R` 上の Euler 特性の高次を消すには両側が要る。二つの基底 $`A_D`、$`A_E` は別々なので、どちらか一方の上で全体を平坦にすることはできない。

取り替えるたびに Euler 特性はランク倍になり、その回収に K 理論の降下と Galois 閉包を使う。本文ではこれが置き換え 1（$`D\to C_D`、§5 の命題 7.5）と置き換え 2（$`E\to C_E`、§6 の漸近版）に分かれている。論文の後半が $`D` 側と $`E` 側でほぼ同じ構造を二回繰り返すのは、それぞれの側で「CM 化」と「Euler 特性の回収」を一度ずつ行っているからである。

*解説 §D.6 局所コホモロジーを経由する方法（見込み）*

上の候補 2 について、CLMST が almost の世界で使っている論法（Cor. 4.0.4 の証明）が、長さ関数 $`\lambda` の一般論にも移せる見込みがある。以下は推測で、細部は確かめていない。

*CLMST の論法*

almost 平坦性（Thm. 4.0.3）から直接得られるのは、基底 $`A` のパラメータ系 $`x` についての消滅だけである。CLMST はそれを一度局所コホモロジー

$$`H^i_\mathfrak{m}(C) \cong \varinjlim_t H^i(x^t;C) \cong \varinjlim_t \operatorname{Tor}^A_{d-i}\bigl(A/(x^t),C\bigr)`

に移し（$`i<d` で almost zero）、スペクトル系列

$$`E_2 = H_{i+j}\bigl(y;H^j_\mathfrak{m}(C)\bigr)\ \Longrightarrow\ H_i(y;C)`

で任意のパラメータ系 $`y` に戻している。$`i>0` のとき、$`j = d` の項は $`i+j>d` なので $`0`、$`j<d` の項は $`H^j_\mathfrak{m}` が almost zero なので almost zero である。局所コホモロジーはパラメータ系の取り方によらない量なので、この経由で「基底に相対的な消滅」が「任意のパラメータ系での消滅」になる。

*$`\lambda` で同じことをする際の問題*

almost zero は任意の加群について意味をもつが、抽象的な \`NormalizedLength.len\` は全加群に値を持つが、加法法則は $`\mathfrak{m}_A` の固定した冪で消される加群にしか要求しない（定義 4.1）。$`H^j_\mathfrak{m}(C)` は $`\mathfrak{m}` 冪ねじれだが一つの冪で消えるとは限らないので、「$`H^j_\mathfrak{m}` の $`\lambda` が $`0`」はそのままでは言えない。これが almost のほうが $`\lambda` より強い唯一の点で、この付録の隙間の正体だと考えられる。

*$`\lambda` の定義域を延ばす*

正規化長さの定義（有限生成部分加群の上限）は、$`\mathfrak{m}_A` 冪ねじれ（固定した冪とは限らない）の加群 $`M` にもそのまま延ばせる。$`M` の有限生成部分加群はどれも一つの冪で消えるからである。

$$`\lambda^{\mathrm{ext}}(M) := \sup\{\lambda(N)\mid N\subseteq M\text{ は有限生成}\}.`

これは Lück が von Neumann 次元を任意の加群へ延ばしたのと同じ方法である。次が期待される。

1. $`\lambda^{\mathrm{ext}}` は元の定義域では $`\lambda` に一致し、部分商で単調で、$`\lambda^{\mathrm{ext}} = 0` は部分商で保たれる。

2. $`\lambda` の各段が $`0` なら、帰納極限の $`\lambda^{\mathrm{ext}}` も $`0`：有限生成部分加群 $`N\subseteq\varinjlim_t M_t` は、ある段の有限生成部分加群の像なので $`\lambda(N)\le\lambda(M_t\text{ の部分加群}) = 0`。

*期待される主張*

\> $`(C,\lambda)` が $`A` 上 $`\lambda`-平坦なら、$`D`（あるいは $`A_n\otimes_A D`）の任意のパラメータ系 $`y` について $`\lambda H_i(y;C) = 0`（$`i>0`）。すなわち $`\lambda`-平坦 $`\Rightarrow` $`\lambda`-CM。

*証明の筋書き*

1. $`\lambda`-平坦性から、$`i<d` で $`\lambda H^i(x^t;C) = \lambda\operatorname{Tor}^A_{d-i}(A/(x^t),C) = 0`（全ての $`t`）。2 により $`\lambda^{\mathrm{ext}}H^i_\mathfrak{m}(C) = 0`。

2. $`H_i(y;C)` は $`(y)` で消されるので、$`K(y;C)\simeq K(y;\mathbf{R}\Gamma_\mathfrak{m} C)` からスペクトル系列 $`H_{i+j}(y;H^j_\mathfrak{m}(C))\Rightarrow H_i(y;C)` を得る（CLMST Cor. 4.0.4 の証明と同じ）。

3. $`E_2` の項 $`H_k(y;H^j_\mathfrak{m}(C))` は $`H^j_\mathfrak{m}(C)` の有限直和の部分商で $`(y)` で消されるので、元の $`\lambda` の定義域に入り、1 と期待 1 により $`j<d` で $`\lambda = 0`。$`j = d` の項は $`i>0` で $`0`。

4. 収束先 $`H_i(y;C)` は有限個の $`E_\infty` の項（$`E_2` の部分商）でフィルトレーションされるので、加法性から $`\lambda H_i(y;C) = 0`。

*確かめるべきこと*

- $`\lambda^{\mathrm{ext}}` が矛盾なく定まり、元の $`\lambda` と一致し、部分商で単調であること（有限生成の段での単調性は CLMST Lemma 2.2.4 から出るはず）。

- $`K(y;C)\simeq K(y;\mathbf{R}\Gamma_\mathfrak{m} C)` と、スペクトル系列の構成が、$`C` が非ネーター的な場合にも使えること（$`\mathfrak{m}_A` は有限生成なので、Čech 複体による局所コホモロジーの記述は使える）。

- $`D` のパラメータ系だけでなく、Serre の論文の補題 5.14 で使う「$`R` の元で像が $`D` のパラメータ系になるもの」でも同じ議論が通ること（像だけで Koszul 複体が決まるので、通るはず）。

これが成り立てば、$`\lambda`-CM（定義 4.14）を仮定から外し、$`\lambda`-平坦（定義 4.9）だけを基本にできる。命題 4.15 の逆が成り立ち、二つの概念は同値になる。

*解説 §D.7 次にすること*

- CLMST Cor. 4.0.4 の証明を読み、almost flat から任意のパラメータ系の almost CM 性を出す論法が、長さ関数 $`\lambda` の一般論に移るかを確かめる。移るなら、$`\lambda`-平坦を基本の定義にし、$`\lambda`-CM を系とする書き直し案をこの付録に書く。

- 移らない場合は、本文の $`D` 側の入力を「$`R` の元 $`x` についての Koszul 消滅」として明示的な仮定にし、定理 8.5 がそれを供給する、という形に分ける（形式化でも仮定の形を合わせる）。

- 補題 5.14 の修正（§5.5 の形への置き換え）と同時に行う。

*$`\lambda`-エタール*

分岐（エタール性）の側も $`\lambda` で測る概念を導入して別の問題に使えないか、という検討は、別のノート（\`research/lambda-etale/lambda-etale-ja.tex\`）にまとめた。

# K 理論の降下の構造（定理 7.3・補題 7.7）

%%%
number := false
tag := "paper-supplement-10-k-theory-descent"
%%%

定理 7.3 と補題 7.7 について、何を主張し、どの既知の結果の上に立ち、なぜこの形で必要になるのかをここにまとめる。元論文 §1.2・§3・§4・§5 と Kerz–Strunk–Tamme（Invent. Math. 211 (2018)、以下 KST）を読んだ整理である。「推測」「未確認」と書いた箇所は原典で確かめていない。形式化の経路の検討は \`formalization-plans/archive/stage-i/kst-lanes/k-theory-kst-route.md\`、研究上の問いは \`research/k-spectral/k-spectral-ja.tex\` §5 にある。

*解説 §E.1 K 理論が使われる場所*

定理 7.3 は二回使われる。

- *置き換え 1*（命題 7.5、元論文 Lemma 3.5・5.2）：$`H=A`。底は正則な $`A_D`、上は Galois 閉包 $`D'`。比べるのは $`E'` の自由分解を $`D'` に延ばした有限 perfect 複体の類である。

- *置き換え 2*（定理 7.9）：$`H` は補題 7.7 のもの。底は $`A_E`、上は $`E'`。比べるのはランク無視の圏 $`P^J_{E'}` の対象である。

どちらも双線形形式 $`\chi^R(-,-)` を展開するのではない。片方を固定した類に二つの準同型 $`\chi_{\mathrm{ord}},\chi_C` を当て、底から来る類での一致（底公式）を、降下によって共役和に移す（命題 3.6）。

*解説 §E.2 perfectoid 代数は K の類か*

- 置き換え 1 では $`C_D` は類ではなく、評価 $`\chi_{C_D}` を定める試験対象である。使うのは Koszul 条件だけで、$`C_D` がネーターかどうかは関係しない。

- 置き換え 2 で初めて $`C_D`（正確には $`U=C_D/I_\sigma C_D`）を類にする。$`U` は有限生成でないので、有限近似列 $`M_n`（§6.5）の極小分解を次数 $`l` で打ち切って $`E'` に底変換した列を、ランク無視の圏の対象にする。打ち切りの誤差と台の条件は、階数 $`o(s_n)` の商で初めて処理される。

- $`C_E` は最後まで評価の側にとどまる。

K 理論をとる場所（降下の場）は一貫して $`A` 上有限型でネーターである。非ネーター性は係数 $`H` の側（非可換、$`A` 上有限でなく、正の次数で有界でもないが、連結）に集約される。perfectoid 化は K の降下に入らない。

*解説 §E.3 係数つき K 理論*

$`A` 上のスキーム $`Y` と連結な $`A` 代数 $`H` に対し $`K(Y;H)=K(\operatorname{Perf}(H\otimes^L_A\mathcal O_Y))` とおく。アフィンなら環 $`H\otimes^L_AB` の K 理論である。幾何（$`Y` を動かし、降下を考える側）と係数（$`H` を固定して運ぶ側）の役割分担であり、降下は前層 $`Y\mapsto K(Y;H)` の性質として述べる。例えば $`H=M_n(A)` なら森田同値で $`K(Y)` に戻り、Azumaya 代数ならひねり K 理論になる。

定理 7.3 を最初から一般の連結係数で述べているのは、置き換え 2 で現れるランク無視の圏がどのスキームの $`\operatorname{Perf}` でもないからである。補題 7.7 でこの圏を「係数つき $`\operatorname{Perf}`」の一例として書き直し、降下定理をそのまま適用する。降下を新しい圏に合わせて作り直すのではなく、新しい圏を既知の形に帰着させる方針である。何が一般論で何が構成に固有かは注意 7.8。

*解説 §E.4 降下という主張の型*

被覆 $`U\to X` について $`F` が降下を満たすとは、$`F(X)` が $`F` の Cech 図式の極限、つまり「$`U` 上のデータと重なりでの貼り合わせ」に一致することである。

- *Galois 降下*：$`U=\operatorname{Spec} L\to X=\operatorname{Spec} K` なら $`U\times_XU\cong G\times U` で、極限は $`F(L)^{hG}`。貼り合わせデータは $`G` 作用である。

- *cdh 降下*：Nisnevich 四角形と抽象爆発四角形（$`Y\to X` 固有、閉集合 $`Z` の外で同型、$`E=Y\times_XZ`）について $`F(X)\simeq F(Y)\times_{F(E)}F(Z)`。重なりの情報が $`E` に集約されるので Cech 条件が四角形に縮む（Voevodsky の cd 構造）。形は Zariski の Mayer–Vietoris と同じで、固有な修正に対する切除である。局所化的不変量では Nisnevich 降下は Thomason–Trobaugh により自動的で、本質は抽象爆発の切除である。帰結として冪零不変性（$`Z=X_{\mathrm{red}}`, $`Y=\emptyset`）と閉被覆の Mayer–Vietoris が得られ、中心の次元について帰納法が回せる。

- *構成可能的・連接的*：捲れ係数のエタールコホモロジーは固有底変換から cdh 降下を満たす。KH、truncating 不変量も満たす。一方 K、HH、HC、$`R\Gamma(-,\mathcal O)` は冪零に敏感で、爆発に対しては pro でしか降下しない（形式関数定理、KST Thm. A）。$`E=\operatorname{fib}(K_\mathbb{Q}\to K[1/p]_\mathbb{Q})` をとるのは K を前者の側へ移す操作と読める。

- *圏の降下と不変量の降下*：エタールな Galois 被覆について $`\operatorname{Perf}(K)\simeq\operatorname{Perf}(L)^{hG}` は成り立つが、K 理論は圏の極限と可換でないので $`K(K)\simeq K(L)^{hG}` は整数係数では一般に成り立たない（Quillen–Lichtenbaum の問題）。定理 7.3 は不変量の水準の降下である。

$`\operatorname{Spec} T\to\operatorname{Spec} A` は一般に cdh 被覆ではない。cdh 被覆は completely decomposed（各点が剰余体を変えずに持ち上がる）であり、次数 $`>1` の Galois 被覆はこれを満たさない。有限全射が被覆になるのは h 位相からである。

*解説 §E.5 定理 7.3 の証明の構造*

1. *cdh 降下（既存の入力）*：$`I=\operatorname{fib}(K_\mathbb{Q}\to\mathrm{HN}(-\otimes\mathbb{Q}/\mathbb{Q}))` は truncating（Goodwillie）。二つの $`\mathrm{HN}` の項が打ち消し合うので $`E(U)\simeq\operatorname{fib}(I(U)\to I(U[1/p]))` も truncating（元論文 (3.4)）。Land–Tamme Thm. A.2・B.3 で係数つき cdh 降下。truncating なので係数については $`\pi_0(H\otimes^L_AB)=\pi_0H\otimes_A\pi_0B` しか効かず、任意の連結な $`H` が扱える。台 $`V(J)\subset V(p)` で切ると実際の台つき有理 K 理論 $`L` になる（(3.6)）。

2. *有限忠実平坦な被覆の降下（Lemma 3.2）*：転送との合成が局所的に階数 $`a` 倍なので、有理係数では $`a^{-1}\mathrm{trf}` がレトラクトを与え、分裂した Cech 降下に帰着する。転送をもつ有理係数の前層で標準的な議論である。整数係数では成り立たない。

3. \*\*$`\tau` 降下（Lemma 3.3）\*\*：$`\tau` は cdh 被覆と有限忠実平坦な被覆で生成される位相で、ほぼ h 位相である。生成する族で層なら $`\tau` 層であり（形式的で hyperdescent は要らない）、有限全射が $`\tau` 被覆であることは平坦化爆発と次元の帰納法で示す（幾何的）。整な $`Y` 上で有限全射は稠密開集合上で平坦であり、そこで同型な平坦化爆発 $`Y'\to Y` で strict transform が有限平坦になる。中心は次元が下がる。

4. \*\*$`hG` との同一視（§3.3）\*\*：両辺が $`\tau` 層なので、被覆が切断をもつ場合に帰着する。切断の $`G` 移動が一致する軌跡の上で抽象爆発四角形を使い、cdh 降下をもう一度使う。自明に作用する安定化群の $`hG` は有理係数なので普通の不変部分である。

平坦な場合でも (4) で cdh 降下が要る。転送から得られるのは $`L(A)` が $`L(T)` のレトラクトであることまでで、それが $`G` 不変部分と一致するには $`f^*\circ\mathrm{trf}=\sum_gg^*` が要る。これは $`T\otimes_AT\cong\prod_GT` となるエタールな Galois 被覆では成り立つが、分岐していると崩れる。軌道の議論は「$`X\times_SX` は cdh 局所的に、冪零を除いて $`G` 個のコピーの非交和とみなせる」ことを示しており、cdh 降下は分岐した被覆を Galois 被覆として扱うために使われている。また平坦でない場合は実際に現れる：正則な $`A` 上の有限拡大 $`D'` が平坦であることは $`D'` が CM であることと同値であり、Galois 閉包は一般に CM ではない。このとき $`K_\mathbb{Q}` そのものは降下しない（標数 $`0` で $`\operatorname{Spec} k\to\operatorname{Spec} k[\varepsilon]` について $`K_1(k[\varepsilon])_\mathbb{Q}=k^\times_\mathbb{Q}\oplus k\neq K_1(k)_\mathbb{Q}`）ので、cdh 局所な $`L` に取り替える必要がある。

*解説 §E.6 分岐の吸収*

元論文は平坦性も tame 分岐も仮定しない。分岐は二か所で別の仕組みで吸収される。

- *K 理論の側*：有理化（$`|G|` と階数が可逆）と cdh 降下（非平坦性と分岐の軌跡を次元の低い問題へ押し込む）。整数係数では惰性群が $`p` 群となる野生分岐で群コホモロジーが残る。幾何ファイバー上の推移性（元論文 §5.1）はノルムと冪等元で示され、不変部分と底変換の可換性（野生分岐で崩れうる）を使わない。

- *長さの側*：判別式型の $`g\in A` で $`A[1/g]\to D[1/g]` は有限エタールである。混標数では正の次数の Koszul ホモロジーが almost イデアル $`(g)_{\mathrm{perfd}}` で消され（CLMST Cor. 4.0.4）、正規化長さ $`0` になる（Prop. 4.0.10）。正標数では trace の分母 $`g` による誤差が $`O(q^{-1})` で消える。分岐は $`\lambda` で見えない。

Galois 降下が要る理由は perfectoid 化そのものより「$`D` が正則でない」ことにある。$`\lambda` は正則な底 $`A` の塔で測る物差しであり、普通の長さとの一致が保証されるのは $`A` から来る類だけである。正標数（$`C_D=D_{\mathrm{perf}}`）でも同じ構造になる。

*解説 §E.7 新しさについて（推測）*

- $`H=A` の場合は既知の理論から導ける可能性が高い（推測）。$`E` は cdh 局所なので $`L_{\mathrm{cdh}}K\simeq\mathrm{KH}`（KST Thm. 6.3）から $`E(U)\simeq\operatorname{fib}(\mathrm{KH}(U)_\mathbb{Q}\to\mathrm{KH}(U[1/p])_\mathbb{Q})` となるはずであり、有理 KH は Beilinson モチーフで表現され h 降下をもつ（Cisinski–Déglise、未確認）。

- 元論文が新しい点として挙げるのは「任意の連結な結合的係数での有限全射降下」（§1.2 末）である。係数 $`H` はスキーム上の層の代数ではなく、モチーフの六関手の枠に載らないので、既知の議論をそのままは流用できない。論文全体の新しさは §6 のランク無視の圏での評価（商の後でのみ台をもつ対象や持ち上がらない冪等元の扱い）にある。

*解説 §E.8 有理化と TC・シントミック*

有理化と $`E` をとる操作で、TC・$`\mathrm{HN}`（de Rham・シントミックの側）は打ち消し合う。したがって定理 7.3 にシントミックコホモロジーは現れない。整数・$`p` 進係数へ精密化すればこの打ち消しは起きず、Bouis の混標数モチーフ的コホモロジー（arXiv:2412.06635、2507.16501）で次数 $`\le i` の $`\mathbb{Z}/p^k(i)^{\mathrm{mot}}\simeq\mathbb{Z}/p^k(i)^{\mathrm{syn}}` としてシントミックが本質的に現れる。そのとき K の降下の側にも perfectoid（非ネーター）が入ってくる。この方向の問いは \`research/k-spectral\` にある。

