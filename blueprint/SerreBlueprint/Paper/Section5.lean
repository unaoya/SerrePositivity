import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Avoidance
import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Basic
import SerrePositivity.IntersectionMultiplicity.Vanishing
import SerrePositivity.LengthAlgebra.Normalized
import SerrePositivity.LengthAlgebra.QuotientBounds
import SerrePositivity.Paper.Section4.LengthHypotheses
import SerrePositivity.Paper.Section4.RankLowerBound
import SerrePositivity.Paper.Section5.Approximation
import SerrePositivity.Paper.Section5.FirstComparison
import SerrePositivity.Paper.Section5.ParameterQuotient
import SerrePositivity.Paper.Section5.Positivity
import SerrePositivity.Paper.Section5.SecondComparison

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§5 Proof of strict positivity" =>
%%%
number := false
tag := "paper-5"
%%%

本論文 §5 の項目と、本体の宣言との対応。各項目の頭は対応表（`research/paper-coverage`）の照合の理由、その下は解説から移した本文（あるものだけ）。

*解説 §9 核の場合の証明*

この節では定理 1.2（核の場合）を証明する。証明は次の段階からなり、各段階は前の節の命題を当てはめる。

- 段階　／　主張　／　使う結果
- 設定　／　補題 9.1（推移性）　／　不変環とノルムの議論
- 置き換え 1　／　補題 9.2（Lemma 5.2）　／　命題 7.5（Lemma 3.5c）
- 置き換え 2 の準備　／　補題 9.3、9.4（Lemma 5.3–5.5）　／　命題 7.10、定理 4.19、命題 6.13
- 置き換え 2　／　命題 9.5（(5.18)）　／　定理 7.9（Theorem 4.7）
- 正値性　／　補題 9.6（Lemma 5.6）　／　命題 7.11
- 結論　／　定理 1.2 の証明　／　上の全て

置き換え 1 は $`(D',\operatorname{length}_{D'})` と $`(C_D,\lambda_D)` の対称な比較、置き換え 2 は $`(E',\operatorname{length}_{E'})` と $`(C_E,\lambda_E)` の漸近版の比較である。$`C_D` の $`\lambda`-CM 性はパラメータ商と次数の上界を与え、有限近似を長さ $`l` の複体列にする。$`C_E` の Koszul 消滅はその列の高次を消す。極小性が $`0` 次の下界を与え、生成元数の正規化極限と非自明性が正値性を与える。

*解説 §9.3 置き換え 2 の準備：パラメータ商と有限近似*

以下、$`\sigma\in G_D` を固定し、$`C = C_D^\sigma`、$`\lambda = \lambda_D` と書く。

# §5.1 Reduction and the first norm comparison

%%%
number := false
tag := "paper-5-1"
%%%

:::lemma_ "paper_5_1" (uses := "paper_eq_5_1, paper_1_1, paper_2_1, ext_GilletSoule, ext_Roberts85, ext_Serre")
**補題 5.1**　完備・代数閉剰余体・正次元素商対への帰着。対応表の状態：一部。

原典 PDF p.23 / layout L1200。prime filtrationとvanishingによる帰着、零次元対、剰余体拡大・完備化の各処理はある。一方、positivity\_of\_residueCharPは核心の実定理を呼ぶため入力依存で、原典の「核心を証明すれば十分」という全帰着を独立の含意型として切り出した宣言は確認しない。

*解説 §9.1 設定（§5.1）*

定理 1.2 の $`D, E` に対し、補題 8.4 の正則部分環 $`A_D\subseteq D`、$`A_E\subseteq E` をとる。$`D'` を $`\operatorname{Frac}(D)/\operatorname{Frac}(A_D)` の Galois 閉包における $`A_D` の整閉包、$`G_D` をその Galois 群とする（$`E'`、$`G_E` も同様）。$`D'` は $`A_D` 上有限な局所整域（優秀性）で、$`A_D` の正規性から $`(D')^{G_D}=A_D` である。定理 8.5 を $`D'`、$`E'` に適用して $`\lambda`-平坦な長さ付き代数 $`(C_D,\lambda_D)`、$`(C_E,\lambda_E)` を得る。$`a_D = \operatorname{rank}_D D'`、$`a_E = \operatorname{rank}_E E'` とおく。
$`D'` が $`A_D` 上有限であることは完備局所整域の優秀性（Nagata）、局所で剰余体が $`k` であることは完備局所環上有限な代数が局所環の有限積になることによる。

*Lean:* \`Paper.Section5.GaloisNormalization\` の \`exists\_regular\_galoisNormalization\`（補題 8.4 で基底を選び、それを保ったまま Galois 閉包へ上げ、不変環・有限性・完備性・剰余体の一致を構成する。補題 8.4 の正規化も証明済み）。

*補題 9.1（幾何ファイバーへの推移性）*

$`A\to T` を有限な環準同型、有限群 $`G` が $`T` に $`A` 上で作用し、$`G` で固定される元が全て $`A` から来るとする。このとき $`G` は $`\operatorname{Spec} T\to\operatorname{Spec} A` の全ての幾何ファイバーに推移的に作用する。特に $`(D',A_D,G_D)` と $`(E',A_E,G_E)` について成り立つ。

*証明*

代数閉体 $`\Omega` への $`A` 代数の構造をとり、$`S=T\otimes_A\Omega` とおく。$`u=\sum_it_i\otimes\omega_i\in S` について、共役の積 $`\prod_gg(u)` は $`\Omega` に入る。実際、多項式 $`\prod_g\sum_ig(t_i)X_i` は $`G` 不変なので係数は $`A` から来て、$`X_i=\omega_i` と特殊化すればよい。$`S` は $`\Omega` 上有限な Artin 環なので、$`\operatorname{Spec} S` は離散である。一つの点の軌道に対応する冪等元 $`e` について $`\prod_gg(e)` は冪等なスカラーで、その点で $`0` でないから $`1` に等しい。したがって軌道は $`\operatorname{Spec} S` 全体である。

*Lean:* \`isGeometricallyTransitive\_of\_fixed\`（証明済み）。

宣言：`SerrePositivity.chi_pos_of_prime_quotients`、`SerrePositivity.Section5.chi_prime_eq_one_of_dim_zero`、`SerrePositivity.Section5.positivity_of_residueCharP`、`SerrePositivity.Section5.positivity_of_residueCharZero`

外の文献：GilletSoule、Roberts85、Serre

:::

:::definition "paper_eq_5_1" (lean := "SerrePositivity.intersectionVanishing_of_adams") (uses := "ext_GilletSoule, ext_Roberts85")
**式 (5.1)**　相補次元未満での交点重複度の消滅。対応表の状態：本体にある。

原典 PDF p.23 / layout L1217。一般の正則局所環で有限長テンソルと次元和\<dim Rからchi=0。原典と同じ一般のvanishingをAdams経路で証明する。

外の文献：GilletSoule、Roberts85

:::

:::definition "paper_eq_5_2" (lean := "SerrePositivity.twistedEuler") (uses := "paper_2_5")
**式 (5.2)**　ねじった正規化Tor Euler値c\_sigma。対応表の状態：本体にある。

原典 PDF p.24 / layout L1269。σでねじったR作用を持つCとEのlambdaChiとして定義する。有限性は別にLemma5.2で示す。

*解説 §9.1 設定（§5.1）*

*補題 9.1（幾何ファイバーへの推移性）*

$`\sigma\in G_D` に対し $`\iota_\sigma\colon R\to D'\xrightarrow{\sigma} D'` とし、$`C_D` に $`\iota_\sigma` で $`R` 作用を入れたものを $`C_D^\sigma` と書く。

$$`c_\sigma = \sum_i (-1)^i \lambda_D \operatorname{Tor}_i^R(C_D^\sigma, E')`

とおく。Tor は $`E'` の自由分解で計算する（形式化では Tor の対称性を使わない）。

*Lean:* \`twistedAlgebraMap\`、\`twistedEuler\`。

:::

:::lemma_ "paper_5_2" (uses := "paper_eq_5_1, paper_3_5")
**補題 5.2**　第1のGalois平均と普通の交点数。対応表の状態：未証明の入力に依存。

原典 PDF p.24 / layout L1274。任意の共役の有限正規化Tor長と、\|G\_D\| a\_D a\_E chi=Σc\_sigmaを同時に与える。有限拡大のrank因子・vanishingは実装されるが、norm比較に使う通常K0降下入力のsorryが残る。

*解説 §9.2 置き換え 1*

*補題 9.2（Lemma 5.2、置き換え 1）*

$$`|G_D|\cdot a_D\cdot a_E\cdot\chi^R(D,E) \;=\; \sum_{\sigma\in G_D} c_\sigma.`

*証明*

$`E'` の有限自由 $`R` 分解 $`F` をとり $`P_\sigma = F\otimes_{R,\iota_\sigma} D'` とおく。$`\sigma` は単射なので $`R\to D'\xrightarrow{\sigma}D'` の核は $`P` のままであり、$`P+Q` が $`\mathfrak{m}`-準素なので $`P_\sigma` のホモロジー $`\operatorname{Tor}^R(E',D')` は閉点に台をもち、$`P_\sigma\in\operatorname{Perf}_{\mathfrak{m}}(D')`。$`\chi_C(P_\sigma) = c_\sigma` である。$`\sigma` を成分ごとに作用させると $`P_1\to P_\sigma` の $`\sigma` 半線形な同型が得られ、$`D'` 部分加群を $`D'` 部分加群に移すのでホモロジーの長さを保つ。よって $`\chi_{\mathrm{ord}}(P_\sigma)=\chi_{\mathrm{ord}}(P_1)=\chi^R(D',E')` は $`\sigma` によらない（剰余体が共通なので $`D'` 上と $`R` 上の長さは一致する）。命題 7.5（$`A = A_D`、$`T = D'`、$`G = G_D`）より

$$`|G_D|\,\chi^R(D',E') = \sum_\sigma c_\sigma.`

$`\sigma` と $`\sigma^{-1}` のどちらを $`P_\sigma` に対応させるかは、群全体で和をとるので関係ない。最後に、$`\operatorname{Frac} D'` の $`\operatorname{Frac} D` 上の基底を $`D'` の中からとると単射 $`D^{a_D}\to D'` が得られ、その余核はねじれ加群なので Krull の単項イデアル定理により次元が $`h` 未満である。$`\chi^R(-,E')` の加法性と消滅定理（$`\dim K+\dim E'<d`）から $`\chi^R(D',E')=a_D\,\chi^R(D,E')`、同様に $`E^{a_E}\to E'` から $`\chi^R(D,E')=a_E\,\chi^R(D,E)` を得る。

*Lean:* \`firstComparison\`、\`firstComparison\_of\_resolution\`、\`normComparison\_of\_lengthAlgebra\`、ランクの因子は \`IntersectionMultiplicity.FiniteExtension\`（引用を除いて証明済み。引用は消滅定理と定理 7.3）。環・有限代数・群作用・長さの条件は引数として明示的に受け取る。

宣言：`SerrePositivity.firstComparison`、`SerrePositivity.normComparison_of_lengthAlgebra`

:::

:::definition "paper_eq_5_3" (uses := "paper_eq_5_1, paper_3_5")
**式 (5.3)**　第1のnorm比較の等式。対応表の状態：未証明の入力に依存。

原典 PDF p.24 / layout L1276。全共役の有限性と和の等式を返すが、普通K0降下入力に依存する。

宣言：`SerrePositivity.firstComparison`

:::

# §5.2 A parameter quotient and its Tor groups

%%%
number := false
tag := "paper-5-2"
%%%

:::definition "paper_eq_5_4" (lean := "SerrePositivity.exists_regular_parameters_in") (uses := "paper_2_5")
**式 (5.4)**　Q内の正則列とDのパラメータの同時選択。対応表の状態：本体にある。

原典 PDF p.24 / layout L1300。prime avoidanceによりQ内からR正則列でD上のparameter systemとなる列を選ぶ。

*解説 §9.3 置き換え 2 の準備：パラメータ商と有限近似*

*補題 9.3（パラメータ商）（(5.4)、Lemma 5.3）*

$`Q` の元 $`x_1,\dots,x_h` で、$`R` 正則列かつ像が $`D` のパラメータ系になるものがある。$`B = R/(x)`、$`I_\sigma=\iota_\sigma(x)D'`、$`U = C/\iota_\sigma(x)C` とおくと、$`B` は次元 $`l` の完全交叉局所環で、次が成り立つ。

*証明*

$`x` は素イデアル回避で一つずつ選ぶ。$`R/(x_1,\dots,x_{i-1})` の随伴素イデアルは非混合性により高さ $`i-1` で、$`Q` を含まない。$`D/(x_1,\dots,x_{i-1})` で次元を下げるのに避けるべき極小素イデアルも、$`P+Q` が $`\mathfrak{m}`-準素であることから $`Q` を含まない。$`D'` は $`D` 上有限なので、$`\iota_\sigma(x)` は $`D'` のパラメータ系である。

:::

:::definition "paper_eq_5_5" (lean := "SerrePositivity.Section5.parameterQuotient_length_eq_multiplicity, SerrePositivity.Section5.koszul_zero_of_cm_parameters, SerrePositivity.Section5.parameterQuotient_len_ne_top_of_cm") (uses := "paper_2_5")
**式 (5.5)**　パラメータ商Uの正の長さとKoszul零性。対応表の状態：本体にある。

原典 PDF p.25 / layout L1318。本文の固定した長さ代数の全パラメータ仮定の文脈で、選んだxからUの長さ・有限性とKoszul零性を得る。存在を供給するTheorem2.5は別にinterfaceと記録する。

*解説 §7.3 パラメータ商（Lemma 5.3）*

*命題 7.10（Lemma 5.3）*

- (b) $`0<\lambda(U)<\infty`。

*解説 §9.3 置き換え 2 の準備：パラメータ商と有限近似*

*補題 9.3（パラメータ商）（(5.4)、Lemma 5.3）*

- (b) $`0<\lambda(U)<\infty`。

:::

:::definition "paper_eq_5_6" (lean := "SerrePositivity.exists_pow_maximalIdeal_map_le, SerrePositivity.Section5.lemma_5_4")
**式 (5.6)**　全近似で共通に使うannihilator冪。対応表の状態：本体にある。

原典 PDF p.25 / layout L1322。局所環射B→D′とprimaryなI\_sigmaに共通の正の冪を選び、商でその像を零とする。近似では同じannihilatorを全M\_nに維持する。

*解説 §9.3 置き換え 2 の準備：パラメータ商と有限近似*

*補題 9.3（パラメータ商）（(5.4)、Lemma 5.3）*

- (c) ある $`a\ge1` で $`\mathfrak{m}_B^a` が $`D'/I_\sigma` と $`U` を消す。

:::

:::lemma_ "paper_5_3" (lean := "SerrePositivity.Section5.lemma_5_3") (uses := "paper_eq_5_5")
**補題 5.3**　パラメータ商を通じたTor長比較と次数上界。対応表の状態：本体にある。

原典 PDF p.25 / layout L1326。固定した長さ代数・正則列・有限B加群の文脈で、Tor\_B(U,L)とTor\_R(C,L)の長さを比較し、有限性およびi\>dim R-hでの消滅を得る。R-正則列と長さ零Koszulの仮定は本文の設定と一致する。

*解説 §5.5 パラメータ商*

§9 の置き換え 2 の準備として、$`C_D` を有限加群の代わりに使えるようにする。正則列 $`x` で割った商 $`U=C/xC` は、$`\lambda` の目では $`B=R/(x)` 上の射影次元が低い加群のように振る舞う。この小節の二つの補題は、$`x` の Koszul ホモロジーの長さ零を入力にとる一般論である。後半は §5.3 の消滅を $`(A,z)` の代わりに $`(R,x)` で使ったものにあたる。$`\lambda`-CM 性からこの入力を供給して論文の Lemma 5.3 を得るのは §7.3 である。

*補題 5.14（$`\lambda` 版の Auslander–Buchsbaum）*

補題 5.13 の設定で、さらに $`R` を次元 $`d` の正則局所環とし、全ての $`v\ge1` と $`q>0` で $`\lambda H_q(x^v;C)=0` とする。このとき有限生成 $`B` 加群 $`L` について

$$`\lambda\operatorname{Tor}_i^R(C,L) = \lambda\operatorname{Tor}_i^B(U, L), \qquad\text{これは } i > d-h \text{ で } 0.`

*証明*

等式は補題 5.13 である。消滅は、補題 5.10 を $`(A,z,T)=(R,x,R)` に当てはめたものである。$`L` の $`R` 上の長さ $`d` 以下の有限自由分解 $`P` をとる。$`x_jL=0` なので $`P` のホモロジーの台は $`V((x))` に入り、$`P\in\operatorname{Perf}_{(x)}(R)` である。列の長さ $`e=h`、$`m=d` として補題 5.10 を使うと、$`\lambda\operatorname{Tor}_i^R(C,L)=\lambda H_i(P\otimes_R C)=0`（$`i>d-h`）を得る。

元論文は導来圏での分裂 $`K(x;R)\otimes^L_RL\simeq\bigoplus_jL[j]^{\binom hj}` を使う。ここでは $`x_jL=0` から $`P` 上で各 $`x_j` の冪が零ホモトピックになることを使い、共通の冪を $`C\otimes_RP` に移して補題 5.10 に渡す。$`B` は次元 $`d-h` の完全交叉局所環だが、一般には正則ではない（例えば $`k[[u,v]]/(u^2)`）。次数の上界は $`B` の大域次元ではなく、正則環 $`R` 上の分解の長さと Koszul 消滅から得る。古典的には、有限 CM $`R` 加群 $`M` の射影次元を $`d-\dim M` とする Auslander–Buchsbaum の公式に対応する。

*Lean:* 消滅は \`ParamQuot.len\_torAlg\_eq\_zero\`。$`C\otimes_RP` に \`LengthAlgebra.lambdaHomology\_projective\_vanishing\`（補題 5.10）を適用して証明している。等式と消滅をまとめた形は \`Section5.lemma\_5\_3\`（証明済み）。

*解説 §7.3 パラメータ商（Lemma 5.3）*

*命題 7.10（Lemma 5.3）*

$`R` を次元 $`d` の正則局所環、$`\iota\colon R\to D'` を有限な局所準同型（$`D'` は次元 $`h` のネーター局所環）、$`(C,\lambda)` を $`D'` 上の非自明な $`\lambda`-CM 代数とし、$`R` は $`\iota` を通して $`C` に作用するとする。$`x_1,\dots,x_h\in R` を $`R` 正則列で $`\iota(x)` が $`D'` のパラメータ系になるものとし、$`B=R/(x)`、$`U=C/\iota(x)C`、$`l=d-h` とおく。このとき次が成り立つ。

- (a) 有限生成 $`B` 加群 $`L` について $`\lambda\operatorname{Tor}_i^R(C,L)=\lambda\operatorname{Tor}_i^B(U,L)` で、これは $`i>l` で $`0`。

*証明*

$`\iota(x)` は $`D'` のパラメータ系で、その冪 $`\iota(x)^v` もそうである。$`\lambda`-CM 性により、全ての $`v\ge1` と $`q>0` で $`\lambda H_q(\iota(x)^v;C)=0`、$`\lambda(U)=\lambda(C/\iota(x)C)<\infty` である。$`J=\mathfrak{m}_{D'}C` は有限生成で、$`I_\sigma` が $`\mathfrak{m}_{D'}`-準素なので $`\sqrt{J}=\sqrt{\iota(x)C}` である。これで補題 5.14 の入力がそろい、(a) を得る。(b) の有限性は上で見た。正値性は、全射 $`U\to C/\mathfrak{m}_{D'}C` と非自明性から出る。

*Lean:* $`\lambda`-CM 性から Koszul 入力を供給する部分は \`LengthAlgebra.CohenMacaulay\` の \`koszulAcyclic\_of\_cm\`、\`koszulFinite\_of\_cm\`。(a) は \`Section5.lemma\_5\_3\`（Koszul 条件と有限分解を明示して証明済み）。両者をつないだ形が \`Paper.Section5.ParameterQuotientCM\` の \`Section5.lemma\_5\_3\_of\_cm\`（$`\lambda`-CM 性と $`x` の像がパラメータ系であることから (a) を出す。証明済み）。§9 の経路（\`Paper.Section5.TowerPositivity\`）はまだ Koszul 条件を直接の仮定として受け取っている。(b) の正値性は \`Paper.Section5.ParameterLengthPositivity\` で、重複度の公式から導いている。

*解説 §9.3 置き換え 2 の準備：パラメータ商と有限近似*

*補題 9.3（パラメータ商）（(5.4)、Lemma 5.3）*

*証明*

$`C` は定理 8.5 (a) と系 8.7 により非自明な $`\lambda`-CM 代数なので、命題 7.10 を $`\iota_\sigma\colon R\to D'` と $`C` に適用して (a)、(b) を得る。(c) は、局所準同型 $`B\to D'/I_\sigma` と、$`I_\sigma` が $`\mathfrak{m}_{D'}`-準素であることから出る（論文の (5.6)）。

*Lean:* $`x` の選択は \`exists\_regular\_parameters\_in\`（非混合性も \`CommutativeAlgebra.Unmixedness\` で証明済み）と、有限拡大へ移す \`Section5.exists\_regular\_parameters\_for\_finite\_extension\`。(a) は \`Section5.lemma\_5\_3\`、(c) は \`Section5.exists\_pow\_maximalIdeal\_map\_le\`。

:::

:::definition "paper_eq_5_7" (lean := "SerrePositivity.Section5.lemma_5_3") (uses := "paper_eq_5_5")
**式 (5.7)**　Tor\_BとTor\_Rの長さおよび消滅上界。対応表の状態：本体にある。

原典 PDF p.25 / layout L1330。有限B加群Lと全iについて同じ長さ等式・有限性・i\>lでの消滅を得る。

*解説 §5.5 パラメータ商*

*補題 5.13（Tor の長さの一致）*

$`R` をネーター環、$`x=(x_1,\dots,x_h)` を $`R` 正則列、$`B=R/(x)` とする。$`C` を $`R` 代数、$`\lambda` を $`J`-冪ねじれ $`C` 加群の上の長さ関数とし、$`J` は有限生成で $`\sqrt{J}=\sqrt{(x)C}` とする。$`U=C/xC` について

$$`\lambda H_q(x;C)=0\quad(q>0),\qquad \lambda(U)<\infty`

なら、有限生成 $`B` 加群 $`L` について

$$`\lambda\operatorname{Tor}_i^R(C,L)=\lambda\operatorname{Tor}_i^B(U,L)<\infty.`

*証明*

$`K(x;R)` は $`B` の自由分解なので $`\operatorname{Tor}_i^R(C,B)=H_i(x;C)` であり、$`i>0` で長さ零、$`i=0` で $`U` である。有限表示 $`0\to L'\to B^a\to L\to0` をとり、$`B^a` に対する高次 Tor の長さ零を使って二つの Tor の長完全列を比較する。零次は $`C` 線形なテンソル積の同型 $`C\otimes_RL\cong U\otimes_BL` で同定し、次数に関する帰納法で等式と有限性を示す。結論は長さの一致であり、二つの Tor を長さの商で同定する自然同型の構成までは主張しない。

元論文は環の変更のスペクトル系列で示すが、上の次元シフトで足りる。

*Lean:* \`IntersectionMultiplicity.ParameterQuotientTor\` の \`ParamQuot.torClaim\`（証明済み）。仮定は $`J^a\subseteq(x)C` の形で受け取る。

*解説 §9.3 置き換え 2 の準備：パラメータ商と有限近似*

*補題 9.3（パラメータ商）（(5.4)、Lemma 5.3）*

- (a) 有限生成 $`B` 加群 $`L` について $`\lambda\operatorname{Tor}_i^R(C,L) = \lambda\operatorname{Tor}_i^B(U,L)` で、これは $`i>l` で $`0`。

:::

# §5.3 Finite approximations preserving the actions

%%%
number := false
tag := "paper-5-3"
%%%

:::definition "paper_eq_5_8" (lean := "SerrePositivity.Section5.paramTheta, SerrePositivity.Section5.paramTheta_comp_tower") (uses := "paper_2_3, paper_2_5")
**式 (5.8)**　近似用のS\_jとSおよび二つの作用。対応表の状態：本体にある。

原典 PDF p.26 / layout L1382。TSとして塔とD′/I\_sigmaをテンソルし、Uへの実際の環射と塔・B作用との両立を構成する。

:::

:::lemma_ "paper_5_4" (lean := "SerrePositivity.Section5.lemma_5_4, SerrePositivity.Section5.paramTheta, SerrePositivity.Section5.finiteApproximation_rank_lower_bound") (uses := "paper_eq_5_10, paper_eq_5_11, paper_eq_5_12, paper_eq_5_6, paper_eq_5_9, paper_2_5")
**補題 5.4**　作用と共通annihilatorを保つ有限近似。対応表の状態：本体にある。

原典 PDF p.26 / layout L1386。塔とB作用を保持する有限近似M\_n、正整数s\_n→∞、共通annihilator、有限長・全指定Tor長の通常極限を構成する。Tor0の近似と有限長商の生成元数評価からnu\_sigmaの正の下界を得る。有限生成でないUも許す。

*解説 §4.5 塔と整合する長さ*

有限加群でない対象を有限長加群の列で近似するための設定と、その存在定理（定理 4.19、Lemma 5.4 の一般形）を述べる。具体例は §8 の塔と Faltings の正規化長さ $`\lambda_\infty` である。近似列からランク無視の圏の対象を作るのは §6.5 である。

*定義 4.18（有限近似列）*

$`B` をネーター局所環、$`k` をその剰余体、$`\mathcal{L}` を有限生成 $`B` 加群の族とする。正の整数の列 $`s_n\to\infty` と有限長 $`B` 加群の列 $`(M_n)` が*有限近似列*であるとは、ある $`a` で全ての $`M_n` が $`\mathfrak{m}_B^a` で消され、全ての $`L\in\mathcal{L}\cup\{k\}` と $`i\ge0` について

$$`\tau_i(L)=\lim_{n}\frac{\operatorname{length}_B\operatorname{Tor}_i^B(M_n,L)}{s_n}`

が有限な値として存在し、$`\lim_n\operatorname{length}_B(M_n)/s_n` も存在することをいう。

*定理 4.19（有限近似列の存在、Lemma 5.4 の一般形）*

$`\lambda` を $`A` 上の塔と整合する長さ（定義 4.17）とし、加法的であるとする。$`T` を $`A` 上有限な局所代数で $`\mathfrak{m}_A^aT=0` となるもの、$`B` を局所環で $`B\to T` と $`A\to T` がともに剰余体に全射なものとする。$`S=\Lambda\otimes_AT` 加群 $`U` が $`\lambda(U)<\infty` をみたし、$`B` の作用が $`S` を通るとする。このとき有限近似列 $`(M_n)` で、$`T` を消す $`B` のイデアルは全ての $`M_n` を消し、

$$`\lim_n\frac{\operatorname{length}_B(M_n)}{s_n}=\lambda(U),\qquad \tau_i(L)=\lambda\operatorname{Tor}_i^B(U,L)\quad(L\in\mathcal{L})`

となるものがある。

*証明*

上限の性質から $`U` を有限生成部分加群で近似し、有限生成加群での一致から、核と余核の $`\lambda` が小さい有限表示加群 $`P_\varepsilon\to U` をとる。段への降下で $`P_\varepsilon` をある段 $`S_j=A_j\otimes_AT` 上の有限表示加群 $`V` の係数拡大として表す。$`S` は $`S_j` 上平坦なので、Tor は係数拡大と両立する。有限段の公式から $`V` の長さと Tor の長さは $`s_j` で割った値になる。$`L` の有限自由分解の階数で核と余核の寄与を抑え、$`\varepsilon\to0` と $`j\to\infty` の対角線をとる。

*Lean:* \`Section2.exists\_tower\_approximation\_B\`（一般部分）と \`Section5.lemma\_5\_4\`（§9 の形）。Lean では具体的な塔 \`Tower\` と $`\lambda_\infty`（\`towerLength\`）の上で述べており、定義 4.17 の抽象的な設定にはまだ書き直していない。証明が使うのは上の四つの性質と加法性だけである。Lean の証明は、誤差を各 $`(L,i)` ごとに $`L` の分解の階数と $`\varepsilon_n=1/(n+1)` の積で押さえて一段ずつ近似をとる（元論文の「$`i\le n` までの誤差を $`1/n` 未満に」という選び方は使わない）。段で計算した Tor と通常の $`\operatorname{Tor}^B` の一致は \`torModuleRestrictEquiv\`。$`s_n\to\infty` は段 $`j_n\ge n` と $`h>0` から出る。\`Section5.lemma\_5\_4\` は (5.11) で $`0\cdot\infty` を避けるため $`\operatorname{length}_B(B/I)<\infty` を仮定にし、極小自由分解を内部で構成して剰余体係数の Tor の極限も同じ近似列の結論に含める。

*解説 §9.3 置き換え 2 の準備：パラメータ商と有限近似*

*補題 9.4（有限近似と切り詰め）（Lemma 5.4、5.5）*

*証明*

$`\lambda_D` は塔と整合する長さの係数制限である（命題 8.3）。定理 4.19 を $`T=D'/I_\sigma` と $`U` に適用し、$`\mathfrak{m}_B^a` で消される有限近似列 $`(M_n)` を $`\mathcal{L}=\{E'\}` についてとる。$`\tau_i(L)=\lambda\operatorname{Tor}_i^B(U,L)`（$`L=k,E'`）であり、補題 9.3 (a) から $`\tau_i(k)=0`（$`i>l`）、$`\lim\operatorname{length}_B(M_n)/s_n=\lambda(U)` である。

:::

:::definition "paper_eq_5_9" (lean := "SerrePositivity.Section5.lemma_5_4") (uses := "paper_eq_5_10, paper_eq_5_11, paper_eq_5_12, paper_eq_5_6, paper_2_5")
**式 (5.9)**　有限近似M\_nの長さの通常極限。対応表の状態：本体にある。

原典 PDF p.26 / layout L1389。通常のatTop極限でlambda(U)へ収束する。超極限だけではない。

:::

:::definition "paper_eq_5_10" (lean := "SerrePositivity.Section5.lemma_5_4") (uses := "paper_eq_5_11, paper_eq_5_12, paper_eq_5_6, paper_eq_5_9, paper_2_5")
**式 (5.10)**　有限近似の全指定Tor長の極限。対応表の状態：本体にある。

原典 PDF p.26 / layout L1392。指定された有限加群族と全次数のTor長について通常極限を同時に与える。

:::

:::definition "paper_eq_5_11" (lean := "SerrePositivity.Section5.lemma_5_4, SerrePositivity.Section5.finiteApproximation_rank_lower_bound, SerrePositivity.Section5.finiteApproximation_rank_pos")
**式 (5.11)**　正規化した最小生成元数の正の下界。対応表の状態：本体にある。

原典 PDF p.26 / layout L1396。Tor0の通常極限と共通annihilatorによるlength≤beta0×length(B/m\^a)から、正のrank極限と下界を得る。

*解説 §6.5 有限近似列*

*命題 6.13（有限近似列から得る対象）*

- (c) $`\nu=\lim_\mathcal{U}\beta_0(M_n)/s_n` は $`\lim_n\operatorname{length}_B(M_n)/s_n` を $`\operatorname{length}_B(B/\mathfrak{m}_B^a)` で割った値以上である。

*解説 §9.3 置き換え 2 の準備：パラメータ商と有限近似*

*補題 9.4（有限近似と切り詰め）（Lemma 5.4、5.5）*

- (c) $`\nu_\sigma=\lim_\mathcal{U}\beta_0/s_n` は $`\lambda(U)/\operatorname{length}(B/\mathfrak{m}_B^a)` 以上で、特に正。

:::

:::definition "paper_eq_5_12" (uses := "paper_eq_5_10, paper_eq_5_9")
**式 (5.12)**　近似誤差をkernel・cokernelの長さで抑えるTor評価。対応表の状態：一部。

原典 PDF p.26 / layout L1419。finite approximationの構成で長さ誤差を制御しているが、原典のri+ri-1およびri+1+riの係数を持つ四項評価を独立の対応宣言として未検収。

宣言：`SerrePositivity.Section5.lemma_5_4`

:::

# §5.4 Bounded complexes and their ordinary evaluation

%%%
number := false
tag := "paper-5-4"
%%%

:::definition "paper_eq_5_13" (lean := "SerrePositivity.Section5.betti_growth_of_approximation_limits, SerrePositivity.Section5.exists_minimal_approximation_sequence") (uses := "paper_eq_5_10, paper_eq_5_11")
**式 (5.13)**　最小分解のrankのOとoの評価。対応表の状態：本体にある。

原典 PDF p.27 / layout L1463。Tor長の極限と高次零性から各次数のrankのO(s\_n)と高次o(s\_n)を導く。

:::

:::lemma_ "paper_5_5" (lean := "SerrePositivity.Asymptotic.minimal_truncated_paper_supported, SerrePositivity.Section5.paperOrdinaryEulerK0_eq_of_common_residueField_limits, SerrePositivity.Asymptotic.minimal_truncated_tail_small") (uses := "paper_eq_4_2, paper_eq_5_10, paper_eq_5_13, paper_eq_5_7")
**補題 5.5**　切詰めた最小分解列の商内支持と通常Euler評価。対応表の状態：本体にある。

原典 PDF p.27 / layout L1476。minimal分解の高次rankがo(s\_n)であることを用い、商内でのパラメータ作用の零性を得る。普通長での全共役のEuler値は近似Tor極限から識別する。一般の連結係数の降下はこの支持・評価部分には不要。

*解説 §6.5 有限近似列*

定義 4.18 の有限近似列から、ランク無視の圏の対象とその評価を得る。近似列の存在は定理 4.19（§4.5）で示した。

*命題 6.13（有限近似列から得る対象）*

$`(M_n)` を局所環 $`B` 上の有限近似列とし、ある $`l` で $`\tau_i(k)=0`（$`i>l`）とする。$`M_n` の極小自由分解を $`l` 次で切り詰めた自由複体の列を $`F=(F_n)` とする。

- (a) $`F_n` は $`0` 次から $`l` 次に項をもち、$`1` 次で極小で、$`0` 次の階数は $`\beta_0(M_n)` である。

- (b) $`B\to T'` を有限な局所準同型とし、$`T'` は §6 の設定の代数で、$`\mathfrak{m}_B` の像が支持のイデアルの根基に入り、$`T'\in\mathcal{L}` であるとする。このとき $`F\otimes_BT'` の像 $`X` はランク無視の圏 $`P_{T'}^J` に入り、$`\chi_{\mathrm{ord}}(X)=\sum_{i=0}^{l}(-1)^i\tau_i(T')` である。

*証明*

(a) は極小分解の性質である。(b) では、$`\tau_i(k)=0`（$`i>l`）から $`l` 次より上の Betti 数が $`o(s_n)` になるので、切り詰めの誤差はランク無視の圏で消える。分解の各段は $`\mathfrak{m}_B^a` の零作用から共通の指数で零ホモトピーをもち、商で $`z` に台をもつ。Euler 評価は各段の Tor の長さの交代和の正規化極限である。(c) は $`\operatorname{length}_B(M_n)\le\beta_0(M_n)\,\operatorname{length}_B(B/\mathfrak{m}_B^a)` による。

*Lean:* 切り詰めは \`Asymptotic.MinimalResolutionFamily\` の \`exists\_minimal\_truncated\_sequence\` と \`Section5.exists\_minimal\_approximation\_sequence\`、支持は \`exists\_supported\_minimal\_approximation\`、評価は \`Paper.Section5.ApproximationBetti\` と \`paperOrdinaryEulerK0\_eq\_lambdaChi\`、(c) は \`finiteApproximation\_rank\_lower\_bound\` と \`length\_le\_tor\_zero\_mul\`（証明済み）。

*解説 §9.3 置き換え 2 の準備：パラメータ商と有限近似*

*補題 9.4（有限近似と切り詰め）（Lemma 5.4、5.5）*

補題 9.3 の設定で、正の整数の列 $`s_n\to\infty` と、各 $`\gamma\in G_E` について自由 $`E'` 複体の有界な列 $`F'_\gamma=(F'_{n,\gamma})_n` で、次をみたすものがある。

- (a) $`F'_{n,\gamma}` は $`0` 次から $`l` 次に項をもち、$`1` 次で極小で、$`0` 次の階数 $`\beta_0` は $`\gamma` によらない。

- (b) $`F'_\gamma` の像はランク無視の圏 $`P_{E'}^J` に入り、$`F'_{\mathrm{id}}` の $`\gamma` によるひねりは $`F'_\gamma` である。普通の Euler 特性は $`\chi_{\mathrm{ord}}(F'_\gamma)=c_\sigma`。

*証明*

命題 6.13 を $`T'=E'` と、$`\gamma` でひねった $`B\to E'` に適用し、$`M_n` の極小自由分解を $`l` 次で切った列を $`E'` に移したものを $`F'_{n,\gamma}` とする。(a) と (c) は命題 6.13 (a)、(c) と補題 9.3 (b) から出る。(b) の Euler 特性は

$$`\chi_{\mathrm{ord}}(F'_\gamma)=\sum_i(-1)^i\tau_i(E')=\sum_i(-1)^i\lambda\operatorname{Tor}_i^B(U,E')=\sum_i(-1)^i\lambda\operatorname{Tor}_i^R(C,E')=c_\sigma`

で、三つ目の等号は補題 9.3 (a) による。ひねりは通常の長さを変えないので、$`\gamma` によらない。

*Lean:* 有限近似は \`Section5.lemma\_5\_4\`（証明済み）、そのための作用は \`Paper.Section5.Preparation\`。切り詰め・支持・Euler の計算は \`Paper.Section5.MinimalApproximation\`、\`SupportedApproximation\`、\`ApproximationEuler\`。\`Section5.lambdaChi\_pos\_of\_parameter\_tower\` はこれらを接続し、近似列を内部で構成する。

:::

:::definition "paper_eq_5_14" (lean := "SerrePositivity.Asymptotic.minimal_boundary_rank_isLittleO, SerrePositivity.Asymptotic.minimal_truncated_paper_supported") (uses := "paper_eq_5_13")
**式 (5.14)**　切詰めの境界誤差のsmall rank因子化。対応表の状態：本体にある。

原典 PDF p.28 / layout L1485。最上段の残る誤差を次の自由項を通す実鎖写像の因子化として扱い、そのrankがo(s\_n)なので商で零となる。

:::

# §5.5 A positive normalized evaluation

%%%
number := false
tag := "paper-5-5"
%%%

:::definition "paper_eq_5_15" (lean := "SerrePositivity.Section4.residue_length_pos_of_lengthAlgebra_values, SerrePositivity.LengthAlgebra.length_quotient_ne_top_of_koszul_finite") (uses := "paper_eq_5_11, paper_2_6")
**式 (5.15)**　第二長さ代数の剰余長etaの正値・有限性。対応表の状態：本体にある。

原典 PDF p.28 / layout L1524。長さ代数のパラメータ商から剰余商への全射と有限長フィルトレーションで正値・有限性を得る。

:::

:::definition "paper_eq_5_16" (lean := "SerrePositivity.len_quotient_map_le_length_mul, SerrePositivity.Section4.quotient_length_of_lengthAlgebra_values")
**式 (5.16)**　基底rankを剰余長で下から抑える定量式。対応表の状態：本体にある。

原典 PDF p.28 / layout L1528。一般の有限長D/HをCでテンソルした商長≤length(D/H)×lambda(C/mC)をH=q\_Eへ適用し、左辺を長さ代数のrank公式でr\_Eに同定する。

:::

:::lemma_ "paper_5_6" (uses := "paper_eq_4_2, paper_eq_5_11, paper_eq_5_16, paper_eq_5_17, paper_2_5")
**補題 5.6**　正規化Euler評価の正の定量的下界。対応表の状態：一部。

原典 PDF p.29 / layout L1535。Euler評価≥eta\_E×正規化生成元数、および生成元数のlambda(U)/length(B/m\^a)下界を確認した。原典(5.17)に明示するr\_E≤t\_E eta\_Eも一般の商長評価にある。一方、除算形の二段階下界を本文のb\_sigma,gammaの実評価と一括して返す宣言としては未照合なのでpartialとする。正値性の核心を新しい仮定として置かない。

*解説 §3.3 スカラーの反復錐*

*補題 3.11（新交叉型の消滅）*

$`m\ge0` と $`X` について、ある $`v\ge1` で次の二つが成り立つとする。

- (a) $`X` は指数 $`v` で $`z` に台をもつ（定義 3.8）。

- (b) $`X` の指数 $`v` の Koszul 振幅は $`[0,m]` に入る（定義 3.9）。

このとき $`H_i(X)=0`（$`i<0` または $`i>m-e`）。特に $`m=e` で $`\ell(H_0X)<\infty` なら $`\chi(X)=\ell(H_0X)`。

*証明*

式 （3.1） の $`j=e` の成分により $`H_i(X)` は $`H_{i+e}(K_v\otimes X)` の直和因子であり、$`i+e>m` なら零である。$`i<0` では $`j=0` の成分を使う。零対象の直和因子は零である。$`m=e` では $`0` 次だけが残る。

消滅に長さの値や Euler 有限性は要らない。「自由振幅 $`[0,m]`」は、具体例で Koszul 振幅の条件を確かめるための条件である。また、$`z` に台をもつ指数 $`v` の存在は仮定に含める。$`e=0` の場合も同じ定理で扱い、$`m<e` なら全次数で消滅する。Lean 内部の cochain 添字は $`q=-i` で本文の $`H_i` に変換する。

*補題 3.12（$`0` 次の下界）*

$`X` が指数 $`v` で $`z` に台をもち、$`H_i(X)=0`（$`i<0`）であるとき、 $`H_0(K_v\otimes X)\cong H_0(X)`。有限な長さをもつ対象 $`Y` への全射 $`H_0(K_v\otimes X)\twoheadrightarrow Y` があれば、$`\ell(H_0X)\ge\ell(Y)`。さらに $`m=e` の消滅と有限性があれば $`\chi(X)\ge\ell(Y)`。

*証明*

式 （3.1） の $`n=0` では $`j>0` の成分が消える。全射の核による短完全列と長さの非負性から不等式が出る。

全射の構成は極小性などの具体的な入力で行う。その下界を Euler 評価の下界にするために、高次の消滅を別に使う。

*Lean:* \`CategoryTheory.IteratedCone\` の \`iteratedZeroCone\_homology\_zero\_iso\`（第零次の同型）、\`iteratedZeroCone\_length\_lower\_bound\`（長さの下界）、\`iteratedZeroCone\_euler\_eq\_length\_zero\`（$`m=e` の消滅の下で $`\chi(X)=\ell(H_0(K_v\otimes X))`）、\`iteratedZeroCone\_euler\_lower\_bound\`（Euler 評価の下界）。いずれも証明済み。

*解説 §6.4 消滅と下界：補題 3.11、3.12 の適用*

§5.3 と同じく、補題 3.11 の仮定（台の条件と Koszul 振幅の条件）と補題 3.12 の全射を、列の圏について確かめる。台の条件は商での零作用、Koszul 振幅の条件は $`K_v\otimes F` の各段のフィルトレーション、全射は各段の極小性から出る。元の列 $`F` の一様な台は使わない。

*補題 6.11（新交叉型の消滅）（補題 5.10 の対応物）*

$`e` を列 $`z` の長さとし、全ての $`v\ge1` と $`j>0` で $`\lambda H_j(z^v;C)=0` とする。$`F = (F_n)` を $`0` 次から $`m` 次に有限自由な項をもつ有界な自由列で、像 $`X` が $`P_T^J` に入るものとする。このとき $`b_i^C(X) = 0`（$`i > m-e`）。特に $`m = e` なら $`\chi_C(X) = b_0^C(X)`。

*証明*

台の条件は $`P_T^J` での零作用である。Koszul 振幅の条件は $`K_v\otimes F` の各段を項でフィルトレーションし、正次数の Koszul ホモロジーの長さ零を使って確認する。指定範囲外のホモロジー列は各段で長さ零なので、評価先でも零対象になる。補題 3.11 から $`H_i^C(X)=0`、したがって $`b_i^C(X)=0` が従う。

*Lean:* \`Asymptotic.RankVanishing\` の \`completedRankHomology\_vanishing\`（補題 3.11 の \`iteratedZeroCone\_vanishing\` を Koszul 塔 \`Asymptotic.KoszulTower\` に適用）、\`PaperVanishing\`（Koszul 条件を入力として証明済み）。

*解説 §6.6 $`\lambda`-平坦な代数での適用*

*系 6.14（$`\lambda`-平坦な代数での比較・消滅・下界）*

- (c) *消滅と下界*：補題 6.11、6.12 が成り立つ。

*証明*

系 5.12 の証明と同じく、系 4.11 で Koszul 条件を得て、命題 6.7、定理 6.9、補題 6.11、6.12 に入れる。

*Lean:* \`Paper.Section4.FlatRealization\` の \`symmetricPaperEuler\_conjSum\_eq\_of\_flat\`、\`paperBaseChangeHomology\_vanishing\_of\_flat\`、\`paperBaseChangeEuler\_minimal\_lower\_bound\_of\_flat\`（基底の Koszul 分解と降下を明示した形で証明済み）。係数環は $`A\to S\to C` と一般の $`S` 上の自由複体列で扱う。

*解説 §7.4 正値性の評価（Lemma 5.6）*

*命題 7.11（Lemma 5.6 の一般形）*

§6 の設定で、$`A` を次元 $`e` の正則局所環、$`z` をその正則パラメータ系、$`T` を局所 $`A` 代数とし、$`(C,\lambda)` を $`\lambda`-平坦で $`\lambda(C/\mathfrak{m}_TC)>0` となる長さ付き $`A` 代数とする。$`F=(F_n)` を $`0` 次から $`e` 次に有限自由な項をもつ有界な自由 $`T` 複体の列で、像 $`X` が $`P_T^J` に入り、各 $`F_n` が $`1` 次で極小なものとし、$`\nu=\lim_\mathcal{U}\beta_0(F_n)/s_n>0` とする。このとき

$$`\chi_C(X)=b_0^C(X)\;\ge\;\nu\cdot\lambda(C/\mathfrak{m}_TC)\;>\;0.`

*証明*

系 6.14 (c) により、補題 6.11 と 6.12 が使える。列の長さは $`e=\dim A` なので、$`m=e` として $`\chi_C(X)=b_0^C(X)\ge\nu\cdot\lambda(C/\mathfrak{m}_TC)` を得る。正値性は $`\nu>0` と仮定から出る。

*Lean:* 一般の下界は \`Asymptotic.PaperMinimalLowerBound\` の \`paperBaseChangeEuler\_minimal\_lower\_bound\`。$`\lambda`-平坦性から入力を供給する形は \`Paper.Section4.FlatRealization\` の \`paperBaseChangeEuler\_minimal\_lower\_bound\_of\_flat\`（証明済み）。

*解説 §9.5 正値性*

*補題 9.6（Lemma 5.6、正値性）*

*証明*

命題 7.11 を $`A = A_E`（次元 $`l`）、$`T = E'`、$`(C_E,\lambda_E)`、$`F = F'_\gamma` に適用する。$`(C_E,\lambda_E)` は定理 8.5 (b) により $`\lambda`-平坦で、系 8.7 により非自明である。$`F'_\gamma` は補題 9.4 (a) により $`0` 次から $`l` 次に項をもつ $`1` 次で極小な自由列で、$`\nu_\sigma>0` は補題 9.4 (c) による。

$`D` 側の $`\lambda`-CM 性（命題 7.10）が複体の長さを $`l` に抑え、$`E` 側の $`\lambda`-平坦性（命題 7.11）が長さ $`l` の複体の高次を消す。2つの $`l` が噛み合うのは $`h + l = \dim R` による。

*Lean:* \`Section5.exists\_secondComparison\_pos\_of\_approximation\` が、同じ有限近似から第二比較の対象と全ての共役の正値性を同時に構成する（保留した降下を除いて証明済み）。個別の入口として \`secondComparison\_minimal\_lower\_bound\`、\`paperEuler\_pos\_of\_finiteApproximation\` もある。

宣言：`SerrePositivity.Asymptotic.paperBaseChangeEuler_minimal_lower_bound`、`SerrePositivity.Section5.finiteApproximation_rank_lower_bound`、`SerrePositivity.Section4.residue_length_pos_of_lengthAlgebra_values`、`SerrePositivity.len_quotient_map_le_length_mul`

:::

:::definition "paper_eq_5_17" (uses := "paper_eq_4_2, paper_eq_5_11, paper_eq_5_16, paper_2_5")
**式 (5.17)**　二段階の明示的な正の下界。対応表の状態：一部。

原典 PDF p.29 / layout L1538。eta×生成元数、およびlambda(U)/length(B/m\^a)という下界までは対応する。(5.16)の商長不等式もあるが、表示の除算形全体と本文のb\_sigma,gammaを一括した型としては未検収。

*解説 §6.4 消滅と下界：補題 3.11、3.12 の適用*

*補題 6.12（$`0` 次の下界）（補題 5.11 の対応物）*

補題 6.11 の設定で $`m=e` とし、各 $`F_n` が $`1` 次で極小であるとする。このとき

$$`b_0^C(X) \;\ge\; \Bigl(\lim_\mathcal{U}\frac{\beta_0(F_n)}{s_n}\Bigr)\cdot\lambda(C/\mathfrak{m}_T C).`

*証明*

各段の極小性は

$$`H_0(K_v\otimes F_n\otimes C) =C^{\oplus\beta_0(F_n)}/(\operatorname{im}d_1+(z^v)) \twoheadrightarrow(C/\mathfrak{m}_T C)^{\oplus\beta_0(F_n)}`

を与える。この全射の列を評価先に送り、補題 3.12 と正規化極限による長さの計算を使う。

*Lean:* $`\chi(X)=\ell(H_0(K_v\otimes X))` の部分は \`Asymptotic.RankVanishing\` の \`completedRankEuler\_eq\_koszul\_zero\_limit\_of\_koszul\`（補題 3.12 の \`iteratedZeroCone\_euler\_eq\_length\_zero\` の適用）、全射による下界は \`completedRankEuler\_koszul\_lower\_bound\`（\`iteratedZeroCone\_euler\_lower\_bound\` の適用）。極小性から全射を作る部分は \`Asymptotic.RankMinimalLowerBound\`、\`PaperMinimalLowerBound\`（証明済み）。

既存の二項係数の数値公式から非負性を使って長さの消滅を得る方法でも、忠実な長さによって同じ零対象の結論に戻せる。実装では対象としての抽象的消滅を使い、数値の二項係数公式との対応も証明している。

*解説 §9.5 正値性*

*補題 9.6（Lemma 5.6、正値性）*

$$`b_{\sigma,\gamma} \;\ge\; \nu_\sigma\cdot\lambda_E(C_E/\mathfrak{m}_{E'}C_E) \;>\; 0.`

宣言：`SerrePositivity.Asymptotic.paperBaseChangeEuler_minimal_lower_bound`、`SerrePositivity.Section5.finiteApproximation_rank_lower_bound`、`SerrePositivity.len_quotient_map_le_length_mul`

:::

:::definition "paper_eq_5_18" (uses := "paper_4_7, paper_5_1, paper_5_2, paper_5_5, paper_5_6")
**式 (5.18)**　第二平均から第1平均の各c\_sigmaの正値性。対応表の状態：未証明の入力に依存。

原典 PDF p.29 / layout L1577。実際の第二比較の等式と各共役の正値性を接続する入口があるが、原典のTheorem4.7の代わりにsupportedRankK0\_descentのsorry入力に依存する。

*解説 §9.4 置き換え 2*

*命題 9.5（式 (5.18)）*

$`b_{\sigma,\gamma} = \chi_{C_E}(F'_\gamma)`（系 6.5 の $`C_E` と $`\lambda_E` による Euler 特性）とおくと

$$`|G_E|\cdot c_\sigma \;=\; \sum_{\gamma\in G_E} b_{\sigma,\gamma}. \tag{9.1}`

*証明*

定理 7.9 を $`A = A_E`、$`T = E'`、$`(C_E,\lambda_E)`、$`G_E` と $`X = F'_{\mathrm{id}}` に適用する。仮定は設定と補題 9.1 からそろう。$`X^\gamma = F'_\gamma` なので、補題 9.4 (b) により左辺の和は $`\sum_\gamma\chi_{\mathrm{ord}}(F'_\gamma)=|G_E|\,c_\sigma` である。

これが §2 の （2.2） である。

*Lean:* \`Section5.secondComparison\_of\_approximation\`（有限近似・Koszul 分解・降下などを明示的な入力として証明済み）。

宣言：`SerrePositivity.Section5.exists_secondComparison_pos_of_regular`、`SerrePositivity.Section5.secondComparison_of_approximation`

:::

