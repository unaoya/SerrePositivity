import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.Paper.Section5.FirstComparison
import SerrePositivity.Paper.Section5.SecondComparison
import SerrePositivity.Paper.Statement

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "§1 Introduction" =>
%%%
number := false
tag := "paper-1"
%%%

本論文 §1 の項目と、本体の宣言との対応。各項目の頭は対応表（`research/paper-coverage`）の照合の理由、その下は解説から移した本文（あるものだけ）。

*解説 §3 共通の抽象論*

この節では、証明で繰り返し使う一般論を、三角圏とアーベル圏の言葉だけで述べる。環や長さ付き代数はここでは使わない。

*前提*

- 長さ付きアーベル圏 $`(\mathcal{A},\ell)`（定義 3.1）。

- 三角圏 $`\mathcal{K}` と、ホモロジー的関手 $`H_*\colon\mathcal{K}\to\mathcal{A}`（定義 3.2）。Euler 評価にはさらに Euler 有限性（定義 3.3）を仮定する。

- §3.3 ではさらに、可換環 $`A` とその元の有限列 $`z` を固定し、$`\mathcal{K}` が $`A` 線形でシフトも $`A` 線形であることを仮定する。

*結論と使う場所*

- 結論　／　使う場所
- Euler 評価（命題 3.4）：Euler 数が $`K_0(\mathcal{K})` 上の準同型になる　／　§5、§6 の評価関手
- 共役和の比較（命題 3.6、基底公式つきの形は系 3.7。群論の部分は補題 3.5）：基底から来る類で一致し不変類が降下すれば、共役和が一致する　／　§5、§6 の比較定理、命題 7.5（Lemma 3.5c）、定理 7.9（Theorem 4.7）
- 反復錐による消滅（補題 3.11）：スカラーが零作用する対象では高次のホモロジーが消える　／　§5、§6 の消滅、§5.5 の次数の上界
- 第零次の下界（補題 3.12）：消滅のもとで Euler 数を第零次の長さで下から押さえる　／　§5、§6 の下界、§9 の正値性

§4 で長さ付き代数から評価先 $`\mathcal{A}` を作り、§5（perfect 複体）と §6（ランク無視の圏）で評価元 $`\mathcal{K}` と関手 $`H_*` を作って、ここでの前提と各結論の仮定を確かめる。§7 と §9 はその適用である。

*解説 §7 論文の状況での命題*

この節では、§5、§6 の一般論に論文の状況を入れて、§9 で使う四つの命題を導く。

- 命題　／　使う一般論　／　§9 での役割
- §7.1 Lemma 3.5　／　定理 5.9（比較）　／　置き換え 1
- §7.2 Theorem 4.7　／　定理 6.9（比較）　／　置き換え 2
- §7.3 Lemma 5.3　／　補題 5.13、5.14（長さの一致と次数の上界）　／　有限近似の準備
- §7.4 Lemma 5.6　／　系 6.14（$`\lambda`-平坦での消滅と下界）　／　正値性

§7.1、§7.2 では次を仮定する。

$`(R,\mathfrak{m})` を正則局所環、$`M, N` を有限生成 $`R` 加群で $`M\otimes_R N` が有限長とする。$`R` は正則なので Tor は有限個を除いて $`0` であり、Serre の交点重複度

$$`\chi^R(M,N) = \sum_i (-1)^i \operatorname{length}_R \operatorname{Tor}_i^R(M,N)`

が定まる。

*Lean:* \`IntersectionMultiplicity.Basic\`（$`\chi` の定義）。

:::theorem "paper_1_1" (lean := "SerrePositivity.main_statement, SerrePositivity.core_statement") (uses := "paper_eq_5_10, paper_eq_5_11, paper_2_2, paper_2_3, paper_2_5, paper_2_6, paper_3_1, paper_4_7, paper_5_1, paper_5_2, paper_5_5, paper_5_6, ext_Stacks_03QH, ext_Stacks_0BRI, ext_Stacks_0BRJ")
**定理 1.1**　Serreの交点重複度の狭義正値性。対応表の状態：未証明の入力に依存。

*主張*　$`(R,\mathfrak m)` を次元 $`d` の可換ネーター正則局所環とする。非零有限生成 $`R` 加群 $`M,N` のテンソル積が有限長で $`\dim_R M+\dim_R N=d` なら、Serre の交点重複度 $`\chi^R(M,N)` は狭義に正である。

原典 PDF p.1 / layout L27。一般の正則局所環と非零有限生成加群、有限長テンソルと相補次元からchi\>0という主張の型は一致する。宣言自身はsorryなしだが、完全な証明はperfectoidizationのE3入力・通常のK0降下・漸近K0降下の三つのsorry付き入力に依存する。

*解説 §9.6 結論*

*定理 1.2 の証明*

補題 9.2、命題 9.5、補題 9.6 を合わせて

$$`|G_D|\, a_D a_E\, \chi^R(D,E) \;=\; \sum_{\sigma\in G_D}c_\sigma \;=\; \frac{1}{|G_E|}\sum_{\sigma\in G_D}\sum_{\gamma\in G_E} b_{\sigma,\gamma} \;>\; 0.`

$`|G_D|a_Da_E>0` なので $`\chi^R(D,E)>0` である。

*Lean:* \`chi\_pos\_of\_firstComparison\`、\`core\_of\_twistedEuler\_pos\` が第一比較と各 $`c_\sigma>0` を接続する。\`Section5.core\_of\_lengthAlgebras\` は与えられた長さ代数から第二比較と正値性を導き、\`core\_of\_lengthAlgebras\_with\_parameter\_choice\` はパラメータの選択も内部で行う。\`Section5.core\_of\_normalization\_bases\` は、正規化基底 $`A_D`、$`A_E` と、不変環が基底になる有限群作用付きの有限局所拡大 $`D'`、$`E'` を受け取り、定理 8.5 で長さ代数を作って $`\chi^R(D,E)>0` を出す（引用を除いて証明済み）。\`Paper.Section5.GaloisNormalization\` と \`Paper.Section5.Core\` が基底と Galois 閉包を構成し、\`core\_statement\` に接続する。一般加群・一般局所環への帰着を経て \`main\_statement\` を導くが、引用と保留K理論への依存は残る。

*定理 1.1（Thm 1.1）*

$`M, N` が $`0` でなく $`\dim M + \dim N = \dim R` なら $`\chi^R(M,N) > 0`。

*Lean:* \`main\_statement\`。

外の文献：Stacks 03QH、Stacks 0BRI、Stacks 0BRJ

:::

# §1.2 Proof strategy

%%%
number := false
tag := "paper-1-2"
%%%

:::definition "paper_fig_1" (lean := "SerrePositivity.firstComparison, SerrePositivity.Section5.secondComparison_of_approximation") (uses := "paper_eq_5_18, paper_5_2, paper_5_6")
**図 Figure 1**　二つのnorm比較の図。対応表の状態：一部。

*主張*　二度のノルム比較により、最初に $`|G_D|a_Da_E\chi^R(D,E)=\sum_\sigma c_\sigma` とし、続いて各 $`\sigma` について $`|G_E|c_\sigma=\sum_\gamma b_{\sigma,\gamma}>0` を得る。最初は $`A_D\subset D'` での通常の台つき比較、次は $`A_E\subset E'` での漸近比較で、厳密な下界には一様な消去冪と生成元数を用いる。

原典 PDF p.3 / layout L127。二つの有限群和の等式に対応する宣言はあるが、図全体のデータやc\_sigma、b\_sigma,gammaの整合的な一括実現は独立の宣言にしていない。比較の適用には下記の未証明降下入力が残る。

:::

# §1.3 Consequences

%%%
number := false
tag := "paper-1-3"
%%%

:::corollary "paper_1_2" (uses := "paper_1_1, ext_Jannsen_A_4_1, ext_Skalit15_3_10, ext_Skalit15_3_4, ext_Skalit15_3_5, ext_Skalit15_3_8")
**系 1.2**　有限なstrict transform交叉と重複度積の下界。対応表の状態：なし。

原典 PDF p.4 / layout L155。associated gradedのテンソルTの次元≤1という条件からchiとHilbert–Samuel重複度積の不等式、および等号とdim T=0の同値をまとめる宣言を確認できない。KST/DerivedBlowupのチャートや主定理だけをこの系の証明とはしない。

外の文献：Jannsen A.4(1)、Skalit15 3.10、Skalit15 3.4、Skalit15 3.5、Skalit15 3.8

:::

