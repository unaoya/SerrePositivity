-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.BhattScholze.Inputs.PerfectoidizationInterface
import SerrePositivity.CommutativeAlgebra.RegularLocalRing.FlatBaseChange
import SerrePositivity.CommutativeAlgebra.RootTower.Basic
import SerrePositivity.CommutativeAlgebra.RootTower.Stage
import SerrePositivity.IntersectionMultiplicity.Basic
import SerrePositivity.LengthAlgebra.RootTowerLength.Tower
import SerrePositivity.Paper.Section2.Lemma2_4
import SerrePositivity.Paper.Section2.LengthAlgebra
import SerrePositivity.Paper.Section2.LengthAlgebra.EqualChar
import SerrePositivity.Paper.Section2.LengthAlgebra.Formulas
import SerrePositivity.Paper.Section2.LengthAlgebra.MixedChar
import SerrePositivity.Paper.Section2.NormalizationBase
import SerrePositivity.Paper.Section2.ResidueFieldExtension
import SerrePositivity.Paper.Section3.LengthComputation
import SerrePositivity.Paper.Section4.LengthHypotheses

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "§2 Residue fields and normalized length" =>
%%%
number := false
tag := "paper-2"
%%%

本論文 §2 の項目と、本体の宣言との対応。各項目の頭は対応表（`research/paper-coverage`）の照合の理由、その下は解説から移した本文（あるものだけ）。

*解説 §4 長さ付き代数*

この節には二つの役割がある。

1. *§3 の評価先を作る*（§4.2）。長さ付き代数 $`(C,\lambda)` から、長さ零の加群で割った Serre 商として、定義 3.1 の長さ付きアーベル圏 $`(\mathcal{A}_\lambda^{\mathrm{fin}},\ell_\lambda)` を作る。評価元 $`\mathcal{K}` とホモロジー的関手 $`H_*` は §5、§6 で作る。

2. *長さ付き代数に課す条件を整理する*（§4.3、§4.4、§4.5）。Koszul 有限性、$`\lambda`-平坦性とランク、$`\lambda`-CM 性を定義し、その間の関係を示す。これは §3 の結果を言い換えたものではなく、§5、§6 で §3 の結論の仮定を確かめるときの材料になる。

- この節で扱う条件　／　§5、§6 で確かめる §3 の仮定
- Koszul 有限性（定義 4.8）　／　Euler 有限性（定義 3.3）：Euler 評価が定まること
- 正次数の Koszul ホモロジーの長さ零　／　Koszul 振幅の条件（定義 3.9）：消滅
- Koszul Euler 特性 $`e_\lambda(z;C)` の値　／　命題 3.6 の (a)：基底公式の係数
- $`\lambda`-平坦性と有限ランク（系 4.11）、$`\lambda`-CM 性（命題 4.15）　／　上の三つをまとめて供給する十分条件

共通定理は上の三つの条件を別々に受け取る。有限性だけで Euler 評価を作り、消滅と値は必要な結論にだけ加えるためである。§4.5 では塔と整合する長さを定義し、有限加群でない対象を有限長加群の列で近似できること（定理 4.19、Lemma 5.4 の一般形）を示す。

*解説 §7 論文の状況での命題*

*補題 7.1（Koszul Euler 特性の階数公式）*

§7.3、§7.4 の設定はそれぞれの命題の中で述べる。いずれも長さ付き代数の性質（$`\lambda`-平坦性、$`\lambda`-CM 性、非自明性）は仮定として受け取り、それをみたす代数の構成は §8 で行う。

*解説 §8 $`\lambda`-平坦な長さ付き代数の構成*

この節は §5、§6 の一般論に、具体的な $`\lambda`-平坦な長さ付き代数を入力として与える。ほぼ全てが文献からの引用である。

*系 8.7（Corollary 2.6 (3)、非自明性）*

*§9 で使う性質*

定理 8.5、系 8.7、命題 8.3 のうち、§9 で使うのは次の四つである。

- (a) $`D` 上の $`\lambda`-CM 性と系 8.7（非自明性）：命題 7.10（パラメータ商）の入力。

- (b) $`A` 上の $`\lambda`-平坦性と有限ランク：命題 7.5（Lemma 3.5c）と定理 7.9（Theorem 4.7）の入力。

- (b) と系 8.7：命題 7.11（正値性の評価）の入力。

- (c) 塔と整合する長さの係数制限であること（命題 8.3）：定理 4.19（有限近似列の存在）の入力。

# §2.1 Extending the residue field

%%%
number := false
tag := "paper-2-1"
%%%

:::lemma_ "paper_2_1" (lean := "SerrePositivity.Section2.lemma_2_1, SerrePositivity.supportDim_baseChange_of_map_maximalIdeal, SerrePositivity.chi_baseChange_of_map_maximalIdeal") (uses := "ext_Ma17_2_2")
**補題 2.1**　剰余体を代数閉体へ拡大する完備平坦局所拡大。対応表の状態：本体にある。

*主張*　完備ネーター局所環 $`(B,\mathfrak b,k)` から、剰余体が $`k` の代数閉包で極大イデアルが $`\mathfrak bB'` となる完備ネーター局所環 $`B'` への平坦局所射がある。任意の有限 $`B` 加群の $`\mathfrak b^a` 商の長さは $`a\ge1` で保存され、次元・有限長・環の正則性も保存される。テンソル積が有限長の有限加群対ではすべての Tor の長さも保存される。

原典 PDF p.5 / layout L215。完備Noether局所環から代数閉剰余体を持つ完備平坦局所拡大を構成し、極大イデアル・Hilbert–Samuel関数・正則性・Tor長を保存する。module dimensionとchiの保存は表示した共通層の宣言で補う。

外の文献：Ma17 2.2

:::

# §2.2 Regular bases and the tower length

%%%
number := false
tag := "paper-2-2"
%%%

:::lemma_ "paper_2_2" (lean := "SerrePositivity.Section2.lemma_2_2") (uses := "ext_KuranoShimomoto, ext_KuranoShimomoto_1_1")
**補題 2.2**　正則な正規化基底の存在。対応表の状態：本体にある。

*主張*　$`D` を次元 $`h>0` の完備ネーター局所整域で剰余体 $`k` が標数 $`p>0` の完全体とすると、剰余体に恒等射を誘導する有限かつ生成点で分離的な正則部分環 $`A\subset D` がとれる。$`\operatorname{char}D=p` では $`A=k[[t_1,\ldots,t_h]]`、標数零では $`A=W(k)[[t_2,\ldots,t_h]]` で $`t_1=p` とし、$`(t_1,\ldots,t_h)` は $`D` のパラメータ系かつ $`A` の正則パラメータ系になる。

原典 PDF p.6 / layout L262。完全な正標数剰余体を持つ完備局所整域に、同じ剰余体の有限・生成的分離な正則基底を構成する。等標数の冪級数環と混標数のWitt冪級数環との具体的同型およびパラメータも結論に含む。

*解説 §8 $`\lambda`-平坦な長さ付き代数の構成*

*補題 8.4（Lemma 2.2、等標数分岐も証明済み）*

剰余体が完全な完備局所整域 $`D` に対し、定義 8.1 の形の正則部分環 $`A\subseteq D` で、$`D` が $`A` 上有限かつ $`\operatorname{Frac}(D)/\operatorname{Frac}(A)` が分離的なものがとれる。

標数 $`p` は Cohen–Gabber の定理（Kurano–Shimomoto の初等的証明。原典は $`k` の完全性も $`D` の整域性も仮定しない一般形）。混標数は Cohen の構造定理で係数環 $`W(k)\subseteq D` をとり、$`p` を $`D` のパラメータ系 $`p,t_2,\dots,t_h` に延ばす。完備性から $`W(k)[[t_2,\dots,t_h]]\to D` は有限で、次元の等しい正則局所整域からの写像なので単射、分離性は標数 $`0` で自動である。

*Lean:* \`Section2.lemma\_2\_2\`。等標数は \`exists\_cohen\_gabber\_normalization\` の微分経路の実構成から接続する。係数切断を変更し、完備微分の生成点の次元を環の次元へ減らし、微分基底を持つパラメータを選ぶ。同じ有限単射の相対微分の消滅から分数体拡大の分離性を証明した。\`Inputs.cohen\_gabber\_normalization\`は証明済みの互換入口である。混標数は \`exists\_cohen\_normalization\_mixedCharacteristic\` で上記の係数写像・有限評価・単射性を実構成し、既存の型を保った入口へ接続済み。

*基底と Galois 閉包：2段階の準備*

1. *正則な基底をとる*：$`D` の中に、$`D` がその上有限で $`\operatorname{Frac}(D)/\operatorname{Frac}(A_D)` が分離的になる正則部分環 $`A_D` をとる（補題 8.4、Cohen–Gabber）。$`A_D` は $`k[[t]]` または $`W(k)[[t]]` の形にとれるので、塔と $`\lambda_\infty` の構成（§8）にも使える。

外の文献：KuranoShimomoto、KuranoShimomoto 1.1

:::

:::definition "paper_eq_2_1" (lean := "SerrePositivity.Section2.TowerStage, SerrePositivity.Section2.Tower") (uses := "paper_2_2")
**式 (2.1)**　根の塔A\_nと未完備極限Lambda。対応表の状態：本体にある。

*主張*　補題 2.2 で選んだ基底環 $`A` のパラメータの整合する根をとり、$`A_n=A[t_1^{1/p^n},\ldots,t_h^{1/p^n}]` とする。未完備の塔の極限を $`\Lambda=\varinjlim_n A_n` とおく。

原典 PDF p.6 / layout L280。パラメータのp\^n乗根を付加した有限段とdirect limitを定義する。完備化A\_inftyと未完備Lambdaを同一視しない。

*解説 §4.5 塔と整合する長さ*

*定義 4.16（塔）*

可換環 $`A` 上の*塔*とは、$`A` 代数の増大列 $`A=A_0\subseteq A_1\subseteq\cdots` で、各 $`A_j` が $`A` 上階数 $`s_j` の有限自由加群であり、遷移写像 $`A_j\to A_{j'}` が平坦なものをいう。$`\Lambda=\bigcup_j A_j` と書く。

*解説 §8 $`\lambda`-平坦な長さ付き代数の構成*

*定義 8.1（塔）*

$`A = k[[t_1,\dots,t_h]]` または $`W(k)[[t_2,\dots,t_h]]`（$`t_1 = p`、$`k` は完全体）に対し $`A_n = A[t^{1/p^n}]`、$`\Lambda = \bigcup A_n`。$`\mathfrak{m}_A` の冪で消される $`\Lambda` 加群に、有限段では $`\lambda_\infty(V_n\otimes\Lambda) = p^{-nh}\operatorname{length}(V_n)`、有限生成加群では全射する有限表示加群の下限、一般には有限生成部分加群の上限、として $`\lambda_\infty` を定める（Faltings）。

:::

:::lemma_ "paper_2_3" (lean := "SerrePositivity.Section2.towerStage_free, SerrePositivity.Section2.finrank_towerStage, SerrePositivity.Section2.towerLength, SerrePositivity.Section2.towerLength_hasSup, SerrePositivity.Section2.towerLengthFun_tensor, SerrePositivity.Section2.towerLengthOn_eq_completedTowerLength") (uses := "paper_eq_2_2, clmst_2_2_1, clmst_2_2_3, clmst_2_2_6, ext_Faltings_Appendix_2")
**補題 2.3**　根の塔の段と正規化長さの構成。対応表の状態：本体にある。

*主張*　各 $`A_n` は剰余体 $`k` をもつ完備正則局所環で、$`b\ge a` なら $`A_b` は $`A_a` 上階数 $`p^{(b-a)h}` の自由加群である。$`\mathfrak m_A` のある冪で消える $`\Lambda` 加群上に非負加法的な長さがあり、有限表示の場合は有限段の長さを $`p^{nh}` で割り、有限生成の場合は有限表示全射からの下限、一般には有限生成部分加群からの上限で求まる。混標数の場合、$`p` 進完備化上の固定冪で消える加群を $`\Lambda` に制限しても長さは同じである。

原典 PDF p.6 / layout L286。各段の有限自由性・ランク、正規化長さの加法性・有限段公式・有限生成上限、および混標数の完備塔との比較を個別の宣言で実装する。Stage.leanの完備正則局所環・段間ランクの証明も原典の構成と照合した。

*解説 §4.1 長さ関数と長さ付き代数*

*定義 4.1（長さ関数）*

$`C` を環、$`J\subseteq C` をイデアルとする。$`C` 加群 $`M` が \*\*$`J`-冪ねじれ\*\*であるとは、ある $`N` で $`J^N M = 0` となること。$`J`-冪ねじれ加群は部分加群・商・拡大で閉じる（$`J^a M' = 0`、$`J^b M'' = 0` なら $`J^{a+b}M = 0`）。$`J`-冪ねじれ $`C` 加群の上の*長さ関数*とは、$`[0,\infty]` 値の関数 $`\lambda` で、$`\lambda(0)=0`、同型で不変、かつ $`J`-冪ねじれ加群の短完全列について加法的なもの。$`0` でない加群の $`\lambda` が $`0` になることを許す。

*例 4.2*

1. 普通の長さ $`\operatorname{length}_C` は全ての $`C` 加群の短完全列について加法的なので、$`J = 0` の長さ関数である（全ての加群は $`0`-冪ねじれ）。その制限として、任意の $`J` について長さ関数になる。

2. Faltings の正規化長さ $`\lambda_\infty`（定義 8.1）は、塔 $`\Lambda` 上の $`\mathfrak{m}_A\Lambda`-冪ねじれ加群の上の長さ関数である。§8 で使う。

*解説 §4.5 塔と整合する長さ*

*定義 4.17（塔と整合する長さ）*

$`A` をネーター局所環、$`(A_j)` をその上の塔とする。$`\mathfrak{m}_A\Lambda`-冪ねじれ $`\Lambda` 加群の上の長さ関数 $`\lambda` が*塔と整合する*とは、次をみたすことをいう。

- (iii) *有限生成加群での一致*：有限生成加群 $`M` について、$`\lambda(M)` は $`M` に全射する有限表示加群の $`\lambda` の下限に等しい。

- (iv) *段への降下*：有限表示の $`\Lambda` 加群は、ある段 $`A_j` 上の有限表示加群の係数拡大である。

長さ付き代数 $`(C,\lambda_C)` が塔と整合するとは、$`\Lambda` 代数の構造 $`\Lambda\to C` があって、$`\lambda_C` が塔と整合する長さの係数制限であることをいう。

§8 では、具体的な塔の上で $`\lambda_\infty` を構成し、これらの性質を示す（命題 8.3）。(i)–(iv) と加法性は、Noether 局所基底・素数・座標条件の下で証明済みである。

この設定から、有限加群でない対象を有限長加群の列で近似できる。近似列の定義は、§6.5 でランク無視の圏の対象を作るときにも使う。

*解説 §8 $`\lambda`-平坦な長さ付き代数の構成*

*定義 8.1（塔）*

各 $`A_n` は剰余体 $`k` の完備正則局所環で、$`A_a\to A_b`（$`a\le b`）はランク $`p^{(b-a)h}` の有限自由である（Lemma 2.3）。CLMST の記法では $`\Lambda` が $`A_\infty^{\mathrm{nc}}`、その $`p` 進完備化が perfectoid 環 $`A_\infty` で、$`\mathfrak{m}_A` の固定した冪で消える加群については両者の上の長さは一致する（Lemma 2.3 の最後の主張）。

*Lean:* \`Paper.Section2.Tower\`、\`TowerLength\`、\`TowerDescent\`、\`TowerStage\`（塔の段の性質と有限段の公式は証明済み）。有限生成・有限表示の場合の一致と一般加法性は、Noether 局所基底・素数・座標条件の下で証明済み。

*命題 8.3（$`\lambda_\infty` は塔と整合する）*

定義 8.1 の $`(A_n)` は定義 4.16 の意味の塔（$`s_n=p^{nh}`）で、$`\lambda_\infty` は加法的で、定義 4.17 の意味で塔と整合する長さである。

*証明*

各段が $`A` 上自由で遷移写像が平坦であることは単項式基底から示す。有限段の公式と段への降下は塔の段の性質から、上限の性質は $`\lambda_\infty` の構成と補題 8.2 から出る。有限生成加群での一致（$`\lambda=\lambda^*`）は有限段の長さ計算から証明済みであり、加法性も有限段の長さと有限生成近似から証明した。

*Lean:* 塔の段は \`Paper.Section2.TowerStage\`（\`flat\_tower\` など）、有限段の公式と降下は \`TowerDescent\`（\`towerLengthFun\_tensor\`、\`exists\_descent\`）、上限の性質は \`towerLength\_hasSup\`。有限生成加群での一致は \`towerLengthFun\_eq\_fgLength\`（証明済み）、加法性は \`towerLengthFun\_add\_of\_exact\`（証明済み、有限段の長さと近似による）。一般の有限生成・有限表示の場合の一致は \`LengthAlgebra.RootTowerLength.FiniteGeneration\` で証明する。

外の文献：CLMST 2.2.1、CLMST 2.2.3、CLMST 2.2.6(a)、Faltings Appendix 2

:::

:::definition "paper_eq_2_2" (lean := "SerrePositivity.Section2.towerLengthFun_tensor")
**式 (2.2)**　有限段からの基底変換の正規化長。対応表の状態：本体にある。

*主張*　塔の段 $`A_n` 上の有限長加群 $`V_n` から降りてくる有限表示加群の正規化長は、$`\lambda_\infty(V_n\otimes_{A_n}\Lambda)=p^{-nh}\operatorname{length}_{A_n}(V_n)` である。

原典 PDF p.6 / layout L293。有限長A\_n加群からの基底変換の長さをstageRank=p\^(nh)で割る公式。

*解説 §4.5 塔と整合する長さ*

*定義 4.17（塔と整合する長さ）*

- (i) *有限段の公式*：有限長 $`A_j` 加群 $`V` について $`\lambda(\Lambda\otimes_{A_j}V)=\operatorname{length}_{A_j}(V)/s_j`。

:::

:::definition "paper_eq_2_3" (lean := "SerrePositivity.Section2.towerLength_hasSup") (uses := "clmst_2_2_1, clmst_2_2_3, clmst_2_2_6, ext_Faltings_Appendix_2")
**式 (2.3)**　有限生成部分加群の長さの上限。対応表の状態：本体にある。

*主張*　$`\mathfrak m_A` のある冪で消える任意の $`\Lambda` 加群 $`V` の正規化長は、有限生成部分加群 $`V_0\subseteq V` の長さ $`\lambda_\infty(V_0)` の上限である。

原典 PDF p.6 / layout L300。NormalizedLength.HasSupとして増大する有限生成部分加群の上限を実現する。

*解説 §4.5 塔と整合する長さ*

*定義 4.17（塔と整合する長さ）*

- (ii) *上限の性質*：$`\lambda(M)` は $`M` の有限生成部分加群の $`\lambda` の上限である。

外の文献：CLMST 2.2.1、CLMST 2.2.3、CLMST 2.2.6(a)、Faltings Appendix 2

:::

:::lemma_ "paper_2_4" (lean := "SerrePositivity.Section2.lemma_2_4_iSup, SerrePositivity.Section2.lemma_2_4_directSum, SerrePositivity.Section2.lemma_2_4_iSup_of_directed, SerrePositivity.Section2.lemma_2_4_directLimit") (uses := "paper_eq_2_3")
**補題 2.4**　長さ零の和・直和・増大和・有向極限。対応表の状態：本体にある。

*主張*　加群が $`\mathfrak m_A` の一つの冪で一様に消えるとき、長さ零の加群の和・直和・有向余極限は長さ零で、増大和の長さは各段の長さの上限である。また各段の長さが零に近づく直系の余極限も長さ零である。

原典 PDF p.7 / layout L326。共通の極大イデアル冪で殺される塔加群について、上限公式、直和・有向和、長さが0へ収束する系のdirect limitの長さ零を与える。遷移射の単射性は仮定しない。

*解説 §8 $`\lambda`-平坦な長さ付き代数の構成*

*補題 8.2（Lemma 2.4）*

共通の冪で消される範囲で、長さ $`0` の加群の和・直和・有向余極限は長さ $`0`。増大列の合併の $`\lambda_\infty` は $`\lambda_\infty` の上限。$`\lambda_\infty(V_a)\to 0` なら $`\lambda_\infty(\varinjlim V_a) = 0`。

*Lean:* \`Paper.Section2.Lemma2\_4\`（証明済み）。

:::

# §2.3 Length algebras and parameter homology

%%%
number := false
tag := "paper-2-3"
%%%

:::theorem "paper_2_5" (lean := "SerrePositivity.Section2.theorem_2_5, SerrePositivity.Section2.mixedPerfectoid_length_properties, SerrePositivity.BhattScholze.Inputs.exists_perfectoidizationInterfaceE3") (uses := "paper_eq_2_1, paper_eq_2_4, paper_eq_2_5, paper_eq_2_6, paper_eq_2_7, paper_eq_2_8, paper_2_2, paper_2_3, paper_2_4, ext_BS19_8_5, clmst_4_0_1, clmst_4_0_10, clmst_4_0_14, clmst_4_0_4, ext_Ma17_2_2, ext_Ma17_2_4, ext_Monsky, ext_Roberts89")
**定理 2.5**　全パラメータに使える長さ代数の存在。対応表の状態：未証明の入力に依存。

*主張*　補題 2.2 の $`D` と選んだ有限・生成点で分離的な基底 $`A` に対し、塔 $`\Lambda` と両立する $`D` 代数 $`C_D` があり、$`\mathfrak d` のある冪で消える加群には制限による非負加法的長さ $`\lambda_D=\lambda_\infty` が入る。任意のパラメータ系 $`z` と $`v\ge1` に対し、$`z^v` の正次数 Koszul ホモロジーは長さ零で、商の長さは $`v^h e((z),D)` となり、基底のパラメータでは $`v^h\operatorname{rank}_A D` になる。有限段・下限・上限による計算は、塔上の加群に対して使える。

原典 PDF p.7 / layout L352。固定した正規化基底の上でCと塔作用を一つ選び、全パラメータと冪についてKoszul消滅・重複度公式・基底のランク公式を得る型がある。等標数の証明は実装されているが、混標数のCの存在はBSpfdのE3界面のsorryに依存する。

*解説 §4.4 $`\lambda`-CM 代数*

*定義 4.14（$`\lambda`-CM）*

$`(D,\mathfrak{m}_D)` を次元 $`h` のネーター局所環とする。$`D` 代数 $`C` と $`\mathfrak{m}_D C`-冪ねじれ $`C` 加群の上の長さ関数 $`\lambda` の組（長さ付き $`D` 代数）$`(C,\lambda)` が \*\*$`\lambda`-CM\*\* であるとは、$`D` の任意のパラメータ系 $`x` について

$$`\lambda H_i(x; C) = 0 \quad (i>0), \qquad \lambda(C/xC) < \infty`

となること。さらに $`\lambda(C/\mathfrak{m}_D C) > 0` のとき*非自明*であるという。

$`(x)` は $`\mathfrak{m}_D`-準素なので $`H_i(x;C)` は $`\mathfrak{m}_D C`-冪ねじれで、$`\lambda` の定義域に入る。古典的には、$`D` の任意のパラメータ系が $`B` 正則列で $`\mathfrak{m}_D B\ne B` となる $`D` 加群 $`B`（balanced な巨大 CM 加群）に当たり、非自明性は $`\mathfrak{m}_D B\ne B` に当たる。

*解説 §8 $`\lambda`-平坦な長さ付き代数の構成*

*定理 8.5（Theorem 2.5、$`\lambda`-CM 代数の存在、引用）*

$`D` と $`A\subseteq D` を補題 8.4 のとおりとする。$`\Lambda` 作用をもつ $`D` 代数 $`C_D` があって、$`\lambda_D := \lambda_\infty`（係数制限）について次が成り立つ。

- (a) $`(C_D,\lambda_D)` は $`D` 上の $`\lambda`-CM 代数で、$`D` の任意のパラメータ系 $`z` について $`\lambda_D(C_D/zC_D) = e((z), D)`。

- (c) $`\lambda_D` は塔の上の Faltings の正規化長さ $`\lambda_\infty` の制限で、補題 8.2 の性質をもつ。

- 標数 $`p`：$`C_D = D_{\mathrm{perf}}`。Monsky（Hilbert–Kunz 重複度の存在）、Roberts の Frobenius ホモロジー定理（Ma, Thm 2.4。ここで必要な場合は注意 8.6 のとおり初等的に示せる）、Koszul の Euler 特性の公式。

証明の筋道。標数 $`p`：$`C_D=D_{\mathrm{perf}}=\bigcup_qD^{1/q}`、$`\Lambda=A_{\mathrm{perf}}` とし、$`B_q=\Lambda\otimes_{A^{1/q}}D^{1/q}` とおく。$`\operatorname{Frac} D/\operatorname{Frac} A` の分離性から $`B_q\subseteq C_D` で、トレースにより $`0\ne g\in A` があって $`g^{1/q}C_D\subseteq B_q`（元論文 (2.7)）。有限段の公式 $`\lambda_\infty(B_q/HB_q)=q^{-h}\operatorname{length}(D/H^{[q]})` と核の評価、補題 8.2 から、$`\lambda_D(C_D/HC_D)` は $`q^{-h}\operatorname{length}(D/H^{[q]})` の極限（Hilbert–Kunz 重複度）になる。(a) の消滅は $`\lambda_\infty H_i(z;B_q)=q^{-h}\operatorname{length} H_i(z^q;D)` と Roberts の定理（$`K(z;D)` は長さ $`h=\dim D` の有限自由複体でホモロジーが有限長なので、$`F^e(K(z;D))=K(z^{p^e};D)` の正次数ホモロジーの長さを $`p^{eh}` で割ると $`0` に収束する）から、値は Koszul の Euler 特性の公式 $`\sum_i(-1)^i\operatorname{length} H_i(z^q;D)=q^he((z),D)` から出る。混標数：$`C_D=(D\otimes_AA_\infty)_{\mathrm{perfd}}`（$`A_\infty` は塔の $`p` 進完備化、perfectoid 化は Bhatt–Scholze）。CLMST Cor. 4.0.4 が $`A_n\otimes_AD` の任意のパラメータ系の正次数 Koszul ホモロジーを almost イデアル $`(g)_{\mathrm{perfd}}` で消し、Prop. 4.0.10 により almost zero な $`\mathfrak{m}_A` 冪ねじれ加群の $`\lambda_\infty` は $`0`、Prop. 4.0.14（$`n=0`）がパラメータ商の長さを Hilbert–Samuel 重複度と同定する。CLMST の $`A_\infty`、$`C_D` はパラメータ系の取り方に依存する（Caution 4.0.2）が、基底 $`A` を固定した上で $`D` の任意のパラメータ系 $`z` について (a) が成り立つという主張とは矛盾しない。

*Lean:* \`Section2.theorem\_2\_5\`。この定理自体は、標数別の構成（\`LengthAlgebraConstruction\`）から証明している。標数 $`p` は perfection・塔の作用・Frobenius 長さ極限を、パラメータ Koszul 複体の初等的な消滅（\`tendsto\_length\_koszulHomologySelf\_frobenius\_pow\`、引用なし）へ接続済み。混標数も完備塔・perfectoidization と CLMST の引用を接続済み。(b) への書き換えは \`lengthAlgebra\_base\_values\`。

外の文献：BS19 8.5、CLMST 4.0.1、CLMST 4.0.10、CLMST 4.0.14、CLMST 4.0.4、Ma17 2.2、Ma17 2.4、Monsky、Roberts89

:::

:::definition "paper_eq_2_4" (lean := "SerrePositivity.Section2.theorem_2_5") (uses := "paper_eq_2_5, paper_2_3, paper_2_4, clmst_4_0_10, clmst_4_0_4, ext_Ma17_2_4, ext_Roberts89")
**式 (2.4)**　全パラメータの正次数Koszul長の零性。対応表の状態：未証明の入力に依存。

*主張*　定理 2.5 の長さ代数では、$`D` の任意のパラメータ系 $`z`、$`v\ge1`、$`i>0` に対し、$`\lambda_D H_i(z_1^v,\ldots,z_h^v;C_D)=0` である。

原典 PDF p.7 / layout L357。同じCの存在と一緒に返す全パラメータ・全冪の公式。混標数でのCの構成がE3入力に依存する。

*解説 §8 $`\lambda`-平坦な長さ付き代数の構成*

*注意 8.6（Roberts の定理を使わない消滅）*

上の証明の標数 $`p` の部分で Roberts の定理を使うのは、パラメータ系 $`z` の Koszul 複体について $`\operatorname{length} H_i(z^q;D)/q^h\to0`（$`i>0`）を得るためだけである。この特殊な場合は、Frobenius も tight closure も使わずに次のように示せる。実際には任意の冪 $`q\ge1` について

$$`\operatorname{length} H_i(z^q;D)\le C\,q^{h-1}\qquad(i>0)`

が成り立つ。

1. $`D` の剰余体 $`k` は完全なので、$`D` は係数体 $`k\to D` をもつ。$`R'=k[[Z_1,\dots,Z_h]]` から $`Z_j\mapsto z_j` で評価すると、$`D` は有限 $`R'` 加群になり、剰余体は共通である。

2. $`Z^q=(Z_1^q,\dots,Z_h^q)` は $`R'` の正則列なので $`K(Z^q)` は $`R'/(Z^q)` の分解で、$`\operatorname{length}_D H_i(z^q;D)=\operatorname{length}_{R'}\operatorname{Tor}_i^{R'}(R'/(Z^q),D)`。

3. 一般点の基底から自由部分加群 $`E\subseteq D` をとると、余核は捩れ加群なので、零でない $`c\in R'` が $`D/E` を消す。Tor の長完全列で $`\operatorname{Tor}_i(N,D)\hookrightarrow\operatorname{Tor}_i(N,D/E)`（$`i\ge1`）となり、$`c` は $`q` によらずすべての $`\operatorname{Tor}_i^{R'}(R'/(Z^q),D)` を消す。

4. $`D` の $`R'` 上の有限自由分解 $`G_\bullet`（$`q` によらない）で Tor を計算すると、$`\operatorname{Tor}_i` は有限長の加群 $`W^{\beta_i}`（$`W=R'/(Z^q)`、$`\beta_i=\operatorname{rank} G_i`）の部分商で、$`c` で消える。有限長の加群では $`c` 倍の核と余核の長さが等しいので

   $$`\operatorname{length}\operatorname{Tor}_i^{R'}(R'/(Z^q),D)\le\beta_i\,\operatorname{length}\bigl(R'/(c,Z^q)\bigr).`

5. $`R'/(c)` は次元 $`h-1` で、$`(Z)^{h(q-1)+1}\subseteq(Z^q)` なので、Hilbert–Samuel 多項式の次数定理から $`\operatorname{length}(R'/(c,Z^q))=O(q^{h-1})`。

$`D` が整域であることも、$`R'\to D` が単射であることも使わない。Roberts の定理は長さ $`h` の任意の有限自由複体についての主張で、$`\operatorname{length} H_i(F^eG)=O(p^{e(h-i)})` のような強い評価や個々の次数の消滅を含み、本当に深いのはその一般の場合である。パラメータ Koszul 複体に限れば、上のとおり $`D` を正則環 $`R'` 上の有限加群とみて、Tor を $`q` によらない分解で計算できることが効いている。

*Lean:* \`CommutativeAlgebra.ParameterKoszulGrowth\` の \`exists\_length\_koszulHomologySelf\_pow\_le\` と \`tendsto\_length\_koszulHomologySelf\_frobenius\_pow\`（証明済み、引用なし）。部品は \`length\_le\_length\_quotient\_smul\_of\_subquotient\`、\`exists\_ne\_zero\_smul\_torModule\_eq\_zero\`、\`length\_torModule\_le\_of\_smul\_eq\_zero\`、\`exists\_length\_quotient\_generator\_pow\_le\`、\`length\_koszulHomologySelf\_eq\_length\_torModule\`。Roberts の一般形の引用（旧 \`Inputs.frobenius\_homology\_length\_tendsto\_zero\`）は主定理の経路で使わないので削除した。

外の文献：CLMST 4.0.10、CLMST 4.0.4、Ma17 2.4、Roberts89

:::

:::definition "paper_eq_2_5" (lean := "SerrePositivity.Section2.theorem_2_5, SerrePositivity.Section2.parameter_quotient_values_pow") (uses := "paper_eq_2_4, paper_eq_2_8, paper_2_3, paper_2_4, clmst_4_0_14, clmst_4_0_4")
**式 (2.5)**　パラメータ商長の重複度公式。対応表の状態：未証明の入力に依存。

*主張*　定理 2.5 の任意の $`D` のパラメータ系 $`z` と $`v\ge1` に対して、$`\lambda_D(C_D/(z_1^v,\ldots,z_h^v)C_D)=v^h e((z),D)` であり、右辺は有限かつ正である。

原典 PDF p.7 / layout L360。全パラメータに共通のCの存在にはE3入力が残る。v=1の重複度公式から冪への拡張自体はsorryなし。

外の文献：CLMST 4.0.14、CLMST 4.0.4

:::

:::definition "paper_eq_2_6" (lean := "SerrePositivity.Section2.theorem_2_5, SerrePositivity.Section2.base_parameter_values_of_multiplicity")
**式 (2.6)**　基底パラメータ商長のrank公式。対応表の状態：未証明の入力に依存。

*主張*　定理 2.5 の基底 $`A` の正則パラメータ $`t_1,\ldots,t_h` では、$`v\ge1` に対して $`\lambda_D(C_D/(t_1^v,\ldots,t_h^v)C_D)=v^h\operatorname{rank}_A D` となる。

原典 PDF p.7 / layout L365。既存のC上の重複度からrank値への移行は証明済みだが、両標数に共通する存在主張にはE3のsorryが残る。

*解説 §4.4 $`\lambda`-CM 代数*

*命題 4.15*

$`A\subseteq D` を正則局所部分環で $`D` が $`A` 上有限なものとし、$`(C,\lambda)` を $`D` 上の $`\lambda`-CM 代数とする。このとき $`(C,\lambda)` は長さ付き $`A` 代数として $`\lambda`-平坦で、ランクは $`A` の正則パラメータ系 $`z` について $`\lambda(C/zC)`。

*証明*

$`\mathfrak{m}_D^N\subseteq\mathfrak{m}_A D` となる $`N` があるので、$`\mathfrak{m}_A C`-冪ねじれと $`\mathfrak{m}_D C`-冪ねじれは同じである。$`z` は $`D` のパラメータ系でもあるので、系 4.11 の逆を適用する。

*Lean:* \`LengthAlgebra.CohenMacaulay\` の \`flat\_of\_cm\` と \`tor\_length\_of\_cm\` で証明済み。有限な単射 $`A\to D` に沿うパラメータの移送と \`restrictToBase\` を用いる。基底の次元と剰余体の Koszul 分解は明示して受け取る。

*解説 §8 $`\lambda`-平坦な長さ付き代数の構成*

*定理 8.5（Theorem 2.5、$`\lambda`-CM 代数の存在、引用）*

- (b) $`(C_D,\lambda_D)` は $`\lambda`-平坦でランク $`\operatorname{rank}_A D` の長さ付き $`A` 代数。

(b) は (a) と命題 4.15 から出る。ランクは $`A` の正則パラメータ系 $`z` について $`e((z),D) = \operatorname{rank}_A D`。元論文は (a) を全ての $`z^v` についての形で述べるが、$`z^v` もパラメータ系なので同じことである。

:::

:::definition "paper_eq_2_7" (lean := "SerrePositivity.Section2.exists_tower_perfection_conductor")
**式 (2.7)**　trace denominatorによる包含。対応表の状態：本体にある。

*主張*　標数 $`p` で $`C_D=D_{\mathrm{perf}}`、$`B_q=\Lambda\otimes_{A^{1/q}}D^{1/q}` とおくと、すべての $`q=p^n` に共通の非零 $`g\in A` があって、$`gC_D\subseteq B_1` かつ $`g^{1/q}C_D\subseteq B_q` となる。

原典 PDF p.8 / layout L392。生成的分離な有限拡大の完全化について、一つの非零gと全p冪根のconductor包含を構成する。等標数の部分である。

:::

:::definition "paper_eq_2_8" (lean := "SerrePositivity.Section2.normalized_frobenius_length_tendsto_perfection_quotient_of_primary") (uses := "paper_eq_2_7, paper_2_4, ext_Ma17_2_2, ext_Monsky")
**式 (2.8)**　完全化の主イデアル商長とHilbert–Kunz極限。対応表の状態：本体にある。

*主張*　定理 2.5 の標数 $`p` の構成で、極大イデアルに準素なイデアル $`H\subset D` について $`\lambda_D(C_D/HC_D)` は $`H` の Hilbert–Kunz 重複度 $`e_{\mathrm{HK}}(H,D)` に等しい。

原典 PDF p.8 / layout L410。primary idealについて正規化Frobenius長の極限と完全化商の塔長を比較する。原典のe\_HKはその極限であり、任意のCでの追加公式とはしない。

*解説 §8 $`\lambda`-平坦な長さ付き代数の構成*

*定理 8.5（Theorem 2.5、$`\lambda`-CM 代数の存在、引用）*

- 混標数：$`C_D = (D\otimes_A A_\infty)_{\mathrm{perfd}}`。Cai–Lee–Ma–Schwede–Tucker の Cor. 4.0.4、Prop. 4.0.10、4.0.14。

外の文献：Ma17 2.2、Monsky

:::

:::corollary "paper_2_6" (lean := "SerrePositivity.cor_2_6_tor, SerrePositivity.Section4.residue_length_pos_of_lengthAlgebra_values") (uses := "paper_eq_2_4, paper_eq_2_6, paper_2_5")
**系 2.6**　有限長基底加群のTor消滅と剰余長の正値性。対応表の状態：本体にある。

*主張*　定理 2.5 の設定で $`r=\operatorname{rank}_A D` とし、$`V` を有限長 $`A` 加群とする。$`i>0` で $`\lambda_D\operatorname{Tor}_i^A(V,C_D)=0`、かつ $`\lambda_D(V\otimes_A C_D)=r\operatorname{length}_A V` で、剰余商 $`C_D/\mathfrak d C_D` の長さは正である。

原典 PDF p.9 / layout L459。本文同様に長さ代数の(2.4)–(2.6)を仮定した文脈で、任意の有限長A加群の高次Torの長さ零とdegree0のr倍公式を与える。剰余商の正値性は有限長商のフィルトレーションの評価で得る。長さ代数の存在をこの補題の新しい仮定に隠していない。

*解説 §8 $`\lambda`-平坦な長さ付き代数の構成*

*系 8.7（Corollary 2.6 (3)、非自明性）*

$`\lambda_D(C_D/\mathfrak{m}_D C_D) > 0`。つまり $`C_D` は非自明な $`\lambda`-CM 代数である。

*証明*

$`D` のパラメータイデアル $`H` をとる。$`D/H` の組成列を $`C_D` とテンソルすると、テンソル積の右完全性により $`C_D/HC_D` は $`C_D/\mathfrak{m}_DC_D` の商を因子とする長さ $`\operatorname{length}_D(D/H)` のフィルトレーションをもつ。よって

$$`0<e(H,D)=\lambda_D(C_D/HC_D)\le\operatorname{length}_D(D/H)\cdot\lambda_D(C_D/\mathfrak{m}_DC_D)`

で、左の等号は定理 8.5 (a) による。Corollary 2.6 の (1)、(2)（$`\lambda_D\operatorname{Tor}_i^A(V,C_D)=0`、$`\lambda_D(V\otimes_AC_D)=r\operatorname{length}_A(V)`）は補題 4.10 を $`(C_D,\lambda_D)` に当てはめたものである。

*Lean:* \`Paper.Section2.Corollary2\_6\`（定理 8.5 を除いて証明済み）。

:::

