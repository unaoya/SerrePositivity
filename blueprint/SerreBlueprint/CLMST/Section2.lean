-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.BhattScholze.PerfectoidIdeal.Roots
import SerrePositivity.BhattScholze.Perfectoidization.Finite
import SerrePositivity.CLMST.KoszulAnnihilation
import SerrePositivity.CLMST.PerfectoidizationIsogeny.Proof
import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
import SerrePositivity.CommutativeAlgebra.RootTower.Perfectoid
import SerrePositivity.CommutativeAlgebra.ScalarIsogeny
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedBaseChangePrincipalH0
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletelyFlat.Definition
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionReflection
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion.Basic
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalClassicalComparison
import SerrePositivity.LengthAlgebra.Normalized
import SerrePositivity.LengthAlgebra.RootTowerLength.Additivity
import SerrePositivity.LengthAlgebra.RootTowerLength.Basic
import SerrePositivity.LengthAlgebra.RootTowerLength.Tower

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "§2 Preliminaries" =>
%%%
number := false
tag := "clmst-2"
%%%

CLMST §2 の項目と、本体の宣言との対応。本文は対応表（`research/clmst-coverage`）の照合の理由で、原典の本文の写しではない。

# §2.1 Pure maps, split maps, and trace

%%%
number := false
tag := "clmst-2-1"
%%%

:::lemma_ "clmst_2_1_1"
*補題 2.1.1*　近似 Gorenstein 環での非分裂元と colon イデアル。対応表の状態：なし。

原典 PDF p.8; layout L370。原典の「近似 Gorenstein 環での非分裂元と colon イデアル」を同じ仮定・結論で述べる宣言を確認できない。

:::

:::proposition "clmst_2_1_2" (uses := "clmst_2_1_1")
*注意 2.1.2*　colon 部分加群の単調性と合併。対応表の状態：なし。

原典 PDF p.8; layout L390。原典の「colon 部分加群の単調性と合併」を同じ仮定・結論で述べる宣言を確認できない。

:::

:::lemma_ "clmst_2_1_3"
*補題 2.1.3*　平坦加群での非分裂元の mM による記述。対応表の状態：なし。

原典 PDF p.9; layout L398。原典の「平坦加群での非分裂元の mM による記述」を同じ仮定・結論で述べる宣言を確認できない。

:::

:::lemma_ "clmst_2_1_4"
*補題 2.1.4*　有限正規拡大の trace と Hom の生成元。対応表の状態：なし。

原典 PDF p.9; layout L431。原典の「有限正規拡大の trace と Hom の生成元」を同じ仮定・結論で述べる宣言を確認できない。

外の文献：CRST18 Lemma 2.10、Mor53、SS75、ST14 Proposition 4.8、Spe20 Lemma 9、dS97

:::

# §2.2 Normalized length

%%%
number := false
tag := "clmst-2-2"
%%%

:::definition "clmst_2_2_1" (lean := "SerrePositivity.Section2.presentedLength, SerrePositivity.Section2.fgLength, SerrePositivity.Section2.towerLengthFun")
*定義 2.2.1*　Faltings の正規化長さの三段階の定義。対応表の状態：本体にある。

*主張*　正則基底 $`A` からパラメータの $`p` 冪根を添加した未完備の塔をとり、その余極限上の $`\mathfrak m_A` 冪ねじれ加群の正規化長を定める。有限表示なら有限段 $`A_n` の長さを $`p^{nd}` で割り、有限生成なら有限表示全射から下限を、一般には有限生成部分加群から上限をとる。

原典 PDF p.10; layout L481。原典の未完備塔 Anc\_infty 上で、有限段長さの正規化、有限表示全射の下限、有限生成部分加群の上限を同じ順で定義する。値域は非負拡張実数。完備塔との同一視は別宣言である。

:::

:::proposition "clmst_2_2_2"
*注意 2.2.2*　正規化長さのより一般の設定。対応表の状態：なし。

原典 PDF p.10; layout L501。原典の「正規化長さのより一般の設定」を同じ仮定・結論で述べる宣言を確認できない。

外の文献：Fal02 Appendix 2、GR04 Remark 14.5.69

:::

:::proposition "clmst_2_2_3" (lean := "SerrePositivity.Section2.towerLengthFun_eq_fgLength_of_noetherian, SerrePositivity.Section2.towerLengthFun_eq_presentedLength_of_noetherian") (uses := "clmst_2_2_4")
*命題 2.2.3*　正規化長さの良定義性と有限生成・有限表示での一致。対応表の状態：本体にある。

*主張*　未完備の塔の余極限上の $`\mathfrak m_A` 冪ねじれ加群に対する正規化長は、無限大を許す実数値としてよく定まり、有限生成・有限表示の場合に各々の定義式と一致する。

原典 PDF p.11; layout L504。原典の有限自由な根の塔について、一般長さと有限生成の下限、および有限表示の段長さとの一致をソースで確認。段の選択は presentedLength の定義と有限段比較で処理する。

外の文献：GR04 Lemma 14.5.74、Shi07 Lemma 2.2

:::

:::lemma_ "clmst_2_2_4" (lean := "SerrePositivity.Section2.towerLengthFun_tensor")
*補題 2.2.4*　有限生成元から作る有限段長さの極限。対応表の状態：一部（special）。

*主張*　未完備の塔の余極限上の有限生成 $`\mathfrak m_A` 冪ねじれ加群 $`M` に有限生成元を一組選び、それらが $`A_n` 上生成する部分加群を $`M_n` とする。$`M` の正規化長は、$`p^{-nd}\operatorname{length}_A(M_n)` の極限、同じく $`M_n` を塔の余極限へ底変換したものの正規化長の極限である。

原典 PDF p.11; layout L523。有限段から基底変換した加群の正確な長さ公式を確認。原典は任意の有限生成 M と任意の有限生成元集合から作る部分加群 Mn の極限公式であり、有限段から降下する場合に範囲を狭めた対応。一般の生成元近似極限を述べる宣言は未確認。

外の文献：Fal02 Appendix 2、Fal02 Appendix 2, Claim、Shi07 Lemma 2.3

:::

:::corollary "clmst_2_2_5" (uses := "clmst_2_2_4")
*系 2.2.5*　全射な有限生成系の colimit と長さの下限。対応表の状態：なし。

原典 PDF p.11; layout L542。原典の「全射な有限生成系の colimit と長さの下限」を同じ仮定・結論で述べる宣言を確認できない。

:::

:::proposition "clmst_2_2_6" (lean := "SerrePositivity.Section2.towerLengthFun_add_of_exact_of_noetherian, SerrePositivity.NormalizedLength.len_iSup_of_directed") (uses := "clmst_2_2_5")
*命題 2.2.6*　短完全列の加法性と単射・全射な filtered colimit。対応表の状態：一部（part）。

*主張*　未完備の塔の余極限上の $`\mathfrak m_A` 冪ねじれ加群の正規化長は短完全列で加法的である。フィルター系の推移射がすべて単射、またはすべて全射で各段の長さが有限なら、余極限の長さは各段の長さの極限である。

原典 PDF p.12; layout L572。(a) の短完全列加法性は具体的な塔で証明。(b\|i) の有向部分加群の和の上限公式もある。一方 (b\|ii) の有限長・全射遷移を持つ一般 filtered colimit の極限公式全体は未確認。len\_directLimit\_eq\_zero\_of\_tendsto は長さ極限零の場合に限る。

外の文献：Fal02 Appendix 2, Lemma、GR04 Proposition 14.5.12(iii)(b)、GR04 Proposition 14.5.75(i)(b)、GR04 Theorem 14.5.75、Shi07 Proposition 2.8

:::

# §2.3 Derived completion and flatness

%%%
number := false
tag := "clmst-2-3"
%%%

:::definition "clmst_2_3_1" (lean := "SerrePositivity.DerivedCompletion.IsComplete, SerrePositivity.DerivedCompletion.IsModuleComplete")
*定義 2.3.1*　導来 I 完備性。対応表の状態：一部（special）。

*主張*　$`D(R)` の複体 $`K` が導来 $`I` 完備であるとは、各 $`f\in I` について $`f` 倍を推移射とする $`K` の塔の導来逆極限が零となることをいう。加群の導来完備性はそれを次数零の複体として判定する。

原典 PDF p.12; layout L611。局所化 R\[1/f\] からの全次数 Hom 消滅で単項 f 完備性を定義する。原典の有限生成 I の全ての f に対する導来逆極限消滅という一般定義に対し、単項への特殊化と同値な記述。一般 I の条件を一つの型として採用してはいない。

外の文献：Stacks Tag 091Q

:::

:::proposition "clmst_2_3_2" (lean := "SerrePositivity.DerivedCompletion.completeReflectorAdjunction, SerrePositivity.DerivedCompletion.complexCompletionFunctor")
*命題 2.3.2*　単項イデアルの導来完備化の反映と逆極限表示。対応表の状態：本体にある。

*主張*　$`I=(f)` が単項なら、導来 $`I` 完備な複体の充満部分圏への反射は $`K\mapsto R\varprojlim_k(K\otimes^{\mathbf L}_{\mathbf Z[x]}\mathbf Z[x]/(x^k))` で与えられる。ここで $`\mathbf Z[x]` は $`x\mapsto f` で作用し、この左随伴は冪等である。

原典 PDF p.13; layout L625。原典自身が I=(f) を仮定する。任意の非有界導来対象の完備化を、冪 Koszul 塔の積の差の錐で構成し、完備対象への反映の随伴を持つ。Koszul 塔は Z\[x\]/x\^n との導来テンソルのモデルで、任意の零因子 f を許す。

外の文献：BS15 Lemma 3.4.8, Lemma 3.4.9、Stacks Tag 091V

:::

:::proposition "clmst_2_3_3" (lean := "SerrePositivity.DerivedCompletion.principalCompletionAdicAlgEquiv")
*命題 2.3.3*　有界冪捩れ加群の pro 比較と古典的完備化。対応表の状態：一部（special）。

*主張*　$`R` 加群 $`M` の $`f` 冪ねじれが有界なら、通常の商 $`M/f^nM` と導来テンソル $`M\otimes_R^{\mathbf L}R/f^nR` の二つの pro 系は同型である。従って導来 $`f` 完備化は次数零に集中し、古典的な完備化に一致する。

原典 PDF p.13; layout L659。原典は任意の有界 f 冪捩れ加群 M の pro 同型と導来完備化全体の離散性を主張する。採用宣言は M=R かつ f が非零因子の場合の H0 と古典的完備環の同型で、一般の捩れ加群・pro 同型までは含まない。

外の文献：Bha19 III, Lemma 2.4

:::

:::definition "clmst_2_3_4" (lean := "SerrePositivity.BhattScholze.Prismatic.IsDerivedCompletelyFlat")
*定義 2.3.4*　導来 I 完全平坦性と忠実平坦性。対応表の状態：一部（special）。

*主張*　$`K\in D(R)` は、$`K\otimes_R^{\mathbf L}R/I` が次数零に集中し、その次数零のコホモロジーが $`R/I` 上平坦（忠実平坦）であるとき、$`I` 完全平坦（完全忠実平坦）と呼ばれる。

原典 PDF p.14; layout L665。剰余への導来底変換が零次に集中し、その H0 が平坦であるという定義に対応。ただし定義域は上に有界な導来対象に限り、原典の全 D(R) と忠実平坦版の両方をまとめた定義ではない。

外の文献：BMS19 Section 4.1

:::

:::lemma_ "clmst_2_3_5" (lean := "SerrePositivity.DerivedCompletion.completedBaseChangeTensorPrincipalH0LinearEquiv, SerrePositivity.DerivedCompletion.principalCompletionAdicAlgEquiv") (uses := "clmst_2_3_3")
*補題 2.3.5*　完全平坦底変換の完備テンソル積の古典的表示。対応表の状態：一部（special）。

*主張*　導来 $`p` 完備環の間の $`p` 完全平坦射 $`R\to S` と、$`p` 冪ねじれが有界な $`R` 加群 $`M` に対して、$`M\otimes_R^{\mathbf L}S` の導来 $`p` 完備化は、$`M\otimes_R S` の古典的 $`p` 完備化と同値である。

原典 PDF p.14; layout L671。M が R 代数 A の場合、完備導来底変換の H0 と通常テンソル環 T の実主元完備化 H0 の線形同型を確認。さらに p が T の非零因子なら古典的完備化との同型を使える。原典は任意の有界 p 冪捩れ加群 M、p 完全平坦な S について完備導来対象全体の同値を主張するため、代数係数・非零因子という特殊な場合の H0 比較に限る。

:::

:::definition "clmst_2_3_6" (lean := "SerrePositivity.DerivedCompletion.derivedComplexCompletionFunctor")
*規約 2.3.6*　導来 p 完備化と完備テンソル積の記号規約。対応表の状態：一部（part）。

*主張*　特に断らない場合、上付きの完備化記号は導来 $`p` 完備化を、帽子を付した導来テンソル積の記号はテンソル後の導来 $`p` 完備化を表す。

原典 PDF p.14; layout L684。任意 f の導来完備化関手はあり f=p に特殊化できる。原典の完備テンソル積も含めた全記号規約に対し、この宣言は完備化関手の側のみ。記号の採用自体は数学的存在定理ではない。

:::

# §2.4 Perfectoid rings and perfectoidization

%%%
number := false
tag := "clmst-2-4"
%%%

:::definition "clmst_2_4_1" (lean := "SerrePositivity.IsIntegralPerfectoid")
*定義 2.4.1*　perfectoid 環の四条件。対応表の状態：本体にある。

*主張*　$`p` 進完備な環 $`S` を考える。$`p=u\varpi^p` となる単元 $`u` と $`\varpi` があり、$`S/p` の Frobenius が全射で、傾化 $`S^\flat=\varprojlim_F S/p` の Witt 環から $`S` への Fontaine 写像の核が単項であるとき、$`S` を perfectoid 環と呼ぶ。

原典 PDF p.14; layout L696。原典の p 進完備性、p=u varpi\^p、mod p Frobenius の全射性、Fontaine 核が単項という四条件を保持。零環は明示的に別分岐とする。原典の末尾の二つの特徴づけまでは定義本体の対応とは別に扱う。

外の文献：And20 2.2、BMS18 Example 3.15、BMS18 Lemma 3.10、BMS18 Section 3、MS21 Definition 2.2

:::

:::proposition "clmst_2_4_2" (lean := "SerrePositivity.Section2.completedTower_isIntegralPerfectoid_of_parameters")
*例 2.4.2*　根の塔と絶対整閉包の完備化の例。対応表の状態：一部（special）。

*主張*　§2.2 の未完備な根の塔の $`p` 進完備化は perfectoid 環である。また剰余標数 $`p>0` の完備ネーター局所整域の絶対整閉包を $`p` 進完備化したものも perfectoid 環である。

原典 PDF p.15; layout L714。(1) の標準パラメータから作る混標数の完備根の塔の perfectoid 性を確認。(2) の一般 R の絶対整閉包の p 進完備化、および等標数の例をこの宣言だけからは得ない。

:::

:::lemma_ "clmst_2_4_3" (lean := "SerrePositivity.BhattScholze.completedTowerRoot_mem_perfectoidIdeal") (uses := "clmst_2_3_5")
*補題 2.4.3*　compatible roots を持つ perfectoid イデアルと閉包の比較。対応表の状態：一部（special）。

*主張*　perfectoid 環の射 $`R\to S` で $`g\in R` の像が整合する $`p` 冪根を $`S` にもつなら、$`(gS)_{\mathrm{perfd}}` は $`(g)_{\mathrm{perfd}}S` の $`p` 進閉包に一致し、正次数の根 $`g^{1/p^e}` が生成するイデアルの $`p` 進閉包にも一致する。よって最後の閉包は根の選び方によらない。

原典 PDF p.15; layout L757。完備根の塔の座標根が対応する perfectoid イデアルに入る包含は証明される。原典の任意の perfectoid 射 R→S における三つの閉包イデアルの等号と根の系の独立性に対し、座標根の片方向の所属に限る。商 perfectoid 化の存在入力への依存も残る。

外の文献：BS19 Proposition 8.13、BS19 Proposition 8.5、BS19 Theorem 7.14

:::

:::proposition "clmst_2_4_4"
*注意 2.4.4*　almost 数学で導来 p 完備を暗黙に課す規約。対応表の状態：なし。

原典 PDF p.16; layout L805。原典の「almost 数学で導来 p 完備を暗黙に課す規約」を同じ仮定・結論で述べる宣言を確認できない。

:::

:::theorem "clmst_2_4_5" (lean := "SerrePositivity.isPerfectoidization_toPerfectoidization, SerrePositivity.CLMST.proposition_2_4_7")
*定理 2.4.5*　有限エタール開集合に対する almost purity。対応表の状態：一部（part）。

*主張*　perfectoid 環 $`R` の有限生成イデアル $`J` と、$`V(J)` の外で有限エタールな有限かつ有限表示の $`R` 代数 $`S` をとる。$`S_{\mathrm{perfd}}` は perfectoid で、元の環とは $`V(J)` の外で一致し、$`n>0` で $`R/p^n\to S_{\mathrm{perfd}}/p^n` は $`J`-almost 有限射影かつ almost 不分岐である。外部で有限群 $`G` の Galois 被覆となる作用があれば、群コホモロジーへの比較と、導来完備テンソルから $`G` で添字づけた積への比較が $`J`-almost 同型になる。

原典 PDF p.16; layout L813。有限代数の perfectoid 化の普遍性と、有界 p 冪捩れを追加した J 同種性を確認。原典の各 mod p\^n の J almost finite etale という圏的結論全体の宣言ではない。標準 perfectoid 化の存在は E3 sorry 入力に依存するため、この部分対応も無条件の検証済み定理とは数えない。

外の文献：BS19 Theorem 10.9、Bha19 VIII, Theorem 3.1

:::

:::proposition "clmst_2_4_6" (uses := "clmst_2_4_5")
*注意 2.4.6*　絶対整閉基底での対称群 Galois 閉包の分裂。対応表の状態：なし。

原典 PDF p.17; layout L838。原典の「絶対整閉基底での対称群 Galois 閉包の分裂」を同じ仮定・結論で述べる宣言を確認できない。

外の文献：And18b Lemma 1.9.2、BS19 Theorem 10.9

:::

:::proposition "clmst_2_4_7" (lean := "SerrePositivity.CLMST.proposition_2_4_7") (uses := "clmst_2_3_5, clmst_2_4_5, clmst_2_4_6, clmst_2_4_8")
*命題 2.4.7*　有限 perfectoid 化への比較写像の J 同種性。対応表の状態：未証明の入力に依存。

*主張*　定理 2.4.5 の対象で $`S` の $`p` 冪ねじれが有界なら、$`S\to S_{\mathrm{perfd}}` は $`J`-isogeny である。すなわち各 $`g\in J` に対してある冪 $`g^N` がこの写像の錐上で $`D(R)` の零射として作用する。

原典 PDF p.17; layout L861。有限・有限表示、有限生成 J、J の外のエタール性、有界 p 冪捩れの仮定を保持し、各 g∈J のある冪が実導来錐を零化する J 同種性を述べる。本文に直接 sorry はないが、標準 perfectoid 化の選択は BhattScholze.Inputs.exists\_perfectoidizationInterfaceE3 に依存する。

外の文献：BS19 Proof of Theorem 10.9, footnote 18、BS19 Proposition 8.13、BS19 Theorem 7.14、BS19 last paragraph of proof of Theorem 10.9、Bha12 Lemma 3.2、Bha18 Lemma 3.2、Stacks Tag 0CQE

:::

:::lemma_ "clmst_2_4_8" (lean := "SerrePositivity.exists_pow_ker_coker_annihilator")
*主張 2.4.8*　分裂積への比較写像の錐の一様冪零化。対応表の状態：一部（part）。

*主張*　命題 2.4.7 の証明で、絶対整閉な perfectoid 基底へ移し、有限表示な有限代数からその基底の有限積への写像 $`\phi\colon S\to\prod_G R` に帰着した設定をとる。$`\phi` が $`g` を反転すると同型になるとき、ある $`N` について $`g^N` 倍が $`\operatorname{cone}(\phi)` 上で $`D(R)` の零射になる。

原典 PDF p.19; layout L968。被約な基底上で有限生成源から有限自由積への写像と、g を反転した同型を仮定し、核と余核の一様冪零化を得る。Claim の核・余核の結論に当たるが、指定した Galois 比較 phi とその導来錐での零写像の同定をこの宣言だけでは供給しない。

外の文献：Bha12 Lemma 3.2

:::

:::proposition "clmst_2_4_9" (lean := "SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput") (uses := "clmst_2_4_5, clmst_2_4_6")
*命題 2.4.9*　p 完全 almost 平坦性・忠実性・純性。対応表の状態：一部（special）。

*主張*　定理 2.4.5 の下で、$`p^n` ねじれ $`R` 加群との正次数の Tor は $`J`-almost 零である。加えて $`S` が $`V(J)` の外で一定の正階数をもてば、$`S_{\mathrm{perfd}}` とのテンソルが $`J`-almost 零となる $`p^n` ねじれ加群自身も $`J`-almost 零であり、単位に沿ったテンソル写像の核も $`J`-almost 零になる。

原典 PDF p.19; layout L994。(a) の任意 p\^k 捩れ試験加群・全正次数 Tor の零化を、単項 J=(a) の場合に証明。原典の任意の有限生成 J、(b) の正の階数での忠実性、および最後の almost 純性の結論全体は未確認。

外の文献：BS19 Theorem 7.14、BS19 last paragraph 19 of proof of Theorem 10.9

:::

# §2.5 Big Cohen-Macaulay algebras

%%%
number := false
tag := "clmst-2-5"
%%%

:::lemma_ "clmst_2_5_1" (uses := "clmst_2_5_2")
*補題 2.5.1*　付値が零へ近づく元を可逆化する BCM 拡大。対応表の状態：なし。

原典 PDF p.20; layout L1062。原典の「付値が零へ近づく元を可逆化する BCM 拡大」を同じ仮定・結論で述べる宣言を確認できない。

外の文献：BIM19 Example 3.8 (7)、BIM19 Example 3.8 (8)、BMP+23 Theorem 2.8、GR04 Section 17.5、Gab18、Gab18 Page 3、Hoc94 Corollary 2.4、Hoc94 Theorem 5.10、MS21 Proof of Theorem 4.5

:::

:::lemma_ "clmst_2_5_2"
*主張 2.5.2*　完備絶対整閉包の元の付値を保つ近似。対応表の状態：なし。

原典 PDF p.21; layout L1094。原典の「完備絶対整閉包の元の付値を保つ近似」を同じ仮定・結論で述べる宣言を確認できない。

:::

:::corollary "clmst_2_5_3" (uses := "clmst_2_5_1")
*系 2.5.3*　BCM 拡大におけるイデアル所属と局所コホモロジーの消滅。対応表の状態：なし。

原典 PDF p.22; layout L1123。原典の「BCM 拡大におけるイデアル所属と局所コホモロジーの消滅」を同じ仮定・結論で述べる宣言を確認できない。

:::

