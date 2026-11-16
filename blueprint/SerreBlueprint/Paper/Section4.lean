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

本論文 §4 の項目と、本体の宣言との対応。本文は対応表（`research/paper-coverage`）の照合の理由で、論文の本文の写しではない。

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

:::

# §4.2 The supported subquotient

%%%
number := false
tag := "paper-4-2"
%%%

:::lemma_ "paper_4_2" (lean := "SerrePositivity.Asymptotic.supportedRankQuotientInclusion, SerrePositivity.Asymptotic.paperSupportedRankEquivalence")
**補題 4.2**　台つき部分商の充満忠実性と冪等完備化。対応表の状態：本体にある。

原典 PDF p.17 / layout L889。台つき部分商からランク商への標準関手のFull・Faithful・三角性のinstanceと、支持つきKaroubi包の同値を確認した。有限ランク誤差の商の後に現れる支持と、lift上の一様支持を区別する。

:::

# §4.3 Nonnegative homology lengths

%%%
number := false
tag := "paper-4-3"
%%%

:::proposition "paper_4_3" (lean := "SerrePositivity.Asymptotic.paperRankHomology, SerrePositivity.Asymptotic.completedRankHomology_isHomological, SerrePositivity.Asymptotic.paperRankBetti_nonneg, SerrePositivity.Asymptotic.paperRankBetti_hasFiniteSupport, SerrePositivity.Asymptotic.paperRankEulerK0, SerrePositivity.Asymptotic.paperBaseChangeHomology, SerrePositivity.Asymptotic.paperBaseChangeHomology_isHomological, SerrePositivity.Asymptotic.paperBaseChangeBetti_nonneg, SerrePositivity.Asymptotic.paperBaseChangeBetti_hasFiniteSupport, SerrePositivity.Asymptotic.paperBaseChangeEulerK0") (uses := "paper_eq_4_1, paper_eq_4_2, paper_eq_4_3, paper_4_1, paper_4_2")
**命題 4.3**　長さのSerre商へのホモロジー関手とEuler評価。対応表の状態：本体にある。

原典 PDF p.18 / layout L937。現在はLengthSerreQuotientへの各次数の関手とIsHomological、非負・有限supportのBetti長、K0のEuler準同型がある。ordinary長とbase-change長に適用し、Karoubi包の全支持対象を扱う。旧表の数値部分のみというpartial判定は維持しない。添字はcochainのq=-iへ読み替える。

外の文献：BalmerSchlichting 1.10、BalmerSchlichting 1.12

:::

:::definition "paper_eq_4_2" (lean := "SerrePositivity.Asymptotic.paperRankBetti_koszul_formula, SerrePositivity.Asymptotic.paperBaseChangeBetti_koszul_formula, SerrePositivity.Asymptotic.paperBaseChangeBetti_koszul_tensor_formula") (uses := "paper_eq_4_3, paper_4_1")
**式 (4.2)**　商内支持からのKoszul–Betti二項係数公式。対応表の状態：本体にある。

原典 PDF p.18 / layout L956。厳密有界自由列の像が商内でsupportedであればよく、元の列の一様支持を追加仮定しない。ordinaryとbase-change lengthの両方へ適用する。原典のLaurent多項式を各係数の等式で与える。

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

:::lemma_ "paper_4_6" (uses := "paper_3_1")
**補題 4.6**　連結結合係数Hによる両ランク商のMorita表示。対応表の状態：なし。

原典 PDF p.21 / layout L1123。任意のNoether基底で生成元のendomorphism dg algebraが連結となり、P\_A≃Perf(H)、P\_T≃Perf(H⊗\^L T)を中心的局所化と両立させる一組の同値は確認できない。KSTの特定dg商やsupportedRankK0\_descentはこの同値を構成していない。

外の文献：Drinfeld 3.1、Drinfeld 3.4、LT 3.12

:::

:::definition "paper_eq_4_7"
**式 (4.7)**　endomorphism代数の積と導来基底変換。対応表の状態：なし。

原典 PDF p.21 / layout L1142。B\_A=∏M\_(s\_n)(A)のflatnessと有限表示TによるB\_A⊗\^L T≃B\_Tの同値を、この生成元表示と一緒に構成する宣言は未確認。

外の文献：Drinfeld 3.1、Drinfeld 3.4

:::

:::theorem "paper_4_7" (uses := "paper_eq_4_1, paper_3_1, paper_4_5, paper_4_6")
**定理 4.7**　漸近Euler評価の共役norm和の比較。対応表の状態：未証明の入力に依存。

原典 PDF p.22 / layout L1171。全支持対象上の共役和の等式の型はあるが、supportedRankK0\_descentが直接sorryを持つ。Lemma4.6を構成してTheorem3.1を実際に適用したものとはせず、別の入力界面として記録する。

宣言：`SerrePositivity.Section4.theorem_4_7`、`SerrePositivity.Section4.theorem_4_7_K0`、`SerrePositivity.Section4.supportedRankK0_descent`

:::

