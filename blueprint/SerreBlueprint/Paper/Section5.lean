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

本論文 §5 の項目と、本体の宣言との対応。本文は対応表（`research/paper-coverage`）の照合の理由で、論文の本文の写しではない。

# §5.1 Reduction and the first norm comparison

%%%
number := false
tag := "paper-5-1"
%%%

:::lemma_ "paper_5_1" (uses := "paper_eq_5_1, paper_1_1, paper_2_1, ext_GilletSoule, ext_Roberts85, ext_Serre")
**補題 5.1**　完備・代数閉剰余体・正次元素商対への帰着。対応表の状態：一部。

原典 PDF p.23 / layout L1200。prime filtrationとvanishingによる帰着、零次元対、剰余体拡大・完備化の各処理はある。一方、positivity\_of\_residueCharPは核心の実定理を呼ぶため入力依存で、原典の「核心を証明すれば十分」という全帰着を独立の含意型として切り出した宣言は確認しない。

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

:::

:::lemma_ "paper_5_2" (uses := "paper_eq_5_1, paper_3_5")
**補題 5.2**　第1のGalois平均と普通の交点数。対応表の状態：未証明の入力に依存。

原典 PDF p.24 / layout L1274。任意の共役の有限正規化Tor長と、\|G\_D\| a\_D a\_E chi=Σc\_sigmaを同時に与える。有限拡大のrank因子・vanishingは実装されるが、norm比較に使う通常K0降下入力のsorryが残る。

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

:::

:::definition "paper_eq_5_5" (lean := "SerrePositivity.Section5.parameterQuotient_length_eq_multiplicity, SerrePositivity.Section5.koszul_zero_of_cm_parameters, SerrePositivity.Section5.parameterQuotient_len_ne_top_of_cm") (uses := "paper_2_5")
**式 (5.5)**　パラメータ商Uの正の長さとKoszul零性。対応表の状態：本体にある。

原典 PDF p.25 / layout L1318。本文の固定した長さ代数の全パラメータ仮定の文脈で、選んだxからUの長さ・有限性とKoszul零性を得る。存在を供給するTheorem2.5は別にinterfaceと記録する。

:::

:::definition "paper_eq_5_6" (lean := "SerrePositivity.exists_pow_maximalIdeal_map_le, SerrePositivity.Section5.lemma_5_4")
**式 (5.6)**　全近似で共通に使うannihilator冪。対応表の状態：本体にある。

原典 PDF p.25 / layout L1322。局所環射B→D′とprimaryなI\_sigmaに共通の正の冪を選び、商でその像を零とする。近似では同じannihilatorを全M\_nに維持する。

:::

:::lemma_ "paper_5_3" (lean := "SerrePositivity.Section5.lemma_5_3") (uses := "paper_eq_5_5")
**補題 5.3**　パラメータ商を通じたTor長比較と次数上界。対応表の状態：本体にある。

原典 PDF p.25 / layout L1326。固定した長さ代数・正則列・有限B加群の文脈で、Tor\_B(U,L)とTor\_R(C,L)の長さを比較し、有限性およびi\>dim R-hでの消滅を得る。R-正則列と長さ零Koszulの仮定は本文の設定と一致する。

:::

:::definition "paper_eq_5_7" (lean := "SerrePositivity.Section5.lemma_5_3") (uses := "paper_eq_5_5")
**式 (5.7)**　Tor\_BとTor\_Rの長さおよび消滅上界。対応表の状態：本体にある。

原典 PDF p.25 / layout L1330。有限B加群Lと全iについて同じ長さ等式・有限性・i\>lでの消滅を得る。

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

宣言：`SerrePositivity.Asymptotic.paperBaseChangeEuler_minimal_lower_bound`、`SerrePositivity.Section5.finiteApproximation_rank_lower_bound`、`SerrePositivity.Section4.residue_length_pos_of_lengthAlgebra_values`、`SerrePositivity.len_quotient_map_le_length_mul`

:::

:::definition "paper_eq_5_17" (uses := "paper_eq_4_2, paper_eq_5_11, paper_eq_5_16, paper_2_5")
**式 (5.17)**　二段階の明示的な正の下界。対応表の状態：一部。

原典 PDF p.29 / layout L1538。eta×生成元数、およびlambda(U)/length(B/m\^a)という下界までは対応する。(5.16)の商長不等式もあるが、表示の除算形全体と本文のb\_sigma,gammaを一括した型としては未検収。

宣言：`SerrePositivity.Asymptotic.paperBaseChangeEuler_minimal_lower_bound`、`SerrePositivity.Section5.finiteApproximation_rank_lower_bound`、`SerrePositivity.len_quotient_map_le_length_mul`

:::

:::definition "paper_eq_5_18" (uses := "paper_4_7, paper_5_1, paper_5_2, paper_5_5, paper_5_6")
**式 (5.18)**　第二平均から第1平均の各c\_sigmaの正値性。対応表の状態：未証明の入力に依存。

原典 PDF p.29 / layout L1577。実際の第二比較の等式と各共役の正値性を接続する入口があるが、原典のTheorem4.7の代わりにsupportedRankK0\_descentのsorry入力に依存する。

宣言：`SerrePositivity.Section5.exists_secondComparison_pos_of_regular`、`SerrePositivity.Section5.secondComparison_of_approximation`

:::

