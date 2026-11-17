import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.CommutativeAlgebra.RegularLocalRing.FlatBaseChange
import SerrePositivity.CommutativeAlgebra.RootTower.Basic
import SerrePositivity.CommutativeAlgebra.RootTower.Stage
import SerrePositivity.IntersectionMultiplicity.Basic
import SerrePositivity.LengthAlgebra.RootTowerLength.Tower
import SerrePositivity.Paper.Section2.Lemma2_4
import SerrePositivity.Paper.Section2.LengthAlgebra.EqualChar
import SerrePositivity.Paper.Section2.NormalizationBase
import SerrePositivity.Paper.Section2.ResidueFieldExtension
import SerrePositivity.Paper.Section3.LengthComputation
import SerrePositivity.Paper.Section4.LengthHypotheses

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§2 Residue fields and normalized length" =>
%%%
number := false
tag := "paper-2"
%%%

本論文 §2 の項目と、本体の宣言との対応。本文は対応表（`research/paper-coverage`）の照合の理由で、論文の本文の写しではない。

# §2.1 Extending the residue field

%%%
number := false
tag := "paper-2-1"
%%%

:::lemma_ "paper_2_1" (lean := "SerrePositivity.Section2.lemma_2_1, SerrePositivity.supportDim_baseChange_of_map_maximalIdeal, SerrePositivity.chi_baseChange_of_map_maximalIdeal") (uses := "ext_Ma17_2_2")
**補題 2.1**　剰余体を代数閉体へ拡大する完備平坦局所拡大。対応表の状態：本体にある。

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

原典 PDF p.6 / layout L262。完全な正標数剰余体を持つ完備局所整域に、同じ剰余体の有限・生成的分離な正則基底を構成する。等標数の冪級数環と混標数のWitt冪級数環との具体的同型およびパラメータも結論に含む。

外の文献：KuranoShimomoto、KuranoShimomoto 1.1

:::

:::definition "paper_eq_2_1" (lean := "SerrePositivity.Section2.TowerStage, SerrePositivity.Section2.Tower") (uses := "paper_2_2")
**式 (2.1)**　根の塔A\_nと未完備極限Lambda。対応表の状態：本体にある。

原典 PDF p.6 / layout L280。パラメータのp\^n乗根を付加した有限段とdirect limitを定義する。完備化A\_inftyと未完備Lambdaを同一視しない。

:::

:::lemma_ "paper_2_3" (lean := "SerrePositivity.Section2.towerStage_free, SerrePositivity.Section2.finrank_towerStage, SerrePositivity.Section2.towerLength, SerrePositivity.Section2.towerLength_hasSup, SerrePositivity.Section2.towerLengthFun_tensor, SerrePositivity.Section2.towerLengthOn_eq_completedTowerLength") (uses := "paper_eq_2_2, clmst_2_2_1, clmst_2_2_3, clmst_2_2_6, ext_Faltings_Appendix_2")
**補題 2.3**　根の塔の段と正規化長さの構成。対応表の状態：本体にある。

原典 PDF p.6 / layout L286。各段の有限自由性・ランク、正規化長さの加法性・有限段公式・有限生成上限、および混標数の完備塔との比較を個別の宣言で実装する。Stage.leanの完備正則局所環・段間ランクの証明も原典の構成と照合した。

外の文献：CLMST 2.2.1、CLMST 2.2.3、CLMST 2.2.6(a)、Faltings Appendix 2

:::

:::definition "paper_eq_2_2" (lean := "SerrePositivity.Section2.towerLengthFun_tensor")
**式 (2.2)**　有限段からの基底変換の正規化長。対応表の状態：本体にある。

原典 PDF p.6 / layout L293。有限長A\_n加群からの基底変換の長さをstageRank=p\^(nh)で割る公式。

:::

:::definition "paper_eq_2_3" (lean := "SerrePositivity.Section2.towerLength_hasSup") (uses := "clmst_2_2_1, clmst_2_2_3, clmst_2_2_6, ext_Faltings_Appendix_2")
**式 (2.3)**　有限生成部分加群の長さの上限。対応表の状態：本体にある。

原典 PDF p.6 / layout L300。NormalizedLength.HasSupとして増大する有限生成部分加群の上限を実現する。

外の文献：CLMST 2.2.1、CLMST 2.2.3、CLMST 2.2.6(a)、Faltings Appendix 2

:::

:::lemma_ "paper_2_4" (lean := "SerrePositivity.Section2.lemma_2_4_iSup, SerrePositivity.Section2.lemma_2_4_directSum, SerrePositivity.Section2.lemma_2_4_iSup_of_directed, SerrePositivity.Section2.lemma_2_4_directLimit") (uses := "paper_eq_2_3")
**補題 2.4**　長さ零の和・直和・増大和・有向極限。対応表の状態：本体にある。

原典 PDF p.7 / layout L326。共通の極大イデアル冪で殺される塔加群について、上限公式、直和・有向和、長さが0へ収束する系のdirect limitの長さ零を与える。遷移射の単射性は仮定しない。

:::

# §2.3 Length algebras and parameter homology

%%%
number := false
tag := "paper-2-3"
%%%

:::theorem "paper_2_5" (uses := "paper_eq_2_1, paper_eq_2_4, paper_eq_2_5, paper_eq_2_6, paper_eq_2_7, paper_eq_2_8, paper_2_2, paper_2_3, paper_2_4, ext_BS19_8_5, clmst_4_0_1, clmst_4_0_10, clmst_4_0_14, clmst_4_0_4, ext_Ma17_2_2, ext_Ma17_2_4, ext_Monsky, ext_Roberts89")
**定理 2.5**　全パラメータに使える長さ代数の存在。対応表の状態：未証明の入力に依存。

原典 PDF p.7 / layout L352。固定した正規化基底の上でCと塔作用を一つ選び、全パラメータと冪についてKoszul消滅・重複度公式・基底のランク公式を得る型がある。等標数の証明は実装されているが、混標数のCの存在はBSpfdのE3界面のsorryに依存する。

宣言：`SerrePositivity.Section2.theorem_2_5`、`SerrePositivity.Section2.mixedPerfectoid_length_properties`、`SerrePositivity.BhattScholze.Inputs.exists_perfectoidizationInterfaceE3`

外の文献：BS19 8.5、CLMST 4.0.1、CLMST 4.0.10、CLMST 4.0.14、CLMST 4.0.4、Ma17 2.2、Ma17 2.4、Monsky、Roberts89

:::

:::definition "paper_eq_2_4" (uses := "paper_eq_2_5, paper_2_3, paper_2_4, clmst_4_0_10, clmst_4_0_4, ext_Ma17_2_4, ext_Roberts89")
**式 (2.4)**　全パラメータの正次数Koszul長の零性。対応表の状態：未証明の入力に依存。

原典 PDF p.7 / layout L357。同じCの存在と一緒に返す全パラメータ・全冪の公式。混標数でのCの構成がE3入力に依存する。

宣言：`SerrePositivity.Section2.theorem_2_5`

外の文献：CLMST 4.0.10、CLMST 4.0.4、Ma17 2.4、Roberts89

:::

:::definition "paper_eq_2_5" (uses := "paper_eq_2_4, paper_eq_2_8, paper_2_3, paper_2_4, clmst_4_0_14, clmst_4_0_4")
**式 (2.5)**　パラメータ商長の重複度公式。対応表の状態：未証明の入力に依存。

原典 PDF p.7 / layout L360。全パラメータに共通のCの存在にはE3入力が残る。v=1の重複度公式から冪への拡張自体はsorryなし。

宣言：`SerrePositivity.Section2.theorem_2_5`、`SerrePositivity.Section2.parameter_quotient_values_pow`

外の文献：CLMST 4.0.14、CLMST 4.0.4

:::

:::definition "paper_eq_2_6"
**式 (2.6)**　基底パラメータ商長のrank公式。対応表の状態：未証明の入力に依存。

原典 PDF p.7 / layout L365。既存のC上の重複度からrank値への移行は証明済みだが、両標数に共通する存在主張にはE3のsorryが残る。

宣言：`SerrePositivity.Section2.theorem_2_5`、`SerrePositivity.Section2.base_parameter_values_of_multiplicity`

:::

:::definition "paper_eq_2_7" (lean := "SerrePositivity.Section2.exists_tower_perfection_conductor")
**式 (2.7)**　trace denominatorによる包含。対応表の状態：本体にある。

原典 PDF p.8 / layout L392。生成的分離な有限拡大の完全化について、一つの非零gと全p冪根のconductor包含を構成する。等標数の部分である。

:::

:::definition "paper_eq_2_8" (lean := "SerrePositivity.Section2.normalized_frobenius_length_tendsto_perfection_quotient_of_primary") (uses := "paper_eq_2_7, paper_2_4, ext_Ma17_2_2, ext_Monsky")
**式 (2.8)**　完全化の主イデアル商長とHilbert–Kunz極限。対応表の状態：本体にある。

原典 PDF p.8 / layout L410。primary idealについて正規化Frobenius長の極限と完全化商の塔長を比較する。原典のe\_HKはその極限であり、任意のCでの追加公式とはしない。

外の文献：Ma17 2.2、Monsky

:::

:::corollary "paper_2_6" (lean := "SerrePositivity.cor_2_6_tor, SerrePositivity.Section4.residue_length_pos_of_lengthAlgebra_values") (uses := "paper_eq_2_4, paper_eq_2_6, paper_2_5")
**系 2.6**　有限長基底加群のTor消滅と剰余長の正値性。対応表の状態：本体にある。

原典 PDF p.9 / layout L459。本文同様に長さ代数の(2.4)–(2.6)を仮定した文脈で、任意の有限長A加群の高次Torの長さ零とdegree0のr倍公式を与える。剰余商の正値性は有限長商のフィルトレーションの評価で得る。長さ代数の存在をこの補題の新しい仮定に隠していない。

:::

