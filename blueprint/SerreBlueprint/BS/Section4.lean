import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§4 " =>
%%%
number := false
tag := "bs-4"
%%%

BS §4 の項目と、本体の宣言との対応。本文は対応表（`research/bs-coverage`）の照合の理由で、原典の本文の写しではない。

:::definition "bs_4_1"
*定義 4.1*　prismatic site。対応表の状態：一部（special）。

affine・向き付き有界基底・admissible cutoff の同じ PrismOver の flat topology と二つの構造環の層条件。一般の形式的スキームや cutoff を外した site の同定は含まない。

宣言：`SerrePositivity.BhattScholze.Prismatic.PrismOver`、`SerrePositivity.BhattScholze.Prismatic.PrismOver.flatTopology`、`SerrePositivity.BhattScholze.Prismatic.PrismOver.isSheaf_of_flatRingCechExact`、`SerrePositivity.BhattScholze.Prismatic.PrismOver.structureRing_isSheaf`、`SerrePositivity.BhattScholze.Prismatic.PrismOver.quotientStructureRing_isSheaf`

:::

:::proposition "bs_4_2"
*注意 4.2*　smooth の仮定についての注意。対応表の状態：なし。

一般 p-adic scheme への left Kan extension と derived site による回収の説明を本体で未同定。

:::

:::proposition "bs_4_3"
*注意 4.3*　prismatic topos の slice 表示と関手性。対応表の状態：なし。

同じ prismatic topos の slice 表示と形式的スキームの射による関手性を未同定。

:::

:::definition "bs_4_4"
*構成 4.4*　prismatic 層と étale 層。対応表の状態：なし。

形式的 étale site への cocontinuous functor と ν\_\* の比較を未同定。

:::

:::proposition "bs_4_5"
*注意 4.5*　位相の取り替え。対応表の状態：なし。

比較の宣言は drafts の derivedGlobalSections\_of\_le にのみ存在。原文の各位相での O\_Δ・crystal の RΓ 比較を本体で未同定。

宣言：`derivedGlobalSections_of_le`

:::

:::proposition "bs_4_6"
*注意 4.6*　完全 prismatic site。対応表の状態：なし。

perfect prismatic site と perfectoid-under category の比較は drafts。通常の個別 prism の商の定理だけではこの site の同値を直接与えない。

宣言：`PerfectPrismaticSite`、`perfectSite`、`perfectFlatTopology`、`perfectSiteEquivPerfectoidUnder`

:::

:::proposition "bs_4_7"
*注意 4.7*　絶対 prismatic site。対応表の状態：なし。

絶対 prismatic site の対応する本体の定義を未同定。

:::

:::lemma_ "bs_4_8"
*補題 4.8*　完全 prism からの写像の一意持ち上げ。対応表の状態：一部（stronger-hyp）。

同じ perfect 向き付き源と bounded 向き付き標的に限定すると、指定商の射の prism 射への存在一意の持ち上げを証明する。一般の非有界・非主 ideal の標的は扱わない。

宣言：`SerrePositivity.BhattScholze.existsUnique_perfectPrismHomLift_to_bounded`、`SerrePositivity.BhattScholze.perfectPrismHom_ext_to_bounded_target`、`SerrePositivity.BhattScholze.existsUnique_perfectPrismRingHomLift_to_bounded`

:::

:::definition "bs_4_9"
*構成 4.9*　HT 比較の写像。対応表の状態：なし。

hodgeTateMap は多項式の reducedModel の cohomology への写像。原文の Rν\_\* O\_Δ に対する Bockstein・ηとの比較が未供給。一般の cup・de Rham 普遍性は証明部品で、同じ η の成分とは数えない。

宣言：`SerrePositivity.BhattScholze.Prismatic.hodgeTateMap`、`SerrePositivity.Cosimplicial.cohomologyCup_comm`、`SerrePositivity.DeRham.exists_unique_dgHom`

:::

:::lemma_ "bs_4_10"
*補題 4.10*　HT 写像の性質。対応表の状態：なし。

bockstein\_sq\_zero は同じ多項式 reducedModel 上の BetaSquareZero を証明するが、site Δ̄ とその β の同定を含まない。模型の定理を原文の局所切断にそのまま適用しない。

宣言：`SerrePositivity.BhattScholze.Prismatic.bockstein_sq_zero`

:::

:::theorem "bs_4_11"
*定理 4.11*　HT 比較。対応表の状態：なし。

一般比較は drafts。本体は模型の写像と同型述語、および結晶基底での模型上の同型。site Δ̄ の ηとの比較がないため原文の同型の partial とはしない。

宣言：`SerrePositivity.BhattScholze.Prismatic.HodgeTateIsoStatement`、`SerrePositivity.BhattScholze.Prismatic.hodgeTate_iso_polynomial_Zp`、`hodgeTate_iso`、`SerrePositivity.BhattScholze.Prismatic.hodgeTate_of_deRham_cartier`

:::

:::corollary "bs_4_12"
*系 4.12*　底変換。対応表の状態：なし。

同じ site prismatic cohomology の底変換同型は drafts。項ごとの envelope 底変換と Tot の交換・site 比較の組み立ては未供給。

宣言：`prismaticCohomology_baseChange'`、`PrismaticCohomologyBaseChangeStatement`

:::

:::proposition "bs_4_13"
*注意 4.13*　Higgs 特殊化。対応表の状態：なし。

持ち上げ X̃ と Frobenius に依存する Higgs specialization および構造写像の分裂を未同定。

:::

:::proposition "bs_4_14"
*注意 4.14*　\\(A/I\^2\\) への持ち上げの障害。対応表の状態：なし。

τ≤1 Δ̄ の分裂 iff A/I² への持ち上げという同じ障害比較を未同定。

:::

:::proposition "bs_4_15"
*命題 4.15*　余接複体と \\(\\tau\^\{\\le 1\}\\overline\{\\Delta\}\\)。対応表の状態：なし。

同じ cotangent complex LX/A と τ≤1 Δ̄\{1\}\[1\] の自然同型を未同定。HT 模型の結果だけではこの指定比較を得ない。

:::

:::definition "bs_4_16"
*記法 4.16*　\\(\\Delta\_\{R/A\}\\) の定義（site の RΓ）。対応表の状態：なし。

site の RΓ としての prismaticCohomology・hodgeTateCohomology は drafts。模型の同名 cohomology と正本を区別する。

宣言：`prismaticCohomology`、`hodgeTateCohomology`、`prismaticCohomologyFrobenius`、`prismaticCohomology_cutoff_invariant`

:::

:::definition "bs_4_17"
*構成 4.17*　弱始対象。対応表の状態：一部（stronger-hyp）。

HasEnvelopes と admissible cutoff を追加すれば、同じ site の C⁰ の弱始性と Cⁿ の標準余積・関手性を直接得る。envelope の存在の供給は変数の場合に限られ、任意 smooth R の入力を無条件とはしない。

宣言：`SerrePositivity.BhattScholze.Prismatic.cechAlexanderObj_weaklyInitial`、`SerrePositivity.BhattScholze.Prismatic.cechAlexanderObj`、`SerrePositivity.BhattScholze.Prismatic.cechSmall_weaklyTerminal`、`SerrePositivity.BhattScholze.Prismatic.cechAlexanderAffine_weaklyInitial`、`SerrePositivity.BhattScholze.Prismatic.cechAlexanderComplex`、`SerrePositivity.BhattScholze.Prismatic.cechAlexander_isCoproduct`

:::

:::definition "bs_4_18"
*構成 4.18*　Čech–Alexander 複体。対応表の状態：なし。

big/small Čech 項・site 対象の同型と模型間の quasiIso は本体にあるが、原文の核心 C•≃RΓ の比較は drafts。構成に使う部品だけでは Δ を計算する主張の partial としない。

宣言：`SerrePositivity.BhattScholze.Prismatic.bigCechEval`、`SerrePositivity.BhattScholze.Prismatic.affineBigCechTerm`、`SerrePositivity.BhattScholze.Prismatic.cechAlexanderBigSiteIso`、`SerrePositivity.BhattScholze.Prismatic.affineToChosenCech_quasiIso`

:::

:::proposition "bs_4_19"
*注意 4.19*　affine 直線の底変換と両立する Čech–Alexander 複体。対応表の状態：一部（special）。

向き付き基底・有限変数の多項式の場合に、同じ Čech–Alexander cosimplicial 項の全単体射に自然な底変換を証明する。site RΓ や Tot の底変換との同一視は含まないが、本項の項ごとの構成の部分は一致。

宣言：`SerrePositivity.BhattScholze.Prismatic.cechAlexanderAffine_baseChange`、`SerrePositivity.BhattScholze.Prismatic.affineCechNerveData`、`SerrePositivity.BhattScholze.Prismatic.cechAlexanderAffine_isCoproduct`、`SerrePositivity.BhattScholze.Prismatic.affineEnvelopeTermCompletedBaseChangeIso`

:::

:::lemma_ "bs_4_20"
*補題 4.20*　底変換。対応表の状態：なし。

原文の Δ の completed base change は drafts。本体の envelope の項ごとの底変換は Tot・site RΓ との比較を含まない。

宣言：`prismaticCohomology_baseChange`、`hodgeTateCohomology_baseChange`、`crystallineCoverMap_prismaticCohomology`

:::

:::lemma_ "bs_4_21"
*補題 4.21*　étale 局所化。対応表の状態：なし。

任意の p-complete étale R→S について同じ Δ の étale localization を未同定。

:::

:::lemma_ "bs_4_22"
*補題 4.22*　完備底変換と totalization。対応表の状態：なし。

原文の一般の completed base change と Tot の交換は drafts。HasCochainCompleteTorAmplitude は本体にあるが、条件の定義だけでは交換定理の部分を直接証明しない。

宣言：`completedBaseChange_tot_comm`、`SerrePositivity.HasCochainCompleteTorAmplitude`

:::

