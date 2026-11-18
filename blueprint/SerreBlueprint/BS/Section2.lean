import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.BhattScholze.Delta.Basic.DeltaQuotient
import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
import SerrePositivity.BhattScholze.Delta.Distinguished.Distinguished
import SerrePositivity.BhattScholze.Delta.Distinguished.Universal
import SerrePositivity.BhattScholze.Delta.DividedPower.Coefficients.Factorial
import SerrePositivity.BhattScholze.Delta.Extension.DeltaAdicCompletion
import SerrePositivity.BhattScholze.Delta.Extension.DeltaLocalization
import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeDelta
import SerrePositivity.BhattScholze.Delta.Perfect.DistinguishedRegular
import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§2 " =>
%%%
number := false
tag := "bs-2"
%%%

BS §2 の項目と、本体の宣言との対応。本文は対応表（`research/bs-coverage`）の照合の理由で、原典の本文の写しではない。

:::definition "bs_2_1" (lean := "SerrePositivity.BhattScholze.DeltaStructure, SerrePositivity.BhattScholze.DeltaStructure.delta_mul, SerrePositivity.BhattScholze.DeltaStructure.delta_add, SerrePositivity.BhattScholze.DeltaStructure.ofFunction")
*定義 2.1*　δ 環。対応表の状態：本体にある。

W₂への切断としての DeltaStructure と ofFunction・delta\_add・delta\_mul により、同じ δ の零・一・加法・積の四公理と構造を往復できる。Witt 第1係数は原文の整数係数加法多項式である。

:::

:::proposition "bs_2_2" (lean := "SerrePositivity.BhattScholze.DeltaStructure.frobeniusLift, SerrePositivity.BhattScholze.DeltaStructure.existsUnique_of_frobeniusLift, SerrePositivity.BhattScholze.DeltaStructure.existsUnique_of_mod_p")
*注意 2.2*　Frobenius 持ち上げ。対応表の状態：本体にある。

同じ φ の構成と、p 正則下での Frobenius 持ち上げからの δ 構造の存在一意性。mod p の一致による記述もある。p が単元なら持ち上げ条件は自動で同じ対応を得る。

:::

:::proposition "bs_2_3"
*注意 2.3*　λ 環との関係。対応表の状態：なし。

λ-ring/p-typical λ-structure との比較定理を未同定。δ の零元条件だけでは Wilkerson の対応を示さない。

:::

:::proposition "bs_2_4" (lean := "SerrePositivity.BhattScholze.WittTwo, SerrePositivity.BhattScholze.DeltaStructure")
*注意 2.4*　δ 構造 ＝ W₂ への切断。対応表の状態：本体にある。

WittTwo と第0係数射の環準同型切断という DeltaStructure の定義は、同じ W₂(R) と (x,δ(x)) による記述に一致。

:::

:::proposition "bs_2_5"
*注意 2.5*　導来 Frobenius 持ち上げ。対応表の状態：なし。

SCR\_Fp の導来 Frobenius 持ち上げの空間との同値を未同定。p 正則な通常環の構成だけではこの比較にならない。

:::

:::proposition "bs_2_6"
*例 2.6*　始 δ 環 \\(\\mathbb Z\_\{(p)\}\\)。対応表の状態：一部（component）。

Z\_(p) の δ 構造の始性と p 冪零 δ 環の零性を直接述べる。p-adic valuation をちょうど1下げる計算と全反復値の単元性までは含まない。

宣言：`SerrePositivity.BhattScholze.DeltaStructure.subsingleton_of_isNilpotent_p`、`SerrePositivity.BhattScholze.existsUnique_primeLocalIntDeltaHom`

:::

:::proposition "bs_2_7"
*注意 2.7*　極限・余極限、Witt。対応表の状態：一部（component）。

通常の tensor pushout と有向余極限の δ 構造・普遍射を直接与える。任意の極限・余極限、Witt の右随伴全体は未供給。ghost 注入性を要する Witt 写像は一般の主張として数えない。

宣言：`SerrePositivity.BhattScholze.tensorDeltaStructure`、`SerrePositivity.BhattScholze.existsUnique_tensorDeltaHom`、`SerrePositivity.BhattScholze.deltaDirectLimitStructure`、`SerrePositivity.BhattScholze.deltaDirectLimitLift_isDeltaHom`、`SerrePositivity.BhattScholze.perfectDeltaTensorStructure`、`SerrePositivity.BhattScholze.deltaWittGhostRingHom`

:::

:::definition "bs_2_8" (lean := "SerrePositivity.BhattScholze.RelativeFreeDeltaRing, SerrePositivity.BhattScholze.existsUnique_relativeFreeDeltaHom, SerrePositivity.BhattScholze.existsUnique_relativeFreePresentationHom")
*記法 2.8*　添加と消去。対応表の状態：本体にある。

相対自由 δ 環と δ 安定閉包の商の普遍性が、添加と関係を課す原文の記法を同じ δ 環上で与える。

:::

:::lemma_ "bs_2_9" (lean := "SerrePositivity.BhattScholze.DeltaStructure.isStable_iff_existsUnique_quotient, SerrePositivity.BhattScholze.DeltaStructure.quotient, SerrePositivity.BhattScholze.DeltaStructure.existsUnique_quotient_lift")
*補題 2.9*　商。対応表の状態：本体にある。

同じ ideal I の δ 安定性 iff A/I に一意の compatible δ 構造、さらに商の普遍射まで。p 正則性を追加しない。

:::

:::proposition "bs_2_10" (lean := "SerrePositivity.BhattScholze.DeltaStructure.deltaClosure, SerrePositivity.BhattScholze.DeltaStructure.existsUnique_deltaClosure_quotient_lift, SerrePositivity.BhattScholze.DeltaStructure.deltaClosure_eq_span_iterates")
*例 2.10*　δ 閉包での商。対応表の状態：本体にある。

同じ I の反復 δ 像の生成 ideal として δClosure を同定し、A/δClosure(I) の普遍性を述べる。

:::

:::lemma_ "bs_2_11"
*補題 2.11*　自由 δ 環、Frobenius の忠実平坦性。対応表の状態：一部（component）。

相対自由 δ 環の係数を Z\_(p) に取れば δ 反復変数による多項式環の表示と普遍性を得る。通常の Frobenius の忠実平坦性と Q 上の φ 反復変数表示は未供給。mod p/完全忠実平坦性で置き換えない。

宣言：`SerrePositivity.BhattScholze.RelativeFreeDeltaRing`、`SerrePositivity.BhattScholze.existsUnique_relativeFreeDeltaHom`

:::

:::corollary "bs_2_12"
*系 2.12*　Frobenius は fpqc 局所全射。対応表の状態：なし。

任意の δ 環・元について fpqc に Frobenius の原像を作る宣言を未同定。完全忠実平坦版だけでは通常の忠実平坦性を含まない。

:::

:::proposition "bs_2_13"
*注意 2.13*　Joyal の δₙ。対応表の状態：一部（stronger-hyp）。

同じ A の ghostMap 注入性を追加すると δWittGhostRingHom と各 ghost 成分の φ 反復公式を得る。一般の p ねじれを持つ δ 環での自然な w\_R と δ\_n の一般多項式表示は含まない。

宣言：`SerrePositivity.BhattScholze.deltaWittGhostRingHom`、`SerrePositivity.BhattScholze.deltaWittGhostVector_frobenius_formula`、`SerrePositivity.BhattScholze.deltaWittGhostRingHom_unique`

:::

:::proposition "bs_2_14"
*注意 2.14*　Joyal の作用素による自由 δ 環。対応表の状態：一部（stronger-hyp）。

係数 δ 環の p 正則性を明示すると、同じ相対自由環の Witt 座標多項式同型を構成する。これを Z\_(p) に適用できるが、一般の係数環で無条件とはしない。

宣言：`SerrePositivity.BhattScholze.relativeFreeWittCoordinateEquiv`、`SerrePositivity.BhattScholze.relativeFreeFiniteWittCoordinateEquiv`

:::

:::lemma_ "bs_2_15" (lean := "SerrePositivity.BhattScholze.DeltaStructure.localization, SerrePositivity.BhattScholze.DeltaStructure.existsUnique_localization, SerrePositivity.BhattScholze.DeltaStructure.existsUnique_localization_lift")
*補題 2.15*　局所化。対応表の状態：本体にある。

φ 安定な同じ multiplicative set の局所化に compatible δ 構造が一意に延長し、δ 準同型の普遍性も得る。

:::

:::proposition "bs_2_16"
*注意 2.16*　p 局所化。対応表の状態：一部（component）。

原文が使う T=\{S,φ(S),…\} の生成部分モノイドとその δ 局所化の普遍射を構成する部分。p-localization の同一視・p∈rad の標的での普遍性全体は未供給。

宣言：`SerrePositivity.BhattScholze.DeltaStructure.frobeniusDenominators`、`SerrePositivity.BhattScholze.DeltaStructure.existsUnique_saturatedLocalization_lift`

:::

:::lemma_ "bs_2_17" (lean := "SerrePositivity.BhattScholze.DeltaStructure.delta_mem_pow, SerrePositivity.BhattScholze.DeltaStructure.adicCompletion, SerrePositivity.BhattScholze.DeltaStructure.existsUnique_adicCompletion")
*補題 2.17*　I 進完備化。対応表の状態：本体にある。

δ(I\^(n+1))⊆I\^n の評価と δ の加法式から原文の連続性を得る。有限生成 I⊇(p) の同じ古典完備化への compatible δ 構造も存在一意。

:::

:::lemma_ "bs_2_18"
*補題 2.18*　エタール射・導来完備化への延長。対応表の状態：なし。

候補は p,d の完備化の H⁰ に δ 構造を入れる定理であり、原文の導来 I 完備 SCR とその完全 étale 代数上の構造の延長との比較を含まない。通常環の部品をそのまま special としない。

宣言：`SerrePositivity.BhattScholze.existsUnique_deltaPDCompletionStructure`、`SerrePositivity.BhattScholze.deltaPDCompletionStructure`

:::

:::definition "bs_2_19" (lean := "SerrePositivity.BhattScholze.DeltaStructure.IsDistinguished, SerrePositivity.BhattScholze.DeltaStructure.IsDeltaHom.map_isDistinguished")
*定義 2.19*　distinguished。対応表の状態：本体にある。

δ(d) が単元という定義および同じ δ 準同型による保存に一致。

:::

:::proposition "bs_2_20"
*例 2.20*　distinguished 元の例。対応表の状態：一部（component）。

列挙中 (1) の d=p の distinguished 性を p∈Jacobson radical の同じ条件下で証明する。q・Ainf の ξ・Breuil–Kisin の他の例は未同定。

宣言：`SerrePositivity.BhattScholze.DeltaStructure.isDistinguished_p`、`SerrePositivity.BhattScholze.DeltaStructure.delta_p_sub_one_mem`

:::

:::proposition "bs_2_21" (lean := "SerrePositivity.BhattScholze.UniversalDistinguishedRing, SerrePositivity.BhattScholze.universalDistinguishedGenerator_isDistinguished, SerrePositivity.BhattScholze.existsUnique_universalDistinguishedHom, SerrePositivity.BhattScholze.universalDistinguished_regular")
*例 2.21*　普遍 distinguished δ 環。対応表の状態：本体にある。

同じ普遍 distinguished δ 環の局所化表示と存在一意の射、mod p 正則性を与える。標的の p-local 条件は原文の Z\_(p)-代数性。

:::

:::proposition "bs_2_22"
*注意 2.22*　distinguished 元を p へ。対応表の状態：なし。

原文の指定合成 A→A→W(A)→W(A/d) で d=pu となる定理を未同定。Construction6.1の別の覆いとは区別する。

:::

:::lemma_ "bs_2_23" (lean := "SerrePositivity.BhattScholze.DeltaStructure.IsDistinguished.unit_mul, SerrePositivity.BhattScholze.DeltaStructure.isDistinguished_unit_mul_iff")
*補題 2.23*　distinguished 元の単元倍。対応表の状態：本体にある。

同じ d,p∈rad と単元 u の条件から ud の distinguished 性を述べる。逆向きも存在。

:::

:::lemma_ "bs_2_24" (lean := "SerrePositivity.BhattScholze.DeltaStructure.isDistinguished_factor")
*補題 2.24*　distinguished 元の因子。対応表の状態：本体にある。

d=fh、f,p∈rad から f が distinguished かつ h 単元という同じ二結論。

:::

:::lemma_ "bs_2_25" (lean := "SerrePositivity.BhattScholze.DeltaStructure.isDistinguished_iff_p_mem_span, SerrePositivity.BhattScholze.DeltaStructure.isDistinguished_iff_of_span_eq, SerrePositivity.BhattScholze.DeltaStructure.isDistinguished_iff_p_mem_span_pow")
*補題 2.25*　\\(p\\in(d,\\varphi(d))\\) ⇔ distinguished。対応表の状態：本体にある。

同じ d,p∈rad 下の δ(d) 単元 iff p∈(d,φ(d)) と、同じ主 ideal の生成元間の不変性を直接述べる。

:::

:::definition "bs_2_26" (lean := "SerrePositivity.BhattScholze.DeltaStructure.IsPerfect")
*定義 2.26*　完全 δ 環。対応表の状態：本体にある。

φ の bijectivity として IsPerfect を定義。環準同型ではこれが同型と同値。

:::

:::proposition "bs_2_27"
*注意 2.27*　完全化。対応表の状態：一部（component）。

左側の perfection colim\_φ の構成・perfect 性・普遍性を同じ δ 環について証明する。逆極限の右随伴は含まない。

宣言：`SerrePositivity.BhattScholze.DeltaPerfection`、`SerrePositivity.BhattScholze.existsUnique_deltaPerfectionHom`、`SerrePositivity.BhattScholze.deltaPerfection_isPerfect`

:::

:::lemma_ "bs_2_28" (lean := "SerrePositivity.BhattScholze.DeltaStructure.torsion_calculation, SerrePositivity.BhattScholze.DeltaStructure.p_mul_injective_of_frobeniusLift_injective, SerrePositivity.BhattScholze.DeltaStructure.p_mul_injective_of_isReduced")
*補題 2.28*　p ねじれ。対応表の状態：本体にある。

同じ任意の δ 環について φ 注入または reduced の二つの場合の p 正則性を証明する。

:::

:::proposition "bs_2_29"
*注意 2.29*　Lemma 2.28 の仮定についての注意。対応表の状態：なし。

Frobenius 注入性と reduced 性が互いに導かないという原文の二反例を未同定。

:::

:::proposition "bs_2_30"
*注意 2.30*　導来 Frobenius 持ち上げによる説明。対応表の状態：一部（component）。

導来 Frobenius による説明全体ではないが、明記された最終式 φ(A\[p\])=0 は torsion\_calculation の第一結論から同じ A で直接得られる。

宣言：`SerrePositivity.BhattScholze.DeltaStructure.torsion_calculation`

:::

:::corollary "bs_2_31"
*系 2.31*　完全 δ 環 ↔ 完全 F\_p 代数。対応表の状態：一部（component）。

完全 p 完備 δ 環を W(A/p) から回収する同型、剰余環の perfect 性、環準同型の δ 適合性を対象ごとに与える。三つの圏の関手と自然同型からなる圏同値全体は未供給。

宣言：`SerrePositivity.BhattScholze.DeltaStructure.IsPerfect.perfectRing_mod_p`、`SerrePositivity.BhattScholze.existsUnique_wittDeltaStructure`、`SerrePositivity.BhattScholze.perfectDeltaWittRecoveryEquiv`、`SerrePositivity.BhattScholze.wittDeltaStructure_ringHom_isDeltaHom_of_complete`、`SerrePositivity.BhattScholze.perfectSource_ringHom_isDeltaHom`

:::

:::lemma_ "bs_2_32" (lean := "SerrePositivity.BhattScholze.DeltaStructure.pow_p_dvd_delta_pow, SerrePositivity.BhattScholze.DeltaStructure.delta_eq_zero_of_has_pow_roots")
*補題 2.32*　完全な元は rank 1。対応表の状態：本体にある。

同じ x の δ(x\^(p\^n)) の p\^n 可除性と、p 分離・全 p 冪根存在下の δ(y)=0 に一致。

:::

:::lemma_ "bs_2_33"
*補題 2.33*　Teichmüller 係数による判定。対応表の状態：一部（special）。

A=W(k) の標準 δ 構造に限定して同じ Teichmüller 第1係数の単元性 iff distinguished を証明する。一般の完全 A への輸送はここでは数えない。

宣言：`SerrePositivity.BhattScholze.wittDeltaStructure_isDistinguished_iff`、`SerrePositivity.BhattScholze.wittDeltaStructure_isDistinguished_iff_teichmuller_coefficient`

:::

:::lemma_ "bs_2_34" (lean := "SerrePositivity.BhattScholze.DeltaStructure.IsDistinguished.mul_injective, SerrePositivity.BhattScholze.DeltaStructure.IsPerfect.distinguished_mul_injective, SerrePositivity.BhattScholze.DeltaStructure.IsDistinguished.quotient_p_pow_torsion_killed_by_p")
*補題 2.34*　d は非零因子、R\[p\]=R\[p\^∞\]。対応表の状態：本体にある。

同じ p 正則・p 分離・A/p reduced の条件から d の正則性と A/d の全 p 冪ねじれを p が消す二結論。

:::

:::lemma_ "bs_2_35" (lean := "SerrePositivity.BhattScholze.DeltaStructure.factorial_dvd_pow_of_prime_dvd_pow, SerrePositivity.BhattScholze.DeltaStructure.exists_factorial_quotient_mem")
*補題 2.35*　γ\_p から全 γ\_n。対応表の状態：本体にある。

Z\_(p)-代数の同じ z で p\|z\^p から n!\|z\^n を示す。p 正則なら分数体内の γ\_n(z) の所属という原文に戻る。さらに pd ideal 内の値も与える。

:::

:::lemma_ "bs_2_36"
*補題 2.36*　A\{φ(x)/p\} ＝ pd 包。対応表の状態：なし。

候補は同じ通常の δ 除算環と DPFamilyPresentation・階乗部分環の同型。原文の universal PD-envelope D\_(x) への分冪構造・普遍 PD 射としての指定同定は未同定で、別の表示環との環同型だけを C≅D の component としない。

宣言：`SerrePositivity.BhattScholze.frobeniusDivisionFactorialEquiv`、`SerrePositivity.BhattScholze.freeCoordinateFrobeniusDivision_primeRegular`、`SerrePositivity.BhattScholze.freeCoordinateFrobeniusDivisionPDEquiv`

:::

:::proposition "bs_2_37"
*注意 2.37*　導来 pushout の離散性。対応表の状態：なし。

通常環の TorAlg 消滅と通常の pushout の普遍性はあるが、原文の SCR の homotopy pushout との比較宣言は未同定。両者の識別を部品だけから既証明としない。

宣言：`SerrePositivity.BhattScholze.frobeniusDivisionPushout_torAlg_subsingleton`、`SerrePositivity.BhattScholze.existsUnique_frobeniusDivisionPushoutLift`

:::

:::lemma_ "bs_2_38"
*補題 2.38*　正則列の pd 包。対応表の状態：なし。

通常の DPFamilyPresentation の p 正則性・底変換と Tor 消滅は本体にあるが、原文の SCR の derived pushout D⁰ および universal PD-envelope との指定同定は未同定。同じ対象への比較を欠く証明部品を partial としない。

宣言：`SerrePositivity.BhattScholze.dpFamilyPresentation_primeRegular`、`SerrePositivity.BhattScholze.dpFamilyPresentation_tor_subsingleton`、`SerrePositivity.BhattScholze.dpFamilyFactorialEquiv`、`SerrePositivity.BhattScholze.dpFamilyBaseChangeEquiv`

:::

:::corollary "bs_2_39"
*系 2.39*　A\{φ(f)/p\} ＝ D\_I(A)。対応表の状態：なし。

通常の δ 除算環と分冪表示環の同型・p 正則性は本体。原文の SCR の derived δ pushout C とその離散性・universal PD-envelope への比較は未同定で、表示環の部品だけでは直接の部分と判定できない。

宣言：`SerrePositivity.BhattScholze.frobeniusDivisionDPEnvelopeEquiv`、`SerrePositivity.BhattScholze.frobeniusDivision_primeRegular`、`SerrePositivity.BhattScholze.frobeniusDivisionPDCompletionEquiv`、`SerrePositivity.BhattScholze.frobeniusDivisionDPFamilyEquiv`

:::

:::proposition "bs_2_40"
*注意 2.40*　\\(D\_I(A)\\) は φ の引き戻し。対応表の状態：なし。

指定 PD-envelope の φ-pullback と選んだ生成列に依存しない普遍性の同定を未同定。除算環の部品だけから φ 降下を主張しない。

:::

:::proposition "bs_2_41"
*Warning 2.41*　部分環は δ 構造によらない。対応表の状態：一部（component）。

原文前半の φ-twisted 除算部分環の δ 構造からの独立性を同じ A\[1/p\] の range 等式で証明する。後半の untwisted R₁,R₂ の非包含の反例は含まない。

宣言：`SerrePositivity.BhattScholze.deltaPDivisionToAway_range_eq_of_deltaStructure`

:::

:::definition "bs_2_42"
*定義 2.42*　相対的 \\(I\\) 完全正則性。対応表の状態：なし。

通常環の Koszul ホモロジーで定めた IsCompletelyRegularRel はあるが、原文の SCR 上の flat map との比較がない。相対導来完全正則性の同じ定義と未照合。

宣言：`SerrePositivity.BhattScholze.Prismatic.IsCompletelyRegularRel`、`SerrePositivity.BhattScholze.Prismatic.relativeKoszulComparison`

:::

:::lemma_ "bs_2_43"
*補題 2.43*　pd 包の押し出しの \\(p\\) 完全平坦性。対応表の状態：なし。

設計と rank-one mod p 計算の部品のみ。原文の相対完全正則列に沿う derived PD pushout の完全平坦性は未同定。

:::

:::corollary "bs_2_44"
*系 2.44*　envelope の p 完全平坦性。対応表の状態：なし。

設計と自由変数での完全忠実平坦性のみ。原文の一般の相対完全正則列の derived δ pushout との比較は未同定。

:::

