import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.BhattScholze.Almost.AlmostConnectivity
import SerrePositivity.BhattScholze.Almost.AlmostTensorForward
import SerrePositivity.BhattScholze.Almost.Lemma103
import SerrePositivity.BhattScholze.Perfectoidization.CompletedTensor
import SerrePositivity.CommutativeAlgebra.EtaleStratification.Stratification

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§10 " =>
%%%
number := false
tag := "bs-10"
%%%

BS §10 の項目と、本体の宣言との対応。本文は対応表（`research/bs-coverage`）の照合の理由で、原典の本文の写しではない。

:::definition "bs_10_1"
*定義 10.1*　J-almost zero。対応表の状態：一部（component）。

同じ J\_perfd を商の普遍 perfectoid 化への核で定め、IsAlmostZero の零化条件を適用する。末尾 J=(p) の核が√pRという同一視まではこの行の型から直接得ていない。

宣言：`SerrePositivity.BhattScholze.Almost.perfectoidKernel`、`SerrePositivity.Almost.IsAlmostZero`

:::

:::proposition "bs_10_2"
*命題 10.2*　almost zero の拡大閉性。対応表の状態：一部（component）。

同じ perfectoid 商の核に関する導来 p 完備短完全列の拡大閉性は直接得る。任意 J は perfectoidKernel\_quotient\_isIntegralPerfectoid と一般商の extension-closed 定理を適用。圏同値と tensor ideal 全体は含まない。

宣言：`SerrePositivity.BhattScholze.Almost.perfectoidIdeal_isAlmostZero_extension`、`SerrePositivity.BhattScholze.integralPerfectoid_completeIdealExtensionClosed`

:::

:::lemma_ "bs_10_3" (lean := "SerrePositivity.BhattScholze.Almost.perfectoidIdeal_lemma103, SerrePositivity.BhattScholze.Almost.integralPerfectoid_completedQuotientTensorIdeal_isZero, SerrePositivity.BhattScholze.Almost.perfectoidIdeal_completedQuotientMul_isIso, SerrePositivity.BhattScholze.Almost.integralPerfectoid_completedIdealTensorQuotient_isZero, SerrePositivity.BhattScholze.Almost.integralPerfectoid_completedIdealMul_isIso, SerrePositivity.BhattScholze.Almost.integralPerfectoid_completedDerivedIdealMul_isIso, SerrePositivity.BhattScholze.Almost.perfectoidKernel_quotient_isIntegralPerfectoid, SerrePositivity.BhattScholze.integralPerfectoid_completedQuotientMul_isIso")
*補題 10.3*　J\_perfd に沿った完備テンソル。対応表の状態：本体にある。

K=perfectoidKernel(J) の商の perfectoid 性と環の第一同型定理に一般商の三定理を適用し、同じ標準積 K⊗̂ᴸK→K・Q⊗̂ᴸQ→Q の同型と K⊗̂ᴸQ=0 を得る。任意 J に対し組み合わせ可能で、単項に限定しない。

:::

:::proposition "bs_10_4"
*命題 10.4*　非有界複体の almost zero。対応表の状態：一部（component）。

同じ任意の p 完備 J と同じ p 完備複体 M について、全 cohomology の K 零化 iff K との completed tensor が零という最初の同値を証明する。後半の導来圏同値・thick tensor ideal 全体は含まない。

宣言：`SerrePositivity.BhattScholze.Almost.isAlmostZero_iff_completedTensor_isZero`、`SerrePositivity.BhattScholze.Almost.isAlmostZero_of_completedTensor_isZero`

:::

:::lemma_ "bs_10_5" (lean := "SerrePositivity.BhattScholze.Almost.connective_iff_almost, SerrePositivity.BhattScholze.Almost.isAlmostConnective_iff_completedTensor_connective")
*補題 10.5*　連結性の判定。対応表の状態：本体にある。

§10.1の立ち仮定 J が導来 p 完備という条件を保ち、同じ M の connective iff 商との完備テンソルが connective かつ J-almost connective に一致。

:::

:::definition "bs_10_6"
*定義 10.6*　J-almost G-Galois 拡大。対応表の状態：なし。

J-almost G-Galois の群作用・指定二射による定義を本体で未同定。

:::

:::proposition "bs_10_7"
*注意 10.7*　mod pⁿ の冪等性。対応表の状態：一部（component）。

原文明記の J\_perfd の mod p\^n 像の冪等性は、任意 J の perfectoid 商の核への一般定理の適用で得る。Galois 条件の mod p\^n 版と単項核の tensor flatness は含まない。

宣言：`SerrePositivity.BhattScholze.Almost.perfectoidIdealMod_idempotent`、`SerrePositivity.BhattScholze.integralPerfectoid_ideal_mod_power_idempotent`

:::

:::proposition "bs_10_8"
*命題 10.8*　André の命題（And18b 1.9.1）。対応表の状態：なし。

J-almost G-Galois から almost finite projective・unramified への同じ主張を未同定。

:::

:::theorem "bs_10_9"
*定理 10.9*　almost purity。対応表の状態：なし。

主 ideal への帰着・分裂比較環・局所化同型の証明部品は本体。指定 S\_perfd の離散性と almost finite projective/unramified の主張は未組立で、補助を partial にしない。

宣言：`SerrePositivity.BhattScholze.Almost.isAlmostZero_iff_forall_gen`、`SerrePositivity.BhattScholze.Almost.trivialCoverComparison_localization_iso`

:::

:::proposition "bs_10_10"
*注意 10.10*　注意。対応表の状態：なし。

証明手法の説明であり、独立した対応数学的宣言は未同定。

:::

:::theorem "bs_10_11"
*定理 10.11*　整代数の perfectoid 化は離散で perfectoid。対応表の状態：未証明の入力に依存。

E3 存在 sorry の integral 欄と universal 欄から、通常の整 R-代数の perfd の離散性・perfectoid 性・普遍環の存在を受け取る。Δ\_S/A,perf 自体の δ 構造・perfect 性との具体的比較は drafts。近似・余極限の部品だけを本項の証明としない。

宣言：`SerrePositivity.BhattScholze.PerfectoidizationInterface.PerfectoidizationInterfaceE3`、`SerrePositivity.BhattScholze.Inputs.exists_perfectoidizationInterfaceE3`、`SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral`

:::

:::lemma_ "bs_10_12" (lean := "SerrePositivity.CommutativeAlgebra.exists_finiteEtaleStratification, SerrePositivity.CommutativeAlgebra.exists_noetherian_finiteEtaleStratification")
*補題 10.12*　有限表示有限射の層別。対応表の状態：本体にある。

同じ有限表示有限 Z\_(p)-代数射に、有限個の g\_i・unit ideal・各 reduced stratum の finite étale/universal homeomorphism 分解・p 反転後同型・p=0又は単元という三結論を与える。root import 閉包内かどうかとは別の宣言の数学的対応。

:::

:::proposition "bs_10_13"
*注意 10.13*　可換環論への応用。対応表の状態：なし。

同じ完備正則局所環の R⁺ と Tor の c-almost 消滅を結ぶ HM17 応用の宣言を未同定。

:::

