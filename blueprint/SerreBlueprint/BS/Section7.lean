import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.BhattScholze.Semiperfectoid.Discrete.PrismRetract
import SerrePositivity.BhattScholze.Semiperfectoid.Surjectivity.RootEnvelope.PerfectPrism
import SerrePositivity.BhattScholze.Semiperfectoid.Surjectivity.Surjectivity
import SerrePositivity.CategoryTheory.InitialOfRetraction

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§7 " =>
%%%
number := false
tag := "bs-7"
%%%

BS §7 の項目と、本体の宣言との対応。本文は対応表（`research/bs-coverage`）の照合の理由で、原典の本文の写しではない。

:::definition "bs_7_1"
*記法 7.1*　semiperfectoid。対応表の状態：なし。

qrsp の有界ねじれ・cotangent flatness を束ねた定義は drafts。本体の semiperfectoid quotient の展開仮定だけでは本項の qrsp 定義全体にならない。

宣言：`IsQuasiregularSemiperfectoid`、`BoundedPTorsion`、`CotangentPCompletelyFlat`

:::

:::proposition "bs_7_2"
*命題 7.2*　普遍 prism の存在。対応表の状態：なし。

全 prism の圏の同じ Δinit\_S の始性は未同定。δ 除算とねじれ除去の完備化前の普遍性は構成の部品。

:::

:::corollary "bs_7_3"
*系 7.3*　S\_perfd の存在（B3）。対応表の状態：一部（component）。

任意の semiperfectoid quotient の同じ単位の普遍 perfectoid 化の存在を証明する。全 prism の Δinit\_S の p 完全化との一般の同一視は未供給。rootRelation の比較は特別な入力のみ。

宣言：`SerrePositivity.BhattScholze.Semiperfectoid.exists_rootRelationPrismaticPerfection`、`SerrePositivity.BhattScholze.Semiperfectoid.exists_perfectoidization_of_perfectoid_surjective_quotient`、`SerrePositivity.BhattScholze.Semiperfectoid.exists_perfectoidization_of_semiperfectoid_quotient`

:::

:::theorem "bs_7_4" (lean := "SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_semiperfectoid_quotient, SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_andre, SerrePositivity.BhattScholze.Semiperfectoid.exists_surjective_perfectoidization_of_semiperfectoid_quotient, SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_semiperfectoid_quotient_of_rootEnvelope")
*定理 7.4*　S → S\_perfd は全射（B4）。対応表の状態：本体にある。

同じ semiperfectoid quotient と任意の普遍 perfectoid 化の単位 f の全射性に一致。André の経路と root-envelope の別経路があり、E3 存在入力を要しない。

:::

:::proposition "bs_7_5"
*注意 7.5*　Zariski 閉集合。対応表の状態：なし。

Spa の Zariski closed と strongly Zariski closed の同定を未同定。環の全射性だけでは同じ adic 空間の比較を示さない。

:::

:::definition "bs_7_6"
*構成 7.6*　導来 prismatic コホモロジー。対応表の状態：なし。

同じ prismatic cohomology の left Kan extension・HT filtration・tensor/底変換/層条件の組み立ては drafts。本体の一般 Kan extension 基盤だけは本項の構成と未接続。

宣言：`derivedPrismaticCohomology`、`hodgeTateFiltration`、`derivedPrismaticCohomology_baseChange`、`derivedPrismaticCohomology_tensor`

:::

:::lemma_ "bs_7_7"
*補題 7.7*　離散な場合の導来 prismatic コホモロジー。対応表の状態：なし。

離散環への δ 延長・prism 構成と retract の一般論は本体だが、指定された Δ\_R/A の Frobenius と同定する比較が drafts。原文の同じ離散 Δ の部分を直接示す宣言ではない。

宣言：`SerrePositivity.BhattScholze.DeltaStructure.existsUnique_over_of_frobeniusLift`、`SerrePositivity.BhattScholze.DeltaStructure.existsUnique_over_of_equiv`、`SerrePositivity.BhattScholze.OrientedPrism.ofDiscreteDelta`、`SerrePositivity.BhattScholze.OrientedPrism.ofDiscreteDelta_bounded`、`SerrePositivity.BhattScholze.OrientedPrism.homOfFrobenius`、`SerrePositivity.BhattScholze.Prismatic.PrismOver.exists_initial_of_primeRegular_evaluation`、`SerrePositivity.BhattScholze.Prismatic.PrismOver.homOfFrobenius`

:::

:::lemma_ "bs_7_8" (lean := "CategoryTheory.initial_of_retraction_idempotent, CategoryTheory.initial_of_natural_legs, SerrePositivity.BhattScholze.Prismatic.PrismOver.exists_split_idempotent, SerrePositivity.BhattScholze.Prismatic.PrismOver.isIdempotentComplete")
*補題 7.8*　離散な場合の始対象。対応表の状態：本体にある。

原文どおりの冪等完備圏 C と忘却を分裂する F:C→Under X から、F(X) の冪等と対応する retract の始性を構成する。

:::

:::proposition "bs_7_9"
*例 7.9*　lci 商の prismatic コホモロジー。対応表の状態：なし。

lci envelope の存在・始性と稠密分冪生成元の部品は本体。原文の指定 Δ\_R/A と包 B の比較がないため、Δ の離散性・始性として数えない。

宣言：`SerrePositivity.BhattScholze.Semiperfectoid.exists_bounded_lciRelationEnvelope`、`SerrePositivity.BhattScholze.Semiperfectoid.IsFiniteLciRelationEnvelope`、`SerrePositivity.BhattScholze.Prismatic.IsPrismaticEnvelope.exists_initial_of_base_quotient`、`SerrePositivity.BhattScholze.Semiperfectoid.exists_lciRelation_regular_completedTensor`、`SerrePositivity.BhattScholze.Semiperfectoid.lciRelationConormalLinearMap_surjective`、`SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_dense_dividedPower_generators_retraction`、`SerrePositivity.BhattScholze.Semiperfectoid.exists_bounded_lciRelationEnvelope_faithful`

:::

:::proposition "bs_7_10"
*命題 7.10*　qrsp の計算。対応表の状態：なし。

rootRelation の有界 Ainf-envelope と完全化の比較・始性は本体にあるが、同じ derived Δ\_S/A の離散性・初期 prism・全入力での忠実平坦性との同定は drafts。

宣言：`SerrePositivity.BhattScholze.Semiperfectoid.exists_rootRelationAinfEnvelope`、`SerrePositivity.BhattScholze.Semiperfectoid.exists_rootRelationCompletedInitial`、`SerrePositivity.BhattScholze.Semiperfectoid.exists_rootRelationPrismaticPerfection`、`SerrePositivity.BhattScholze.Semiperfectoid.exists_ainfClassicalPrism`、`SerrePositivity.BhattScholze.Semiperfectoid.existsUnique_perfectEnvelopeHom`、`SerrePositivity.BhattScholze.Semiperfectoid.existsUnique_perfectPrismComparison`、`SerrePositivity.BhattScholze.Semiperfectoid.classicalPrismPerfection_cor73`、`SerrePositivity.BhattScholze.Semiperfectoid.classicalPrismPerfection_initial`、`SerrePositivity.BhattScholze.Semiperfectoid.rootRelationCompletedQuotientMap_surjective`

:::

:::proposition "bs_7_11"
*命題 7.11*　quasisyntomic 被覆の prismatic site への持ち上げ。対応表の状態：なし。

任意の quasisyntomic R に対する prismatic site の指定被覆とその perfection の flatness を未同定。

:::

:::proposition "bs_7_12"
*例 7.12*　quasisyntomic 被覆の例。対応表の状態：なし。

相対 perfectoid を使う同じ site の終対象の被覆性を未同定。André の別の PD 経路は本項の証明ではない。

:::

:::proposition "bs_7_13"
*例 7.13*　正則環の絶対 prismatic site の終対象の被覆。対応表の状態：なし。

絶対 site の終対象を prism perfection が覆うという同じ主張を未同定。

:::

:::theorem "bs_7_14"
*定理 7.14*　André の補題。対応表の状態：一部（component）。

第一文の p 完全忠実平坦な絶対整閉 perfectoid 拡大と両立する p 冪根は証明済み。末尾の mod p ind-syntomic に選べるという精密化は含まない。

宣言：`SerrePositivity.BhattScholze.Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed`、`SerrePositivity.BhattScholze.Andre.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed`、`SerrePositivity.IsAbsolutelyIntegrallyClosed.exists_compatible_pow_roots`

:::

:::proposition "bs_7_15"
*注意 7.15*　André の補題の精密形。対応表の状態：一部（component）。

同じモニック根の商 S の envelope T の ϖ 剰余に関する PD 表示・PD 射の普遍性と被覆性の成分を直接扱う。最終的な mod p ind-syntomic 性とその二つの一般的補題全体は未供給。

宣言：`SerrePositivity.BhattScholze.Andre.VarpiComparison.perfectPrismPDTensorVarpi_isDPMorphism`、`SerrePositivity.BhattScholze.Andre.existsUnique_perfectPrismVarpiPDMorphism_of_unconditional`、`SerrePositivity.BhattScholze.Andre.VarpiComparison.hodgeTate_completelyFaithfullyFlat_iff`

:::

