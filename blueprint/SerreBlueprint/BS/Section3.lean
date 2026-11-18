import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
import SerrePositivity.BhattScholze.Prism.Basic.UniversalOriented
import SerrePositivity.BhattScholze.Prism.Basic.UniversalOrientedFrobenius

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§3 " =>
%%%
number := false
tag := "bs-3"
%%%

BS §3 の項目と、本体の宣言との対応。本文は対応表（`research/bs-coverage`）の照合の理由で、原典の本文の写しではない。

:::lemma_ "bs_3_1"
*補題 3.1*　δ-pair の条件。対応表の状態：一部（special）。

I=(d) の場合に (1) と (2) を distinguished 性と比較して同値とする。局所主 ideal の ind-Zariski 被覆 (3) は扱わない。

宣言：`SerrePositivity.BhattScholze.DeltaStructure.isDistinguished_iff_p_mem_span_pow`、`SerrePositivity.BhattScholze.DeltaStructure.IsDistinguished.p_mem_span_pow`、`SerrePositivity.BhattScholze.OrientedPrism.isDistinguished_generator`、`SerrePositivity.BhattScholze.DeltaStructure.isDistinguished_iff_p_mem_span`

:::

:::definition "bs_3_2"
*定義 3.2*　prism の圏。対応表の状態：一部（special）。

生成元とその正則性を選んだ向き付き prism とその射・有界性の定義。一般の Cartier 因子、全 δ-pair の圏および flat map の全記述は含まない。

宣言：`SerrePositivity.BhattScholze.OrientedPrism`、`SerrePositivity.BhattScholze.OrientedPrism.Hom`、`SerrePositivity.BhattScholze.Prismatic.IsBoundedPrism`

:::

:::proposition "bs_3_3" (lean := "SerrePositivity.BhattScholze.OrientedPrism.crystalline, SerrePositivity.BhattScholze.OrientedPrism.exists_crystalline_iff")
*例 3.3*　結晶 prism。対応表の状態：本体にある。

I=(p) なら p 自体を向きに選べる。同じ δ 環の結晶 prism の存在 iff p 正則かつ古典 p 完備を述べる。

:::

:::proposition "bs_3_4" (lean := "SerrePositivity.BhattScholze.universalOrientedPrism, SerrePositivity.BhattScholze.universalOrientedPrism_bounded, SerrePositivity.BhattScholze.existsUnique_universalOrientedPrismHom, SerrePositivity.BhattScholze.universalOrientedPrism_frobenius_isCompletelyFlat, SerrePositivity.BhattScholze.universalOrientedPrism_regular")
*例 3.4*　普遍向き付き prism。対応表の状態：本体にある。

同じ普遍向き付き prism の構成・有界性・向きを保つ射の存在一意性に加え、universalOrientedPrism\_regular が p,d 正則列を、frobenius\_isCompletelyFlat が mod p の d 完全平坦性を与える。

:::

:::lemma_ "bs_3_5"
*補題 3.5*　剛性。対応表の状態：一部（special）。

向き付き prism の同じ射の I⊗B≃J と IB=J および像の生成元の正則性。一般の非主 ideal と後半の必要十分条件の十分方向は含まない。

宣言：`SerrePositivity.BhattScholze.OrientedPrism.Hom.map_ideal_eq`、`SerrePositivity.BhattScholze.OrientedPrism.Hom.idealBaseChangeEquiv`、`SerrePositivity.BhattScholze.OrientedPrism.Hom.idealTensorEquiv`、`SerrePositivity.BhattScholze.OrientedPrism.Hom.existsUnique_generator_unit`、`SerrePositivity.BhattScholze.OrientedPrism.Hom.map_generator_mul_injective`

:::

:::lemma_ "bs_3_6"
*補題 3.6*　φ(I)A は主で生成元は distinguished。対応表の状態：なし。

一般 prism の φ(I)A の主性と二つの可逆加群の自明化を未同定。向きを仮定して初めから主 ideal とするだけでは一般の結論を示さない。

:::

:::lemma_ "bs_3_7"
*補題 3.7*　有界 prism の性質。対応表の状態：一部（special）。

向き付き有界 P の古典完備性、bounded-above の導来完全平坦複体・指定 K-flat 複体の離散性、完全平坦 δ 代数からの prism 構成を得る。任意 D(A)・非主 ideal と局所向きの構成(4)は含まない。

宣言：`SerrePositivity.BhattScholze.boundedPrism_pair_isAdicComplete`、`SerrePositivity.BhattScholze.Prismatic.derivedCompletelyFlat_isDiscrete_of_boundedPrism`、`SerrePositivity.BhattScholze.Prismatic.completelyFlatCochain_isDiscrete_of_boundedPrism`、`SerrePositivity.BhattScholze.Prismatic.prismCompletedTensor_completelyFaithfullyFlat`、`SerrePositivity.BhattScholze.Prismatic.exists_boundedPrism_of_completelyFlat_deltaAlgebra`

:::

:::lemma_ "bs_3_8"
*補題 3.8*　完全 prism の性質。対応表の状態：一部（special）。

完全な向き付き prism の商の全 p 冪ねじれを p が消すことと古典 (p,d) 完備性を証明する。一般の完全 prism の ideal が主であるという結論は向きとして仮定している。

宣言：`SerrePositivity.BhattScholze.OrientedPrism.quotient_p_pow_torsion_killed_by_p`、`SerrePositivity.BhattScholze.perfectPrism_pair_isAdicComplete`、`SerrePositivity.BhattScholze.OrientedPrism.isDistinguished_generator`

:::

:::lemma_ "bs_3_9"
*補題 3.9*　prism の完全化。対応表の状態：一部（special）。

向き付き入力の同じ prism perfection と、完全 prism への射の普遍性を与える。未完備 Aperf の諸正則性と derived/classical 完備化の比較全体は含まない。

宣言：`SerrePositivity.BhattScholze.classicalPrismPerfection`、`SerrePositivity.BhattScholze.existsUnique_classicalPrismPerfectionHom`、`SerrePositivity.BhattScholze.existsUnique_perfectDeltaPDPrismHom`、`SerrePositivity.BhattScholze.existsUnique_deltaPerfectionPDCompletionHom`、`SerrePositivity.BhattScholze.existsUnique_pCompletedPrismHom`

:::

:::theorem "bs_3_10"
*定理 3.10*　perfectoid 環 ＝ 完全 prism。対応表の状態：一部（component）。

完全向き付き prism の商の perfectoid 性、perfectoid 環の prism 表示および射の持ち上げ・Witt 回収を個々に与える。絶対圏の関手と自然同型からなる原文の圏同値そのものは未供給。

宣言：`SerrePositivity.BhattScholze.OrientedPrism.quotient_isIntegralPerfectoid`、`SerrePositivity.BhattScholze.exists_perfectoidTrialPrism`、`SerrePositivity.BhattScholze.existsUnique_perfectPrismHomLift`、`SerrePositivity.BhattScholze.wittDistinguishedQuotient_isIntegralPerfectoid`、`SerrePositivity.BhattScholze.Semiperfectoid.exists_fontaineCompatibleWittEquiv`、`SerrePositivity.BhattScholze.Semiperfectoid.exists_ainfClassicalPrism`

:::

:::proposition "bs_3_11"
*注意 3.11*　正則局所環の perfectoid 被覆。対応表の状態：なし。

完備正則局所環の Cohen 表示から Frobenius lift と忠実平坦 perfectoid 被覆を作る宣言を未同定。

:::

:::corollary "bs_3_12"
*系 3.12*　全 prism の site。対応表の状態：一部（special）。

固定向き付き有界基底と濃度 cutoff の site に限り、flat topology と同じ構造環・商環の層条件を証明する。全 bounded prism の site と RΓ の高次消滅との接続は未供給。

宣言：`SerrePositivity.BhattScholze.Prismatic.PrismOver.flatTopology`、`SerrePositivity.BhattScholze.Prismatic.PrismOver.exists_isPushout_isFaithfullyFlat`、`SerrePositivity.BhattScholze.Prismatic.PrismOver.isSheaf_of_flatRingCechExact`、`SerrePositivity.BhattScholze.Prismatic.PrismOver.isPushout_flatResidueRing`、`SerrePositivity.BhattScholze.Prismatic.PrismOver.structureRing_isSheaf`、`SerrePositivity.BhattScholze.Prismatic.PrismOver.quotientStructureRing_isSheaf`

:::

:::proposition "bs_3_13"
*命題 3.13*　正則イデアルの prismatic envelope。対応表の状態：一部（special）。

向き付き基底、B が完備自由 δ 環、J が d と変数で生成される場合の envelope の存在・普遍性・完全平坦性と底変換。一般の相対完全正則列と flat localization (3) は含まない。

宣言：`SerrePositivity.BhattScholze.Prismatic.exists_prismaticEnvelope_of_variables`、`SerrePositivity.BhattScholze.Prismatic.IsPrismaticEnvelope`、`SerrePositivity.BhattScholze.Prismatic.IsPrismaticEnvelope.unique`、`SerrePositivity.BhattScholze.Prismatic.prismaticEnvelope_completedBaseChange_of_variables`

:::

:::proposition "bs_3_14"
*例 3.14*　Prop 3.13 の典型的な適用。対応表の状態：一部（special）。

自由変数と variable substitution の場合の同じ envelope の普遍性と存在。任意の完全滑らかな B₀→R の場合は扱わない。

宣言：`SerrePositivity.BhattScholze.Prismatic.exists_prismaticEnvelope_of_variables`、`SerrePositivity.BhattScholze.Prismatic.isPrismaticEnvelope_variableSubstitution`、`SerrePositivity.BhattScholze.Prismatic.IsPrismaticEnvelope.of_closure`

:::

