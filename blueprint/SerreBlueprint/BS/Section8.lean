import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§8 " =>
%%%
number := false
tag := "bs-8"
%%%

BS §8 の項目と、本体の宣言との対応。本文は対応表（`research/bs-coverage`）の照合の理由で、原典の本文の写しではない。

:::definition "bs_8_1"
*記法 8.1*　設定。対応表の状態：なし。

固定した Ainf(R)・ideal・distinguished 元を束ねる記法は drafts。本体には個々の perfect prism 表示があるが、この正本の構成としては未接続。

宣言：`perfectPrism`、`perfectPrismRing`

:::

:::definition "bs_8_2"
*定義 8.2*　perfectoid 化 S\_perfd。対応表の状態：未証明の入力に依存。

通常の離散 R-代数上の底の D(R) 関手 perfd・unit・H⁰ を E3 の存在 sorry から受け取る。原文の animated 定義域、Δ の φ-perfection と底変換の式および E∞ 構造を実装したものではない。

宣言：`SerrePositivity.BhattScholze.PerfectoidizationInterface.PerfectoidizationInterfaceE3`、`SerrePositivity.BhattScholze.Inputs.exists_perfectoidizationInterfaceE3`

:::

:::proposition "bs_8_3"
*例 8.3*　標数 p の場合。対応表の状態：なし。

標数 p で指定した derived perfectoidization と通常の perfection が一致する宣言は drafts。通常環の perfection の存在だけでは同じ比較を示さない。

宣言：`perfectoidization_charP`

:::

:::lemma_ "bs_8_4"
*補題 8.4*　coconnective。対応表の状態：なし。

本体の E3 から coconnective 欄は2026-10-26に削除済み。出典の参考記載だけを interface の根拠としない。補題自体の宣言は drafts。

宣言：`prismaticPerfection_coconnective`、`perfectoidization_coconnective`、`prismaticPerfection_h0_perfectDelta`

:::

:::proposition "bs_8_5"
*命題 8.5*　perfectoid 標的の極限。対応表の状態：未証明の入力に依存。

E3 存在 sorry から通常 R-代数と Type u の perfectoid 標的の指定 limitCone・極限性を受け取る。全 perfect site の RΓ 比較・全宇宙の巨大極限・A 非依存を構成済みとはしない。

宣言：`SerrePositivity.BhattScholze.PerfectoidizationInterface.PerfectoidizationInterfaceE3`、`SerrePositivity.BhattScholze.Inputs.exists_perfectoidizationInterfaceE3`

:::

:::lemma_ "bs_8_6"
*補題 8.6*　強い降下（descendability）。対応表の状態：なし。

指定 prismatic cohomology とその perfection の rootMap の descendability は drafts。一般の降下基盤だけでは原文の同じ二つの射に未適用。

宣言：`prismaticCohomology_rootMap_descendable`、`prismaticPerfection_rootMap_descendable'`、`rootMap_modP_eq_deRham`

:::

:::definition "bs_8_7"
*定義 8.7*　p 進形式スキームの arc 位相。対応表の状態：一部（special）。

affine p 完備環・濃度 cutoff に限定した rank-one 付値環による同じ arc-cover 条件と生成位相。一般の形式的スキームの open cover との貼り合わせは未供給。

宣言：`SerrePositivity.BhattScholze.Perfectoidization.Arc.IsArcCoverFamily`、`SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTopology`、`SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTopologyPerfd`

:::

:::lemma_ "bs_8_8"
*補題 8.8*　perfectoid による被覆。対応表の状態：一部（special）。

同じ p 完備 affine S の perfectoid 一点 arc-cover と cutoff 内の cover-density を証明する。非 affine 形式的スキームの大域被覆は扱わない。

宣言：`SerrePositivity.BhattScholze.Perfectoidization.Arc.exists_perfectoid_arcCover`、`SerrePositivity.BhattScholze.Perfectoidization.Arc.affPerfdInclusion_isCoverDense`

:::

:::proposition "bs_8_9"
*注意 8.9*　より簡単な基底。対応表の状態：なし。

全 rank-one 付値環の絶対整閉化の積による指定 arc-cover と非層性の説明を未同定。

:::

:::proposition "bs_8_10"
*命題 8.10*　arc 層性。対応表の状態：なし。

Milnor Čech 完全性・tilt・perfect Čech 項の部品は本体。原文の Perfd 上 O の arc 層条件・高次消滅・全 representable の層条件をまとめる定理は drafts。

宣言：`SerrePositivity.BhattScholze.Perfectoidization.Arc.cechExact_of_milnorTensor`、`SerrePositivity.BhattScholze.Perfectoidization.Arc.tilt_rankOneValuationRing`、`SerrePositivity.Cech.cechConerve_perfectRing`、`structurePresheaf_isArcSheaf`、`homPresheaf_isArcSheaf`

:::

:::corollary "bs_8_11"
*系 8.11*　arc 降下の系。対応表の状態：なし。

E3 に対応する arc-RΓ 欄はない。同じ S\_perfd=RΓ\_arc と arc descent の宣言は drafts であり、8.5の制限付き極限と同一視しない。

宣言：`perfectoidization_eq_arcCohomology`

:::

:::corollary "bs_8_12"
*系 8.12*　excision。対応表の状態：未証明の入力に依存。

E3 存在 sorry の excision から、離散 S,S′ の底の D(R) の指定四辺の pullback と、環の普遍 perfectoid 化の pullback を導く。animated 入力・E∞積構造の全主張は含まない。

宣言：`SerrePositivity.BhattScholze.PerfectoidizationInterface.PerfectoidizationInterfaceE3`、`SerrePositivity.BhattScholze.Inputs.exists_perfectoidizationInterfaceE3`、`SerrePositivity.BhattScholze.Inputs.perfectoidization_excision_isPullback`

:::

:::proposition "bs_8_13"
*命題 8.13*　完備テンソルとの可換性。対応表の状態：一部（stronger-hyp）。

指定された環の普遍 perfectoid 化を入力すると、元の completed derived tensor の H⁰ の単位を保つ普遍性・比較環同型を証明する。perfectoid 側の元の derived tensor が離散という定理もあるが、任意 animated 入力の E∞ 対称モノイダル関手を構成したとはしない。

宣言：`SerrePositivity.BhattScholze.prop813CompletedTensorMap_isPerfectoidization`、`SerrePositivity.BhattScholze.exists_prop813BaseChange_of_perfectoid_quotient`、`SerrePositivity.BhattScholze.prop813_perfectoidTensor_pure`、`SerrePositivity.BhattScholze.prop813ComparisonEquiv`、`SerrePositivity.BhattScholze.prop813ComparisonEquiv_comp`

:::

:::corollary "bs_8_14"
*系 8.14*　離散なら普遍 perfectoid 環。対応表の状態：未証明の入力に依存。

E3 存在 sorry の universal 欄により、離散な通常 R-代数の perfd が離散なら H⁰ の指定単位が普遍 perfectoid 化となる。一般の animated S の原文全体には拡張しない。

宣言：`SerrePositivity.BhattScholze.PerfectoidizationInterface.PerfectoidizationInterfaceE3`、`SerrePositivity.BhattScholze.Inputs.exists_perfectoidizationInterfaceE3`

:::

