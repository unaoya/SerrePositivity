import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§6 " =>
%%%
number := false
tag := "bs-6"
%%%

BS §6 の項目と、本体の宣言との対応。本文は対応表（`research/bs-coverage`）の照合の理由で、原典の本文の写しではない。

:::definition "bs_6_1"
*構成 6.1*　普遍向き付き prism から結晶 prism へ。対応表の状態：一部（stronger-hyp）。

原文の同じ α の有限完全 Tor 振幅(2)を上界3で証明する。(1)の検出は具体的 K-flat cochain model とその底変換も K-flat とする入力で与える。Frobenius の flatness から完全平坦性への橋はあるが、site Δ の底変換(3)は drafts。

宣言：`SerrePositivity.BhattScholze.Prismatic.Construction61.completelyFlat_of_flat`、`SerrePositivity.BhattScholze.Prismatic.Construction61.crystallineCoverMap_torAmplitude`、`SerrePositivity.BhattScholze.Prismatic.Construction61.quasiIso_of_completedCover_map_quasiIso`、`SerrePositivity.BhattScholze.Prismatic.Construction61.cochain_acyclic_of_completedCover_acyclic`

:::

:::proposition "bs_6_2"
*命題 6.2*　affine 直線の HT 比較。対応表の状態：なし。

affine line の site 比較と高次消滅の組み立ては drafts。Construction6.1の保存性・Tor 振幅だけはこの結論の直接の部分ではない。

宣言：`hodgeTate_iso_of_construction61`、`affineLine_moduleComparison`、`hodgeTate_iso`、`bockstein_sq_zero'`

:::

:::theorem "bs_6_3"
*定理 6.3*　HT 比較。対応表の状態：なし。

本体は模型上の HodgeTateMap・HodgeTateIsoStatement と結晶基底の結果。一般の site の cohomology sheaf との比較と向き付き基底への帰着は drafts。

宣言：`hodgeTate_iso`、`SerrePositivity.BhattScholze.Prismatic.HodgeTateIsoStatement`、`SerrePositivity.BhattScholze.Prismatic.hodgeTateMap`

:::

:::theorem "bs_6_4"
*定理 6.4*　de Rham 比較。対応表の状態：なし。

Witt の prism と模型間の completed derived quasiIso は本体にある。原文の site Δ の φ-pullback と de Rham の自然同型への比較は未供給で、部品を partial としない。

宣言：`SerrePositivity.BhattScholze.Prismatic.wittCrystallineDelta`、`SerrePositivity.BhattScholze.Prismatic.UniversalOrientedResidue`、`SerrePositivity.BhattScholze.Prismatic.psiPrism`、`SerrePositivity.BhattScholze.Prismatic.wittBigCompletedBridge_quasiIso`、`SerrePositivity.BhattScholze.Prismatic.wittToSmallCompletedBridge_quasiIso`、`SerrePositivity.BhattScholze.Prismatic.wittToSmallDerivedCompletedIso`

:::

