import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§5 " =>
%%%
number := false
tag := "bs-5"
%%%

BS §5 の項目と、本体の宣言との対応。本文は対応表（`research/bs-coverage`）の照合の理由で、原典の本文の写しではない。

:::definition "bs_5_1"
*記法 5.1*　標数 p の記法（結晶 site）。対応表の状態：なし。

本項は R\^(1)=R⊗\_\{A/I,ψ\}A/p の指定 Frobenius twist の記法。候補 CrysOver と結晶基底の構成だけでは、この同じ twist を構成する宣言にならない。

宣言：`SerrePositivity.BhattScholze.Prismatic.CrysOver`、`SerrePositivity.BhattScholze.Prismatic.crysAlgebras`、`SerrePositivity.BhattScholze.Prismatic.crystallineBasePrism`

:::

:::theorem "bs_5_2"
*定理 5.2*　標数 p の結晶比較。対応表の状態：なし。

本体は指定した Čech/PD 模型間の bridge quasiIso。原文の二つの site の RΓ、E∞積と Frobenius への比較は未供給。通常の模型の cohomology 同型を同じ site 比較の component としない。

宣言：`SerrePositivity.BhattScholze.Prismatic.crystallineBridgeModP_isCohomologyIso`、`SerrePositivity.BhattScholze.Prismatic.crystallineBridge`、`SerrePositivity.BhattScholze.Prismatic.pdDeltaModel`、`SerrePositivity.BhattScholze.Prismatic.crystallineSmallBridgeCochainMap_quasiIso`、`SerrePositivity.BhattScholze.Prismatic.wittBigCompletedBridge_quasiIso`

:::

:::proposition "bs_5_3"
*注意 5.3*　Thm 5.2 についての注意。対応表の状態：なし。

Frobenius-pullback と crystalline RΓ の指定同型は未同定。5.2の模型だけではこの帰結を得ない。

:::

:::lemma_ "bs_5_4"
*補題 5.4*　Frobenius 捻りと Čech 脈体の擬同型。対応表の状態：一部（special）。

N が余単体的可換環から来る加群の場合、同じ polynomial Čech と relative Frobenius の pushout 射が unnormalized cochain cohomology の同型となる。任意の cosimplicial module は扱わない。

宣言：`SerrePositivity.BhattScholze.Prismatic.frobeniusTwist_cech_quasiIso`、`SerrePositivity.BhattScholze.Prismatic.frobeniusTwist_cech_quasiIso_infinite`

:::

:::corollary "bs_5_5"
*系 5.5*　標数 p の HT 比較。対応表の状態：なし。

結晶基底 Zp の多項式の reducedModel の HodgeTateIsoStatement は本体にあるが、site Δ̄ の η との比較は未供給。arbitrary smooth S と site 底変換を含む原文とは未接続。

宣言：`SerrePositivity.BhattScholze.Prismatic.hodgeTate_iso_polynomial_Zp`、`SerrePositivity.BhattScholze.Prismatic.hodgeTate_of_deRham_cartier`

:::

