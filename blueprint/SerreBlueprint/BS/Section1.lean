import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§1 " =>
%%%
number := false
tag := "bs-1"
%%%

BS §1 の項目と、本体の宣言との対応。本文は対応表（`research/bs-coverage`）の照合の理由で、原典の本文の写しではない。

:::definition "bs_1_1"
*定義 1.1*　。対応表の状態：一部（special）。

I=(d) に生成元と正則性を指定し、古典的な p,d 完備性を持つ向き付き prism の場合。一般の Cartier 因子・導来 (p,I) 完備の定義全体は含まない。

宣言：`SerrePositivity.BhattScholze.OrientedPrism`、`SerrePositivity.BhattScholze.OrientedPrism.ofDistinguished`

:::

:::proposition "bs_1_2"
*注意 1.2*　。対応表の状態：一部（component）。

δ 構造から φ(x)=x\^p+pδ(x) の環準同型を構成する部分。p 正則時の逆構成は2.2の宣言で補えるが、この行の二宣言だけで回想の全記述を覆ったとはしない。

宣言：`SerrePositivity.BhattScholze.DeltaStructure`、`SerrePositivity.BhattScholze.DeltaStructure.frobeniusLift`

:::

:::proposition "bs_1_3"
*例 1.3*　。対応表の状態：一部（component）。

列挙した例のうち結晶 prism の構成・特徴付けと完全な向き付き prism の商の perfectoid 性。圏同値、Breuil–Kisin・q 型および非 prism の反例は含まない。

宣言：`SerrePositivity.BhattScholze.OrientedPrism.crystalline`、`SerrePositivity.BhattScholze.OrientedPrism.exists_crystalline_iff`、`SerrePositivity.BhattScholze.OrientedPrism.quotient_isIntegralPerfectoid`

:::

:::definition "bs_1_4"
*定義 1.4*　。対応表の状態：一部（special）。

有界性は商の p 冪ねじれを一様な冪で消す同じ条件。ただし入力 P は向き付き prism に限定される。

宣言：`SerrePositivity.BhattScholze.Prismatic.IsBoundedPrism`

:::

:::proposition "bs_1_5"
*命題 1.5*　Proposition 3.5。対応表の状態：一部（special）。

同じ prism の射の ideal の像の等式を向き付きの場合に証明する。一般の非主 Cartier 因子は扱わない。

宣言：`SerrePositivity.BhattScholze.OrientedPrism.Hom.map_ideal_eq`、`SerrePositivity.BhattScholze.OrientedPrism.Hom.existsUnique_generator_unit`、`SerrePositivity.BhattScholze.OrientedPrism.Hom.idealBaseChangeEquiv`

:::

:::definition "bs_1_6"
*定義 1.6*　。対応表の状態：一部（component）。

向き付き有界基底・κ-small な affine の対象 PrismOver のデータ。原文の一般形式的スキームの site と二つの構造層・RΓ の構成までは含まない。

宣言：`SerrePositivity.BhattScholze.Prismatic.PrismOver`

:::

:::proposition "bs_1_7"
*注意 1.7*　。対応表の状態：なし。

原文は絶対・étale・quasisyntomic 等の site の変種の説明。対応する数学的宣言は未同定。perfect site は4.6で別途判定する。

:::

:::theorem "bs_1_8"
*定理 1.8*　。対応表の状態：なし。

一般の比較定理の宣言は drafts にのみある。本体の結晶基底の HodgeTateIsoStatement は reducedModel のコホモロジーに関する定理で、原文の site RΓ との同一視を伴わないため部品として記録する。

宣言：`hodgeTate_iso`、`SerrePositivity.BhattScholze.Prismatic.hodgeTate_of_deRham_cartier`、`deRham_iso_rootAlgebra_modP`

:::

:::proposition "bs_1_9"
*例 1.9*　。対応表の状態：なし。

結晶 Frobenius 降下および Ainf 比較の帰結を扱う対応宣言を未同定。1.8の比較を部品だけから既証明としない。

:::

:::proposition "bs_1_10"
*注意 1.10*　。対応表の状態：なし。

Ainf・Breuil–Kisin・q-de Rham 比較の説明。対応する site 比較の宣言を未同定。

:::

:::proposition "bs_1_11"
*注意 1.11*　。対応表の状態：なし。

affine 比較から一般の形式的スキーム・stack への拡張の説明。affine 模型のみではこの降下比較を直接導かない。

:::

:::theorem "bs_1_12"
*定理 1.12*　。対応表の状態：一部（component）。

(2) の semiperfectoid quotient の普遍 perfectoid 化の存在と全射性は同じ環・単位について直接証明される。(1) の全 prism での始対象・その perfection との指定同一視は含まない。

宣言：`SerrePositivity.BhattScholze.Semiperfectoid.exists_perfectoidization_of_semiperfectoid_quotient`、`SerrePositivity.BhattScholze.Semiperfectoid.perfectPrismQuotientPerfectoidizationMap_isPerfectoidization`、`SerrePositivity.BhattScholze.Semiperfectoid.exists_surjective_perfectoidization_of_semiperfectoid_quotient`

:::

:::proposition "bs_1_13"
*注意 1.13*　Almost mathematics with respect to any closed set。対応表の状態：一部（component）。

任意の p 完備 ideal J の同じ普遍 perfectoid 化の核 K について、商の perfectoid 性と integralPerfectoid\_completedDerivedIdealMul\_isIso を組み、原文の K⊗̂ᴸK→K の同型を直接得る。good almost mathematics の圏全体を構成したとはしない。

宣言：`SerrePositivity.BhattScholze.Almost.perfectoidKernel`、`SerrePositivity.BhattScholze.Almost.perfectoidKernel_quotient_isIntegralPerfectoid`、`SerrePositivity.BhattScholze.Almost.integralPerfectoid_completedDerivedIdealMul_isIso`

:::

:::theorem "bs_1_14"
*定理 1.14*　。対応表の状態：なし。

qrsp の離散性・flatness・始性は drafts。Nygaard・TP 比較も未同定。本体の δ/envelope の部品だけでは原文の Δ\_S の主張を得ない。

宣言：`qrsp_isDiscretePrismatic`、`qrsp_completelyFaithfullyFlat`、`qrsp_initial`

:::

:::proposition "bs_1_15"
*注意 1.15*　。対応表の状態：なし。

TP の Frobenius と prismatic δ 構造の比較を未同定。

:::

:::theorem "bs_1_16"
*定理 1.16*　Theorem 15.3。対応表の状態：なし。

quasisyntomic Nygaard filtration と site 比較を未同定。

:::

:::theorem "bs_1_17"
*定理 1.17*　。対応表の状態：未証明の入力に依存。

(1) の整代数の普遍 perfectoid 化の存在は Inputs の E3 存在 sorry を取り出して導く。原文(2)の任意 J の almost 有限 étale 性はこの宣言には含まない。

宣言：`SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral`、`SerrePositivity.BhattScholze.Inputs.exists_perfectoidizationInterfaceE3`

:::

:::theorem "bs_1_18"
*定理 1.18*　Theorem 14.1。対応表の状態：なし。

p-adic Tate twist の奇数次数消滅の対応宣言を未同定。

:::

