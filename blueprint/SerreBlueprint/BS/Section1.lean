-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.BhattScholze.Almost.AlmostConnectivity
import SerrePositivity.BhattScholze.Almost.Lemma103
import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
import SerrePositivity.BhattScholze.Inputs.PerfectoidizationInterface
import SerrePositivity.BhattScholze.Perfectoidization.Interface.IntegralExistence
import SerrePositivity.BhattScholze.Prism.Basic.Bounded
import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
import SerrePositivity.BhattScholze.Prism.Basic.Rigidity
import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
import SerrePositivity.BhattScholze.Prismatic.Site.PrismOver
import SerrePositivity.BhattScholze.Semiperfectoid.Perfection.Perfectoidization
import SerrePositivity.BhattScholze.Semiperfectoid.Surjectivity.Surjectivity

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "§1 Introduction" =>
%%%
number := false
tag := "bs-1"
%%%

BS §1 の項目と、本体の宣言との対応。本文は対応表（`research/bs-coverage`）の照合の理由で、原典の本文の写しではない。

:::definition "bs_1_1" (lean := "SerrePositivity.BhattScholze.OrientedPrism, SerrePositivity.BhattScholze.OrientedPrism.ofDistinguished")
*定義 1.1*　。対応表の状態：一部（special）。

*主張*　prism は $`\delta` 環 $`A` と Cartier 因子を定めるイデアル $`I\subset A` の組で、$`A` が導来 $`(p,I)` 完備であり $`p\in I+\varphi_A(I)A` を満たすものをいう。prism の射はイデアルを保つ $`\delta` 環の射である。

I=(d) に生成元と正則性を指定し、古典的な p,d 完備性を持つ向き付き prism の場合。一般の Cartier 因子・導来 (p,I) 完備の定義全体は含まない。

:::

:::proposition "bs_1_2" (lean := "SerrePositivity.BhattScholze.DeltaStructure, SerrePositivity.BhattScholze.DeltaStructure.frobeniusLift")
*注意 1.2*　。対応表の状態：一部（component）。

*主張*　$`\delta` 構造から $`\varphi_A(x)=x^p+p\delta_A(x)` で Frobenius の持ち上げが得られ、$`p` ねじれのない可換環ではこの対応は全単射である。prism の完備性条件の下で Cartier イデアルが $`(d)` なら、$`p\in(d,\varphi_A(d))` は $`\delta_A(d)` が単元であることに等しい。

δ 構造から φ(x)=x\^p+pδ(x) の環準同型を構成する部分。p 正則時の逆構成は2.2の宣言で補えるが、この行の二宣言だけで回想の全記述を覆ったとはしない。

:::

:::proposition "bs_1_3" (lean := "SerrePositivity.BhattScholze.OrientedPrism.crystalline, SerrePositivity.BhattScholze.OrientedPrism.exists_crystalline_iff, SerrePositivity.BhattScholze.OrientedPrism.quotient_isIntegralPerfectoid")
*例 1.3*　。対応表の状態：一部（component）。

*主張*　典型的な prism は Frobenius 持ち上げのある $`p` 完備 $`p` ねじれなし環の $`(A,(p))`、perfectoid 環 $`R` に対応する $`(A_{\inf}(R),\ker\theta)`、$`u\mapsto\pi` を用いる $`W(k)[[u]]` 上の Breuil–Kisin 型、$`(\mathbf Z_p[[q-1]],([p]_q))` の q 結晶型である。同じ $`\delta` 環に複数の prism 構造が入り得る一方、$`W(\mathbf F_p[x]/(x^2))` は prism の台にならない例である。

列挙した例のうち結晶 prism の構成・特徴付けと完全な向き付き prism の商の perfectoid 性。圏同値、Breuil–Kisin・q 型および非 prism の反例は含まない。

:::

:::definition "bs_1_4" (lean := "SerrePositivity.BhattScholze.Prismatic.IsBoundedPrism")
*定義 1.4*　。対応表の状態：一部（special）。

*主張*　prism $`(A,I)` が有界であるとは、$`A/I` の $`p` 冪ねじれがある固定の $`p^n` で消えることをいう。

有界性は商の p 冪ねじれを一様な冪で消す同じ条件。ただし入力 P は向き付き prism に限定される。

:::

:::proposition "bs_1_5" (lean := "SerrePositivity.BhattScholze.OrientedPrism.Hom.map_ideal_eq, SerrePositivity.BhattScholze.OrientedPrism.Hom.existsUnique_generator_unit, SerrePositivity.BhattScholze.OrientedPrism.Hom.idealBaseChangeEquiv")
*命題 1.5*　Proposition 3.5。対応表の状態：一部（special）。

*主張*　prism の射 $`(A,I)\to(B,J)` では、標的の Cartier イデアルは $`IB` に等しい。

同じ prism の射の ideal の像の等式を向き付きの場合に証明する。一般の非主 Cartier 因子は扱わない。

:::

:::definition "bs_1_6" (lean := "SerrePositivity.BhattScholze.Prismatic.PrismOver")
*定義 1.6*　。対応表の状態：一部（component）。

*主張*　有界 prism $`(A,I)` と $`A/I` 上滑らかな $`p` 進形式スキーム $`X` に対し、prismatic site は基底の下の prism $`(B,J)` と基底上の射 $`\operatorname{Spf}(B/J)\to X` の圏の反対圏である。被覆は $`(p,I)` 完全忠実平坦な射で、構造層は $`I` ねじれのない $`\delta` $`A` 代数 $`B` を、剰余構造層は $`\mathcal O(X)` 代数 $`B/J` を与え、後者は前者を $`A/I` へテンソルした層である。

向き付き有界基底・κ-small な affine の対象 PrismOver のデータ。原文の一般形式的スキームの site と二つの構造層・RΓ の構成までは含まない。

:::

:::proposition "bs_1_7"
*注意 1.7*　。対応表の状態：なし。

原文は絶対・étale・quasisyntomic 等の site の変種の説明。対応する数学的宣言は未同定。perfect site は4.6で別途判定する。

:::

:::theorem "bs_1_8"
*定理 1.8*　。対応表の状態：なし。

一般の比較定理の宣言は drafts にのみある。本体の結晶基底の HodgeTateIsoStatement は reducedModel のコホモロジーに関する定理で、原文の site RΓ との同一視を伴わないため部品として記録する。

宣言：`SerrePositivity.BhattScholze.Prismatic.hodgeTate_of_deRham_cartier`

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

:::theorem "bs_1_12" (lean := "SerrePositivity.BhattScholze.Semiperfectoid.exists_perfectoidization_of_semiperfectoid_quotient, SerrePositivity.BhattScholze.Semiperfectoid.perfectPrismQuotientPerfectoidizationMap_isPerfectoidization, SerrePositivity.BhattScholze.Semiperfectoid.exists_surjective_perfectoidization_of_semiperfectoid_quotient")
*定理 1.12*　。対応表の状態：一部（component）。

*主張*　semiperfectoid 環 $`S` に対し、写像 $`S\to A/I` を備えた prism の圏は始対象 $`(\Delta_S^{\mathrm{init}},I)` をもち、その $`I` は単項である。始対象の $`(p,I)` 完備完全化を $`I` で割ると perfectoid 環 $`S_{\mathrm{perfd}}` となり、$`S` からの写像は全射で、perfectoid 環への写像について普遍的である。

(2) の semiperfectoid quotient の普遍 perfectoid 化の存在と全射性は同じ環・単位について直接証明される。(1) の全 prism での始対象・その perfection との指定同一視は含まない。

:::

:::proposition "bs_1_13" (lean := "SerrePositivity.BhattScholze.Almost.perfectoidKernel, SerrePositivity.BhattScholze.Almost.perfectoidKernel_quotient_isIntegralPerfectoid, SerrePositivity.BhattScholze.Almost.integralPerfectoid_completedDerivedIdealMul_isIso")
*注意 1.13*　Almost mathematics with respect to any closed set。対応表の状態：一部（component）。

*主張*　perfectoid 環 $`R` の $`p` 完備イデアル $`J` に対し、$`R\to(R/J)_{\mathrm{perfd}}` は perfectoid 環の全射である。その核 $`J_{\mathrm{perfd}}` は導来 $`p` 完備テンソルで自分自身に掛け合わせても変わらず、$`p` 完備加群と導来圏での $`J`-almost の基準を与える。

任意の p 完備 ideal J の同じ普遍 perfectoid 化の核 K について、商の perfectoid 性と integralPerfectoid\_completedDerivedIdealMul\_isIso を組み、原文の K⊗̂ᴸK→K の同型を直接得る。good almost mathematics の圏全体を構成したとはしない。

:::

:::theorem "bs_1_14"
*定理 1.14*　。対応表の状態：なし。

qrsp の離散性・flatness・始性は drafts。Nygaard・TP 比較も未同定。本体の δ/envelope の部品だけでは原文の Δ\_S の主張を得ない。

:::

:::proposition "bs_1_15"
*注意 1.15*　。対応表の状態：なし。

TP の Frobenius と prismatic δ 構造の比較を未同定。

:::

:::theorem "bs_1_16"
*定理 1.16*　Theorem 15.3。対応表の状態：なし。

quasisyntomic Nygaard filtration と site 比較を未同定。

:::

:::theorem "bs_1_17" (lean := "SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral, SerrePositivity.BhattScholze.Inputs.exists_perfectoidizationInterfaceE3")
*定理 1.17*　。対応表の状態：未証明の入力に依存。

*主張*　perfectoid 環 $`R` 上の整代数 $`S` には、perfectoid 環への写像に関して普遍的な perfectoid 化 $`S_{\mathrm{perfd}}` が存在する。有限生成イデアル $`J\subset R` の零点集合の外で $`R\to S` が有限エタールなら、$`R\to S_{\mathrm{perfd}}` は $`J`-almost 有限エタールである。

(1) の整代数の普遍 perfectoid 化の存在は Inputs の E3 存在 sorry を取り出して導く。原文(2)の任意 J の almost 有限 étale 性はこの宣言には含まない。

:::

:::theorem "bs_1_18"
*定理 1.18*　Theorem 14.1。対応表の状態：なし。

p-adic Tate twist の奇数次数消滅の対応宣言を未同定。

:::

