import Verso
import VersoManual
import VersoBlueprint
import Mathlib.Algebra.TrivSqZeroExt.Basic
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Definition
import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PullbackMapComponentEquivalence

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 7.3 The Cotangent Complex Formalism" =>
%%%
number := false
tag := "ha-7-3"
%%%

HA 7.3 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 7.3.1 Stable Envelopes and Tangent Bundles

%%%
number := false
tag := "ha-7-3-1"
%%%

:::definition "ha_7_3_1_1" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable, SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable")
*HA 定義 7.3.1.1*　Stable Envelopes and Tangent Bundles (p. 1280)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1280)）。対応表の状態：一部（component）。

*主張*　可提示 ∞ 圏の安定包は、可提示安定圏からの右随伴であって、可提示安定な任意の圏からの右随伴の圏を合成によって同値にする圏論的ファイブレーションである。

stable envelopeの条件(i)に明記された同じC′の安定性・可呈示性はIsStableとIsPresentableの同じ対象への適用で直接表す。環スペクトルやstable envelopeの存在・普遍性の定理ではない。

可提示ファイブレーションに相対化する場合、合成が可提示ファイブレーションとなり、デカルト辺を保ち、各ファイバーで安定包となることを要求する。原典の (3) の最後は、比較射の終域である元のファイバー $`C_D` を指すと読む。

:::

# 7.3.4 Tangent Bundles to ∞-Categories of Algebras

%%%
number := false
tag := "ha-7-3-4"
%%%

:::definition "ha_7_3_4_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable")
*HA 定義 7.3.4.1*　Tangent Bundles to ∞-Categories of Algebras (p. 1310)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1310)）。対応表の状態：一部（component）。

*主張*　安定 $`O` モノイダル ∞ 圏とは、$`O^\otimes` 上の余デカルト・オペラッド・ファイブレーションで、色のファイバーが安定、演算の移送が各変数で完全なものである。

同じq:C⊗→O⊗のCocartesianFibrationは条件(1)、同じ各vertexFiberのIsStableは条件(2)を直接表す。多変数演算のexact性は含まない。

安定性は色の単項部分で検査する。多項演算は入力のファイバーの積から出力のファイバーへの関手を定め、各変数に有限極限と有限余極限の保存を要求する。

:::

:::proposition "ha_7_3_4_17" (lean := "TrivSqZeroExt, TrivSqZeroExt.inr_mul_inr")
*HA 注意 7.3.4.17*　Tangent Bundles to ∞-Categories of Algebras (p. 1317)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1317)）。対応表の状態：一部（special）。

*主張*　平方零拡大 $`A\oplus M` のホモトピーは $`\pi_*A\oplus\pi_*M` で、斉次元の積は $`(a,m)(a',m')=(aa',am'+(-1)^{|a'||m|}a'm)` である。

KB-W2原文・型再照合：仮定：通常可換環 A と離散 A 加群 M（Lean が強い：離散入力の場合）。結論：台が A×M の通常の自明平方零拡大と M 成分同士の積の零性を与える（原典末尾の古典平方零拡大の場合に一致）。全次数の符号付き π の積と環スペクトルの Ω∞ との比較は含まれない。

$`M` 成分どうしの積は零で、交差項は $`A` の作用になる。環も加群も離散なら古典的平方零拡大を回収する。

:::

# 7.3.6 The Tangent Correspondence

%%%
number := false
tag := "ha-7-3-6"
%%%

:::lemma_ "ha_7_3_6_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.pullbackMap_isQCatEquivalence_of_components")
*HA 補題 7.3.6.2*　The Tangent Correspondence (p. 1328)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1328)）。対応表の状態：一部（stronger-hyp）。

*主張*　$`\Delta^1` 上の単体集合の圏論的同値は、終頂点 $`1` 上の厳密なファイバーに制限しても圏論的同値である。

KB-W2原文・型再照合：仮定：Δ¹ 上の準圏 A・B、categorical equivalence A→B、両射影の EquivalenceLifting（Lean が強い：任意の単体集合と射影に対してこの持ち上げ性・準圏性を追加する）。結論：底ともう一脚を恒等、第二脚を端点 \{1\}→Δ¹ とすると同じ pullback.map が準圏同値となる（この仮定での端点ファイバーの結論に一致）。任意の A・B への一般化は含まれない。

単体的圏化の後、これらのファイバーは $`1` の上の対象が張る充満部分単体的圏になる。元の同値の比較をこれらの部分に制限する。

:::

