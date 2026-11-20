-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.Data.Finset.Powerset
import Mathlib.RepresentationTheory.Basic
import SerrePositivity.InfinityCategories.HA.Section6_1_1.SquareDuality
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Bicartesian
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFunctorCriterion
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionRepresentableLimits
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.HomotopyFiniteBiproduct
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.HomotopyPreadditive
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableFiniteLimitsColimits
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.NativeFilteredPreservation
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.UniversalityOfColimits.FilteredColimitFiniteLimitPreservation
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.QuasicategoryCore

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 6.1 The Calculus of Functors" =>
%%%
number := false
tag := "ha-6-1"
%%%

HA 6.1 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 6.1.1 n-Excisive Functors

%%%
number := false
tag := "ha-6-1-1"
%%%

:::definition "ha_6_1_1_1" (lean := "Finset.powerset, Finset.mem_powerset")
*HA 記法 6.1.1.1*　部分集合 poset と cube（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1015)）。対応表の状態：一部（component）。

*主張*　有限集合 $`S` の部分集合を包含で順序付けて $`\mathcal P(S)` とし、濃度が高々 $`i` または $`i` を超える部分集合をそれぞれ $`\mathcal P_{\le i}(S)`、$`\mathcal P_{>i}(S)` と書く。

KB-W2型再照合：仮定：有限集合 S を Finset で与える（HA と一致する有限集合の模型）。結論：powerset S は全有限部分集合を列挙し、その所属が部分集合関係と同値（P(S) の部分に一致）。cardinality の上下による三つの部分 poset の専用の型は含まれない。

部分集合の元の個数に応じて立方体の添字の部分順序を選ぶ。特に濃度高々一の部分には空集合と一元集合が入る。

:::

:::definition "ha_6_1_1_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare")
*HA 定義 6.1.1.2*　Cartesian・strongly coCartesian cube（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1015)）。対応表の状態：一部（component）。

*主張*　$`S` 立方体は $`N(\mathcal P(S))\to C` で、空集合での値が残りの極限ならデカルト、空集合と一元集合への制限の左 Kan 拡張なら強余デカルトである。

KB-W2型再照合：仮定：S が二元集合で、cube を Δ¹×Δ¹ の四角形として与える（Lean が強い：二次元の場合）。結論：Cartesian 性を対応 cospan の ∞ 極限錐、pushout 性を対応 span の ∞ 余極限余錐で定義する（二次元の二条件に一致する部分）。全有限 S の cube と P≤1 からの Kan 延長の一般定義は含まれない。

デカルト性は始頂点での極限性を要求する。強余デカルト性では濃度二以上の各頂点が、濃度高々一の部分での値から余極限として回収される。

:::

:::definition "ha_6_1_1_3" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sends_pushouts_to_pullbacks_of_suspensionSquares")
*HA 定義 6.1.1.3*　n-excisive 関手（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1015)）。対応表の状態：一部（stronger-hyp）。

*主張*　$`n`-切除的関手は、$`(n+1)` 元集合で添字付けた強余デカルト立方体をデカルト立方体に送る。

KB-W2型再照合：仮定：n=1、C は零対象・有限余極限を持つ準圏、D は有限極限を持つ準圏、F は全 suspension square を pullback に送る（Lean が強い：C の pointed 性と suspension での保存を追加）。結論：F は全 pushout square を pullback square に送る（原典の一次の切除性の要求する結論にこの仮定で一致）。任意 n の cube による述語と Excn の全部分圏、一次の必要十分条件全体は含まれない。

始域には有限余極限、終域には有限極限を仮定する。該当する関手からなる充満部分圏が $`\operatorname{Exc}_n(C,D)` である。

:::

:::proposition "ha_6_1_1_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift_ι, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_edge")
*HA 例 6.1.1.4*　n-Excisive Functors (p. 1015)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1015)）。対応表の状態：一部（component）。

*主張*　$`0`-切除的関手は、すべての射を同値に送る関手、すなわち終域の最大 Kan 部分複体を経由する関手である。

同じF:C→Dについて、quasicategoryCoreLiftとその包含との合成式は、全辺が可逆ならDのcoreを経由するという原文末尾の成分を直接与える。0-excisiveを定義する一辺cubeの極限条件との比較は含まない。

一元集合の立方体は一つの辺である。強余デカルト性は自動的で、デカルト性はその辺が同値であることになる。

:::

:::definition "ha_6_1_1_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.UniversalityOfColimits.smallSpaceColimitFunctor, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.UniversalityOfColimits.smallSpaceFilteredColimit_map_isLimit_finite, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionSpace_hasFiniteLimits")
*HA 定義 6.1.1.6*　differentiable ∞ 圏の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1016)）。対応表の状態：一部（special）。

*主張*　微分可能な ∞ 圏は有限極限と逐次余極限を持ち、逐次余極限の関手が有限極限を保つ。

KB-W2型再照合：仮定：C=S を構成済みの空間 ∞ 圏に限定（Lean が強い：空間の場合）。結論：有限極限が存在し、選んだ全小余極限関手のうち filtered 添字のものは全有限極限錐を保つ。特に順序添字で differentiable の三条件を満たす（この場合の定義条件に一致）。任意 C に対する differentiable の専用述語は含まれない。

逐次図式の添字は非負整数の順序の nerve である。存在条件に加え、任意の有限図式について極限と逐次余極限を交換できることを要求する。

:::

:::proposition "ha_6_1_1_7" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_of_isStable")
*HA 例 6.1.1.7*　stable 圏の differentiability の判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1016)）。対応表の状態：一部（component）。

*主張*　安定 ∞ 圏の微分可能性は、逐次余極限の存在、または同値な条件として可算余積の存在で判定できる。

KB-W2型再照合：仮定：安定な準圏 C（HA と一致）。結論：C は全有限形状の極限を持つ（明記された条件(a)の自動成立に一致）。順序余極限と可算余積の存在の同値、条件(c)の自動成立は含まれない。

有限極限は安定性で存在する。逐次余極限の関手は余極限を保つので、安定圏の関手として有限極限も保つ。

:::

:::proposition "ha_6_1_1_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.UniversalityOfColimits.smallSpaceColimitFunctor, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.UniversalityOfColimits.smallSpaceFilteredColimit_map_isLimit_finite, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionSpace_hasFiniteLimits")
*HA 例 6.1.1.8*　∞ トポスの differentiability（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1016)）。対応表の状態：一部（special）。

*主張*　任意の ∞ トポスは微分可能である。

KB-W2型再照合：仮定：∞ トポスを S の場合に限定（Lean が強い：構成済みの空間 ∞ 圏の場合）。結論：有限極限と全小余極限が存在し、filtered 余極限関手が全有限極限を保つので順序余極限も左完全（S が differentiable という結論に一致）。一般 ∞ トポスの切除と filtered exactness の主張は含まれない。

∞ トポスでの濾過余極限と有限極限の交換を、逐次図式に適用する。

:::

:::proposition "ha_6_1_1_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ind_hasSmallKappaFilteredColimits, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.indInclusion_preservesSmallKappaFilteredColimits")
*HA 例 6.1.1.9*　compactly generated 圏と differentiability（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1016)）。対応表の状態：一部（component）。

*主張*　コンパクト生成 ∞ 圏は微分可能である。

KB-W2型再照合：仮定：C=Indℵ₀(A) を指定し、A は小さい冪等完備な compact 生成部分の模型（Lean が強い：指定した Ind 模型の場合）。結論：Indℵ₀(A) に全小 filtered 余極限が存在し、前層への全部分包含がそれらを保つ（冒頭の前層圏での filtered 余極限閉性に一致する部分）。任意の compactly generated C との全比較、presentability と有限極限の左完全性の全結論は含まれない。

コンパクト対象の Ind 完備化を空間値前層圏に入れると、濾過余極限は前層圏で計算できる。有限極限と濾過余極限が交換するため、逐次余極限にもこれが適用できる。

:::

:::corollary "ha_6_1_1_16" (lean := "SerrePositivity.InfinityCategories.HA.Section6_1_1.isPushoutSquare_iff_reverseGrid, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pullback_of_pushout_square, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pushout_of_pullback_square")
*HA 系 6.1.1.16*　stable 圏の cube の双対性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1019)）。対応表の状態：一部（special）。

*主張*　安定 ∞ 圏の立方体を添字の補集合で反転して反対圏に移しても、強余デカルト性とデカルト性はいずれも同値な条件として保たれる。

Sが二元集合の場合に、同じsquareをreverseGridで反転するとpushout⇔pullbackを得て、安定性の二方向により反転前後のCartesian/coCartesian性を比較できる。全有限SのKan extensionによるstrongly coCartesian性と一般cubeは含まない。

反対を取ると極限と余極限が入れ替わる。安定性によって立方体の極限と余極限の判定が対応し、強い条件については各面での押し出しと引き戻しの一致を使う。

:::

# 6.1.4 Symmetric Functors

%%%
number := false
tag := "ha-6-1-4"
%%%

:::definition "ha_6_1_4_1" (lean := "CategoryTheory.cechNerveTerminalFrom, CategoryTheory.CechNerveTerminalFrom.iso")
*HA 記法 6.1.4.1*　EG・extended power・対称多変数関手（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1045)）。対応表の状態：一部（component）。

*主張*　群 $`G` の $`EG` を $`G\to *` の Čech nerve、$`BG` を自由作用の商とし、$`K` の第 $`n` 拡張冪を $`(K^n\times E\Sigma_n)/\Sigma_n` とする。

KB-W2型再照合：仮定：C=Type と群 G の underlying set、または通常の G-作用の圏（EG の定義部分の模型）。結論：G→終対象の Čech nerve を G\^(m+1) の simplicial object と自然同型で比較する（冒頭の EG の構成に一致）。可縮 Kan 性・自由作用と商 BG、extended power K(n) と SymFun の構成は含まれない。

$`EG` は可縮 Kan 複体で、$`K` が ∞ 圏なら拡張冪は対称群作用のホモトピー商を表す。この圏からの関手は対称 $`n` 変数関手であり、基礎関手が各変数で被約なら被約とする。

:::

:::lemma_ "ha_6_1_4_12" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pushout_of_pullback_square")
*HA 補題 6.1.4.12*　一次切除関手による strongly coCartesian cube の保存（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1050)）。対応表の状態：一部（special）。

*主張*　有限余極限を持つ圏から安定 ∞ 圏への $`1`-切除的関手は、強余デカルト立方体を強余デカルト立方体に送る。

Sが二元集合の場合に、1-excisiveなFが同じpushout squareをpullbackに送ることを入力すると、IsStable.pushout\_of\_pullback\_squareは同じ像のsquareをpushoutにする。多次元cubeのP≤1からの左Kan延長の保存は含まない。

$`1`-切除性により押し出しである二次元の面を引き戻しに送る。終域が安定なのでその面は押し出しでもあり、立方体の強余デカルト性が従う。

:::

# 6.1.6 Norm Maps

%%%
number := false
tag := "ha-6-1-6"
%%%

:::proposition "ha_6_1_6_17" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.preadditive_ho, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteBiproducts_ho")
*HA 例 6.1.6.17*　stable ∞ 圏の semiadditivity（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1066)）。対応表の状態：一部（component）。

*主張*　任意の安定 ∞ 圏は半加法的である。

KB-W2型再照合：仮定：安定な準圏 C（HA と一致）。結論：hC は前加法圏で全有限双積を持つ（本文で明記された hC の additive 性に一致する部分）。C の全相対 norm の可逆性を束ねる semiadditive 述語への比較は含まれない。

ホモトピー圏は加法的で、安定 ∞ 圏には有限積と有限余積がある。二つを比較する双積の射はホモトピー圏で同型なので、∞ 圏でも同値である。

:::

:::proposition "ha_6_1_6_23" (lean := "Representation.norm, Representation.norm_comp_self, Representation.self_comp_norm")
*HA 注意 6.1.6.23*　有限群の norm と作用の和（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1067)）。対応表の状態：一部（component）。

*主張*　半加法的 ∞ 圏の有限群作用で、余不変対象から不変対象へのノルムを元の対象への往復で見ると、群の全元の作用の和になる。

KB-W2型再照合：仮定：有限群 G の通常の半環上の線形表現（Lean が強い：加法的な通常の線形模型）。結論：群作用の射の和を定め、その前後への全群元の作用による不変性を証明する（第二段落末尾の通常の和の左右不変性に一致）。この和を HA の相対 norm と同定し、MG→MG の一般の coherent な写像を構成する部分は含まれない。

標準射 $`M\to M_G\to M^G\to M` の合成は $`\sum_{g\in G}\phi_g` である。通常圏では外側二つがエピ射と単射なので、この式がノルムを決定し、和の左右の作用による不変性がその存在を与える。

:::

