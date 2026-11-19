import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Definition
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.Pointed
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FiniteLimitsColimits

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 6.2 Differentiation" =>
%%%
number := false
tag := "ha-6-2"
%%%

HA 6.2 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 6.2.2 Stabilization of Differentiable Fibrations

%%%
number := false
tag := "ha-6-2-2"
%%%

:::definition "ha_6_2_2_18" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable")
*HA 定義 6.2.2.18*　Stabilization of Differentiable Fibrations (p. 1088)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1088)）。対応表の状態：一部（component）。

*主張*　被約局所微分可能ファイブレーションの安定化は、局所余デカルトな族として各ファイバーをそのスペクトル対象の圏に置き換え、辺に沿う移送を微分で与える比較である。

条件(2)の同じqの各vertexFiberの安定性をIsStableが直接表す。局所coCartesian性、微分・stabilizationの比較、テンソル積関手の完全性は含まない。

比較 $`U` は各ファイバーで左完全で、零次評価 $`\Omega^\infty` を通る完全関手がスペクトル対象の圏への同値となる。各辺で $`U` と移送を比較する自然変換が、元の移送の微分の普遍性を満たすことも要求する。

:::

# 6.2.4 Generalized Smash Products

%%%
number := false
tag := "ha-6-2-4"
%%%

:::definition "ha_6_2_4_10" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable")
*HA 定義 6.2.4.10*　Generalized Smash Products (p. 1109)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1109)）。対応表の状態：一部（component）。

*主張*　安定 ∞ オペラッドとは、射影が局所余デカルトで、基礎 ∞ 圏が安定、全ての有限項のテンソルが各変数で完全な ∞ オペラッドである。

条件(2)の同じ underlying O の安定性をIsStableが直接表す。局所coCartesian性、微分・stabilizationの比較、テンソル積関手の完全性は含まない。

局所余デカルト性が演算の共表現可能性を与える。有限集合 $`I` ごとに誘導される $`O^I\to O` の各変数で有限極限・有限余極限の保存を検査する。

:::

# 6.2.5 Stabilization of ∞-Operads

%%%
number := false
tag := "ha-6-2-5"
%%%

:::definition "ha_6_2_5_5" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable")
*HA 定義 6.2.5.5*　Stabilization of ∞-Operads (p. 1113)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1113)）。対応表の状態：一部（component）。

*主張*　共表現可能な局所 $`S` 族が安定であるには、各ファイバーの安定性と、辺上の多項演算の各変数での完全性を要求する。

stableの場合の条件(a)の同じ各Osの安定性をIsStableが直接表す。局所coCartesian性、微分・stabilizationの比較、テンソル積関手の完全性は含まない。

微分可能な族では、各ファイバーに微分可能性と有限余極限の存在を要求し、辺上の演算には逐次余極限の保存を課す。演算には $`\langle n\rangle\to\langle1\rangle` の活性写像を使う。

:::

# 6.2.6 Uniqueness of Stabilizations

%%%
number := false
tag := "ha-6-2-6"
%%%

:::definition "ha_6_2_6_1" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits")
*HA 定義 6.2.6.1*　Uniqueness of Stabilizations (p. 1121)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1121)）。対応表の状態：一部（component）。

*主張*　右完全な局所オペラッド族とは、共表現可能で、各ファイバーが点付き有限余完備で、各辺上の正の項数の演算が各変数で右完全となる族である。

原文の条件(b)は同じ各OsのHasZeroVertexとHasFiniteColimitsで直接表す。局所coCartesian性と各多変数テンソルのright exact性、および後続のAlgexの構成は含まない。

微分可能な族への写像のうち、各点でオペラッドの射となり、基礎では被約かつ切除的となるものを、対応する関手圏の充満部分圏として取る。

:::

