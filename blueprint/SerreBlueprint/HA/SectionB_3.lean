import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianInnerAnodynePullback
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianInnerHornPullback
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceLiftingPullback

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA B.3 Flat Inner Fibrations" =>
%%%
number := false
tag := "ha-B-3"
%%%

HA B.3 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

:::definition "ha_B_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence, CategoryTheory.Limits.pullback.fst")
*HA 定義 B.3.1*　Flat Inner Fibrations (p. 1494)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1494)）。対応表の状態：本体にある。

*主張*　準圏から $`\Delta^2` への関手が平坦であるとは、内角 $`\Lambda_1^2` の逆像の包含が圏論的同値となることである。

原文の同じp:X→Δ²に対し、pullback.fst p (horn 2 1).ι はX×Δ²Λ²₁→Xそのものである。その射のIsQCatEquivalenceが原文のflatという定義全体と一致する。後続のhomotopy pushoutの説明は独立の番号付き主張ではない。

$`0,1` の辺上の部分と $`1,2` の辺上の部分を、中央ファイバーで貼った四角形が Joyal の意味でホモトピー押し出しとなる。これは二つの対応を合成する条件である。

:::

:::proposition "ha_B_3_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianFibration_innerHorn_pullback_isPrecompositionEquivalence")
*HA 例 B.3.4*　middle への coCartesian lift による flat 性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1495)）。対応表の状態：一部（stronger-hyp）。

*主張*　$`\Delta^2` 上の内ファイブレーションで、$`0` 上の各対象から $`1` 上へ相対余デカルト辺が存在すれば、ファイブレーションは平坦である。

KB-W2原文・型再照合：仮定：p:X→∆2が全体でcoCartesian fibration（Leanが強い：各0頂点からmiddleへのcoCartesian liftだけでなく全辺のliftを仮定）。結論：inner horn Λ²₁の逆像包含は前合成同値、従ってcategorical equivalence（原典のflatnessの結論に一致）。原典の弱い片側lift仮定だけからの判定は含まれない。

$`0` から $`2` へ行く射を選んだとき、$`1` を経由する因子分解の圏で余デカルト移送が始対象を与える。その可縮性が平坦性の判定に使える。

:::

:::proposition "ha_B_3_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianFibration_pullback_innerAnodyne_isPrecompositionEquivalence")
*HA 例 B.3.11*　coCartesian・Cartesian fibration の flat 性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1498)）。対応表の状態：一部（component）。

*主張*　余デカルト・ファイブレーションは平坦な圏論的ファイブレーションであり、デカルト・ファイブレーションも平坦である。

KB-W2原文・型再照合：仮定：p:X→SがcoCartesian fibration（HAの前半と一致）。結論：各2単体に引き戻したinner hornの逆像包含は前合成同値、従ってcategorical equivalence（coCartesianなpがflatという前半のflatnessの結論に一致）。Cartesian側の対称な主張とcategorical fibrationの全比較をこの行の宣言だけでは含まない。

余デカルトの場合は $`\Delta^2` に制限して $`0\to1` の持ち上げを使う。デカルトの場合には反対を取って同じ判定を適用する。

:::

:::proposition "ha_B_3_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianFibration_pullback_innerAnodyne_isPrecompositionEquivalence")
*HA 命題 B.3.14*　flat 性と全 inner-anodyne 引き戻しの同値性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1499)）。対応表の状態：一部（stronger-hyp）。

*主張*　内ファイブレーションが平坦であることは、底上の全ての内 anodyne 射を引き戻すと圏論的同値になることで判定できる。

KB-W2原文・型再照合：仮定：pがcoCartesian fibrationで任意inner-anodyne A→Bと底への射を指定（Leanが強い：一般flat inner fibrationよりcoCartesianの場合に限定）。結論：その引き戻しの射が前合成同値、従ってcategorical equivalence（条件(1)にこの場合一致）。全inner fibrationに対する(1)⇔flatnessの一般のiffは含まれない。

内角に対する平坦性の判定を、任意の次元の生成内角包含に拡張し、それらから作る内 anodyne 射にも適用する。

:::

:::corollary "ha_B_3_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence.pullback_snd_isPrecompositionEquivalence_of_kanEquivalenceLifting")
*HA 系 B.3.15*　flat categorical fibration に沿う圏同値の引き戻し（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1499)）。対応表の状態：一部（stronger-hyp）。

*主張*　準圏の間の平坦な圏論的ファイブレーションに沿う引き戻しは、底上の圏論的同値を保つ。

KB-W2原文・型再照合：仮定：A,B,Cは準圏、A→Bは圏同値、p:C→Bは全単射な前合成同値を持ち上げるEquivalenceLiftingを満たす（Leanが強い：A,Bの準圏性と操作的RLPを明記）。結論：同じpullback射A×B C→Cは前合成同値、従って圏同値（指定された引き戻し比較の結論に一致）。任意simplicial set A,Bおよびflat categorical fibrationの定義だけからの全比較は含まれない。

任意の単体集合 $`A\to B` が底上の圏論的同値であるとき、全体の準圏とのファイバー積の比較も圏論的同値になる。

:::

