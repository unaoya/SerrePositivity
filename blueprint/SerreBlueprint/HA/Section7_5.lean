import Verso
import VersoManual
import VersoBlueprint
import Mathlib.GroupTheory.OreLocalization.OreSet
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.OreLocalization.OreSet
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Unramified.Basic

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 7.5 Étale Morphisms" =>
%%%
number := false
tag := "ha-7-5"
%%%

HA 7.5 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

:::definition "ha_7_5_0_1" (lean := "Algebra.Etale, Algebra.Smooth.flat")
*HA 定義 7.5.0.1*　Étale Morphisms (p. 1373)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1373)）。対応表の状態：一部（component）。

*主張*　可換環の射がエタールであるとは、有限表示かつ平坦で、乗法 $`B\otimes_A B\to B` が環の直積分解の一方への射影となることである。

KB-W2原文・型再照合：仮定：通常可換環 A→B と Algebra.Etale A B（Lean が強い：形式的 étale と有限表示の定義を仮定する）。結論：B の有限表示性と A 加群としての flat 性を得る（HA の三条件のうち (1)・(2) に一致）。乗法射が積の第一射影となることまで含めた定義との双方向の同値はここでは得ていない。

最後の条件では他方の環 $`R` を選んで $`B\otimes_A B\simeq B\times R` とする。この条件はエタール射の対角の開閉性を環で表す。

:::

:::proposition "ha_7_5_0_2" (lean := "IsLocalization.away_fst")
*HA 注意 7.5.0.2*　Étale Morphisms (p. 1373)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1373)）。対応表の状態：一部（special）。

*主張*　乗法が直積の一方への射影であることは、ある冪等元 $`e\in B\otimes_A B` の反転で乗法が同型になることと同値である。

KB-W2原文・型再照合：仮定：通常可換環の直積 B×R と第一射影（Lean が強い：原典の積表示を既に標準形にした場合）。結論：第一射影が冪等元 (1,0) での局所化となる（原典の積表示から局所化を得る方向のこの場合に一致）。任意の乗法射に対する両条件の同値は含まれない。

直積表示があれば $`e` は $`(1,0)` に対応する。逆向きには $`1-e` を反転して残りの因子を得る。

:::

:::proposition "ha_7_5_0_3" (lean := "Algebra.FormallyUnramified")
*HA 注意 7.5.0.3*　Étale Morphisms (p. 1373)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1373)）。対応表の状態：一部（stronger-hyp）。

*主張*　エタール環準同型 $`A\to B` では $`\Omega_{B/A}=0` であり、任意の $`B` 加群 $`M` に対して平方零拡大 $`B\oplus M\to B` の $`A` 代数としての切断は一意である。

同じ通常可換環A→Bについて、Algebra.FormallyUnramifiedはΩB/Aの零性を直接持つ。Mathlibの形式的不分岐条件を追加してその成分を得る場合に限定する。HAの三条件によるétale定義から形式的不分岐性を導く比較と、原文の切断の主張は含まない。

二つの切断が定める $`B\otimes_A B\to B\oplus M` は、対角を切り出す冪等元を可逆にするので、乗法を経由する。原典の括弧の $`A`-modules は、微分の普遍性とこの証明に従い $`A` 代数として読む。

:::

# 7.5.1 Étale Morphisms of E\_1-Rings

%%%
number := false
tag := "ha-7-5-1"
%%%

:::definition "ha_7_5_1_12" (lean := "OreLocalization.OreSet, OreLocalization.nonempty_oreSet_iff")
*HA 定義 7.5.1.12*　Étale Morphisms of \$E\_\{1\}\$-Rings (p. 1377)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1377)）。対応表の状態：Mathlib にある。

*主張*　$`E_1` 環の $`\pi_0` の元 $`x` が準中心的であるとは、その非負整数冪の集合が左 Ore 条件を満たすことである。

仮定：通常の結合環 R と元 x（HA の π₀ R と一致）。結論：S を x の冪の部分モノイドとすると、選択を含む OreSet の存在が左 Ore の二条件と同値となる（HA の quasi-central の定義が依存する条件と一致。零消去条件は差を取ることで通常の右消去条件となる）。

分母は $`1,x,x^2,\ldots` であり、共通倍と消滅の条件は $`\pi_0R` の積について検査する。

:::

