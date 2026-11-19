import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Elements
import Mathlib.Order.Setoid.Basic
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FiniteLimitsColimits

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 6.3 The Chain Rule" =>
%%%
number := false
tag := "ha-6-3"
%%%

HA 6.3 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 6.3.2 Composition of Correspondences

%%%
number := false
tag := "ha-6-3-2"
%%%

:::definition "ha_6_3_2_5" (lean := "CategoryTheory.Functor.Elements, CategoryTheory.Functor.Elements.Hom")
*HA 記法 6.3.2.5*　両端固定の単体圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1152)）。対応表の状態：一部（component）。

*主張*　単体集合 $`S` の単体の圏では対象は $`\Delta^m\to S`、射は $`S` 上で可換な単調写像である。

KB-W2型再照合：仮定：任意の単体集合 S を前層として与える（HA と一致）。結論：S.Elements の反対圏の対象は次数と単体、射は∆m→∆nと制限の可換条件である（冒頭の単体圏∆Sの定義に一致する部分）。指定両端s,t・正の次数・端点保存射に制限する∆S\^\{s,t\}の専用構成は含まれない。

端点 $`s,t` を指定した部分圏では、正の次元の単体で始点と終点がそれぞれ $`s,t` のものを取り、射でも双方の端点を保存させる。

:::

:::definition "ha_6_3_2_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits")
*HA 定義 6.3.2.12*　Composition of Correspondences (p. 1155)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1155)）。対応表の状態：一部（component）。

*主張*　$`\Delta^2` 上のオペラッド族が thin であるとは、共表現可能で終頂点のファイバーが有限極限を持ち、すべての正の項数で分割の鎖から作る演算の図式が極限図式になることである。

原文が指定する同じO2の有限極限という成分はHasFiniteLimits O2そのもの。spray・Part(S)上の指定の極限図式は構成されていない。

$`n` 個の入力の同値関係の鎖を通る演算を始点から終点への関手として比較する。空の鎖に当たる直接の演算を錐の頂点とし、非空鎖が与える図式の極限となることを、$`\operatorname{Fun}(O_0^n,O_2)` で要求する。

:::

# 6.3.3 Derivatives of the Identity Functor

%%%
number := false
tag := "ha-6-3-3"
%%%

:::definition "ha_6_3_3_1" (lean := "Setoid.le_def, Setoid.completeLattice, Setoid.top_def, Setoid.bot_def")
*HA 定義 6.3.3.1*　同値関係の poset と両端の除去（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1157)）。対応表の状態：一部（component）。

*主張*　非空有限集合の同値関係を包含で順序付け、最小元を離散関係、最大元を全ての対を同値とする関係とする。

KB-W2型再照合：仮定：有限非空Iを型として与える（HAと一致）。結論：同値関係の型Setoid Iは関係の含意を順序とし、全関係をtop・等号をbottomとする（Equiv(I)と二端の定義に一致する部分）。両端を除く三つの部分posetの専用の型は含まれない。

上付き $`+` は最大元を除いた部分、$`-` は最小元を除いた部分、$`\pm` はその交わりである。この区別で非自明な分割の図式を指定する。

:::

