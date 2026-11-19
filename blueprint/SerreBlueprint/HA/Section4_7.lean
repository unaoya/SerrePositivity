import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.DoldKan.Equivalence
import Mathlib.CategoryTheory.Monad.Adjunction
import SerrePositivity.CategoryTheory.Simplex.Prefix
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 4.7 Monads and the Barr-Beck Theorem" =>
%%%
number := false
tag := "ha-4-7"
%%%

HA 4.7 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

:::proposition "ha_4_7_0_4" (lean := "CategoryTheory.Adjunction.toMonad")
*HA 注意 4.7.0.4*　Monads and the Barr-Beck Theorem (p. 657)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=657)）。対応表の状態：一部（component）。

*主張*　モナド性の定理で得るモナドは、基礎自己関手として $`GF` であり、右随伴 $`G` の自己準同型対象の普遍性によって代数構造も決まる。

原文が明示的に述べるclassical settingの構成(a)では、同じ通常圏の随伴F⊣GからAdjunction.toMonadがG∘Fを台とするモナドを直接構成する。この通常圏に関する明示的な成分に限り、∞圏の高次整合性と一意性は含まない。

自己関手 $`U` から $`T` への射は $`UG\to G` という作用に対応する。この普遍性から $`T` の代数構造と $`G` への作用が得られ、比較関手を構成できる。

:::

# 4.7.2 Split Simplicial Objects

%%%
number := false
tag := "ha-4-7-2"
%%%

:::proposition "ha_4_7_2_12" (lean := "CategoryTheory.Abelian.DoldKan.equivalence")
*HA 例 4.7.2.12*　Split Simplicial Objects (p. 682)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=682)）。対応表の状態：一部（component）。

*主張*　アーベル圏の単体的対象の分裂増大構造は、正規化鎖複体の増大と、それを分裂完全にする収縮ホモトピーに対応する。

原文冒頭で明示する同じアーベル圏CについてDoldKan.equivalenceは単体対象と非負鎖複体の圏同値を直接返す。後半の増大・shift・Δ−∞での分裂と鎖縮約の全対応は含まない。

増大は $`d_0:C_0\to C_{-1}` で $`d_0d_1=0` を満たす。分裂を表す写像族は $`d_0h_0=\mathrm{id}` と $`d_{n+1}h_{n+1}+h_nd_n=\mathrm{id}_{C_n}` を満たす。

:::

:::proposition "ha_4_7_2_14" (lean := "SerrePositivity.SimplexPrefix.functor")
*HA 注意 4.7.2.14*　Split Simplicial Objects (p. 683)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=683)）。対応表の状態：一部（component）。

*主張*　増大単体圏での平行移動 $`T` は、増大を忘れた単体的対象だけから作れる。

通常の単体圏上のPrefix.functorは原文のρの非負次数部分\[n\]↦\[0\]⋆\[n\]を直接構成する。増大単体圏からの因子化と∞関手圏へのTの構成は含まない。

定義に使う添字の関手 $`\rho` の値は非増大の単体圏に入る。このため出力が増大単体的対象でも、入力には非増大の図式で足りる。

:::

# 4.7.4 BiCartesian Fibrations

%%%
number := false
tag := "ha-4-7-4"
%%%

:::definition "ha_4_7_4_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration")
*HA 定義 4.7.4.1*　BiCartesian Fibrations (p. 694)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=694)）。対応表の状態：一部（component）。

*主張*　双デカルト・ファイブレーションとは、デカルトかつ余デカルトな単体集合の射である。

原文冒頭のbiCartesian fibrationの定義は、同じq:X→SについてCartesianFibration qとCocartesianFibration qの両方を要求することに一致する。後続のmarked SSet上のCartesian model structureの説明まで含めない。

二方向の移送が使える。これに続き、底上の印付き単体集合のデカルト構造と余デカルト構造を参照して、双方を扱うモデル構造を定める。

:::

