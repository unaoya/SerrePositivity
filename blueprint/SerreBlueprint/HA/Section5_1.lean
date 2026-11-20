-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 5.1 Definitions and Basic Properties" =>
%%%
number := false
tag := "ha-5-1"
%%%

HA 5.1 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 5.1.2 The Additivity Theorem

%%%
number := false
tag := "ha-5-1-2"
%%%

:::proposition "ha_5_1_2_4" (lean := "CategoryTheory.BraidedCategory")
*HA 例 5.1.2.4*　E₂ と通常の braided monoidal 圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=769)）。対応表の状態：一部（component）。

*主張*　通常圏の nerve の $`E_k` モノイダル構造は、$`k=1` でモノイダル、$`k=2` で組み紐モノイダル、$`k\ge3` で対称モノイダル構造に対応する。

KB-W2型再照合：仮定：通常のモノイダル圏 C（HA と一致）。結論：自然な braiding と二つの六角式による braided category を定義する（原典が明示する通常圏の構造の部分に一致）。N(C) の E₂ モノイダル構造との同値と Eckmann–Hilton の比較は含まれない。

$`E_2` 構造を二重の結合的構造として扱うと、二つの積が共通の単位を持つ。交換の自然同型で両方の積を同定し、残る交換の同型を組み紐として読む。その整合性は組み紐の二つの六角形条件を与える。

:::

:::definition "ha_5_1_2_14" (lean := "CategoryTheory.TransportEnrichment, CategoryTheory.TransportEnrichment.eComp_eq, TopCat.toSSet")
*HA 記法 5.1.2.14*　位相的豊穣図式への Sing の適用（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=775)）。対応表の状態：一部（component）。

*主張*　位相圏 $`C` から、対象を固定して各写像空間の特異複体を取る単体的圏 $`\operatorname{Sing}(C)` を作れる。

KB-W2型再照合：仮定：TopCat 上の enriched category C と Sing の実モノイダル構造（HA と一致する位相的圏の場合。Sing の instance は Mathlib の SimplicialSet.TopAdj で構成済み）。結論：全 Hom に Sing を施し、同じ対象を持つ SSet 豊穣圏とその合成を与える（冒頭の Sing(C) の部分に一致）。little cubes 由来の W・T・U と、指定 functor への Sing の比較は含まれない。

位相関手の値にも特異複体を取る。小立方体の比較では有限基点付き集合で活性となる射の成分を選び、同じ操作で活性射の空間を記述する反変関手を単体化する。

:::

