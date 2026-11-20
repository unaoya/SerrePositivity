-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.SimplexCategory.SemiSimplexCategory
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import SerrePositivity.InfinityCategories.HTT.Section5_2_5.Adjunction
import SerrePositivity.InfinityCategories.HTT.Section6_1_2.OppositeIso
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.FunctorCategory

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 6.5 Homotopy Theory in an ∞-Topos" =>
%%%
number := false
tag := "htt-6-5"
%%%

HTT 6.5 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 6.5.3 Hypercoverings

%%%
number := false
tag := "htt-6-5-3"
%%%

:::definition "htt_6_5_3_1" (lean := "CategoryTheory.SimplicialObject.truncation, CategoryTheory.SimplicialObject.cosk, CategoryTheory.SimplicialObject.coskAdj, SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso, SerrePositivity.InfinityCategories.HTT.Section5_2_5.nerveAdjunctionOfAdjunction, SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveOppositeIso")
*HTT 記法 6.5.3.1*　切断制限と余骨格の随伴（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=693)）。対応表の状態：一部（special）。

*主張*　可提示 ∞ 圏の単体的対象の $`n`-余骨格 $`\operatorname{cosk}_n` は、次元 $`0,\ldots,n` への制限と、その包含に沿う右 Kan 拡張の合成である。

KB-W2原文・型再照合：仮定：presentable X を通常圏 D の nerve に特殊化し、対応する ordinary right Kan extensions が存在（Lean が強い。D と Hom は nerve 比較と同じ宇宙に配置）。結論：Δ≤n への制限、その right Kan extension の右随伴、両者の合成としての coskeleton は一致。関手圏・反対圏の nerve 同型と随伴の nerve 比較を併用する。任意の準圏 X の coskeleton 全体は含まない。

高次部分を単に削った対象は小さい添字上の図式である。余骨格は右 Kan 拡張でその図式を再び全次数へ戻し、低次と両立する高次項を普遍的に決める。

:::

:::definition "htt_6_5_3_6" (lean := "SemiSimplexCategory, SemiSimplexCategory.Hom, SemiSimplexCategory.toSimplexCategory")
*HTT 記法 6.5.3.6*　半単体圏と半単体対象の記法（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=694)）。対応表の状態：一部（component）。

*主張*　半単体的対象は、有限非空全順序集合と単調単射のなす圏の反対圏の nerve からの図式である。

KB-W2原文・型再照合：仮定：非空有限全順序集合と単射な単調写像（HTT と一致）。結論：Δs と Δ への inclusion の定義は一致。Mathlib の射は order embedding であり有限全順序集合では単射単調写像と同じ。任意準圏 X への N(Δs)op 図式を束縛した semisimplicial object の型までは定義しない。

添字が単射に限られると、反対圏で顔作用は残り、退化作用を与える必要がない。この規約では空順序集合に当たる増大項は含まれない。

:::

