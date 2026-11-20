-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentEdges
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatSimplicial

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 3.0 The ∞-Category of ∞-Categories（章の導入）" =>
%%%
number := false
tag := "htt-3-0"
%%%

HTT 3.0 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

:::definition "htt_3_0_0_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCat_sHom, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity")
*HTT 定義 3.0.0.1*　小高次圏の単体圏と Cat∞ の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=162)）。対応表の状態：本体にある。

*主張*　小さい ∞ 圏を対象とし、関手 ∞ 圏 $`\operatorname{Fun}(\mathcal C,\mathcal D)` の最大 Kan 部分集合を写像対象とする単体的圏の整合的 nerve が $`\mathrm{Cat}_\infty` である。

仮定：同一宇宙の小準圏 C,D（HTT と一致）。結論：対象は準圏、豊穣 Hom は Fun(C,D) の最大 Kan core、その coherent nerve が Cat∞ となり一致。豊穣 Hom を同型類の集合に商していない。

関手はすべて残し、関手どうしの自然変換のうち可逆なものを写像空間の辺として採る。したがって対象を ∞ 圏として扱いながら、各写像対象は空間になる。

:::

:::proposition "htt_3_0_0_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCat_category, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCat_simplicialCategory, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity")
*HTT 注意 3.0.0.2*　関手の厳密な合成による豊穣圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=162)）。対応表の状態：本体にある。

*主張*　$`\mathrm{Cat}_\infty` の元になる単体的圏では、∞ 関手の合成は単体的写像の合成として厳密に結合的である。

仮定：小準圏と単体集合の射（HTT と一致）。結論：元の射の厳密な合成と結合律を持つ通常圏・豊穣圏から coherent nerve を取る構成で一致。合成のデータを別途 up-to-homotopy に置き換えない。

写像空間の高次データを付け加えても、合成そのものは内部 Hom で定まる。素朴な合成を使えることが、この模型で別々の整合データを指定せずに済む理由である。

:::

:::proposition "htt_3_0_0_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCat_sHom_kanComplex, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinity_quasicategory")
*HTT 注意 3.0.0.3*　Cat∞ の準圏性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=162)）。対応表の状態：本体にある。

*主張*　$`\mathrm{Cat}_\infty` は、元の単体的圏の写像対象が Kan 複体であることから ∞ 圏になる。

仮定：小準圏の単体圏 QCat（HTT と一致）。結論：全 Hom が Kan で CatInfinity が準圏となり一致。未供給の filler や ModelCategory の仮定はない。

構成で関手圏の core を使うため、写像対象には Kan 条件がある。これを整合的 nerve の内角充填条件に渡す。

:::

:::proposition "htt_3_0_0_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCat_sHom, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdge, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdge_recover")
*HTT 注意 3.0.0.4*　Cat∞ の対象と関手と可逆変換（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=163)）。対応表の状態：本体にある。

*主張*　$`\mathrm{Cat}_\infty` の対象は ∞ 圏、辺は関手であり、関手間の二射として記録されるのは可逆な自然変換である。

仮定：準圏の coherent nerve Cat∞（HTT と一致）。結論：対象が準圏、辺が元の関手、豊穣 Hom の高次単体が関手圏の Kan core に制限されるため可逆変換だけを保持するという説明は一致。辺の構成と回収も相互に逆である。

例えば自然変換が対象ごとの同値でないなら、それは関手 ∞ 圏の辺にはなっても、core の辺には入らない。非可逆な変換まで含めた議論には別の構成が必要になる。

:::

:::proposition "htt_3_0_0_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity")
*HTT 注意 3.0.0.5*　宇宙を変えた高次圏の圏の記法（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=163)）。対応表の状態：本体にある。

*主張*　小さい ∞ 圏だけを集める $`\mathrm{Cat}_\infty` と、大きい ∞ 圏も許す $`\widehat{\mathrm{Cat}}_\infty` を、それぞれの単体的圏の整合的 nerve として区別する。

仮定：小さい／大きいを指定する二つの宇宙（HTT と一致）。結論：CatInfinity.\{u\} は宇宙 u の全小準圏、同じ定義を大きい宇宙で適用したものが大きい準圏の圏となり一致。not necessarily small を無制限な全宇宙の集合と解釈しない。

関手 ∞ 圏が入る大きさを選ぶときは、対象の ∞ 圏の大きさと、それらをすべて集める圏の大きさの両方を見る。集合と小さい集合全部の圏との区別と同じ問題が生じる。

:::

