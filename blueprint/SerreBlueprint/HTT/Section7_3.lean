-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Maps.Proper.UniversallyClosed
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Sheaf
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.F1BNerveComparisonLimit
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.UniversalityOfColimits.FilteredColimitFiniteLimitPreservation
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.FunctorCategory

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 7.3 The Proper Base Change Theorem" =>
%%%
number := false
tag := "htt-7-3"
%%%

HTT 7.3 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 7.3.1 Proper Maps of ∞-Topoi

%%%
number := false
tag := "htt-7-3-1"
%%%

:::definition "htt_7_3_1_7" (lean := "LocallyCompactSpace, exists_compact_subset")
*HTT 定義 7.3.1.7*　非 Hausdorff 空間の局所コンパクト性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=771)）。対応表の状態：Mathlib にある。

*主張*　局所コンパクトとは、開集合 $`U` とその点 $`x` ごとに、$`U` 内に $`x` の開近傍を含むコンパクト集合があることをいう。

仮定：任意の位相空間 X、Hausdorff 仮定なし（HTT と一致）。結論：各点の任意の近傍内にコンパクト近傍があるという LocallyCompactSpace の条件と、開 U 内の x を内部に持つ K⊆U の表示は一致。

Hausdorff 性は仮定しないため、このコンパクト集合は閉である必要がない。また $`U` が任意なので、コンパクト近傍を一つ持つことより局所的な条件として述べる。

:::

:::proposition "htt_7_3_1_8" (lean := "LocallyCompactSpace, WeaklyLocallyCompactSpace.locallyCompactSpace")
*HTT 例 7.3.1.8*　Hausdorff 空間の局所コンパクト性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=771)）。対応表の状態：Mathlib にある。

*主張*　Hausdorff 空間では第7.3.1.7項の局所コンパクト性は通常の局所コンパクト性と一致する。

仮定：Hausdorff X（Lean の逆向きは R1Space まで弱い）。結論：各点に一つコンパクト近傍がある usual な WeaklyLocallyCompactSpace から、全近傍にコンパクト近傍を持つ LocallyCompactSpace となる。逆方向は同じ条件を全空間近傍へ適用するだけであり、一致。

Hausdorff 条件の下ではコンパクト集合は閉であり、コンパクト近傍を任意の開近傍の中に選べる形で通常の定義を使える。

:::

:::proposition "htt_7_3_1_9" (lean := "LocallyCompactSpace.of_hasBasis")
*HTT 例 7.3.1.9*　コンパクト開基底と局所コンパクト性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=771)）。対応表の状態：Mathlib にある。

*主張*　コンパクト開集合が開基を成す位相空間は局所コンパクトである。

仮定：各点の近傍基底がコンパクト集合からなる（原典の compact open basis は IsTopologicalBasis.mem\_nhds\_iff によりこの入力を満たし、一致）。結論：LocallyCompactSpace X（一致）。PrespectralSpace の既存 instance も同じ近傍基底を使い、Hausdorff 仮定を要しない。

点 $`x` と開近傍 $`U` が与えられたとき、$`x` を含む基底元を $`U` に含めて選ぶ。その基底元自身がコンパクトな近傍となる。

:::

:::proposition "htt_7_3_1_10" (lean := "ContinuousMap.curry, ContinuousMap.uncurry")
*HTT 注意 7.3.1.10*　局所コンパクト始域の指数法則（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=771)）。対応表の状態：一部（direction）。

*主張*　局所コンパクトな $`X` に対し、コンパクト開位相を持つ $`Y^X` は $`Z\mapsto\operatorname{Hom}(Z\times X,Y)` を表現する。

KB-W2原文・型再照合：仮定：局所コンパクト X と任意の Y,Z（HTT の十分性の方向と一致）。結論：compact-open C(X,Y) への Z の連続写像と Z×X→Y の currying/uncurrying は互いに逆で表現の十分性を与える。指数法則から局所コンパクト性を得る必要性は含まない。

点ごとに $`X` 上の写像を対応させる写像と、積上の写像との間のカリー化を連続性つきで行う。コンパクト開位相で局所コンパクト性が効くのは、この対応に必要な評価の連続性である。

:::

:::definition "htt_7_3_1_12" (lean := "T35Space, completelyRegularSpace_iff")
*HTT 定義 7.3.1.12*　点と閉集合を分離する完全正則性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=772)）。対応表の状態：Mathlib にある。

*主張*　各点が閉である位相空間が完全正則であるとは、閉集合とその外の点を、点で $`0`、閉集合上で $`1` の連続区間値関数で分離できることをいう。

仮定：任意の位相空間 X（HTT と一致）。結論：Mathlib T35Space は T0 と CompletelyRegularSpace で、後者は単位区間値連続関数により点と閉集合を分離する条件。既存の R1Space/T1Space instance で点は閉となり、原典の T1 を含む completely regular と一致。CompletelyRegularSpace 単独を対応とはしない。

点と閉集合を単に異なる開近傍に入れるのではなく、一つの連続関数で数値的に分離する。この版では点が閉であるという条件も定義に含む。

:::

:::proposition "htt_7_3_1_13" (lean := "t35Space_iff_isEmbedding_stoneCechUnit")
*HTT 注意 7.3.1.13*　完全正則空間のコンパクト化への埋込み（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=773)）。対応表の状態：Mathlib にある。

*主張*　位相空間が完全正則であることは、コンパクト Hausdorff 空間の部分空間として埋め込めることと同値である。

仮定：任意の X（HTT と一致）。結論：T35Space X iff StoneCech X への標準写像が embedding。StoneCech X は compact Hausdorff で、完全正則性はその部分空間へ継承されるため原典の存在による特徴づけと一致。

閉集合を点から分離する連続関数をまとめると、区間の積への埋め込みとしてこの性質を使える。逆向きはコンパクト Hausdorff 空間の分離を部分空間で読む。

:::

:::definition "htt_7_3_1_14" (lean := "isProperMap_iff_universally_closed")
*HTT 定義 7.3.1.14*　普遍閉写像としての固有写像（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=773)）。対応表の状態：Mathlib にある。

*主張*　任意の位相空間の間の写像が固有であるとは、あらゆる底変換後の写像が閉写像であることをいう。

仮定：任意の位相空間の連続写像 p:X→Y（HTT の map と一致）。結論：IsProperMap p iff 全ての Z に対する p×idZ が閉、すなわち普遍閉性による定義に一致。一般の base change は積からの pullback 部分空間への制限という同じ位相的定義で、Hausdorff を要求しない。

元の写像が閉であることは、底の恒等射に沿う場合にすぎない。底を替えても閉集合の像が閉であるという条件を使う。

:::

:::proposition "htt_7_3_1_15" (lean := "isProperMap_iff_isClosedMap_and_compact_fibers")
*HTT 注意 7.3.1.15*　固有写像の閉性とコンパクトなファイバー（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=773)）。対応表の状態：Mathlib にある。

*主張*　位相空間の間の写像は、閉写像であり各ファイバーがコンパクトであるとき、かつそのときに限り固有である。

仮定：位相空間間の連続写像 p、分離公理なし（HTT と一致）。結論：IsProperMap p iff IsClosedMap p∧∀y,IsCompact(p⁻¹\{y\})（一致）。

ファイバーは閉写像の底変換に関する問題を点の上で検査する。ここで要求するコンパクト性に Hausdorff 性は含めない。

:::

# 7.3.3 Products of ∞-Topoi

%%%
number := false
tag := "htt-7-3-3"
%%%

:::definition "htt_7_3_3_1" (lean := "TopCat.Presheaf, TopCat.Presheaf.IsSheaf, CategoryTheory.Presheaf.isSheaf_iff_isLimit, SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone_isLimit_iff")
*HTT 定義 7.3.3.1*　圏値の前層と被覆極限による層条件（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=781)）。対応表の状態：一部（special）。

*主張*　空間 $`X` 上の $`\mathcal C` 値前層は開集合の包含順序からの反変関手であり、各被覆篩で制限錐が極限となるものが充満部分圏 $`\operatorname{Shv}(X;\mathcal C)` をなす。

KB-W2原文・型再照合：仮定：位相空間 X と C=N(D)、D は通常圏（Lean が強い特殊形）。結論：Opens(X)op⥤D の ordinary sheaf condition は全 covering sieve の指定錐の極限性。nerveFunctorCategoryIso と nerveCone\_isLimit\_iff により同じ図式を N(D) に移すと原典の定義に一致。一般の準圏 C の higher sheaf full subcategory は含まない。

値域で反対圏を取ると、同じ条件は篩の右錐を余極限図式へ送ることになる。被覆の開集合の値に加え、包含に沿う制限写像も極限を構成するデータである。

:::

:::proposition "htt_7_3_3_2" (lean := "TopCat.Presheaf, TopCat.Presheaf.IsSheaf, CategoryTheory.Presheaf.isSheaf_iff_isLimit, SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone_isLimit_iff")
*HTT 注意 7.3.3.2*　圏値の層条件の極限による表示（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=782)）。対応表の状態：一部（special）。

*主張*　$`\mathcal C` 値前層が層である条件は、各被覆篩に対して $`F(U)\to\lim_{V\in S}F(V)` が同値になることである。

KB-W2原文・型再照合：仮定：位相空間 X、C=N(D) の通常圏値の前層（Lean が強い特殊形）。結論：CategoryTheory.Presheaf.isSheaf\_iff\_isLimit は各被覆 sieve における F(U) の指定極限錐の iff であり、native nerve の極限比較により原典のこの場合と一致。一般の準圏値の sheaf condition の比較はない。

右辺は集合の積ではなく、開集合とその間の包含を添字とする極限である。したがって各開集合の局所切断を選ぶだけでなく、その制限どうしの整合性も入る。

:::

# 7.3.4 Sheaves on Locally Compact Spaces

%%%
number := false
tag := "htt-7-3-4"
%%%

:::proposition "htt_7_3_4_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.UniversalityOfColimits.smallSpaceColimitFunctor, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.UniversalityOfColimits.smallSpaceFilteredColimit_map_isLimit_finite")
*HTT 例 7.3.4.4*　空間の filtered 余極限の左完全性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=787)）。対応表の状態：一部（component）。

*主張*　空間の ∞ 圏とその $`n`-切断空間の充満部分圏（$`n\ge-2`）では、filtered 余極限が有限極限と可換する。

KB-W2原文・型再照合：仮定：小さい filtered 準圏 I と任意の有限単体集合形状 K（HTT の Space 部分と一致）。結論：SpaceInfinity の実際の余極限関手が全ての指定された K 形状の極限錐を保つ。原典の最初の Space の主張は一致するが、τ≤nSpace の truncation の全次数の同じ閉性・保存の型は含まない。

空間での可換性を切断空間へ制限できるのは、切断空間の充満部分圏が filtered 余極限と極限の両方で閉じているためである。

:::

