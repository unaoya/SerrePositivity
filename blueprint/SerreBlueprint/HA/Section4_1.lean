import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.Quasicategory.Nerve
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.SemiSimplexCategory
import Mathlib.CategoryTheory.Monoidal.Arrow
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon
import Mathlib.CategoryTheory.Monoidal.Internal.Types.Basic
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.Monoidal.PushoutProduct
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Topology.Homotopy.HSpaces
import SerrePositivity.DifferentialGraded.Algebras.ModelCategory
import SerrePositivity.HomotopicalAlgebra.Monoidal.CofibrantTensor
import SerrePositivity.HomotopicalAlgebra.Monoidal.ModelCategory
import SerrePositivity.HomotopicalAlgebra.Monoidal.MonoidAxiom
import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelHammockLocalization
import SerrePositivity.InfinityCategories.HA.Section4_1_2.BarVertexInclusion
import SerrePositivity.InfinityCategories.HA.Section4_1_4.EmptyRelativeFunctorHom
import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollageInclusions
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Cube
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.BaseChange
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.MarkedCocartesianFunctorInvertibleDetection
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.MarkedCocartesianFunctorSpace
import SerrePositivity.KST.Comparison.BarSegal

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 4.1 Associative Algebras" =>
%%%
number := false
tag := "ha-4-1"
%%%

HA 4.1 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

:::proposition "ha_4_1_0_1" (lean := "IsTopologicalGroup.toHSpace")
*HA 例 4.1.0.1*　Associative Algebras (p. 451)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=451)）。対応表の状態：一部（component）。

*主張*　位相モノイドは、単位を基点とし積を乗法とするホモトピー結合的 H 空間を与える。

KB-W2型再照合：仮定：単位付き乗法と連続な乗法（Lean は結合律を仮定しない。HA の位相モノイドはこれを満たす）。結論：元の乗法と単位 1 から H-space を得て、単位ホモトピーには厳密な単位律を使う（この成分は一致）。H-space のホモトピー結合性は型に含まれない。

単位と結合の法則は位相モノイドで等式として成り立つため、H 空間の法則を与えるホモトピーに定値のものを選べる。

:::

:::proposition "ha_4_1_0_2"
*HA 例 4.1.0.2*　Associative Algebras (p. 452)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=452)）。対応表の状態：Mathlib にある。

*主張*　点付き位相空間の基点付きループ空間は、定値ループを単位とし連結を積とする H 空間である。

仮定：位相空間 X と基点 x（HA と一致）。結論：ループ空間 Path x x が定値ループを単位、区間を二等分した Path.trans を積とする H-space となる（一致）。

前半で第一のループ、後半で第二のループを走る。連結する区間の取り方を連続的に変えると、単位則や結合則に必要なホモトピーが得られる。

宣言：`Path.instHSpace`

:::

# 4.1.1 The Associative ∞-Operad

%%%
number := false
tag := "ha-4-1-1"
%%%

:::proposition "ha_4_1_1_2" (lean := "CategoryTheory.Mon")
*HA 注意 4.1.1.2*　The Associative ∞-Operad (p. 455)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=455)）。対応表の状態：一部（component）。

*主張*　対称モノイダル圏の結合代数は、色付きオペラッド $`\mathrm{Assoc}` からその圏へのオペラッドの射で表される。

KB-W2型再照合：仮定：通常のモノイダル圏（HA の対称モノイダル圏を含む）。結論：単位・乗法・結合律を持つ通常の結合代数を内部モノイド Mon として与える（結論の代数側の構造に一致）。Assoc からの colored operad 写像との対応は型に含まれない。

一つの色の像が代数の基礎対象となり、空列から単位、二項の標準順序から乗法が得られる。任意の有限全順序集合での演算は、その順に乗法を反復して復元できる。

:::

:::definition "ha_4_1_1_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration") (uses := "ha_2_1_2_10, htt_1_1_2_4, htt_2_4_2_1")
*HA 定義 4.1.1.10*　The Associative ∞-Operad (p. 457)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=457)）。対応表の状態：本体にある。

*主張*　モノイダル ∞ 圏とは、結合オペラッド $`\mathrm{Assoc}^\otimes` 上の余デカルト・ファイブレーションである ∞ オペラッドである。

既に与えられたC⊗→Assoc⊗という∞-operad mapにCocartesianFibration qを適用すると、原文が追加しているcoCartesian fibration条件とそのまま一致する。通常圏のmonoidal/action構造による代用を取りやめ、同じ単体写像の条件を根拠にする。

結合オペラッドの演算に沿う余デカルト移送が、順序を持つテンソル積とその高次の整合性を与える。

:::

:::proposition "ha_4_1_1_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianFibration_pullback_snd")
*HA 命題 4.1.1.14*　The Associative ∞-Operad (p. 457)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=457)）。対応表の状態：一部（direction）。

*主張*　$`N(\mathrm{Fin}_*)` 上の ∞ オペラッドが対称モノイダルであることは、$`\mathrm{Assoc}^\otimes` に沿う引き戻しがモノイダルであることと同値である。

KB-W2型再照合：仮定：単体集合上の余デカルトファイブレーションと底変換写像（HA の p が対称モノイダルである方向の余デカルト性に一致）。結論：引き戻し写像は余デカルトファイブレーションとなる（Assoc⊗ への底変換に適用した片方向に一致）。逆向きの二単体による検出は含まれない。

結合オペラッドへの制限は対称モノイダル構造からモノイダル構造を得る。逆向きの判定では有限基点付き集合の演算に必要な余デカルト持ち上げを、この引き戻しで検査できる。

:::

# 4.1.2 Monoid Objects of ∞-Categories

%%%
number := false
tag := "ha-4-1-2"
%%%

:::proposition "ha_4_1_2_1" (lean := "CategoryTheory.yonedaMonFullyFaithful, CategoryTheory.yonedaMonObjRepresentableBy, CategoryTheory.yonedaMonObjIsoOfRepresentableBy")
*HA 注意 4.1.2.1*　Monoid Objects of ∞-Categories (p. 460)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=460)）。対応表の状態：Mathlib にある。

*主張*　有限積を持つ圏のモノイド対象は、基礎の集合値関手が表現可能な反変モノイド値関手に対応する。

仮定：有限積を直積モノイダル構造として持つ通常圏 C（HA と一致）。結論：内部モノイドをモノイド値の前層へ充満忠実に送り、基礎集合値前層が表現可能であることとその像に入ることを示す（一致）。

モノイド対象 $`M` は各 $`X` に $`\operatorname{Hom}(X,M)` のモノイドを対応させる。逆に、米田の補題で自然な単位と積を $`M` 上の射に戻す。

:::

:::proposition "ha_4_1_2_2" (lean := "monTypeEquivalenceMon")
*HA 例 4.1.2.2*　Monoid Objects of ∞-Categories (p. 460)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=460)）。対応表の状態：Mathlib にある。

*主張*　集合の圏のモノイド対象は、結合的な二項演算と左右の単位元を持つ通常のモノイドである。

仮定：集合の通常圏 Type に直積モノイダル構造を取る（HA と一致）。結論：内部モノイドの圏は単位と結合的積を持つ通常のモノイドの圏と同値（一致）。

単位射は一点集合から単位元を選ぶ。その元は左右の単位則で一意に定まる。

:::

:::proposition "ha_4_1_2_3" (lean := "MonCat.toCat, MonCat.toCat_full, MonCat.toCat_faithful, CategoryTheory.SingleObj.toEnd")
*HA 注意 4.1.2.3*　Monoid Objects of ∞-Categories (p. 461)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=461)）。対応表の状態：一部（component）。

*主張*　モノイドの圏は、一つの指定対象だけを持つ通常圏の圏と同値である。

KB-W2型再照合：仮定：通常のモノイド（HA と一致）。結論：単一対象の圏に送り、指定対象の自己準同型モノイドを元のモノイドと同定し、通常圏への関手が充満忠実となる（この成分に一致）。指定された一対象を持つ圏全体への本質的全射性を表す型は含まれない。

対象を一つ取り、その自己射をモノイドの元、合成を乗法、恒等射を単位にする。関手はちょうどモノイド準同型を与える。

:::

:::definition "ha_4_1_2_4" (lean := "SerrePositivity.KST.Comparison.constantMonoidBarIso, SerrePositivity.KST.Comparison.monoidWordEquiv")
*HA 構成 4.1.2.4*　The Milnor Construction（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=461)）。対応表の状態：一部（component）。

*主張*　モノイドの分類単体集合は対応する一対象圏の nerve であり、各次数の Segal 写像が全単射となる単体集合をちょうど与える。

KB-W2型再照合：仮定：通常のモノイド T を定値単体モノイドとする（HA の通常モノイドの場合）。結論：bar が SingleObj T の nerve に同型で、その n 単体と n 個の T の元の列が全単射になる（分類空間の構成と Segal 写像の成分に一致）。任意の単体集合からのモノイド再構成は含まれない。

次数 $`n` には $`M^n` が現れ、内側の面が積、退化が単位を使う。この構成は充満忠実で、元の積を $`d_1:X_2\to X_1` から復元できる。Kan となるのはモノイドが群の場合である。

:::

:::definition "ha_4_1_2_12" (lean := "SemiSimplexCategory.toSimplexCategory")
*HA 定義 4.1.2.12*　Monoid Objects of ∞-Categories (p. 464)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=464)）。対応表の状態：一部（component）。

*主張*　非単位的モノイド対象は、単射だけを持つ単体圏の反対からの図式で、各段が隣接する辺への制限によってその積を表すものである。

KB-W2型再照合：仮定：有限順序集合 \[n\] と単射の順序写像（HA の ∆s と一致）。結論：これらからなる半単体圏と単体圏への包含を与える（添字圏の成分に一致）。非単位的モノイドの Segal 条件と充満部分準圏は含まれない。

半単体的図式には面写像があり、退化写像はデータに含まれない。辺を並べる Segal の条件を満たす図式の充満部分圏を $`\operatorname{Mon}^{\mathrm{nu}}(C)` とする。原典の途中に現れる共変の表記は、最初の半単体的対象の定義と末尾の関手圏に合わせて反変と読む。

:::

# 4.1.3 Planar ∞-Operads and A\_∞-Algebras

%%%
number := false
tag := "ha-4-1-3"
%%%

:::definition "ha_4_1_3_1" (lean := "SimplexCategory.subinterval")
*HA 定義 4.1.3.1*　Planar ∞-Operads and \$A\_\{\\infty\}\$-Algebras (p. 465)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=465)）。対応表の状態：一部（component）。

*主張*　単体圏の射が慣性であるとは、始域を終域内の連続する区間に同型に写すことである。

KB-W2型再照合：仮定：有限順序集合 \[n\] の中の連続した区間 \[j,j+l\]（HA の凸部分集合の具体的条件と一致）。結論：\[l\] をその区間へ送る単体圏の射を構成する（inert 射の具体的な構成に一致）。Cut による判定と任意の射についての同値は含まれない。

別の表現では、この射を $`\operatorname{Cut}` で反変に移したとき、結合オペラッド内の慣性射になることをいう。

:::

:::definition "ha_4_1_3_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration")
*HA 定義 4.1.3.6*　Planar ∞-Operads and \$A\_\{\\infty\}\$-Algebras (p. 466)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=466)）。対応表の状態：本体にある。

*主張*　$`A_\infty` モノイダル ∞ 圏は、$`N(\Delta^{\mathrm{op}})` 上の平面 ∞ オペラッドで、射影が余デカルト・ファイブレーションであるものである。

既に与えられたplanar ∞-operad qにCocartesianFibration qを適用すると、原文が追加しているcoCartesian fibration条件とそのまま一致する。通常圏のmonoidal/action構造による代用を取りやめ、同じ単体写像の条件を根拠にする。

平面オペラッドの慣性辺の移送に加え、単体圏の反対の任意の辺に沿う余デカルト移送を持つことが条件になる。

:::

:::definition "ha_4_1_3_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate_vertex")
*HA 定義 4.1.3.9*　Planar ∞-Operads and \$A\_\{\\infty\}\$-Algebras (p. 466)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=466)）。対応表の状態：一部（component）。

*主張*　平面 ∞ オペラッドの慣性辺は、底で慣性である相対余デカルト辺であり、平面 ∞ オペラッドの射は底上でこれらの辺を保つ写像である。

KB-W2型再照合：仮定：同じ底の上の関手と始域の指定辺（Lean では planar 条件は不要で、HA の inert 辺の集合を明示する）。結論：指定辺の像が余デカルトであることを射の条件として表す（底が同じなので inert 保存の条件に一致）。始域の inert 集合を Cut の底から定める構成は含まれない。

射は $`N(\Delta^{\mathrm{op}})` への二つの射影と可換である。底での慣性の判定には単体圏の連続区間を使う。

:::

:::proposition "ha_4_1_3_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianFibration_pullback_snd, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_pullback")
*HA 注意 4.1.3.11*　Planar ∞-Operads and \$A\_\{\\infty\}\$-Algebras (p. 467)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=467)）。対応表の状態：一部（direction）。

*主張*　結合オペラッドへのオペラッド・ファイブレーションを $`N(\Delta^{\mathrm{op}})` に引き戻すと平面 ∞ オペラッドになり、慣性辺は元のオペラッドへの像で判定できる。

KB-W2型再照合：仮定：底変換の単体写像（Lean では planar 条件は不要。HA の Cut を底変換に取る）。結論：元の射影が余デカルトなら引き戻しも余デカルトで、元で余デカルトな辺の引き戻しも余デカルトとなる（この二つの含意に一致）。planar 条件と逆向きの検出は型に含まれない。

この比較は余デカルト・ファイブレーションであるための必要十分条件も与える。従って元の射がその条件を満たすとき、引き戻しは $`A_\infty` モノイダル圏となる。

:::

:::definition "ha_4_1_3_16" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate_vertex")
*HA 定義 4.1.3.16*　Planar ∞-Operads and \$A\_\{\\infty\}\$-Algebras (p. 468)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=468)）。対応表の状態：一部（component）。

*主張*　平面 ∞ オペラッドの $`A_\infty` 代数対象は、$`N(\Delta^{\mathrm{op}})` 上の射影の慣性辺保存切断である。

KB-W2型再照合：仮定：底への写像 q とその底の指定辺（Lean では planar 条件は不要で、N(∆ᵒᵖ) の inert 辺を明示する）。結論：底上で指定辺を余デカルト辺に送る section の充満部分複体を構成する（A∞ 代数の section 条件に一致）。planar operad と inert 辺の組は型に含まれない。

切断全体の関手圏から、この条件を満たす対象で張る充満部分圏を取ると $`\operatorname{Alg}_{A_\infty}(O)` となる。

:::

:::definition "ha_4_1_3_20" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace, SemiSimplexCategory.toSimplexCategory")
*HA 定義 4.1.3.20*　Planar ∞-Operads and \$A\_\{\\infty\}\$-Algebras (p. 468)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=468)）。対応表の状態：一部（component）。

*主張*　非単位的 $`A_\infty` 代数対象は、単射だけを取った単体圏の反対の nerve から平面 ∞ オペラッドへの慣性辺保存射である。

KB-W2型再照合：仮定：底への射影 q、半単体圏の神経からの包含とその指定辺（Lean では planar 条件は不要で、HA の inert 辺を明示する）。結論：その包含の上で指定辺を余デカルト辺へ送る相対関手の充満部分複体を与える（非単位的 A∞ 代数の関手空間の成分に一致）。planar operad と inert 辺の組は型に含まれない。

この定義は底 $`N(\Delta^{\mathrm{op}})` 上で行う。原典末尾の $`E_\infty` という表記は、冒頭の定義と添字に従って $`A_\infty` と読む。

:::

# 4.1.4 Nonunital A\_n-Algebras and Nonunital A\_n-Monoids

%%%
number := false
tag := "ha-4-1-4"
%%%

:::definition "ha_4_1_4_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace")
*HA 定義 4.1.4.2*　Nonunital \$A\_\{n\}\$-Algebras and Nonunital \$A\_\{n\}\$-Monoids (p. 469)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=469)）。対応表の状態：一部（component）。

*主張*　非単位的 $`A_n` 代数は、$`1\le m\le n` の $`[m]` に制限した単射の単体圏の反対からの底上の関手で、慣性辺を余デカルト辺に移すものをいう。

KB-W2型再照合：仮定：底の上の写像 q と Tⁿᵒᵖ の包含、その指定辺（Lean では planar 条件は不要で、包含と inert 辺を明示する）。結論：底の上で inert 辺を余デカルト辺に送る関手の充満部分複体を与える（HA の関手空間の成分に一致）。Tⁿ とその inert 辺の定義は含まれない。

有限段のデータだけを指定する。底での連続区間 $`[m']\hookrightarrow[m]` に対応する $`A([m])\to A([m'])` にこの保存条件を課す。

:::

:::proposition "ha_4_1_4_4" (lean := "SerrePositivity.InfinityCategories.HA.Section4_1_4.markedCocartesianFunctorSpace_isTerminal_of_isInitial")
*HA 例 4.1.4.4*　Nonunital A0 -Algebras（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=469)）。対応表の状態：本体にある。

*主張*　任意の平面 ∞ オペラッドで、非単位的 $`A_0` 代数の ∞ 圏は $`\Delta^0` と同型である。

仮定：相対関手の始域が初対象（T⁰ が空という HA の仮定と一致し、q やマークは任意）。結論：マークを保つ相対関手空間が単体集合の終対象、すなわち Δ0 と同型となる（一致）。

$`n=0` の場合に指定する段の圏 $`T^0` が空なので、相対関手のデータが一意に決まる。

:::

:::definition "ha_4_1_4_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorEvaluate")
*HA 記法 4.1.4.5*　Nonunital \$A\_\{n\}\$-Algebras and Nonunital \$A\_\{n\}\$-Monoids (p. 470)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=470)）。対応表の状態：一部（component）。

*主張*　$`n\ge1` の非単位的 $`A_n` 代数の忘却関手は、$`[1]` で評価して基礎 ∞ 圏の対象を取る関手である。

KB-W2型再照合：仮定：マークを保つ相対関手空間と添字の指定頂点（Lean では Tⁿ の \[1\] を頂点として明示する）。結論：その頂点の底ファイバーへの評価を与える（忘却写像の成分に一致）。有限次数の非単位的 Aₙ の型は含まれない。

平面オペラッドの $`[1]` 上のファイバーが基礎の圏である。記号上は代数とその基礎対象に同じ文字を使うことがある。

:::

# 4.1.5 From A\_n-Algebras to A\_n+1-Algebras

%%%
number := false
tag := "ha-4-1-5"
%%%

:::definition "ha_4_1_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeSplitIso")
*HA 記法 4.1.5.1*　From \$A\_\{n\}\$-Algebras to \$A\_\{n+1\}\$-Algebras (p. 474)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=474)）。対応表の状態：一部（component）。

*主張*　単体的 $`n` 立方体 $`2^n` は $`n` 元集合の冪集合の包含順序の nerve であり、$`\partial 2^n` は始頂点と終頂点を同時には含まない単体の部分集合である。

cube (Fin n)は原文と同じ包含順序の冪集合のnerveを直接与え、cubeSplitIsoは座標一個を分離する積同型を与える。候補cubeBoundaryの座標面の合併と、原文の初終点を同時に含まない単体による∂2ⁿは同一視しない。n重積の一括同型も含まない。

各元が部分集合に属するかどうかを座標にすると $`2^n\simeq(\Delta^1)^n` となる。原典の境界はこの両端による条件で指定されている。

:::

:::proposition "ha_4_1_5_5" (lean := "CategoryTheory.Nerve.quasicategory")
*HA 警告 4.1.5.5*　From \$A\_\{n\}\$-Algebras to \$A\_\{n+1\}\$-Algebras (p. 475)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=475)）。対応表の状態：一部（component）。

*主張*　$`T^n` は単体圏の部分圏の nerve なので ∞ 圏であるが、指定の辺を除いた部分単体集合 $`T^{\circ n}` は一般には ∞ 圏にならない。

KB-W2型再照合：仮定：通常圏 C（HA の Tⁿ を与える半単体圏の充満部分圏を C に取る）。結論：その神経が準圏となる（Tⁿ が準圏である成分に一致）。辺を除いた T◦ⁿ が一般に準圏でないことは含まれない。

辺を除いた部分では、残った二辺の合成に必要な辺が除かれている場合がある。そのため内角充填を一般には期待できない。

:::

# 4.1.7 Monoidal Model Categories

%%%
number := false
tag := "ha-4-1-7"
%%%

:::definition "ha_4_1_7_3" (lean := "SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelHammock_isLocalization")
*HA 記法 4.1.7.3*　Monoidal Model Categories (p. 486)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=486)）。対応表の状態：一部（special）。

*主張*　同値で印を付ける関手の左随伴を、印付きの対 $`(C,W)\mapsto C[W^{-1}]` と書く。

KB-W2型再照合：仮定：C はモデル圏の通常の nerve で、W は弱同値。関手的分解と指定フレームを要求する（Lean が強い：一般の準圏と system を扱わない）。結論：指定された弱同値を反転する普遍的な C\[W⁻¹\] の模型（一致する特殊例。全 system に対する左随伴の構成は型にない）。

左随伴は指定した射を同値にする局所化である。ここでの構成は有限積を保つため、モノイダル構造の局所化にも使える。

:::

:::proposition "ha_4_1_7_6" (lean := "SerrePositivity.Quillen.tensor_isCofibrant")
*HA 例 4.1.7.6*　余ファイブラント対象の局所化が受け継ぐモノイダル構造（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=487)）。対応表の状態：一部（component）。

*主張*　モノイダルモデル圏の余ファイブラント対象をその弱同値で局所化すると、基礎 ∞ 圏にモノイダル構造が入る。対称性も引き継がれる。

KB-W2型再照合：仮定：余ファイブラントな X,Y と、組紐付き閉モノイダルモデル圏のテンソルの Quillen 条件（Lean が強い：組紐付き閉の場合）。結論：X⊗Y が余ファイブラントであること（HA の Aᶜ がテンソルで閉じる部分に一致）。弱同値の両側保存と、局所化上のモノイダル ∞ 構造はこの型に含まれない。

余ファイブラント対象のテンソルは余ファイブラントで、その間の弱同値は余ファイブラント対象との左右のテンソルで保たれる。したがってテンソルを局所化へ降ろせる。

:::

:::proposition "ha_4_1_7_11" (lean := "SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.cofibrantFibrantObjects_sHom_kanComplex")
*HA 注意 4.1.7.11*　Monoidal Model Categories (p. 488)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=488)）。対応表の状態：一部（special）。

*主張*　単体的モノイダルモデル圏でファイブラントかつ余ファイブラントな対象から作る単体的色付きオペラッドは、各多重写像空間が Kan 複体であり、そのオペラッド nerve は ∞ オペラッドとなる。

KB-W2型再照合：仮定：固定 SM7 を持つ単体モデル圏の二つの cofibrant-fibrant 対象（Lean が強い：入力数 1 に限る）。結論：二対象間の単体豊穣 Hom は Kan（HA の一入力の場合と一致。多入力 operad 全体の fibrancy は型に含まれない）。

多重写像空間は入力対象のテンソル積から出力対象への単体的写像対象である。始域は余ファイブラント、終域はファイブラントなので Kan 性が従う。

:::

# 4.1.8 Rectification of Associative Algebras

%%%
number := false
tag := "ha-4-1-8"
%%%

:::definition "ha_4_1_8_1" (lean := "SerrePositivity.Quillen.HasMonoidAxiom, SerrePositivity.Quillen.tensorCells_retracts_le_weakEquivalences")
*HA 定義 4.1.8.1*　Monoid Axiom（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=491)）。対応表の状態：一部（component）。

*主張*　組合せ的対称モノイダルモデル圏のモノイド公理は、任意の対象とのテンソルで作る自明余ファイブレーションの像の弱飽和閉包が弱同値だけからなるという条件である。

KB-W2型再照合：仮定：モノイダル圏とモデル構造（Lean が弱い：組合せ的・対称であることを仮定しない）。結論：自明余ファイブレーションを右から任意の対象でテンソルして作る、指定宇宙の余積・押し出し・超限合成とそのレトラクトの弱同値性（対称な場合に HA の生成射と同じ右テンソル側）。全宇宙の最小弱飽和類との比較は型に含まれない。

生成射は $`\mathrm{id}_X\otimes f` で、$`f` は自明余ファイブレーション、$`X` は任意である。押し出し・超限合成・レトラクトもまとめて弱同値に入ることを求める。

:::

:::proposition "ha_4_1_8_3" (lean := "SerrePositivity.DGAlgebra.modelCategory, SerrePositivity.DGAlgebra.modelCategory_weakEquivalences, SerrePositivity.DGAlgebra.modelCategory_fibrations, SerrePositivity.DGAlgebra.forget_isRightQuillen")
*HA 命題 4.1.8.3*　Rectification of Associative Algebras (p. 492)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=492)）。対応表の状態：一部（special）。

*主張*　組合せ的モノイダルモデル圏で全対象が余ファイブラント、または対称でモノイド公理を満たすなら、結合代数の圏に基礎対象で弱同値とファイブレーションを判定する組合せ的モデル構造が入る。

KB-W2型再照合：仮定：可換環 R 上の鎖複体に射影モデル構造を選ぶ（Lean は底をこの例に固定）。結論：厳密な結合 dg 代数にモデル構造があり、弱同値は底の擬同型、ファイブレーションは底の射影ファイブレーション、忘却は右 Quillen（(1) のモデル構造と右類の記述および (2) に一致）。組合せ性・単体モデル構造・左固有性はこの型に含まれない。

忘却関手は右 Quillen であり、適合する単体構造も継承される。全対象が余ファイブラントで基礎の弱同値が濾過余極限で閉じている場合、代数のモデル圏は左固有になる。

:::

:::definition "ha_4_1_8_10" (lean := "CategoryTheory.MonoidalCategory.Arrow.pushoutProduct, CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.symmetricCategory")
*HA 記法 4.1.8.10*　Rectification of Associative Algebras (p. 495)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=495)）。対応表の状態：一部（special）。

*主張*　射 $`f:X\to X'`、$`g:Y\to Y'` の押し出し積は $`(X\otimes Y')\sqcup_{X\otimes Y}(X'\otimes Y)\to X'\otimes Y'` である。

KB-W2型再照合：仮定：押し出しを持つモノイダル圏（定義は HA と一致。矢印圏の構造には Lean が強い：始対象を持つ Cartesian 閉の場合）。結論：指定の押し出しからテンソル先への射を与える二関手（HA と一致）と、Cartesian 閉の場合の矢印圏の対称モノイダル構造（HA の構造の主張をこの場合に確認）。

この操作で矢印圏にモノイダル構造を入れる。基礎のテンソルが対称なら、押し出し積も因子交換の対称性を持つ。

:::

:::lemma_ "ha_4_1_8_12" (lean := "SerrePositivity.Quillen.pushoutProduct_cofibration")
*HA 補題 4.1.8.12*　Rectification of Associative Algebras (p. 495)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=495)）。対応表の状態：一部（component）。

*主張*　モノイダルモデル圏の二つの余ファイブレーションの間をそれぞれ対象ごとの弱同値で比較し、四つの射の端点がすべて余ファイブラントなら、押し出し積の比較も同じ性質を持つ。

KB-W2型再照合：仮定：テンソルが Quillen 二関手で二本の射が余ファイブレーション（横射について HA と一致、比較四角形や対象の余ファイブラント性は要求しない）。結論：上段・下段に適用すると横の押し出し積が余ファイブレーションとなる部分に一致。縦射の弱同値性は型に含まれない。

各押し出し積は余ファイブレーションで、その両端は余ファイブラントとなる。始域の張り合わせと終域のテンソル積は、それぞれ上段から下段への弱同値を誘導する。

:::

