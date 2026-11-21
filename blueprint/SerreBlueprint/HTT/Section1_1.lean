-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.AlgebraicTopology.Quasicategory.Nerve
import Mathlib.AlgebraicTopology.Quasicategory.StrictSegal
import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
import Mathlib.AlgebraicTopology.SimplicialNerve
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal
import Mathlib.CategoryTheory.Enriched.EnrichedCat
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.NatTrans
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Homotopy.Basic
import SerrePositivity.HomotopicalAlgebra.Topological.WeakEquivalence
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathNerve
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Quasicategory

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 1.1 Foundations for Higher Category Theory" =>
%%%
number := false
tag := "htt-1-1"
%%%

HTT 1.1 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 1.1.1 Goals and Obstacles

%%%
number := false
tag := "htt-1-1-1"
%%%

:::proposition "htt_1_1_1_2" (lean := "ContinuousMap.Homotopy")
*HTT 例 1.1.1.2*　連続写像とホモトピーの圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=21)）。対応表の状態：一部（component）。

*主張*　位相空間の間の連続写像を対象、ホモトピーの端点固定類を射として、写像のなす圏を考えられる。

冒頭で明示された同じ連続写像f₀,f₁のhomotopyはContinuousMap.Homotopyそのもので、I×X→Yと端点条件を持つ。X×Iとの積の交換以外の比較を要しない。後続の写像空間の高次圏・ホモトピー圏の主張は含まない。

$`X` から $`Y` への写像をただホモトピーで同一視すると、どう変形したかの情報は残らない。ここでは写像を残し、区間を媒介とする変形を射として集める。変形の連結を射の合成とするには、そのホモトピー類をとる。

:::

:::proposition "htt_1_1_1_3" (lean := "CategoryTheory.Functor.category, CategoryTheory.NatTrans")
*HTT 例 1.1.1.3*　関手と自然変換がなす圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=21)）。対応表の状態：Mathlib にある。

*主張*　通常圏 $`\mathcal C,\mathcal D` に対し、関手 $`\mathcal C\to\mathcal D` と自然変換は関手圏 $`\operatorname{Fun}(\mathcal C,\mathcal D)` をなす。

仮定：通常圏 C、D（HTT と一致）。結論：C ⥤ D に圏構造を与え、その射は各射に対する自然性を満たす成分族 NatTrans（一致）。

自然変換の成分は $`\mathcal C` の各対象について与え、任意の射で自然性を課す。成分ごとの合成はこの自然性を保つため、関手どうしの射として合成できる。

:::

:::proposition "htt_1_1_1_4" (lean := "ZerothHomotopy, FundamentalGroupoid.fundamentalGroupoidFunctor")
*HTT 例 1.1.1.4*　位相空間の基本高次亜群（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=21)）。対応表の状態：一部（special）。

*主張*　空間 $`X` の基本 $`n`-亜群は道と高次ホモトピーを集め、有限の $`n` では最高次をホモトピーで割るという構想で、$`n=0` は弧状連結成分、$`n=1` は基本亜群になる。

KB-W2原文・型再照合：仮定：位相空間 X、n を 0 または 1 に限定（Lean が強い特殊形）。結論：ZerothHomotopy は path components、FundamentalGroupoid の対象は X の点、射は端点付きの道を端点固定ホモトピーで割ったものなので、この二つの n の原典の構成に一致。n≥2 と ∞ の比較は含まない。

点を対象にした道の圏を考えると、一段上に道の変形がある。一段で打ち切ると端点固定で同値な道は同じ射になるが、打ち切りを上げるとその変形自体を保持する、という例である。

:::

# 1.1.2 ∞-Categories

%%%
number := false
tag := "htt-1-1-2"
%%%

:::definition "htt_1_1_2_1" (lean := "SSet.KanComplex.iff")
*HTT 定義 1.1.2.1*　全ホーンを充填する Kan 複体（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=26)）。対応表の状態：Mathlib にある。

*主張*　単体的集合が Kan 複体であるとは、すべての角包含 $`\Lambda_i^n\hookrightarrow\Delta^n` に対し、角からの写像が単体へ延びることをいう。

仮定：任意の単体集合 S（HTT と一致）。結論：KanComplex S と、正次数の各内外ホーンから S への射が標準単体に延びることの同値（一致）。

各角では面が一つ欠けており、充填はその面と単体全体を同時に補う。位相空間の特異複体では、幾何学的な角へのレトラクションに角上の写像を合成して延長を作れる。

:::

:::proposition "htt_1_1_2_2" (lean := "CategoryTheory.Nerve.strictSegal, SSet.StrictSegal.quasicategory")
*HTT 命題 1.1.2.2*　通常圏の nerve と一意な内ホーン充填（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=27)）。対応表の状態：一部（component）。

*主張*　単体的集合が小さい通常圏の nerve と同型であることは、すべての内角が一意に充填されることと同値である。

KB-W2原文・型再照合：仮定：K が通常圏の nerve である、すなわち原典 (1) の場合（Lean が強い特殊形）。結論：Nerve.strictSegal と StrictSegal.quasicategory から各 inner horn の filler の存在を得る。これは (2) の存在部分に一致するが、一意性と (2)⇒(1) の再構成は得ていない。

二次元の一意充填から、接続する二辺の合成が決まる。三次元の充填は二通りの合成順を比較し、より高い充填の一意性は、形成した圏の nerve との比較を可能にする。

:::

:::definition "htt_1_1_2_4" (lean := "SSet.Quasicategory")
*HTT 定義 1.1.2.4*　内ホーン充填による準圏の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=32)）。対応表の状態：Mathlib にある。

*主張*　∞ 圏とは、各内角 $`\Lambda_i^n`（$`0<i<n`）からの写像が $`\Delta^n` に延びる単体的集合である。

仮定：任意の単体集合 S（HTT と一致）。結論：Quasicategory S のデータは内ホーン射の延長の存在（一致）。

二次元では接続する二辺の合成を指定できることに対応する。内角条件は充填の存在を要求するので、同じ二辺の複数の充填も許す。

:::

:::proposition "htt_1_1_2_5" (lean := "SSet.instQuasicategoryOfKanComplex")
*HTT 例 1.1.2.5*　Kan 複体と特異複体の準圏性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=32)）。対応表の状態：一部（component）。

*主張*　Kan 複体は ∞ 圏であり、特に空間 $`X` の特異複体をその基本 ∞ 亜群として使える。

KB-W2原文・型再照合：仮定：任意の Kan 複体 S（HTT と一致）。結論：Quasicategory S を得るので「Any Kan complex is an ∞-category」という最初の assertion に一致。一般の X の singular complex の Kan 性と π≤∞X の同定は含まない。

内角を含むすべての角を埋められるため、特異複体は ∞ 圏として扱える。外角が埋まることは、道の逆向きも使えるという亜群の側面に対応する。

:::

:::proposition "htt_1_1_2_6" (lean := "CategoryTheory.Nerve.quasicategory")
*HTT 例 1.1.2.6*　通常圏の nerve の準圏性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=32)）。対応表の状態：Mathlib にある。

*主張*　任意の通常圏の nerve は ∞ 圏である。

仮定：通常圏 C（HTT と一致）。結論：Quasicategory (nerve C) を与える（一致）。

nerve の単体は接続する射の列により決まり、欠けた内側の面は隣り合う射の合成で与えられる。通常圏で成り立つ内角の一意性は、∞ 圏の要求より強い。

:::

# 1.1.3 Equivalences of Topological Categories

%%%
number := false
tag := "htt-1-1-3"
%%%

:::definition "htt_1_1_3_4" (lean := "SerrePositivity.TopologicalHomotopy.weakHomotopyEquivalences")
*HTT 定義 1.1.3.4*　位相空間の弱ホモトピー同値（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=34)）。対応表の状態：本体にある。

*主張*　連続写像が弱ホモトピー同値であるとは、$`\pi_0` で全単射を、すべての基点と正次数についてホモトピー群の同型を誘導することをいう。

仮定：位相空間間の連続写像 f（HTT と一致）。結論：π₀ と全基点・全正次数の誘導写像の全単射で弱ホモトピー同値を定める（一致）。

$`\pi_0` は成分の対応を、基点付きの群は各成分内部の高次の情報を検査する。比較する基点は $`x` とその像 $`f(x)` である。

:::

:::definition "htt_1_1_3_6" (lean := "SerrePositivity.TopologicalHomotopy.weakHomotopyEquivalences")
*HTT 定義 1.1.3.6*　位相豊穣関手の弱同値（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=35)）。対応表の状態：一部（component）。

*主張*　位相圏の間の関手が同値であるとは、各写像空間に弱ホモトピー同値を誘導し、ホモトピー圏上で本質的全射であることをいう。

KB-W2原文・型再照合：仮定：位相豊穣関手 F の各 Hom に誘導される連続写像を入力（HTT の各 Hom の条件と一致）。結論：weakHomotopyEquivalences は π0 と全基点・正次数 πn の全単射を要求するので、明記された第一条件の弱ホモトピー同値の判定を表す。F 全体の hF の本質的全射を組み合わせた定義と hC との比較はない。

対象についてはホモトピー圏の同型までを許す一方、固定した二対象の間では写像空間全体を比較する。射の成分集合における全単射だけでは後者を尽くさない。

:::

# 1.1.4 Simplicial Categories

%%%
number := false
tag := "htt-1-1-4"
%%%

:::definition "htt_1_1_4_1" (lean := "CategoryTheory.SimplicialCategory, CategoryTheory.SimplicialCategory.sHom, CategoryTheory.EnrichedCat")
*HTT 定義 1.1.4.1*　単体集合に豊穣な圏の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=36)）。対応表の状態：Mathlib にある。

*主張*　単体的圏は単体的集合に豊穣化した圏であり、豊穣関手を射とする圏を $`\mathrm{Cat}_\Delta` と記す。

仮定：対象型 C と単体集合への豊穣化（HTT と一致。Lean の通常圏構造は豊穣 Hom の零単体との同定を伴う）。結論：単体集合 sHom、豊穣合成、豊穣関手を射とする EnrichedCat SSet を与える（一致）。

合成は二つの写像単体集合の積から第三の写像単体集合への単体的写像である。この合成は豊穣圏の結合律を満たし、その上で写像単体集合の高次単体を扱う。

:::

# 1.1.5 Comparing ∞-Categories with Simplicial Categories

%%%
number := false
tag := "htt-1-1-5"
%%%

:::definition "htt_1_1_5_1" (lean := "CategoryTheory.SimplicialThickening, CategoryTheory.SimplicialThickening.Path, CategoryTheory.SimplicialThickening.compFunctor")
*HTT 定義 1.1.5.1*　端点を含む部分集合による厚化（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=38)）。対応表の状態：Mathlib にある。

*主張*　有限非空全順序集合 $`J` から作る $`\mathfrak C[\Delta^J]` の対象は $`J` の元で、$`i\le j` の写像単体集合は両端を含む区間内の部分集合の包含順序の nerve、$`i>j` では空であり、合成は和集合で与える。

仮定：非空有限全順序 J（Lean が弱い：任意の全順序型 J）。結論：対象は J、豊穣 Hom は両端を含む区間部分集合の包含順の nerve、合成は和集合（一致）。

$`i,j` の間にある各点を経由点として入れるかどうかが、写像単体集合の頂点を区別する。経由点を足す操作が順序を与え、途中の点 $`j` で二つの経路をつなぐ操作は部分集合の和集合になる。

:::

:::proposition "htt_1_1_5_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathInteriorNerveIso")
*HTT 注意 1.1.5.2*　厚化の立方体 Hom と弱可縮性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=39)）。対応表の状態：一部（component）。

*主張*　$`\mathfrak C[\Delta^n]\to[n]` の対象上で恒等な関手は豊穣圏として同値で、各 $`i\le j` の写像空間の収縮性が異なる経由点列を結びつける。

KB-W2原文・型再照合：仮定：\[n\] 内の a\<b（Lean が強い特殊形）。結論：pathInteriorNerveIso は原典 C\[Δn\] の Hom=nerve(Path a b) を内部点の冪集合の nerve と同型にするので、明記された cube の記述に一致。全ての a≤b と \[n\] への enriched weak equivalence、および cosimplicial cofibrant replacement は含まない。

直行する射の頂点と中継点を経由した合成の頂点は区別される。両者が属する写像空間は内部点の選択を表す立方体であり、$`[n]` への比較はその立方体を一点に送る。

:::

:::definition "htt_1_1_5_3" (lean := "CategoryTheory.SimplicialThickening.functor")
*HTT 定義 1.1.5.3*　単調写像が誘導する厚化関手（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=39)）。対応表の状態：Mathlib にある。

*主張*　単調写像 $`f:J\to J'` が誘導する豊穣関手 $`\mathfrak C[f]` は、対象を $`f` で、写像空間の部分集合を $`I\mapsto f(I)` で送る。

仮定：全順序集合間の単調写像 f（HTT と一致）。結論：厚化の間の豊穣関手を構成し、対象には f、区間部分集合には f の像を適用する（一致）。

$`f` が内部点を同一視しても、像部分集合には両端の像が残る。部分集合の像は包含と和集合を保つので、写像空間の単体と合成の両方に作用する。

:::

:::proposition "htt_1_1_5_4" (lean := "CategoryTheory.SimplicialThickening.functor_comp")
*HTT 注意 1.1.5.4*　厚化関手の合成と標準の辺（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=40)）。対応表の状態：一部（component）。

*主張*　$`\mathfrak C[f]` は端点だけからなる頂点をその像の端点だけからなる頂点へ送り、この構成は余単体的対象 $`[n]\mapsto\mathfrak C[\Delta^n]` を定める。

KB-W2原文・型再照合：仮定：全順序間の単調写像 f,g（HTT と一致）。結論：厚化の functor(g∘f)=functor(f)∘functor(g) を得るので cosimplicial thickening の合成則の assertion に一致。先に述べられた二端点の特別な頂点 pij の像の式をこの宣言では別個に証明していない。

単調写像を二度適用した部分集合の像は、合成した単調写像による像に等しい。この等しさが、端点の指定を含めた余単体構造を与える。

:::

:::definition "htt_1_1_5_5" (lean := "CategoryTheory.SimplicialNerve")
*HTT 定義 1.1.5.5*　単体的圏と位相豊穣圏の nerve（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=40)）。対応表の状態：一部（component）。

*主張*　単体的圏 $`\mathcal C` の整合的 nerve の $`n`-単体は豊穣関手 $`\mathfrak C[\Delta^n]\to\mathcal C` であり、位相圏の場合は写像空間を特異複体にして同じ構成を行う。

KB-W2原文・型再照合：仮定：単体的圏 C（HTT の最初の文と一致）。結論：SimplicialNerve C は各 n で厚化から C への enriched functors を持つ単体集合で、最初の定義に一致。位相豊穣 C の Hom に Sing を施す base change と topological nerve の定義は含まない。

顔・退化作用は標準単体間の写像が誘導する豊穣関手との前合成で与えられる。例えば三対象の単体では、二辺の合成と第三の辺を結ぶデータも写像空間の中に現れる。

:::

:::proposition "htt_1_1_5_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory")
*HTT 命題 1.1.5.10*　局所 Kan 圏の nerve の準圏性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=41)）。対応表の状態：本体にある。

*主張*　写像単体集合がすべて Kan 複体である単体的圏の整合的 nerve は ∞ 圏である。

仮定：単体的圏 C のすべての豊穣 Hom が Kan 複体（HTT と一致）。結論：Quasicategory (SimplicialNerve C)（一致）。

nerve の内角を延長する問題は、すでに与えられた豊穣関手の断片を一つの標準単体に整合させる問題である。仮定は個々の写像対象に置かれ、結論は対象と射をまとめた nerve について述べる。

:::

