import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.GroupTheory.Coxeter.Matrix
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Cube
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HollowCube
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HollowCylinder
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Quasicategory
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanIntervalEvaluation
import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanPrismExtension

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "2.4 Simplicial Categories" =>
%%%
number := false
tag := "kerodon-2-4"
%%%

Kerodon の 2.4 節（[Tag 00JN](https://kerodon.net/tag/00JN)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 2.4.1 Simplicial Enrichment

%%%
number := false
tag := "kerodon-2-4-1"
%%%

Kerodon [Tag 00JQ](https://kerodon.net/tag/00JQ)

:::definition "kerodon_2_4_1_1" (lean := "CategoryTheory.SimplicialCategory, CategoryTheory.SimplicialCategory.sHom")
Kerodon Definition 2.4.1.1（[Tag 00JR](https://kerodon.net/tag/00JR)）。対応表の状態：Mathlib にある。

仮定：対象型 C（Kerodon と一致。Lean では Hom の 0 単体から得る普通圏の構造も入力し、豊穣化との整合を課す）。結論：各組の単体集合 sHom、積からの合成と単位、結合・単位条件を備える（一致）。

*定義 2.7 （単体的圏）*

単体的圏とは、対象の集合と、対象 $`x,y` ごとの単体的集合 $`\mathcal C(x,y)`、単体的集合の射としての合成 $`\mathcal C(y,z)\times\mathcal C(x,y)\to\mathcal C(x,z)`、恒等射 $`\mathrm{id}_x\in\mathcal C(x,x)([0])` の組で、合成が結合的かつ単位的であるものをいう。

:::

:::definition "kerodon_2_4_1_3" (lean := "CategoryTheory.SimplicialCategory.homEquiv'") (uses := "kerodon_1_1_0_6")
Kerodon Construction 2.4.1.3（[Tag 00JT](https://kerodon.net/tag/00JT)）。対応表の状態：一部。

B6：homEquiv' は n=0 で Hom 集合を sHom の0単体に同一視する成分を直接与える。全次数での圏と単体的演算の一式は未確認。

:::

:::definition "kerodon_2_4_1_6" (lean := "SSet.Edge, CategoryTheory.SimplicialCategory.homEquiv'")
Kerodon Definition 2.4.1.6（[Tag 00JW](https://kerodon.net/tag/00JW)）。対応表の状態：一部。

B6：sHom の0単体を homEquiv' で指定し Edge を取ると、d₁=f,d₀=g という原文のホモトピーのデータを直接表す。専用の名前付き述語や合成法は含まない。

:::

:::definition "kerodon_2_4_1_8" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1")
Kerodon Definition 2.4.1.8（[Tag 00JY](https://kerodon.net/tag/00JY)）。対応表の状態：なし。

B6：simplicialNerve\_quasicategory は局所 Kan 性を入力仮定として使う定理。その仮定から局所 Kan の定義を表す宣言を取り出せるわけではなく、結論は nerve の準圏性という別の主張。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory`

:::

:::definition "kerodon_2_4_1_11" (lean := "CategoryTheory.EnrichedFunctor")
Kerodon Definition 2.4.1.11（[Tag 00K1](https://kerodon.net/tag/00K1)）。対応表の状態：Mathlib にある。

仮定：単体集合で豊穣化した C, D（Kerodon と一致。EnrichedFunctor は任意の基礎モノイダル圏 V でも使える）。結論：対象の写像と各 Hom の単体写像が豊穣合成と恒等を保存する（一致）。

*定義 3.1 （単体的関手）*

単体的圏 $`\mathcal C,\mathcal D` の間の単体的関手 $`F\colon\mathcal C\to\mathcal D` とは、対象の対応 $`x\mapsto F(x)` と、対象 $`x,y` ごとの単体的集合の射 $`F_{x,y}\colon\mathcal C(x,y)\to\mathcal D(F(x),F(y))` の組で、合成と恒等射を保つものをいう。単体的圏と単体的関手のなす圏を $`\mathrm{sCat}` と書く。

:::

:::proposition "kerodon_2_4_1_13"
Kerodon Proposition 2.4.1.13（[Tag 00K3](https://kerodon.net/tag/00K3)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。一般の EnrichedCat は双圏。Cat\_Δ の小極限と小余極限のインスタンスは未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

# 2.4.3 The Homotopy Coherent Nerve

%%%
number := false
tag := "kerodon-2-4-3"
%%%

Kerodon [Tag 00KM](https://kerodon.net/tag/00KM)

*定理 3.5 （関手性）*

単体的関手 $`F\colon\mathcal C\to\mathcal D` に後合成 $`\sigma\mapsto F\circ\sigma` を対応させることで、$`N^{hc}` は関手 $`\mathrm{sCat}\to\mathrm{sSet}` になる。

*注意 （大きさ）*

定理 3.5 の $`\mathrm{sCat}` と $`\mathrm{sSet}` は、大きさを制限しない、すべての単体的圏（対象が集合をなすもの）とすべての単体的集合の圏である。どちらも対象の全体は集合にならず、各 $`\mathrm{Hom}` は集合だが小さいとは限らない。$`N^{hc}` を単体的集合として定めるのに必要なのは $`\mathcal C` の対象が集合をなすことで、$`\mathcal C` が小さいことは要らない。

*coherent-nerve-diagrams.html — 1. 定義 — 低次元*

- 次元　／　データ
- 0　／　対象 $`x`
- 1　／　射 $`f_{01}\in\mathrm{Map}(x_0,x_1)_0`
- 2　／　$`f_{01},f_{12},f_{02}` とホモトピー $`H_{012}\colon f_{02}\Rightarrow f_{12}\circ f_{01}`
- 3　／　4 つの面と、$`\mathrm{Map}(x_0,x_3)` の正方形（§3）

*coherent-nerve-diagrams.html — 3. ホモトピー整合的図式 — 動機*

$`J` 型の図式として、厳密な図式 $`J\to\mathcal C` は硬すぎ、ホモトピー可換図式 $`J\to h\mathcal C` は情報が足りない。ホモトピーを*データとして*持ち、ホモトピー同士の整合性も高次ホモトピーとして持つのがホモトピー整合的図式である。

*coherent-nerve-diagrams.html — 3. ホモトピー整合的図式 — 定義*

$$`\mathfrak C[N(J)]\longrightarrow\mathcal C\ \ \text{（単体的関手）}\qquad\Longleftrightarrow\qquad N(J)\longrightarrow N^{hc}(\mathcal C).`

$`J` の合成可能な列 $`j_0\to\cdots\to j_n` ごとに $`\mathfrak C[\Delta^n]` 型のデータを、面・退化と両立するように与える。面 $`d_i`（$`0\lt i\lt n`）は $`J` での合成を、退化は恒等射を表すので、恒等射を含む列のホモトピーは自明になる。

*coherent-nerve-diagrams.html — 3. ホモトピー整合的図式 — 列 $`[n]` の場合*

$`n=3` で新しく必要になるのは $`\mathrm{Map}(x_0,x_3)` の中の正方形である。

$$`\begin{array}{ccc} f_{03} & \xrightarrow{\ H_{013}\ } & f_{13}f_{01}\\[2pt] {\scriptstyle H_{023}}\downarrow & & \downarrow{\scriptstyle H_{123}\,\circ\, f_{01}}\\[2pt] f_{23}f_{02} & \xrightarrow{\ f_{23}\,\circ\, H_{012}\ } & f_{23}f_{12}f_{01} \end{array}`

頂点は部分集合 $`\{0,3\},\{0,1,3\},\{0,2,3\},\{0,1,2,3\}`、辺は低次のホモトピーとその whiskering で、すべて既知のデータから決まる。新しいデータは正方形の内部（2 次のホモトピー）である。一般の $`n` では $`(\Delta^1)^{n-1}` の立方体で、境界は低次のデータで決まり、内部が新しいデータになる。

*coherent-nerve-diagrams.html — 3. ホモトピー整合的図式 — 障害*

境界が与えられても内部を埋められるとは限らない。$`n` 段目の障害は $`\pi_{n-2}\mathrm{Map}(x_0,x_n)` にあり、低次のデータの選び方に依存する。ホモトピー可換図式は 2 段目までしか見ておらず、ホモトピー整合的図式は全段を選んだデータごと持っている。

*coherent-nerve-diagrams.html — 4. 具体例 — 例 1：可換正方形と loop*

$$`\begin{array}{ccc} \ast & \longrightarrow & \ast\\ \downarrow & & \downarrow{\scriptstyle x}\\ \ast & \xrightarrow{\ x\ } & X \end{array}`

$`J=[1]\times[1]`。$`J` の中では二つの経路の合成は同じ射 $`a\to d` なので、整合的図式のデータは 2 単体二つ $`f_{ad}\Rightarrow f_{bd}f_{ab}` と $`f_{ad}\Rightarrow f_{cd}f_{ac}`、つなげると $`x` における loop $`\gamma` になる。

- ホモトピー可換図式としては、どの $`\gamma` でも同じ一つの図式。

- 整合的図式としては、$`\gamma` と $`\gamma'` が同値になるのは、端点を止めてホモトピックなとき。同値類はおよそ $`\pi_1(X,x)` で数えられる。

- 違いは実際に現れる：この正方形はホモトピー引き戻し $`\ast\times^h_X\ast=\Omega X` への写像 $`\ast\to\Omega X` を誘導し、それは点 $`\gamma` を選ぶ。たとえば $`X=S^1` なら、整合的な正方形は回転数 $`k\in\mathbb Z` で分類される。

*coherent-nerve-diagrams.html — 4. 具体例 — 例 2：ホモトピー整合的な $`\mathbb Z/2` 作用*

$`J=B(\mathbb Z/2)`（1 対象、射 $`e,\tau`、$`\tau^2=e`）、値は空間 $`X`。$`N(J)` の単体は $`\{e,\tau\}` の列で、$`e` を含む列のデータは自明（退化）になる。非自明なデータは次のとおり。

- \*\*1 単体 $`(\tau)`\*\*：写像 $`t\colon X\to X`。

- \*\*2 単体 $`(\tau,\tau)`\*\*：合成は $`e` なので、ホモトピー $`H\colon\mathrm{id}_X\Rightarrow t\circ t`。

- \*\*3 単体 $`(\tau,\tau,\tau)`\*\*：§3 の正方形で、$`f_{01}=f_{12}=f_{23}=t`、$`f_{02}=f_{13}=\mathrm{id}`、$`f_{03}=t`。辺 $`H_{013}`、$`H_{023}` は $`e` を含む列なので定値。残る二辺は
  $$`H\circ t\colon t\Rightarrow t^3,\qquad t\circ H\colon t\Rightarrow t^3,`
  で、内部は*この二つのホモトピーの間のホモトピー*である。これは $`\mathbb Z/2` 作用の古典的な整合性条件そのもの。

- さらに高次の単体 $`(\tau,\dots,\tau)` ごとに、より高次の整合性が続く。

$`t` と $`H` だけ（「ホモトピーで $`t^2\simeq\mathrm{id}`」）では、一般に整合的な作用に延長できない。延長の障害は $`\pi_*\mathrm{Map}(X,X)` にある。整合的な作用まで与えると、straightening によって $`B\mathbb Z/2=\mathbb{RP}^\infty` 上の fiber が $`X` の fibration と同じものになる。たとえば $`S^n` の対蹠作用は $`S^\infty\times_{\mathbb Z/2}S^n\to\mathbb{RP}^\infty` に対応する。

*coherent-nerve-diagrams.html — 4. 具体例 — 例 3：持ち上がらないホモトピー可換図式（Toda 括弧）*

安定域（$`n` が十分大きい）で次の列を考える。

$$`S^{n+2}\xrightarrow{\ 2\ }S^{n+2}\xrightarrow{\ \eta\ }S^{n+1}\xrightarrow{\ 2\ }S^{n+1}`

$`\eta\circ2\simeq0` かつ $`2\circ\eta\simeq0` なので、$`f_{02},f_{13},f_{03}` をすべて零写像とすれば、$`[3]` 型のホモトピー可換図式になる。整合的図式に持ち上げようとすると、次の順に進む。

1. 零ホモトピー $`H_{012}\colon0\Rightarrow\eta\circ2` と $`H_{123}\colon0\Rightarrow2\circ\eta` を選ぶ。

2. §3 の正方形の境界は、$`\mathrm{Map}(S^{n+2},S^{n+1})` の零写像における loop になる。その類は $`[\Sigma S^{n+2},S^{n+1}]=\pi_2^s\cong\mathbb Z/2\{\eta^2\}` の元で、選択全体にわたる集合が Toda 括弧 $`\langle2,\eta,2\rangle` である。

3. Toda の計算により $`\langle2,\eta,2\rangle=\{\eta^2\}`（不定性なし）なので、どう選んでも loop は非自明で、正方形の内部を埋められない。

このホモトピー可換図式は整合的図式にも厳密な図式にも持ち上がらない。§3 の「$`n=3` の障害は $`\pi_1\mathrm{Map}(x_0,x_3)`」の具体例であり、Toda 括弧はこの障害そのものである。

原典との違い

- HTT は $`\mathfrak C[\Delta^n]` を Def. 1.1.5.1 で、上と同じ部分集合の半順序で定義する。Kerodon は coherent nerve を「単体的圏の homotopy coherent nerve」として同じく $`\mathrm{Path}[n]` で書く。

- W 構成との一致（Cordier）、厳密化定理（Vogt）は古典的な結果で、HTT では Prop. 4.2.4.4 の形で使われる。

このリポジトリとの対応（既出の宣言のみ）

- coherent nerve 自体は Mathlib の \`SimplicialNerve\` をそのまま使う。Kan 豊穣なら準圏であることは \`simplicialNerve\_quasicategory\`（Coherent/Quasicategory、第 3 章 §2）。

- $`\mathcal S`・$`\mathrm{Cat}_\infty` は \`SpaceInfinity\`・\`CatInfinity\`（F1/CatInfinity）。写像空間が元の Hom と同値であることは \`coherentHomEquivalence\`。

- strict な図式を整合的図式とみなすのは \`kanDiagramCoherentNerve\`（F1/KanDiagramCoherentNerve、第 5 章 §3）。厳密化定理の「strict → coherent」の向きにあたる。

*f-a-basics.html — 3. 単体の見方：結合律と五角形*

3 単体は四角形と対角線 2 本で、二通りの三角形分割 $`\{012,023\}`、$`\{013,123\}` が二通りの括弧付けに対応し、中身が結合律。4 単体は五角形と対角線 5 本で、5 通りの三角形分割（Catalan 数 $`C_3`）が 4 個の射の括弧付けに対応する。共有する対角線で三角形を切り落とした残りの四角形で flip すると隣の分割になり、その四角形は頂点を一つ除いた面 $`d_i`。5 本の辺が $`d_0,\dots,d_4` に対応して一周する。これが Mac Lane の五角形。

原図（0 / 1 / 2 / 3 / 4 / d₄ / d₂ / d₀ / d₃ / d₁ / f₄∘(f₃∘(f₂∘f₁)) / f₄∘((f₃∘f₂)∘f₁) / (f₄∘(f₃∘f₂))∘f₁ / ((f₄∘f₃)∘f₂)∘f₁ / (f₄∘f₃)∘(f₂∘f₁)）

- 面　／　頂点　／　associator　／　種類
- $`d_0`　／　1234　／　$`\alpha_{f_4,f_3,f_2}\circ f_1`　／　右から $`f_1` で whisker
- $`d_1`　／　0234　／　$`\alpha_{f_4,f_3,f_2f_1}`　／　合成に対する associator
- $`d_2`　／　0134　／　$`\alpha_{f_4,f_3f_2,f_1}`　／　合成に対する associator
- $`d_3`　／　0124　／　$`\alpha_{f_4f_3,f_2,f_1}`　／　合成に対する associator
- $`d_4`　／　0123　／　$`f_4\circ\alpha_{f_3,f_2,f_1}`　／　左から $`f_4` で whisker

*f-a-basics.html — 3. 単体の見方：結合律と五角形 — 3 次元を経由した見方*

頂点を $`(t,t^2,t^3,t^4)` 上に置いて最後の座標を落とすと、像は三角両錐（頂点 1, 3、赤道 0, 2, 4）。辺 13 だけが内部の軸になる。中身の埋め方は二通りで、$`\{d_1,d_3\}`（赤道の三角形 024 で貼り合わせた 2 個）と $`\{d_0,d_2,d_4\}`（軸 13 のまわりの 3 個）。これは Pachner の 2-3 move。さらに平面に落とすと、下面 $`\{012,023,034\}` が頂点 0 からの扇形 $`T_0`、上面 $`\{014,124,234\}` が頂点 4 からの扇形 $`T_4` で、四面体を一つ通過するごとに一回 flip する。$`T_0\to T_2\to T_4`（2 手）と $`T_0\to T_3\to T_1\to T_4`（3 手）が五角形の二つの道。3 単体でも 4 単体でも、境界は奇数番目の面と偶数番目の面に分かれる（Street の orientals）。

*f-a-basics.html — 3. 単体の見方：結合律と五角形 — 写像空間の立方体と horn*

$`\sigma\colon\Delta^n\to\mathcal C` は $`\mathrm{Map}(\sigma(0),\sigma(n))` の中に $`(n-1)` 次元の立方体 $`\mathfrak C\Delta^n=(\Delta^1)^{n-1}` を描く。点は経路（経由する中間頂点の集合）、辺は頂点の挿入（三角形）。多角形の描像と一次元ずれていて、括弧付けは点ではなく道、結合律は線ではなく面になる。

原図（0123 / 013 / 023 / 03 / 123 / 012 / 013 / 023 / n = 3：Map(0,3) は正方形 / n = 4：Map(0,4) は立方体（色付き = interchange） / 024 / 0124 / 0234 / 01234 / 04 / 014 / 034 / 0134）

- $`n=4` の立方体の 6 面：座標 $`i=1,2,3` を 0 に固定すると $`d_1,d_2,d_3`。座標 1 を 1 に固定すると $`d_0` を $`f_1` で whisker したもの、座標 3 を 1 に固定すると $`d_4` を $`f_4` で whisker したもの、座標 2 を 1 に固定すると interchange の正方形。interchange をつぶすと Mac Lane の五角形。頂点を除く順番 $`3!=6` 通りから interchange で同一視して 5 通り。

- *inner horn* $`\Lambda^4_k`（$`k=1,2,3`）：欠けた面 $`d_k` は立方体の面そのものなので、蓋の開いた箱を Kan 複体の中で埋めるだけ。

- *左 horn* $`\Lambda^4_0`：欠けた $`d_0` は $`f_1^*\colon\mathrm{Map}(1,4)\to\mathrm{Map}(0,4)` で送った形でしか見えないので、$`f_1` で割る必要がある。$`f_1` が同値なら埋まる（Joyal）。$`\mathcal C_{x/}` では先頭に $`x` が加わり、欠けた面が $`\mathrm{Map}(x,4)` の立方体の面になるので、割る必要がなくなる（left fibration の直観）。

*f-c-spaces.html — 4. $`N^{hc}` と quasicategory 性 — 4.1 低次元の単体*

- 0 単体：対象。1 単体：$`\mathcal C(x,y)` の頂点。

- 2 単体：$`f\colon x_0\to x_1`、$`g\colon x_1\to x_2`、$`h\colon x_0\to x_2` と $`\mathcal C(x_0,x_2)` の辺 $`h\to gf`。$`\mathcal Kan` ではホモトピー $`h\simeq g\circ f`。

- 3 単体：四つの 2 単体と $`\mathcal C(x_0,x_3)` の正方形（二通りの貼り合わせのホモトピーをつなぐ）。

- 確かめ：Hom が離散な普通の圏なら立方体からの写像は定数で、$`N^{hc}(\mathcal C)=N(\mathcal C)`。

*route-classification.html — 5. 段 3：$`\mathcal S=N^{hc}(\mathrm{Kan})` と写像空間の比較定理 — 5.2（3.2）低い次元の単体と $`h\mathcal S`*

$`\mathrm{Kan}` の Hom は $`\mathrm{Fun}(K,L)`（$`L` が Kan なので Kan）。

- 次元　／　新しい Hom　／　$`\mathcal S` の単体
- 0　／　—　／　Kan 複体
- 1　／　$`(0,1)=\Delta^0`　／　写像 $`f\colon K_0\to K_1`
- 2　／　$`(0,2)=\Delta^1`　／　$`f_{01},f_{12},f_{02}` とホモトピー $`f_{02}\Rightarrow f_{12}f_{01}`
- 3　／　$`(0,3)=\Delta^1\times\Delta^1`　／　四隅 $`f_{03},f_{13}f_{01},f_{23}f_{02},f_{23}f_{12}f_{01}`、四辺 $`H_{013},H_{023},f_{23}H_{012},H_{123}f_{01}` の正方形（ホモトピーのホモトピー）

\*\*$`hN^{hc}(D)=\pi_0D`\*\*：辺 $`f,g` がホモトピック ⟺ 境界 $`(f,\mathrm{id},g)` の 2 単体 ⟺ $`D(x,y)` の $`g` から $`f` への辺、なのでホモトピー類は連結成分。合成は定値ホモトピーで $`D` の合成。よって $`h\mathcal S=h\mathrm{Kan}`、同値はホモトピー同値（Whitehead により弱同値）。例：$`\Delta^0\to K` の射のホモトピー類は $`\pi_0K`。

*1 圏のナーブとの比較*：$`N(\mathrm{Kan})\subset\mathcal S`（ホモトピーを恒等に取る）、$`hN(\mathrm{Kan})=\mathrm{Kan}` ではホモトピー同値は可逆でない。$`\mathcal S\simeq N(\mathrm{Kan})[W^{-1}]`（補章 3）。

*Lean での扱い*：辺と豊穣圏の射の対応 \`coherentNerveEdgeToHom\`、\`coherentNerveEdgeToHom\_edge\`（F1/Coherent/EdgeEquiv）。$`\pi_0` の同一視は \`pinchedHomPiZeroEquiv\` と 3.3 の比較定理の組み合わせ。

:::definition "kerodon_2_4_3_1" (uses := "kerodon_2_3_5_1")
Kerodon Notation 2.4.3.1（[Tag 00KN](https://kerodon.net/tag/00KN)）。対応表の状態：なし。

B6：原文は逆包含順の有限鎖の nerve。SimplicialThickening と pathInteriorEquiv は包含順の別模型で、次数・合成を保つ原文との比較がないため、その模型の同型だけでは partial にしない。

*定義 3.3 （$`\mathfrak C[\Delta^n]`）*

$`n\ge0` について、単体的圏 $`\mathfrak C[\Delta^n]` を次で定める。

- 対象：$`0,1,\dots,n`。

- 射の単体的集合：$`i\le j` なら $`\mathfrak C\Delta^n=N(P_{ij})`。ここで $`P_{ij}` は $`\{i,j\}\subseteq S\subseteq\{i,i+1,\dots,j\}` をみたす部分集合 $`S` の全体に包含で順序を入れた半順序集合。$`i>j` なら空。

- 合成：和集合 $`P_{jk}\times P_{ij}\to P_{ik}`、$`(T,S)\mapsto T\cup S` が誘導する射 $`N(P_{jk})\times N(P_{ij})\to N(P_{ik})`。恒等射は $`\{i\}\in P_{ii}`。

$`\theta\colon[m]\to[n]` について、単体的関手 $`\mathfrak C[\theta]\colon\mathfrak C[\Delta^m]\to\mathfrak C[\Delta^n]` を、対象を $`i\mapsto\theta(i)`、射を $`S\mapsto\theta(S)` で定める。これにより関手 $`\mathfrak C\colon\Delta\to\mathrm{sCat}` が得られる。

宣言：`CategoryTheory.SimplicialThickening`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.path_hom_iff`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathInteriorEquiv`

:::

:::definition "kerodon_2_4_3_5" (uses := "kerodon_1_1_0_6")
Kerodon Definition 2.4.3.5（[Tag 00KS](https://kerodon.net/tag/00KS)）。対応表の状態：なし。

B6：SimplicialNerve の定義域は包含順の thickening。原文の逆包含 Path による関手集合との比較が単体構造まで必要で、似た nerve の定義だけでは原文の構成を直接得ない。

*定義 3.4 （homotopy coherent nerve）*

単体的圏 $`\mathcal C` について、単体的集合 $`N^{hc}(\mathcal C)` を

$$`N^{hc}(\mathcal C)([n])=\mathrm{Hom}_{\mathrm{sCat}}(\mathfrak C[\Delta^n],\mathcal C),\qquad N^{hc}(\mathcal C)(\theta)(\sigma)=\sigma\circ\mathfrak C[\theta]`

で定める。

宣言：`CategoryTheory.SimplicialNerve`

:::

# 2.4.4 The Path Category of a Simplicial Set

%%%
number := false
tag := "kerodon-2-4-4"
%%%

Kerodon [Tag 00L0](https://kerodon.net/tag/00L0)

*coherent-nerve-diagrams.html — 2. 普遍性*

- レベル　／　普遍性
- $`\mathfrak C[\Delta^n]`　／　Boardman–Vogt の W 構成 $`W[n]` と一致（Cordier）。自由で Bergner cofibrant、$`[n]` の解消。$`W[n]\to\mathcal C` はちょうど $`[n]` 型のホモトピー整合的図式（§3）。cofibrant な解消は弱同値を除いて一意なので、他の解消（Dwyer–Kan の自由解消など）を使っても得られるナーブは同値。
- $`N^{hc}`　／　Quillen 同値なので、∞ 圏の同値 $`\mathrm{sCat}[\text{DK}^{-1}]\simeq\mathrm{QCat}[\text{圏同値}^{-1}]` を誘導する。選び方によらない比較。
- 出てくる ∞ 圏　／　単体的モデル圏 $`\mathbf M` について $`N^{hc}(\mathbf M^\circ)\simeq N(\mathbf M^c)[W^{-1}]`（HA §1.3.4）。右辺は局所化の普遍性で特徴づけられる。

したがって $`\mathcal S` は sSet（Kan–Quillen）を弱同値で、$`\mathrm{Cat}_\infty` は準圏を圏同値で局所化したもので、$`N^{hc}` はその局所化を明示的な準圏として書き下す道具である。内在的な普遍性としては、$`\mathcal S\simeq\mathcal P(\ast)`（一点の自由余完備化）や左 fibration の分類、$`\mathrm{Cat}_\infty` については Toën の一意性定理（自己同値は op のみ）や cocartesian fibration の分類がある。

*f-c-spaces.html — 3. $`\mathfrak C[\Delta^n]` と一般の $`\mathfrak C` — 3.2 一般の $`K`*

$`\mathfrak C[K]=\operatorname{colim}_{\Delta^n\to K}\mathfrak C[\Delta^n]`（sCat での余極限、米田に沿った左 Kan 拡張）。これで $`\mathfrak C\dashv N^{hc}`。

- $`K`　／　$`\mathrm{Hom}_{\mathfrak C[K]}(0,2)`　／　意味
- $`\Delta^2`　／　$`\Delta^1`（$`h\to gf`）　／　指定されたホモトピーで可換な三角形
- $`\Lambda^2_1`　／　点（$`gf` だけ）　／　自由な合成
- $`\partial\Delta^2`　／　2 点 $`\{h,gf\}`　／　可換性の指定なし

一般の Hom は Dugger–Spivak の necklace（$`\Delta^{n_1}\vee\cdots\vee\Delta^{n_k}`）による余極限で書ける。半順序集合の脈体 $`N(P)` なら $`\mathrm{Hom}(x,y)` は $`x` から $`y` への鎖の半順序集合の脈体。sCat の余極限は合成で生成し直す必要があり、一般の $`K` の計算は大変。$`N^{hc}` の定義には $`\mathfrak C[\Delta^n]` で足り、4 の証明に要るのは $`\mathfrak C[\Lambda^n_i]` だけ。

:::definition "kerodon_2_4_4_1" (uses := "kerodon_1_1_0_6")
Kerodon Definition 2.4.4.1（[Tag 00L1](https://kerodon.net/tag/00L1)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。S から coherent nerve への写像を表現する path 圏の普遍性の型は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::definition "kerodon_2_4_4_2" (uses := "kerodon_1_1_0_6")
Kerodon Notation 2.4.4.2（[Tag 00L2](https://kerodon.net/tag/00L2)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。任意の単体集合 S からの Path\[S\] の構成は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::proposition "kerodon_2_4_4_3"
Kerodon Proposition 2.4.4.3（[Tag 00L3](https://kerodon.net/tag/00L3)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。任意 S の path 圏の存在は未発見。coherentResolution の値域は SSet。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::corollary "kerodon_2_4_4_4"
Kerodon Corollary 2.4.4.4（[Tag 00L4](https://kerodon.net/tag/00L4)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。coherent nerve の左随伴 ℭ : SSet → Cat\_Δ は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::proposition "kerodon_2_4_4_7"
Kerodon Proposition 2.4.4.7（[Tag 00L7](https://kerodon.net/tag/00L7)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。自由パス圏はあるが、グラフから定数単体圏への指定写像が path 圏の普遍性を満たす宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::definition "kerodon_2_4_4_9" (uses := "kerodon_1_1_0_6")
Kerodon Notation 2.4.4.9（[Tag 00L9](https://kerodon.net/tag/00L9)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。非退化単体と端点を指定した減少部分集合列の組 E(S,m) は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::theorem "kerodon_2_4_4_10" (uses := "kerodon_1_1_0_6, kerodon_1_2_3_13, kerodon_1_3_7_7, kerodon_2_4_4_9, kerodon_2_4_4_16")
Kerodon Theorem 2.4.4.10（[Tag 00LA](https://kerodon.net/tag/00LA)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。任意 S の path 圏からの豊穣関手を E(S,m) によるデータで特徴づける定理は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::proposition "kerodon_2_4_4_13"
Kerodon Proposition 2.4.4.13（[Tag 00LC](https://kerodon.net/tag/00LC)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。1骨格からの因子化と、自由パス圏から Path\[S\]₀ への同型は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::proposition "kerodon_2_4_4_15" (uses := "kerodon_1_1_0_6, kerodon_2_4_4_1")
Kerodon Proposition 2.4.4.15（[Tag 00LE](https://kerodon.net/tag/00LE)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。一般の半順序 Q の Path\[Q\] が N(Q) に対し普遍性を満たす定理は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::lemma_ "kerodon_2_4_4_16" (uses := "kerodon_1_3_7_8, kerodon_1_3_7_11, kerodon_2_4_4_9")
Kerodon Lemma 2.4.4.16（[Tag 00LF](https://kerodon.net/tag/00LF)）。対応表の状態：なし。

B6：pathPrefix/pathSuffix は経路の部分集合の切り分けという証明部品。原文は指定の u が三つの条件を満たす主張で、いずれの条件もこれらの型の結論ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathPrefix`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathSuffix`

:::

:::corollary "kerodon_2_4_4_18"
Kerodon Corollary 2.4.4.18（[Tag 0324](https://kerodon.net/tag/0324)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。途中点の上下の path 圏からの豊穣圏の押し出しの比較は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::corollary "kerodon_2_4_4_20"
Kerodon Corollary 2.4.4.20（[Tag 0326](https://kerodon.net/tag/0326)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。上下の押し出しを Path\[Q\] に入れる関手の一意な左逆は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

# 2.4.5 From Simplicial Categories to ∞-Categories

%%%
number := false
tag := "kerodon-2-4-5"
%%%

Kerodon [Tag 00LH](https://kerodon.net/tag/00LH)

*f-c-spaces.html — 4. $`N^{hc}` と quasicategory 性 — 4.3 局所 Kan でないと失敗する例*

開いた箱の包含は anodyne だが inner anodyne ではないので、Hom が quasicategory なだけでは延長できない。$`n=3`、$`i=1`：$`\mathrm{Hom}(0,3)` は頂点 $`\{0,3\},\{0,1,3\},\{0,2,3\},\{0,1,2,3\}` の正方形で、与えられるのは三辺 $`\{0,3\}\to\{0,1,3\}`、$`\{0,1,3\}\to\{0,1,2,3\}`、$`\{0,2,3\}\to\{0,1,2,3\}`。三角形 $`(\{0,3\},\{0,1,3\},\{0,1,2,3\})` は合成で埋まるが、残る三角形は辺 $`\{0,2,3\}\to\{0,1,2,3\}` と合成 $`\{0,3\}\to\{0,1,2,3\}` から欠けた辺 $`\{0,3\}\to\{0,2,3\}` を作る外側の horn $`\Lambda^2_2` で、その辺が可逆でないと埋まらない。Hom が ∞ 圏の単体的圏は (∞,2) 圏で、2 射の向きを忘れられないので coherent nerve は quasicategory にならない。

:::theorem "kerodon_2_4_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory")
Kerodon Theorem 2.4.5.1（[Tag 00LJ](https://kerodon.net/tag/00LJ)）。対応表の状態：本体にある。

仮定：単体圏 C で、任意の X,Y の sHom X Y が KanComplex（Kerodon と一致）。結論：SimplicialNerve C が Quasicategory、すなわちすべての内角を充填する（一致）。

*定理 3.6 （局所 Kan なら quasicategory）*

単体的圏 $`\mathcal C` のすべての射の単体的集合 $`\mathcal C(x,y)` が Kan 複体であるとき（$`\mathcal C` は局所 Kan であるという）、$`N^{hc}(\mathcal C)` は quasicategory である。

:::

:::definition "kerodon_2_4_5_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeSplitIso")
Kerodon Notation 2.4.5.2（[Tag 00LK](https://kerodon.net/tag/00LK)）。対応表の状態：本体にある。

仮定：任意の座標集合 I（Kerodon と一致）。結論：部分集合を包含で順序づけた Set I の nerve として I 立方体を得る。任意の座標 i の分離は残りの立方体と Δ¹ の積への同型（一致）。

:::

:::proposition "kerodon_2_4_5_4" (uses := "kerodon_1_1_0_6")
Kerodon Remark 2.4.5.4（[Tag 00LM](https://kerodon.net/tag/00LM)）。対応表の状態：なし。

B6：pathInteriorNerveIso は包含順の path と内部点集合の包含順の nerve の同型。原文の逆包含から補集合で得る特定同型・合成式との比較を含まないため別模型として none。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathInteriorNerveIso`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathInteriorEquiv`

:::

:::definition "kerodon_2_4_5_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeBoundary, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hollowCube") (uses := "kerodon_1_1_0_6, kerodon_2_4_5_2")
Kerodon Notation 2.4.5.5（[Tag 00LN](https://kerodon.net/tag/00LN)）。対応表の状態：一部。

B6：cubeBoundary の一定座標条件は全ての面の和という原文の境界を直接表す。hollowCube は指定座標の下面を欠く側だけで、二種類の hollow cube の両方は含まない。

:::

:::proposition "kerodon_2_4_5_8" (uses := "kerodon_1_1_0_6, kerodon_2_4_4_10, kerodon_2_4_4_16, kerodon_2_4_5_4, kerodon_2_4_5_5")
Kerodon Proposition 2.4.5.8（[Tag 00LR](https://kerodon.net/tag/00LR)）。対応表の状態：なし。

B6：pathThrough/pathFaceIso は包含順の経路部分の部品で、hornHollowHom\_extension の結論も Hom への延長。原文の Path\[Λ\]→Path\[Δ\] という特定関手の (a)〜(c) は直接述べない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceIso`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHollowHom_extension`

:::

:::proposition "kerodon_2_4_5_9"
Kerodon Proposition 2.4.5.9（[Tag 00LS](https://kerodon.net/tag/00LS)）。対応表の状態：なし。

B6：hornCompositionHom\_composition\_overlap は内角から作る Hom の面の整合性。任意の E と D の豊穣関手の延長集合の全単射とは対象・結論が異なる証明部品。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornCompositionHom_composition_overlap`

:::

:::corollary "kerodon_2_4_5_10" (uses := "kerodon_1_1_0_6")
Kerodon Corollary 2.4.5.10（[Tag 00LT](https://kerodon.net/tag/00LT)）。対応表の状態：なし。

B6：hornFilledFunctor と面の等式は包含順模型の充填関手を作るが、逆包含模型の指定の λ₀ とその制限条件を同一視する宣言がない。原文の全単射の方向とはまだ数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHollowHom_extension`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFilledFunctor`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFilledFunctor_face`

:::

:::theorem "kerodon_2_4_5_11" (lean := "SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpoint_zero_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIntervalEvaluation_trivialKanFibration")
Kerodon Theorem 2.4.5.11（[Tag 00LU](https://kerodon.net/tag/00LU)）。対応表の状態：一部。

B6：intervalEndpoint\_zero\_trivialKanFibration と kanIntervalEvaluation\_trivialKanFibration は Kan X から各端点評価が自明 Kan fibration となる向き。各評価の性質から Kan 性を得る逆向きは含まない。

:::

:::corollary "kerodon_2_4_5_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hollowCube_extension, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hollowCube_anodyne, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hollowCylinder_anodyne")
Kerodon Corollary 2.4.5.12（[Tag 00LV](https://kerodon.net/tag/00LV)）。対応表の状態：一部。

B6：hollowCube\_extension は指定座標の下面を欠く hollow cube から Kan X への任意の写像の延長を直接与える。原文の二つの延長のうち上面を含む側のみ。

:::

# 2.4.6 The Homotopy Category of a Simplicial Category

%%%
number := false
tag := "kerodon-2-4-6"
%%%

Kerodon [Tag 00LW](https://kerodon.net/tag/00LW)

:::definition "kerodon_2_4_6_1"
Kerodon Construction 2.4.6.1（[Tag 00LX](https://kerodon.net/tag/00LX)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。個々の sHom の π₀ は使われるが、それらを Hom とする単体圏のホモトピー圏の構成は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::proposition "kerodon_2_4_6_7"
Kerodon Proposition 2.4.6.7（[Tag 00M2](https://kerodon.net/tag/00M2)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。成分の比較補題はあるが、離散的な単体圏への関手を hC で一意に因子化する宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::corollary "kerodon_2_4_6_8"
Kerodon Corollary 2.4.6.8（[Tag 00M3](https://kerodon.net/tag/00M3)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。普通圏を定数単体圏とする包含への左随伴 h は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::proposition "kerodon_2_4_6_9"
Kerodon Proposition 2.4.6.9（[Tag 00M4](https://kerodon.net/tag/00M4)）。対応表の状態：なし。

B6：頂点・辺の全単射とホモトピー類の等式は比較を作る材料だが、原文の特定の U による圏同型の部分結論ではない。包含順/逆包含の nerve の比較も必要。

宣言：`SerrePositivity.EInfinity.Hammock.coherentEdge_homMk_eq_of_homotopy`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeEquiv`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv`

:::

:::proposition "kerodon_2_4_6_10" (uses := "kerodon_1_1_0_6, kerodon_2_4_6_13")
Kerodon Proposition 2.4.6.10（[Tag 00M5](https://kerodon.net/tag/00M5)）。対応表の状態：なし。

B6：coherentTriangleMappingEdge は長辺 h から合成 f≫g への辺で、原文は合成から h へのホモトピー。一般の Hom は Kan とも仮定しないので向きを反転できず、定値合成三角形だけも指定全単射を与えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct`、`SerrePositivity.KST.SConstruction.coherentTriangleMappingEdge`

:::

:::proposition "kerodon_2_4_6_12"
Kerodon Proposition 2.4.6.12（[Tag 00M7](https://kerodon.net/tag/00M7)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。内角の空洞立方体の補題はあるが、境界包含に沿う Path の全 Hom と境界立方体の表示は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::corollary "kerodon_2_4_6_13" (uses := "kerodon_1_1_0_6")
Kerodon Corollary 2.4.6.13（[Tag 00M8](https://kerodon.net/tag/00M8)）。対応表の状態：なし。

B6：次元2の候補も長辺から合成への逆向きの辺であり、原文の立方体境界の特定の λ₀ に沿う延長と同一視できない。次元特殊化だけではこの差は解消しない。

宣言：`SerrePositivity.KST.SConstruction.coherentTriangleMappingEdge`

:::

:::definition "kerodon_2_4_6_16"
Kerodon Construction 2.4.6.16（[Tag 02BJ](https://kerodon.net/tag/02BJ)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。豊穣 Hom のホモトピー圏を Hom 圏とする h₂C は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::proposition "kerodon_2_4_6_21"
Kerodon Proposition 2.4.6.21（[Tag 02BP](https://kerodon.net/tag/02BP)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。h₂C の指定写像に沿う単体関手の一意因子化は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

# 2.4.7 Example: Braid Monoids

%%%
number := false
tag := "kerodon-2-4-7"
%%%

Kerodon [Tag 00MZ](https://kerodon.net/tag/00MZ)

:::definition "kerodon_2_4_7_1" (lean := "CoxeterSystem, CoxeterMatrix")
Kerodon Definition 2.4.7.1（[Tag 00N0](https://kerodon.net/tag/00N0)）。対応表の状態：Mathlib にある。

仮定：群 W と生成元を添字づける型 B（Kerodon と一致。積の位数は CoxeterMatrix に持たせ、無限位数を 0 と記す）。結論：Coxeter 行列の表示で定めた群から W への生成元を指定する同型を与える型（一致）。

:::

:::definition "kerodon_2_4_7_3" (lean := "CoxeterSystem.length")
Kerodon Notation 2.4.7.3（[Tag 00N2](https://kerodon.net/tag/00N2)）。対応表の状態：Mathlib にある。

仮定：CoxeterMatrix M に対する CoxeterSystem M W と w : W（Kerodon と一致）。結論：w を指定生成元の積で表す語のうち最短の長さを Nat で返す（一致）。

:::

:::definition "kerodon_2_4_7_5"
Kerodon Construction 2.4.7.5（[Tag 00N4](https://kerodon.net/tag/00N4)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Coxeter 群内の braid word の等式はあるが、二乗関係を外した Artin 群と正モノイドの構成は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::definition "kerodon_2_4_7_6"
Kerodon Notation 2.4.7.6（[Tag 00N5](https://kerodon.net/tag/00N5)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。非単位元の自由モノイドに、積と長さの加法性で決まる細分順序を入れた単体モノイドは未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::theorem "kerodon_2_4_7_9"
Kerodon Theorem 2.4.7.9（[Tag 00N8](https://kerodon.net/tag/00N8)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。有限 Coxeter 系の正 braid モノイドに対する Deligne の主張は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::definition "kerodon_2_4_7_10"
Kerodon Notation 2.4.7.10（[Tag 00N9](https://kerodon.net/tag/00N9)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。群の普通 nerve はあるが、長さ加法性で切り出した B°W は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::definition "kerodon_2_4_7_11"
Kerodon Construction 2.4.7.11（[Tag 00NA](https://kerodon.net/tag/00NA)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。長さ加法的な語を区間ごとの積へ送り、BM(W) の coherent nerve に入れる写像は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::proposition "kerodon_2_4_7_12"
Kerodon Proposition 2.4.7.12（[Tag 00NB](https://kerodon.net/tag/00NB)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。BM(W) が B°W の path 圏を表す普遍性は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::corollary "kerodon_2_4_7_13"
Kerodon Corollary 2.4.7.13（[Tag 00NC](https://kerodon.net/tag/00NC)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Path\[B°W\] の自己射単体モノイドと正 braid モノイドの弱ホモトピー同値は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

