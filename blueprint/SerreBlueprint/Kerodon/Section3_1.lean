import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneKanReplacement
import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyClasses
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorRestrictionFibration
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.HomotopyDetection
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanSourceReplacement
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PrismCellPushout
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorExtensionSpace
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorSpace
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeJoinPrismCell
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeJoinPrismCoverage
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeJoinPrismInitialPushout
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeJoinPrismStage
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopyInverse
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakMappingSpaces
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead
import SerrePositivity.KST.SConstruction.AnodyneExtensionChoices

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "3.1 The Homotopy Theory of Kan Complexes" =>
%%%
number := false
tag := "kerodon-3-1"
%%%

Kerodon の 3.1 節（[Tag 00SZ](https://kerodon.net/tag/00SZ)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 3.1.1 Kan Fibrations

%%%
number := false
tag := "kerodon-3-1-1"
%%%

Kerodon [Tag 00T0](https://kerodon.net/tag/00T0)

:::definition "kerodon_3_1_1_1" (lean := "SSet.modelCategoryQuillen.fibration_iff, SSet.modelCategoryQuillen.J")
Kerodon Definition 3.1.1.1（[Tag 00T1](https://kerodon.net/tag/00T1)）。対応表の状態：Mathlib にある。

*主張*　単体集合の射は、$`n>0` のすべての角包含 $`\Lambda_i^n\subseteq\Delta^n` に対して右持ち上げ性をもつとき Kan ファイブレーションである。

仮定：任意の単体集合の射 p : X ⟶ S（Kerodon と一致）。結論：Fibration p は、すべての次元 n\>0 とすべての番号 i のホーン包含を集めた J に対する右持ち上げ性 J.rlp p と同値（一致）。

*定義 5.3 （fibration）*

- 名前　／　包含
- Kan fibration　／　$`\Lambda^n_i\subseteq\Delta^n`（$`n\ge1`、$`0\le i\le n`）

:::

# 3.1.2 Anodyne Morphisms

%%%
number := false
tag := "kerodon-3-1-2"
%%%

Kerodon [Tag 00UG](https://kerodon.net/tag/00UG)

*f-01-simplicial-kan.html — 1. 単体的集合の組合せ論（Simplicial） — 1.3 anodyne 射と inner anodyne 射*

Kan fibration に対して左持ち上げ性質を持つ射を *anodyne* といい、inner fibration に対して左持ち上げ性質を持つ射を *inner anodyne* という。

$$`\text{anodyne} = {}^{\text{⧄}}(\text{Kan fibration}),\qquad \text{inner anodyne} = {}^{\text{⧄}}(\text{inner fibration})`

- \`anodyneExtensions := (fibrations \_).llp\`、\`innerAnodyneExtensions := innerFibrations.llp\`（Mathlib）。

*f-02-model-free.html — 3. 道具 2：ホモトピーと anodyne 局所化 — 3.1 端点の包含は anodyne*

単体的集合 $`X` について、端点の包含 $`X \to \Delta^1 \times X`（$`0` 側・$`1` 側）は anodyne である
（\`endpoint\_zero\_anodyne\`・\`endpoint\_one\_anodyne\`、HomotopicalAlgebra/Simplicial/AnodyneIntervalEndpoints.lean:85・90）。
証明は、$`\Delta^0 \to \Delta^1` が anodyne であることと、anodyne と単射の pushout-product が anodyne であること（Mathlib）から出る。

*route-classification.html — 2. 段 0：単体的集合とホーン — 2.6（0.5）アノダイン写像*

*なぜ必要か*：実際の議論ではホーン以外の包含（$`\{0\}\hookrightarrow\Delta^n`、$`\{0\}\times K\hookrightarrow\Delta^1\times K` など）に対する持ち上げが要る。一つずつ確かめる代わりに、ホーンから形式的に作れる包含のクラスを考える。

*弱飽和クラス*：押し出し・超限合成・レトラクトで閉じたクラス。*基本補題*：任意のクラス $`P` について「全ての $`p\in P` に対して左持ち上げ性質を持つ写像」の全体は弱飽和（持ち上げ問題を一段ずつ解けば解が運べる）。よって生成元に対する持ち上げ性質から、その弱飽和閉包全体に対する持ち上げ性質が自動的に従う。

- 名前　／　生成元の弱飽和閉包　／　右持ち上げ性質を持つもの
- アノダイン　／　全てのホーン　／　Kan fibration
- 内アノダイン　／　内ホーン　／　内 fibration
- 左アノダイン　／　$`\Lambda^n_i`（$`0\le i\lt n`）　／　左 fibration

内アノダイン ⊂ 左アノダイン ⊂ アノダイン。\*\*ある写像 $`i` に対する $`p` の持ち上げ性質を示すには、(1) $`i` がアノダイン（$`i` だけの性質で一度示せば済む）、(2) $`p` が生成元に対して持ち上げ性質を持つ（定義そのもの）、の二つを確かめればよい\*\*。

*例*：

- $`\{0\}\hookrightarrow\Delta^2` は左アノダイン：$`\{0\}\hookrightarrow\Delta^{\{0,1\}}`（$`\Lambda^1_0`）、$`\Delta^{\{0,1\}}\hookrightarrow\Lambda^2_0`（辺 $`\{0,2\}` を $`\Lambda^1_0` の押し出しで付け足す）、$`\Lambda^2_0\hookrightarrow\Delta^2`。一般に $`\{0\}\hookrightarrow\Delta^n` も左アノダイン（始対象の包含）。したがって Kan・左 fibration は「底の 2 単体と頂点 0 の上の点から、頂点 0 がその点の 2 単体」を持ち上げる。右 fibration が持ち上げるのは $`\{2\}\hookrightarrow\Delta^2`。内アノダイン写像は頂点の上で全単射（内ホーンは全頂点を含む）なので $`\{0\}\hookrightarrow\Delta^2` は内アノダインでない。

- spine $`\mathrm{Sp}^n\hookrightarrow\Delta^n` は内アノダイン（Joyal）：$`n=2` は $`\Lambda^2_1`、$`n=3` は $`\Lambda^2_1` で $`\{0,2\},\{1,3\}` と面を足し、$`\{0,3\}` と面 $`\{0,1,3\}` を足して $`\Lambda^3_2`、最後に埋める。準圏では射の列から $`n` 単体が本質的に一意に決まる（最短路 §8 の「$`\mathrm{Corr}` の単体は spine で決まる」と同じ現象）。

- 非例：$`\partial\Delta^1\hookrightarrow\Delta^1` はアノダインでない（アノダインは弱同値）。$`\Lambda^2_0\hookrightarrow\Delta^2` は左アノダインだが内アノダインでない。

*Joyal の積の補題*（HTT Cor. 2.3.2.4、Prop. 2.1.2.7）：$`A\hookrightarrow B` が内（左）アノダイン、$`K\hookrightarrow L` が単射なら $`(A\times L)\sqcup_{A\times K}(B\times K)\hookrightarrow B\times L` も内（左）アノダイン。最小の例：$`\{0\}\hookrightarrow\Delta^1` と $`\partial\Delta^1\hookrightarrow\Delta^1` で「正方形から一辺を除いた三辺 ⊂ 正方形」（二つの 2 単体に分けてホーンを二回埋める）。

*帰結*（指数随伴 $`\mathrm{Hom}(A\times K,X)=\mathrm{Hom}(A,\mathrm{Fun}(K,X))` と組み合わせて）：

- 帰結　／　意味
- $`\mathcal C` が準圏なら $`\mathrm{Fun}(K,\mathcal C)` も準圏　／　$`\Lambda^n_i\to\mathrm{Fun}(K,\mathcal C)` の延長は $`\Lambda^n_i\times K\to\mathcal C` の延長で、$`\Lambda^n_i\times K\hookrightarrow\Delta^n\times K` は積の補題（$`\emptyset\hookrightarrow K`）で内アノダイン
- $`K\subseteq L` なら $`\mathrm{Fun}(L,\mathcal C)\to\mathrm{Fun}(K,\mathcal C)` は内 fibration　／　制限は fibration
- $`p` が左 fibration なら $`\mathrm{Fun}(L,E)\to\mathrm{Fun}(K,E)\times_{\mathrm{Fun}(K,B)}\mathrm{Fun}(L,B)` も左 fibration　／　相対的な関手空間も左 fibration
- さらに $`K\subseteq L` が左アノダインなら上は自明 Kan fibration　／　選択の空間は可縮

*「選択の空間が可縮」の具体的な意味*：左 fibration $`p`、$`e\in E`（$`b` の上）、$`u\colon b\to b'` について、$`q\colon\mathrm{Fun}(\Delta^1,E)\to E\times_B\mathrm{Fun}(\Delta^1,B)` の $`(e,u)` 上の fiber $`L(e,u)` を取る。頂点は $`e` を始点とする $`u` の持ち上げ、辺は二つの持ち上げの $`u` の上でのホモトピー（始点側は $`e` で一定の $`\Delta^1\times\Delta^1\to E`）。積の補題を $`\{0\}\hookrightarrow\Delta^1` と $`\partial\Delta^n\hookrightarrow\Delta^n` に使い指数随伴で戻すと $`q` は自明 Kan fibration、よって $`L(e,u)\to\Delta^0` も自明 Kan fibration。

- $`n`　／　$`\partial\Delta^n\to L(e,u)` が埋まる　／　意味
- 0　／　空から点　／　持ち上げが存在（輸送の存在）
- 1　／　二点を辺で結べる　／　二つの持ち上げは $`u` の上でホモトピック（正方形の三辺から右の辺＝$`E_{b'}` の中の同値と内部を埋める）
- 2　／　三本のホモトピーの三角形　／　ホモトピーの選び方も本質的に一意
- $`\ge3`　／　全ての球面　／　全次元で一意（＝可縮）

離散 opfibration では持ち上げの集合が一点、左 fibration では可縮な Kan 複体。「一意に存在」の ∞ 版。

*何を固定するか*：

- 固定　／　動く　／　空間　／　可縮か
- $`e` と $`u`　／　終点　／　$`L(e,u)`　／　可縮
- $`e` だけ　／　$`u` と終点　／　$`u` を動かした全体　／　可縮でない（$`b` から出る底の辺の空間と同値）
- なし　／　全て　／　$`\mathrm{Fun}(\Delta^1,E)`　／　可縮でない（$`q` が自明 fibration なので $`E\times_B\mathrm{Fun}(\Delta^1,B)` と同値）
- $`e`、$`u`、終点 $`e'`　／　辺だけ　／　$`u` 上の $`e\to e'` の辺　／　一般に可縮でない（$`\mathrm{Map}_{E_{b'}}(u_!e,e')` と同値、空のことも）

終点を固定しないのが正しい：輸送は「$`e` を $`u` に沿って押し出した先」を決める操作で、終点は結果として決まる（離散 opfibration でも終点は指定しない）。

:::definition "kerodon_3_1_2_1" (lean := "SSet.anodyneExtensions, SSet.anodyneExtensions_eq_retracts_transfiniteCompositions")
Kerodon Definition 3.1.2.1（[Tag 00UH](https://kerodon.net/tag/00UH)）。対応表の状態：Mathlib にある。

*主張*　無害射は、全ての正次元の角包含を含み、押し出し・レトラクト・超限合成で閉じた最小の射の族に属する単体集合の射である。

仮定：任意の単体集合の射 f（Kerodon と一致）。結論：anodyneExtensions は、定義上は Kan fibration に対する左持ち上げ性で、J の押し出し・超限合成のレトラクトで得る弱飽和閉包と一致する（一致）。

:::

:::proposition "kerodon_3_1_2_9"
Kerodon Proposition 3.1.2.9（[Tag 014D](https://kerodon.net/tag/014D)）。対応表の状態：Mathlib にある。

*主張*　単体集合の二つの単射の少なくとも一方が無害射なら、それらの押し出し積も無害射である。

仮定：単体集合の二単射と、少なくとも片方が anodyne であること（Kerodon と一致）。結論：二つの積を共通部分上で貼った押し出しから終域の積への比較包含が anodyne。左右の二通りを別の補題で与える（一致）。

宣言：`SSet.anodyneExtensions_pushoutObjObjι`、`SSet.anodyneExtensions_pushoutObjObjι'`、`SSet.anodyneExtensions_unionProd_ι`

:::

:::lemma_ "kerodon_3_1_2_10" (uses := "kerodon_1_1_0_6")
Kerodon Lemma 3.1.2.10（[Tag 00TG](https://kerodon.net/tag/00TG)）。対応表の状態：なし。

B6：anodyne 性は原文の指定射間の retract の射と往復恒等式を与えない。 候補：指定形状の積の部分複体の包含の anodyne 性は pairing で示される。ホーン包含からの指定のレトラクトは未確認。

宣言：`SSet.prodStdSimplex.anodyneExtensions_unionProd_ι`

:::

:::lemma_ "kerodon_3_1_2_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isPushout_prism_mono_cell") (uses := "kerodon_1_1_0_6")
Kerodon Lemma 3.1.2.11（[Tag 03X4](https://kerodon.net/tag/03X4)）。対応表の状態：一部。

*主張*　単体集合 $`X` が $`Y\subseteq X` と正次元単体 $`\sigma:\Delta^n\to X` の像との合併で、$`\sigma^{-1}(Y)=\Lambda_i^n` なら、その引き戻し正方形は押し出し正方形でもある。

B6：isPushout\_prism\_mono\_cell は原文の和と逆像の条件から同じ押し出し正方形を直接返す。セル σ に Mono を加える場合に限定。

:::

:::lemma_ "kerodon_3_1_2_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismCell_isPushout, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismStage_top, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismInitial_isPushout")
Kerodon Lemma 3.1.2.12（[Tag 00TH](https://kerodon.net/tag/00TH)）。対応表の状態：本体にある。

*主張*　$`n\geq0` に対し、$`\Delta^1\times\Delta^n` は $`(\Delta^1\times\partial\Delta^n)\cup(\{1\}\times\Delta^n)` から、順に $`i=0,\ldots,n` で $`\Lambda_{i+1}^{n+1}\subseteq\Delta^{n+1}` を押し出して得られる。

仮定：n : ℕ（Kerodon と一致）。結論：Δ¹×Δⁿ 内の増大列は最初が境界の積と終端面の押し出し、最後が全体で、k から k+1 は (n+1) 次元の k+1 番目のホーンの押し出し（一致）。

:::

# 3.1.3 Exponentiation for Kan Fibrations

%%%
number := false
tag := "kerodon-3-1-3"
%%%

Kerodon [Tag 00TJ](https://kerodon.net/tag/00TJ)

:::theorem "kerodon_3_1_3_1"
Kerodon Theorem 3.1.3.1（[Tag 00TK](https://kerodon.net/tag/00TK)）。対応表の状態：Mathlib にある。

*主張*　Kan ファイブレーション $`X\to S` と単射 $`A\to B` に対し、$`\operatorname{Fun}(B,X)\to\operatorname{Fun}(B,S)\times_{\operatorname{Fun}(A,S)}\operatorname{Fun}(A,X)` は Kan ファイブレーションである。

仮定：単射 i : A ⟶ B、Kan fibration p : X ⟶ S と内部 Hom の指定の引き戻し（Kerodon と一致。Lean は普遍性を持つ引き戻しの選択を明示）。結論：Xᴮ から Sᴮ ×\_(Sᴬ) Xᴬ への比較射が Fibration（一致）。

宣言：`SSet.fibration_pullbackObjObjπ`

:::

:::corollary "kerodon_3_1_3_2"
Kerodon Corollary 3.1.3.2（[Tag 00TL](https://kerodon.net/tag/00TL)）。対応表の状態：Mathlib にある。

*主張*　Kan ファイブレーション $`X\to S` と任意の単体集合 $`B` に対し、後合成 $`\operatorname{Fun}(B,X)\to\operatorname{Fun}(B,S)` は Kan ファイブレーションである。

仮定：任意の単体集合 B と Kan fibration p : X ⟶ S（Kerodon と一致）。結論：p による後合成 (ihom B).map p は Fibration（一致）。

宣言：`SSet.instFibrationMapIhom`

:::

:::corollary "kerodon_3_1_3_3"
Kerodon Corollary 3.1.3.3（[Tag 00TM](https://kerodon.net/tag/00TM)）。対応表の状態：Mathlib にある。

*主張*　Kan 複体 $`X` と単射 $`A\to B` に対し、制限 $`\operatorname{Fun}(B,X)\to\operatorname{Fun}(A,X)` は Kan ファイブレーションである。

仮定：単射 i : A ⟶ B、Kan 複体 X（Kerodon と一致）。結論：前合成 (MonoidalClosed.pre i).app X は Fibration（一致）。

宣言：`SSet.instFibrationAppPreOfMonoOfKanComplex`

:::

:::corollary "kerodon_3_1_3_4"
Kerodon Corollary 3.1.3.4（[Tag 00TN](https://kerodon.net/tag/00TN)）。対応表の状態：Mathlib にある。

*主張*　$`X` が Kan 複体なら、任意の単体集合 $`B` に対して $`\operatorname{Fun}(B,X)` も Kan 複体である。

仮定：任意の単体集合 B と Kan 複体 X（Kerodon と一致）。結論：内部 Hom (ihom B).obj X が KanComplex（一致）。

*定理 2.9 （$`\mathcal Kan` の射の単体的集合は Kan 複体）*

Kan 複体 $`X,Y` について、$`\mathcal Kan(X,Y)=\mathrm{Fun}(X,Y)` は Kan 複体である。

宣言：`SSet.instKanComplexObjIhom`

:::

:::theorem "kerodon_3_1_3_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.trivialKanFibration_pre_of_anodyne")
Kerodon Theorem 3.1.3.5（[Tag 014E](https://kerodon.net/tag/014E)）。対応表の状態：一部。

*主張*　無害射 $`A\to B` と Kan ファイブレーション $`X\to S` に対し、$`\operatorname{Fun}(B,X)\to\operatorname{Fun}(B,S)\times_{\operatorname{Fun}(A,S)}\operatorname{Fun}(A,X)` は自明な Kan ファイブレーションである。

B6：trivialKanFibration\_pre\_of\_anodyne は底 S が終対象のときの同じ制限射の自明 Kan 性。pullbackObjObjπ は p 自身が自明 Kan の場合も直接扱う。一般の底上の任意の Kan fibration の主張は含まない。

:::

:::corollary "kerodon_3_1_3_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.trivialKanFibration_pre_of_anodyne")
Kerodon Corollary 3.1.3.6（[Tag 00UT](https://kerodon.net/tag/00UT)）。対応表の状態：本体にある。

*主張*　$`A\to B` が無害射で $`X` が Kan 複体なら、制限 $`\operatorname{Fun}(B,X)\to\operatorname{Fun}(A,X)` は自明な Kan ファイブレーションである。

仮定：anodyne 射 i : A ⟶ B と Kan 複体 X（Kerodon と一致）。結論：Xᴮ → Xᴬ の前合成射は任意の単射に対する右持ち上げ性を持つ自明 Kan fibration（一致）。

:::

:::definition "kerodon_3_1_3_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace")
Kerodon Construction 3.1.3.7（[Tag 01AB](https://kerodon.net/tag/01AB)）。対応表の状態：本体にある。

*主張*　$`\operatorname{Fun}(B,X)` のうち、$`A\to X` への制限を固定する部分と、$`B\to S` への後合成を固定する部分を、それぞれ対応する写像のファイバーとして定める。両条件が整合する場合は、その二つのファイバーの共通部分も定める。

仮定：単体集合の写像 i, f, q, g と、両方の条件を課す場合の可換性 f≫q=i≫g（Kerodon と一致）。結論：後合成を g に固定した頂点ファイバーと、その中で i への制限を f に固定したファイバー。底を終対象とした場合に前合成だけのファイバーを得る（一致）。

*定義 10.1 （相対関手空間）*

単体的集合の射 $`r\colon K\to S`、$`q\colon X\to S` について、$`r` を $`\mathrm{Fun}(K,S)` の頂点とみて（$`K\times\Delta^0\cong K`）、ファイバー（定義 6.2）

$$`\mathrm{Fun}_{/S}(K,X)=\mathrm{Fun}(K,X)\times_{\mathrm{Fun}(K,S)}\Delta^0`

を相対関手空間という（$`q_*` の $`r` 上のファイバー。定義 2.3）。その $`n` 単体は $`q\circ f=r\circ\mathrm{pr}_K` をみたす射 $`f\colon K\times\Delta^n\to X` である。

:::

:::proposition "kerodon_3_1_3_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre_fibration, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace_isContractibleKan")
Kerodon Proposition 3.1.3.13（[Tag 01GK](https://kerodon.net/tag/01GK)）。対応表の状態：一部。

*主張*　単射 $`A\to B` と Kan ファイブレーション $`X\to S` による可換正方形の持ち上げの単体集合は Kan 複体である。$`A\to B` が無害射ならこの Kan 複体は可縮である。

B6：relativeFunctorExtensionSpace\_isContractibleKan は同じ指定境界と底を持つ延長空間の可縮 Kan 性を直接返す。i を left anodyne とする追加仮定で、Kan fibration は left fibration でもある。一般の anodyne i 全体の後半は含まない。

:::

:::corollary "kerodon_3_1_3_14" (lean := "SerrePositivity.KST.SConstruction.anodyneExtensionChoices_isContractibleKan")
Kerodon Corollary 3.1.3.14（[Tag 01GL](https://kerodon.net/tag/01GL)）。対応表の状態：一部。

*主張*　$`A\subseteq B` と Kan 複体 $`X` に対し、指定した $`A\to X` の $`B` への延長の単体集合は Kan 複体であり、包含が無害射なら可縮である。

B6：anodyneExtensionChoices\_isContractibleKan は原文後半の、i が anodyne の場合の指定延長空間の可縮 Kan 性を直接返す。単射だけの場合の前半を含まない。

:::

:::corollary "kerodon_3_1_3_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace_kanComplex")
Kerodon Corollary 3.1.3.15（[Tag 01GM](https://kerodon.net/tag/01GM)）。対応表の状態：本体にある。

*主張*　Kan ファイブレーション $`X\to S` と単体集合の射 $`B\to S` に対し、$`S` 上の $`B\to X` の単体集合は Kan 複体である。

仮定：写像 b : B ⟶ S と q : X ⟶ S（Lean が弱い：q は全ホーンの Kan fibration でなく LeftFibration で足りる）。結論：q による後合成の b 上のファイバー relativeFunctorSpace が KanComplex（一致）。

:::

# 3.1.4 Covering Maps

%%%
number := false
tag := "kerodon-3-1-4"
%%%

Kerodon [Tag 0219](https://kerodon.net/tag/0219)

:::definition "kerodon_3_1_4_1"
Kerodon Definition 3.1.4.1（[Tag 021A](https://kerodon.net/tag/021A)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。確認済み・なし。全ホーンに一意な持ち上げを要求する単体集合の被覆写像の型は未発見。位相・箙の被覆は別。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_1_4_7"
Kerodon Proposition 3.1.4.7（[Tag 021G](https://kerodon.net/tag/021G)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。確認済み・なし。相対内部 Hom の Kan fibration 性はあるが、一意な持ち上げを保つ被覆版は未発見。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_1_4_8"
Kerodon Corollary 3.1.4.8（[Tag 021H](https://kerodon.net/tag/021H)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。確認済み・なし。後合成の fibration 性はあるが、一意持ち上げの被覆版は未発見。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_1_4_9"
Kerodon Proposition 3.1.4.9（[Tag 021J](https://kerodon.net/tag/021J)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。確認済み・なし。位相被覆と特異単体集合はあるが、特異化が一意なホーン持ち上げを保つ宣言は未発見。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_1_4_12"
Kerodon Proposition 3.1.4.12（[Tag 021M](https://kerodon.net/tag/021M)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。確認済み・なし。単体写像による全引き戻し条件や、標準単体上の成分ごとの同型による被覆の特徴づけは未発見。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_1_4_14"
Kerodon Corollary 3.1.4.14（[Tag 021P](https://kerodon.net/tag/021P)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。確認済み・なし。単射に対する直和成分・被覆・Kan fibration の三条件の比較は未発見。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.1.5 The Homotopy Category of Kan Complexes

%%%
number := false
tag := "kerodon-3-1-5"
%%%

Kerodon [Tag 00TR](https://kerodon.net/tag/00TR)

*f-01-simplicial-kan.html — 1. 単体的集合の組合せ論（Simplicial） — 1.5 prism とホモトピー*

写像 $`f, g : X \to Y` の間の*ホモトピー*は、$`\Delta^1 \times X \to Y` で、両端が $`f, g` になるものである（Mathlib の \`SSet.Homotopy\`）。
ホモトピー同値 \`IsSimplicialHomotopyEquivalence f\`（InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/SimplicialHomotopyEquivalence.lean:52）は、逆向きの写像と両側のホモトピーがあることをいう。
prism $`\Delta^1 \times \Delta^n` の shuffle による分割は Mathlib にあり、端の包含 \`prismEndpoint\` は InfinityCategories/Kerodon/TheHomotopyTheoryOfInfinityCategories/IsomorphismsAndIsofibrations/PrismContraction.lean にある。

:::definition "kerodon_3_1_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex")
Kerodon Definition 3.1.5.1（[Tag 00TS](https://kerodon.net/tag/00TS)）。対応表の状態：本体にある。

*主張*　単体集合の二つの射 $`X\to Y` は、$`\operatorname{Fun}(X,Y)` の同じ連結成分に属するときホモトピックである。

仮定：任意の単体集合 X,Y と平行な射 f,g（Kerodon と一致）。結論：functorVertex が二射を内部 Hom の 0 単体に送り、SSet.π₀.mk の像の等式で同じ連結成分という関係を表せる（一致）。

:::

:::definition "kerodon_3_1_5_2" (lean := "SSet.Homotopy")
Kerodon Definition 3.1.5.2（[Tag 00TT](https://kerodon.net/tag/00TT)）。対応表の状態：Mathlib にある。

*主張*　$`f_0,f_1:X\to Y` の間のホモトピーは、各端 $`i=0,1` で $`f_i` に制限される射 $`\Delta^1\times X\to Y` である。

仮定：任意の単体集合 X,Y と平行な射 f₀,f₁（Kerodon と一致。相対版の部分複体は既定値 ⊥）。結論：X×Δ¹ から Y への射が両端点で f₀,f₁ となる構造（一致。Kerodon は積を Δ¹×X の順に書く）。

:::

:::proposition "kerodon_3_1_5_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge")
Kerodon Proposition 3.1.5.4（[Tag 00TU](https://kerodon.net/tag/00TU)）。対応表の状態：本体にある。

*主張*　単体集合の二つの射がホモトピックであることは、向きを問わずホモトピーを有限回つないで結べることと同値である。標的が Kan 複体なら、始点から終点へのひとつのホモトピーの存在と同値である。

仮定：任意の単体集合 X,Y と平行な射 f,g（Kerodon と一致。Kan 性は不要）。結論：写像空間の π₀ の等式は頂点間の辺関係の対称・反射・推移閉包。各辺と向き付きの区間ホモトピーを相互に変換するため、この閉包は原文の有限列の条件を表す（一致）。

:::

:::definition "kerodon_3_1_5_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex")
Kerodon Notation 3.1.5.9（[Tag 00TX](https://kerodon.net/tag/00TX)）。対応表の状態：本体にある。

*主張*　単体集合の射 $`f:X\to Y` のホモトピー類を、$`\pi_0\operatorname{Fun}(X,Y)` の元 $`[f]` と書く。

仮定：任意の単体集合の射 f : X ⟶ Y（Kerodon と一致）。結論：functorVertex f は Fun(X,Y) の 0 単体で、その SSet.π₀.mk による像が \[f\]（一致）。

:::

:::definition "kerodon_3_1_5_10" (lean := "SerrePositivity.SimplicialModel.HomotopyClasses.obj, SerrePositivity.SimplicialModel.HomotopyClasses.pre, SerrePositivity.SimplicialModel.HomotopyClasses.post") (uses := "kerodon_1_2_5_1")
Kerodon Construction 3.1.5.10（[Tag 00TY](https://kerodon.net/tag/00TY)）。対応表の状態：一部。

*主張*　Kan 複体のホモトピー圏の対象は Kan 複体、射は単体写像のホモトピー類であり、合成は写像の合成から誘導される。

B6：HomotopyClasses.obj は π₀ Fun(X,Y)、pre/post は代表の合成による写像を直接構成する。Kan に対象を限れば原文の Hom と前後合成の構成成分。同じ Hom を射とする束ねた圏そのものは含まない。

:::

# 3.1.6 The ∞-Category of Spaces

%%%
number := false
tag := "kerodon-3-1-6"
%%%

Kerodon [Tag 01YX](https://kerodon.net/tag/01YX)

*注意 （$`\mathcal S` の大きさ）*

$`\mathcal Kan` の対象は小さい Kan 複体で、その全体は $`\mathbb U` の部分集合として集合をなすが、小さくはない。したがって $`\mathcal S` は単体的集合だが小さくない。一方、小さい Kan 複体 $`X,Y` について $`\mathcal Kan(X,Y)=\mathrm{Fun}(X,Y)` は小さい（宇宙は直積と冪集合で閉じている）。

*f-c-spaces.html — 6. $`\mathcal S` の他の定義との比較*

- 定義　／　特徴づけ　／　得意なこと　／　他との同値に必要な定理
- (a) $`N^{hc}(\mathcal Kan)`　／　単体が具体的　／　単体の計算、写像空間　／　写像空間の比較定理（7）
- (b) 局所化 $`N(\mathcal Kan_0)[\mathrm{he}^{-1}]`　／　外向きの普遍性　／　1 圏の関手から $`\mathcal S` への関手を作る　／　$`N(\mathcal Kan_0)\to N^{hc}(\mathcal Kan)` が he での局所化
- (c) 普遍左 fibration　／　$`\mathrm{Fun}(B,\mathcal S)\simeq\mathrm{LFib}(B)`　／　straightening が定義から出る（HoTT の univalent universe にあたる）　／　存在の構成と、(a) との比較（straightening そのもの）
- (d) $`\mathrm{Cat}_\infty` の ∞ 亜群の充満部分圏　／　$`\mathrm{Cat}_\infty` が先にある　／　$`\mathcal S\subseteq\mathrm{Cat}_\infty` が定義から　／　$`\mathrm{Cat}_\infty` の写像空間の計算

(b) の $`\mathcal Kan_0` は Kan 複体と写像の普通の圏。(c) は Cisinski の本の流儀に近い。どれを定義にしても残りとの比較は重い定理で、(a)⇔(c) は straightening の同値定理そのもの、(a)⇔(b) は局所化の理論の応用。入門テキストで (a) を採る利点は $`\mathcal S` の単体を紙の上に書けることで、代償は写像空間の比較定理を最初に払うこと。

:::definition "kerodon_3_1_6_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.kanObject_simplicialCategory")
Kerodon Construction 3.1.6.1（[Tag 00TZ](https://kerodon.net/tag/00TZ)）。対応表の状態：本体にある。

*主張*　空間の無限圏を表す単体集合 $`S` を、Kan 複体の単体圏のホモトピー整合神経として定める。

仮定：固定した宇宙の単体集合（Kerodon と一致）。結論：Kan 複体を対象、内部 Hom を豊穣 Hom とする KanObject の coherent nerve が SpaceInfinity（一致。Lean の coherent nerve は Ch 2 で記録した包含順の規約）。

*定義 2.8 （Kan 複体のなす単体的圏 $`\mathcal Kan`）*

単体的圏 $`\mathcal Kan` を次で定める。

- 対象：小さい Kan 複体（定義 1.9、冒頭の規約）。

- 射の単体的集合：$`\mathcal Kan(X,Y)=\mathrm{Fun}(X,Y)`（定義 2.2）。

- 合成と恒等射：定義 2.5。

定理 2.6 によりこれは単体的圏である。

*定義 3.7 （空間の ∞ 圏 $`\mathcal S`）*

$`\mathcal S=N^{hc}(\mathcal Kan)` と定める（$`\mathcal Kan` は定義 2.8）。定理 2.9 により $`\mathcal Kan` は局所 Kan なので、定理 3.6 により $`\mathcal S` は quasicategory である。

:::

:::proposition "kerodon_3_1_6_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinity_quasicategory")
Kerodon Proposition 3.1.6.2（[Tag 01YY](https://kerodon.net/tag/01YY)）。対応表の状態：本体にある。

*主張*　空間の単体集合 $`S` は無限圏である。

仮定：SpaceInfinity を作る宇宙だけ（Kerodon と一致。個別の充填性の仮定はない）。結論：SpaceInfinity が Quasicategory（一致）。

:::

:::proposition "kerodon_3_1_6_3"
Kerodon Remark 3.1.6.3（[Tag 01YZ](https://kerodon.net/tag/01YZ)）。対応表の状態：なし。

B6：包含順の coherent nerve の構成であり、原文の逆包含 nerve と低次比較への同定がない。 候補：一般の単体圏で普通 nerve から coherent nerve への写像があり、KanObject に特殊化できる。単射性と全低次単体の比較は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent`

:::

:::definition "kerodon_3_1_6_9"
Kerodon Variant 3.1.6.9（[Tag 02BQ](https://kerodon.net/tag/02BQ)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。確認済み・なし。KanObject の単体的 Hom はあるが、各 Hom のホモトピー圏を持つ厳密双圏 h₂Kan は未発見。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.1.7 Homotopy Equivalences and Weak Homotopy Equivalences

%%%
number := false
tag := "kerodon-3-1-7"
%%%

Kerodon [Tag 00U1](https://kerodon.net/tag/00U1)

*f-02-model-free.html — 3. 道具 2：ホモトピーと anodyne 局所化 — 3.2 anodyne 局所化*

単体的集合の圏を、anodyne 射を可逆にして局所化した 1 圏を考える（Gabriel–Zisman の局所化）。

$$`\texttt{anodyneQ} : \mathbf{sSet} \to \mathbf{sSet}[\text{anodyne}^{-1}]`

（\`anodyneQ := SSet.anodyneExtensions.Q\`、HomotopicalAlgebra/Simplicial/AnodyneHomotopyLocalization.lean:101）。これは「空間のホモトピー圏」の一つの定義である。
§3.1 から、ホモトピックな写像は anodyneQ で同じ射になる（\`map\_homotopy\_eq\`、同 :82）。

:::definition "kerodon_3_1_7_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_1_5_1")
Kerodon Definition 3.1.7.1（[Tag 00U2](https://kerodon.net/tag/00U2)）。対応表の状態：一部。

*主張*　単体集合の射のホモトピー逆とは、両側の合成がそれぞれ恒等射にホモトピックになる逆向きの射である。そのような射が存在するとき元の射はホモトピー同値である。

B6：IsSimplicialHomotopyEquivalence は同じ f,g の両合成について一段の区間ホモトピーを持つ場合を直接表す。原文の有限鎖によるホモトピーより強い仮定に限定。

*定義 13.1 （ホモトピー同値）*

Kan 複体の射 $`f\colon X\to Y` がホモトピー同値であるとは、射 $`g\colon Y\to X` と射 $`h\colon X\times\Delta^1\to X`、$`k\colon Y\times\Delta^1\to Y` で、$`h` の $`X\times\{0\}`、$`X\times\{1\}` への制限がそれぞれ $`g\circ f`、$`\mathrm{id}_X`、$`k` の $`Y\times\{0\}`、$`Y\times\{1\}` への制限がそれぞれ $`f\circ g`、$`\mathrm{id}_Y` となるものが存在することをいう。Kan 複体 $`X,Y` の間にホモトピー同値があるとき、$`X` と $`Y` はホモトピー同値であるという。

:::

:::proposition "kerodon_3_1_7_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isSimplicialHomotopyEquivalence_of_postcomposition_piZero_bijective, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence.isWeakHomotopyEquivalence") (uses := "kerodon_1_1_0_6")
Kerodon Remark 3.1.7.6（[Tag 00U5](https://kerodon.net/tag/00U5)）。対応表の状態：一部。

*主張*　単体集合の射 $`f:X\to Y` がホモトピー同値であることは、任意の標的への写像のホモトピー類に前合成で全単射を誘導することと同値であり、任意の始域からの写像のホモトピー類に後合成で全単射を誘導することとも同値である。特に $`\pi_0(f)` は全単射となる。

B6：isSimplicialHomotopyEquivalence\_of\_postcomposition\_piZero\_bijective は原文の第三条件から第一条件への向きを Kan の始域・終域に限って直接返す。三条件一般の iff は含まない。

:::

:::proposition "kerodon_3_1_7_9" (uses := "kerodon_1_1_0_6")
Kerodon Proposition 3.1.7.9（[Tag 00U8](https://kerodon.net/tag/00U8)）。対応表の状態：なし。

B6：自然変換からのホモトピーは証明部品であり、随伴関手の nerve の逆と両側ホモトピーを結論していない。 候補：自然変換から nerve の単体ホモトピーを構成する補助宣言はある。任意の左・右随伴についてのホモトピー同値の結論は未確認。

宣言：`SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy`

:::

:::proposition "kerodon_3_1_7_10" (uses := "kerodon_1_1_0_6, kerodon_1_5_5_5")
Kerodon Proposition 3.1.7.10（[Tag 00U9](https://kerodon.net/tag/00U9)）。対応表の状態：なし。

B6：切断の存在と同じ底上のホモトピーは材料。ホモトピー逆の存在をまとめる直接の結論はなく、原文の有限鎖との比較も必要。 候補：一般の自明 Kan fibration に切断があり、同じ底上の二つの持ち上げはホモトピック。一般のホモトピー同値を一つにまとめた宣言は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_homotopy_over_trivialKanFibration`

:::

:::definition "kerodon_3_1_7_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence")
Kerodon Definition 3.1.7.12（[Tag 00UA](https://kerodon.net/tag/00UA)）。対応表の状態：本体にある。

*主張*　単体集合の射 $`X\to Y` は、任意の Kan 複体 $`Z` への写像のホモトピー類に前合成で全単射 $`\pi_0\operatorname{Fun}(Y,Z)\to\pi_0\operatorname{Fun}(X,Z)` を誘導するとき弱ホモトピー同値である。

仮定：任意の単体集合の射 f : X ⟶ Y（Kerodon と一致）。結論：すべての Kan 複体 Z に対して、前合成が π₀ Fun(Y,Z) から π₀ Fun(X,Z) への全単射となる述語（一致）。

:::

:::proposition "kerodon_3_1_7_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence.isWeakHomotopyEquivalence, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence.isSimplicialHomotopyEquivalence, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_iff_isSimplicialHomotopyEquivalence") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_1_7_6")
Kerodon Proposition 3.1.7.13（[Tag 00UB](https://kerodon.net/tag/00UB)）。対応表の状態：一部。

*主張*　単体集合のホモトピー同値は弱ホモトピー同値であり、両端が Kan 複体なら逆も成り立つ。

B6：前向きの型は一段のホモトピー逆を持つ f から同じ f の弱同値性を直接返す。有限鎖での逆だけより強い仮定。Kan の場合の逆向きも引用型にある。

:::

:::proposition "kerodon_3_1_7_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.homotopyEquivalence_pre_of_anodyne")
Kerodon Proposition 3.1.7.14（[Tag 00UP](https://kerodon.net/tag/00UP)）。対応表の状態：本体にある。

*主張*　単体集合の無害射は弱ホモトピー同値である。

仮定：任意の anodyne 射 f : A ⟶ B（Kerodon と一致。引用の前合成の検査では任意の Kan 標的 Z を固定）。結論：前合成がホモトピー同値で、その π₀ 写像は全単射。anodyne 局所化で f を反転した際にも同じ f の IsWeakHomotopyEquivalence を得る（一致）。

:::

:::proposition "kerodon_3_1_7_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence.precompose_kan, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_iff_precompose_kan")
Kerodon Proposition 3.1.7.17（[Tag 03PJ](https://kerodon.net/tag/03PJ)）。対応表の状態：本体にある。

*主張*　弱ホモトピー同値 $`X\to Y` と Kan 複体 $`Z` に対し、前合成 $`\operatorname{Fun}(Y,Z)\to\operatorname{Fun}(X,Z)` はホモトピー同値である。

仮定：任意の単体集合の弱ホモトピー同値 f : X ⟶ Y と Kan 複体 Z（Kerodon と一致）。結論：前合成 Fun(Y,Z) → Fun(X,Z) は区間ホモトピーでの両側逆を持つ（一致。Kan 写像空間では一段のホモトピーで足りる。Lean は全 Z での条件からの逆方向も与える）。

:::

:::proposition "kerodon_3_1_7_18"
Kerodon Proposition 3.1.7.18（[Tag 00ZZ](https://kerodon.net/tag/00ZZ)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。確認済み・なし。引用は単体加群の正規化の擬同型を検査する。単体集合の自由整数鎖写像の鎖ホモトピー同値は未発見。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_1_7_23"
Kerodon Proposition 3.1.7.23（[Tag 02L2](https://kerodon.net/tag/02L2)）。対応表の状態：本体にある。

*主張*　単体集合の二つの弱ホモトピー同値の直積も弱ホモトピー同値である。

仮定：単体集合の二写像 f,g が IsWeakHomotopyEquivalence（Kerodon と一致）。結論：点ごとの直積の写像 f ⊗ₘ g が IsWeakHomotopyEquivalence（一致）。

宣言：`SerrePositivity.EInfinity.Hammock.weakTensor`

:::

# 3.1.8 Fibrant Replacement

%%%
number := false
tag := "kerodon-3-1-8"
%%%

Kerodon [Tag 00UU](https://kerodon.net/tag/00UU)

*f-01-simplicial-kan.html — 1. 単体的集合の組合せ論（Simplicial） — 1.4 分解と置き換え*

small object argument から、どんな射も「anodyne の後に fibration」に分解できる。これを使って、任意の単体的集合を Kan 複体や quasicategory に置き換える。

- 置き換え　／　主張　／　宣言（いまの所在）
- inner anodyne と inner fibration への分解　／　任意の $`f : X \to Y` は $`X \xrightarrow{i} Z \xrightarrow{p} Y`（$`i` は inner anodyne、$`p` は inner fibration）と分解する　／　\`exists\_innerAnodyne\_innerFibration\_factorization\`（InfinityCategories/Kerodon/TheHomotopyTheoryOfInfinityCategories/InnerFibrations/InnerAnodyneReplacement.lean:39）
- quasicategory への置き換え　／　上で $`Y` が quasicategory なら $`Z` も quasicategory にできる。第 3 章の「局所化の存在」の証明で使う　／　\`exists\_quasicategory\_resolution\_over\`（同 :47）
- Kan 置換（関手的）　／　関手 $`R` と自然変換 $`X \to RX` で、$`X \to RX` は anodyne、$`RX` は Kan 複体　／　\`AnodyneKanReplacement.functor\`・\`unit\_anodyne\`・\`terminal\_rlp\`（HomotopicalAlgebra/Simplicial/AnodyneKanReplacement.lean:53〜68）
- Kan の Ex∞　／　$`\mathrm{Ex}^\infty X = \operatorname{colim}_n \mathrm{Ex}^n X` は Kan 複体で、$`X \to \mathrm{Ex}^\infty X` は anodyne。Ex∞ は有限極限を保ち、Kan fibration を保つ　／　\`exInfinity\_kanComplex\`・\`exInfinityUnit\_anodyne\`・\`exInfinity\_preservesFiniteLimits\`・\`exInfinity\_map\_rlp\`（KST/Comparison/ExInfinity\*）。Ex（一回分）は Mathlib の \`SSet.ex\`

二つの Kan 置換の違いは次のとおり。small object argument による置換は作り方が抽象的で、Ex∞ は具体的（細分を使う）。Ex∞ は有限極限を保つので、fiber や pullback と相性がよい。

*f-02-model-free.html — 2. 道具 1：small object argument と Kan 置換*

持ち上げ性質で定まる射の族 $`I` について、small object argument は、任意の射を「$`I` の pushout の超限合成」と「$`I` に対する右持ち上げ性質を持つ射」に、関手的に分解する。
$`I` を horn の包含の集合 $`J` にとれば、次が得られる。

$$`X \xrightarrow{\ \text{anodyne}\ } RX \xrightarrow{\ \text{Kan fibration}\ } \ast`

つまり、関手的な Kan 置換 $`X \to RX` である（\`AnodyneKanReplacement.factorization : FunctorialFactorizationData anodyneExtensions J.rlp\`、HomotopicalAlgebra/Simplicial/AnodyneKanReplacement.lean:44）。
これは small object argument（Mathlib）と anodyne の定義だけから作られており、モデル構造は使っていない。

関連する一般的な補題もある：\`generatedLeft\_map\`（HomotopicalAlgebra/Generated/FunctorClosure.lean:70）。余極限を保つ関手 $`F` が $`I` を $`W` に送るなら、$`I` から生成される射（$`{}^{\text{⧄}}(I^{\text{⧄}})`）もすべて $`W` に送る。
これは、宇宙の持ち上げが anodyne を保つこと、inner anodyne を保つことなどに使われる。

:::proposition "kerodon_3_1_8_1" (lean := "SerrePositivity.SimplicialModel.AnodyneKanReplacement.factorization")
Kerodon Proposition 3.1.8.1（[Tag 00UV](https://kerodon.net/tag/00UV)）。対応表の状態：本体にある。

*主張*　任意の単体集合の射は無害射の後に Kan ファイブレーションを合成したものに分解できる。分解は関手的に、かつ中間対象の関手がフィルター付き余極限を保つように選べる。

仮定：任意の単体集合の射 f : X ⟶ Y（Kerodon と一致）。結論：anodyneExtensions と全ホーン集合 J に対する RLP の FunctorialFactorizationData。中間対象と両射は f の可換正方形に関手的（一致）。

:::

:::corollary "kerodon_3_1_8_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit_anodyne")
Kerodon Corollary 3.1.8.2（[Tag 00UW](https://kerodon.net/tag/00UW)）。対応表の状態：本体にある。

*主張*　任意の単体集合からある Kan 複体への無害射が存在する。

仮定：任意の単体集合 A（Kerodon と一致）。結論：anodyneKanObject A は実際の Kan 複体であり、A からの anodyne な単位射を持つ（一致）。

:::

:::corollary "kerodon_3_1_8_5" (lean := "SSet.anodyneExtensions, SSet.anodyneExtensions_eq_llp_rlp")
Kerodon Corollary 3.1.8.5（[Tag 00X8](https://kerodon.net/tag/00X8)）。対応表の状態：Mathlib にある。

*主張*　単体集合の射が無害射であることは、全ての Kan ファイブレーションに対して左持ち上げ性をもつことと同値である。

仮定：任意の単体集合の射 f（Kerodon と一致）。結論：anodyneExtensions f と J.rlp の全射に対する左持ち上げ性が同値。J.rlp は Kan fibration のクラス（一致）。

:::

:::proposition "kerodon_3_1_8_6"
Kerodon Proposition 3.1.8.6（[Tag 012U](https://kerodon.net/tag/012U)）。対応表の状態：なし。

B6：引用は anodyne を反転する SSet 上の関手。原文は Kan 上の任意の関手で、二つの条件のいずれの含意も引用の結論ではない。 候補：SSet 上で anodyne を反転する関手はホモトピックな射を同じ射へ送る。Kan 上の関手の二条件の同値は未確認。

宣言：`SerrePositivity.SimplicialModel.AnodyneHomotopy.map_homotopy_eq`

:::

:::corollary "kerodon_3_1_8_7"
Kerodon Corollary 3.1.8.7（[Tag 012V](https://kerodon.net/tag/012V)）。対応表の状態：なし。

B6：homEquiv は対象ごとの局所化 Hom の比較で、原文の関手圏間の同型の構成ではない。 候補：anodyne 局所化で Kan 標的への射をホモトピー類と比較。hKan からの関手圏の指定同型は未発見。

宣言：`SerrePositivity.SimplicialModel.KanLocalizedRepresentatives.homEquiv`

:::

:::definition "kerodon_3_1_8_8"
Kerodon Variant 3.1.8.8（[Tag 012W](https://kerodon.net/tag/012W)）。対応表の状態：なし。

B6：自明 fibration の反転と局所化 Hom の比較は、指定の関手圏の同値という結論の成分でなく材料。 候補：anodyne 局所化の射の比較と自明 Kan fibration の反転はある。弱同値を反転する関手の圏と Fun(hKan,C) の同値は未確認。

宣言：`SerrePositivity.SimplicialModel.KanLocalizedRepresentatives.homEquiv`、`SerrePositivity.KST.SConstruction.map_isIso_of_trivialKanFibration`

:::

:::definition "kerodon_3_1_8_12" (uses := "kerodon_1_1_0_6, kerodon_3_1_8_1")
Kerodon Variant 3.1.8.12（[Tag 050L](https://kerodon.net/tag/050L)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。確認済み・なし。全ホーンの分解はあるが、閾値より高次のホーンだけを添付し低次の単体を保つ分解は未発見。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

