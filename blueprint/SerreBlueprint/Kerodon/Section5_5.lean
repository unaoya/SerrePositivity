import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.SimplicialNerve
import Mathlib.CategoryTheory.WithTerminal.Basic
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoreKan
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LeftUnstraighteningFiberValue
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceFiberVertices
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaces
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatSimplicial
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.QuasicategoryCore
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "5.5 The ∞-Category QC" =>
%%%
number := false
tag := "kerodon-5-5"
%%%

Kerodon の 5.5 節（[Tag 01YV](https://kerodon.net/tag/01YV)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 5.5.1 Digression: Slicing and the Homotopy Coherent Nerve

%%%
number := false
tag := "kerodon-5-5-1"
%%%

Kerodon [Tag 01Z5](https://kerodon.net/tag/01Z5)

:::definition "kerodon_5_5_1_1"
Kerodon Construction 5.5.1.1（[Tag 01Z6](https://kerodon.net/tag/01Z6)）。対応表の状態：なし。

Overは通常圏のsliceであり、原文の豊穣sliceのHomを単体集合の厳密fiberで作る構成への比較がない。通常圏の同名構成だけでは数えない。

宣言：`CategoryTheory.Over`

:::

:::definition "kerodon_5_5_1_3"
Kerodon Variant 5.5.1.3（[Tag 01Z8](https://kerodon.net/tag/01Z8)）。対応表の状態：なし。

Underは通常圏のcosliceであり、原文の豊穣cosliceの単体集合のHomの厳密fiberへの比較がない。

宣言：`CategoryTheory.Under`

:::

:::definition "kerodon_5_5_1_8" (lean := "CategoryTheory.WithInitial")
Kerodon Notation 5.5.1.8（[Tag 01ZD](https://kerodon.net/tag/01ZD)）。対応表の状態：一部。

WithInitialは通常圏の場合に原文の対象集合Ob(C)⊔\{X₀\}を直接構成する。単体豊穣Homとその合成まで含む錐の全構成ではない。

:::

:::definition "kerodon_5_5_1_9" (lean := "CategoryTheory.WithTerminal")
Kerodon Variant 5.5.1.9（[Tag 01ZE](https://kerodon.net/tag/01ZE)）。対応表の状態：一部。

WithTerminalは通常圏の場合に原文の対象集合Ob(C)⊔\{Y₀\}を直接構成する。単体豊穣Homと合成は含まない。

:::

:::definition "kerodon_5_5_1_15"
Kerodon Construction 5.5.1.15（[Tag 01ZL](https://kerodon.net/tag/01ZL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の slice・錐・単体豊穣 slice と一点・局所 Kan・hc nerve の比較を照合。豊穣 slice/coslice の錐から C への指定 contraction functor。単体集合の join の評価は豊穣な関手ではない。

:::

:::proposition "kerodon_5_5_1_16"
Kerodon Proposition 5.5.1.16（[Tag 01ZM](https://kerodon.net/tag/01ZM)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の slice・錐・単体豊穣 slice と一点・局所 Kan・hc nerve の比較を照合。豊穣錐上の関手と指定頂点の豊穣 slice/coslice への関手の対応。通常の Over/Under の普遍性では enriched functor を量化しない。

:::

:::definition "kerodon_5_5_1_17"
Kerodon Construction 5.5.1.17（[Tag 01ZN](https://kerodon.net/tag/01ZN)）。対応表の状態：なし。

coherentCosliceFiberComparisonは一つの豊穣Homからcosliceのfiberへの射。原文は豊穣slice/cosliceのcoherent nerve全体からの比較関手であり、指定射への制限との比較が引用型にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentCosliceFiberComparison`

:::

:::theorem "kerodon_5_5_1_21"
Kerodon Theorem 5.5.1.21（[Tag 01ZS](https://kerodon.net/tag/01ZS)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の slice・錐・単体豊穣 slice と一点・局所 Kan・hc nerve の比較を照合。豊穣 coslice の hc nerve 比較の圏同値性を合成 Hom の仮定から導く結論。単一の Kan ファイバーの比較は全 coslice の同値ではない。

:::

:::proposition "kerodon_5_5_1_22"
Kerodon Proposition 5.5.1.22（[Tag 01ZT](https://kerodon.net/tag/01ZT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の slice・錐・単体豊穣 slice と一点・局所 Kan・hc nerve の比較を照合。豊穣 coslice の指定の充満部分圏への制限での比較の充満忠実性。coherent nerve の後合成の関手性からはこの仮定付き判定が出ない。

:::

# 5.5.2 The ∞-Category of Pointed Spaces

%%%
number := false
tag := "kerodon-5-5-2"
%%%

Kerodon [Tag 01ZV](https://kerodon.net/tag/01ZV)

*f-01-simplicial-kan.html — 5. 基点付きの空間*

基点付き単体的集合は \`PointedSimplicialSet := PointedObject SSet\`（SerrePositivity/Spectra/PointedSimplicialSet/Basic.lean:35）。\`PointedObject\` はリポジトリ独自の定義で、Mathlib には基点付き単体的集合はない。

- 構成・結果　／　主張　／　宣言（いまの所在）
- smash 積と基点付き内部 Hom　／　smash 積で対称モノイダル閉圏になり、$`X \wedge - \dashv \mathrm{Map}_*(X, -)`　／　\`PointedObject.smash\`・\`smashHomAdjunction\`・\`internalHom\`（SerrePositivity/Spectra/Pointed・PointedSimplicialSet）
- 懸垂とループ　／　$`\Sigma X = S^1 \wedge X`、$`\Omega Y = \mathrm{Map}_*(S^1, Y)`、$`\Sigma \dashv \Omega`　／　\`suspension\`・\`loopSpace\`・\`suspensionLoopEquiv\`（KST/Spectra/SuspensionLoop.lean:30・37・51）
- Ω は Kan 複体を保つ　／　$`Y` が Kan なら $`\Omega Y` と $`\mathrm{Map}_*(X, Y)` も Kan　／　\`loopSpace\_kanComplex\`（同 :44）・\`basedHom\_kanComplex\`（PointedMapping.lean:57）
- 道空間 fibration　／　基点付き道空間 $`PY \to Y`（端点への写像）は Kan fibration で、$`PY` は可縮　／　\`basedPathSpace\`・\`pathEndpoint\_fibration\`（KST/Spectra/PathSpace.lean）
- Ω は道空間 fibration の fiber　／　$`\Omega Y \cong \mathrm{fib}(PY \to Y)`　／　\`loopBasedPathFiberIso\`（KST/Spectra/LoopPathFiber.lean:123）
- ループのホモトピー群　／　$`\pi_n(\Omega Y) \cong \pi_{n+1}(Y)`（$`n \ge 1`）　／　\`loopPositiveHomotopyEquiv\`（KST/Spectra/LoopHomotopyGroups.lean:42）

最後の同型は、道空間 fibration $`\Omega Y \to PY \to Y` の長完全列（§3.3）と $`PY` の可縮性から出る。これがスペクトラムの理論（Ω スペクトラム、KST/Spectra の本体）の出発点になる。

*unstraightening-analogy.html — 2. 「点付き」の三つの版*

点付き圏の射 $`(\mathcal C,c)\to(\mathcal D,d)` の取り方で、$`\mathcal C` 上の fiber が変わる。

- 射の定義　／　$`\mathcal C` 上の fiber
- 厳密：$`F(c)=d`　／　離散圏 $`\mathrm{Ob}\,\mathcal C`
- 擬（(2,1) 圏での coslice $`\mathrm{Cat}_{*/}`）：$`F` と同型 $`F(c)\cong d`　／　$`\mathcal C^{\simeq}`（core）
- lax：$`F` と射 $`F(c)\to d`　／　$`\mathcal C` そのもの

fiber をちょうど $`\mathcal C` にしたければ lax 版を使う。$`\mathrm{Cat}_*^{\mathrm{lax}}\to\mathrm{Cat}` は恒等関手の Grothendieck 構成そのもので、普遍 cocartesian fibration である。擬関手 $`F\colon B\to\mathrm{Cat}` に沿う引き戻しは $`\int F`。fiber は「点の選び方の圏」$`\mathrm{Fun}([0],\mathcal C)=\mathcal C` で、集合の場合の「点を選ぶ自由度」が射を含めた形に格上げされている。

\*\*∞ で $`\mathcal S` を使う理由\*\*：$`\mathcal S_*=\mathcal S_{*/}` の射は $`f\colon X\to Y` と $`Y` 内の道 $`f(x)\rightsquigarrow y` の組。$`Y` が ∞ 亜群なので擬と lax の区別が消え、coslice を取るだけで fiber が $`\mathrm{Map}(*,X)\simeq X` になる。$`\mathrm{Cat}_\infty` では単なる coslice $`(\mathrm{Cat}_\infty)_{*/}` の fiber は core $`\mathcal C^{\simeq}` にしかならず、lax 版を別に作る必要がある。

*unstraightening-analogy.html — 2. 「点付き」の三つの版 — 引き戻しの定義*

- *1 圏*：厳密な引き戻しと擬引き戻し（iso-comma）がある。(2,1) 圏としての正しい概念は後者だが、片方が isofibration（Grothendieck fibration は常にそう）なら両者は圏同値。普遍 fibration に沿う引き戻しは厳密なもので計算してよい。

- *∞*：正しいのはホモトピー引き戻し。準圏の模型では $`\mathcal S_*\to\mathcal S` が左 fibration（とくに categorical fibration）なので、単体的集合の厳密な引き戻しがホモトピー引き戻しを計算する。1 圏の「isofibration なら厳密でよい」と同じ構造である。

:::definition "kerodon_5_5_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity")
Kerodon Construction 5.5.2.1（[Tag 01ZW](https://kerodon.net/tag/01ZW)）。対応表の状態：本体にある。

仮定：Kan 複体の coherent nerve と点 Δ⁰（Kerodon と一致）。結論：PointedSpaceInfinity は SpaceInfinity の Δ⁰ を表す頂点の下の coslice（一致）。

*unstraightening.html — 1. 普遍左 fibration $`\mathcal S_\to\mathcal S`*

場所：F1/PointedSpaces（Kerodon Construction 5.5.2.1、Prop. 5.5.2.2）。$`\mathcal S_*=\mathcal S_{\ast/}` の対象は「空間 $`K` と点 $`\ast\to K`」で、射影は点を忘れる写像である。*左 fibration であることは、第 1 章の「quasicategory の coslice 射影は左 fibration」をそのまま使うだけ*で、新しい議論は要らない。

:::

:::proposition "kerodon_5_5_2_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceInfinity_quasicategory, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection_leftFibration")
Kerodon Proposition 5.5.2.2（[Tag 01ZX](https://kerodon.net/tag/01ZX)）。対応表の状態：本体にある。

仮定：点付き空間の coslice PointedSpaceInfinity とその射影（Kerodon と一致）。結論：PointedSpaceInfinity が Quasicategory、射影が LeftFibration（一致）。

*unstraightening.html — 1. 普遍左 fibration $`\mathcal S_\to\mathcal S`*

すべての unstraightening の元になるのは、一点空間 $`\ast\in\mathcal S` の下の coslice、つまり「点つき空間の ∞ 圏」である。

\`\`\`text
noncomputable def PointedSpaceInfinity : SSet.\{u + 1\} :=
  sliceUnder (SSet.yonedaEquiv.symm pointSpaceVertex.\{u\})
noncomputable def pointedSpaceProjection : PointedSpaceInfinity.\{u\} ⟶ SpaceInfinity.\{u\}
instance pointedSpaceProjection\_leftFibration : LeftFibration pointedSpaceProjection.\{u\}
\`\`\`

*unstraightening.html — 1. 普遍左 fibration $`\mathcal S_\to\mathcal S` — fiber は空間そのもの*

\`\`\`text
noncomputable def pointedSpaceFiberValueEquivalence (s : SpaceInfinity.\{u\} \_⦋0⦌) :
    QCatEquivalence (vertexFiber pointedSpaceProjection s)
      ((SSet.uliftFunctor.\{u + 1, u\}).obj (spaceInfinityObject s).obj)
\`\`\`

$`\mathcal S` の頂点 $`s`（Kan 複体 $`K` を表す）上の fiber は $`K` と同値（F1/LeftUnstraighteningFiberValue）。証明の流れは次のとおり。

1. coslice $`\mathcal S_{\ast/}` の $`s` 上の fiber は、左 pinched 写像空間 $`\mathrm{Map}^L_{\mathcal S}(\ast,s)` と同型（Core の coslice の fiber の計算、F1/PointedSpaceMappingSpaces）。

2. 左の写像空間を右の写像空間に移す（第 2 章の \`pinchedHomLeftRightEquivalence\`）。

3. coherent nerve の写像空間は元の単体的圏の Hom と同値（\`coherentHomEquivalence\`）。$`\mathcal S` の場合、それは Kan 複体の関手単体集合 $`\mathrm{Fun}(\Delta^0,K)=K`。

つまり「$`\mathcal S_*\to\mathcal S` の fiber が $`K` になる」のは、「$`\ast` から $`K` への写像の空間は $`K` そのもの」ということの言い換えである。

:::

:::proposition "kerodon_5_5_2_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberValueEquivalence, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv")
Kerodon Proposition 5.5.2.6（[Tag 02S2](https://kerodon.net/tag/02S2)）。対応表の状態：一部。

pointedSpaceFiberValueEquivalenceは各Sの頂点で、原文の輸送の値となるfiberとそのKan複体の同値を直接与える。豊穣関手の逆であるためのHom作用と自然性は含まない。

:::

:::proposition "kerodon_5_5_2_8"
Kerodon Proposition 5.5.2.8（[Tag 0200](https://kerodon.net/tag/0200)）。対応表の状態：なし。

coherentPointedFiberComparisonは各Kのfiberからの射。原文の全coslice比較関手の制限がこの射という比較がなく、その全関手の同値を直接結論しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentPointedFiberComparison`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentPointedFiberComparison_isQCatEquivalence`

:::

:::corollary "kerodon_5_5_2_10"
Kerodon Corollary 5.5.2.10（[Tag 0202](https://kerodon.net/tag/0202)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：点付き Kan の hc nerve・各ファイバーの比較・通常群と nerveを照合。点付き Kan の hc nerve と S\_\* のホモトピー圏の同型。KST の pointedKanHomotopyClass\_comparison は指定辺の同値関係を比較するが両圏の比較同型を構成しない。

:::

:::proposition "kerodon_5_5_2_13"
Kerodon Proposition 5.5.2.13（[Tag 0205](https://kerodon.net/tag/0205)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：点付き Kan の hc nerve・各ファイバーの比較・通常群と nerveを照合。G↦BG の N(Group)→S\_\* の充満忠実性。KST の群の nerve の座標計算と通常 nerve の充満忠実性は点付き空間の写像空間を比較しない。

:::

# 5.5.3 The ∞-Category of ∞-Categories

%%%
number := false
tag := "kerodon-5-5-3"
%%%

Kerodon [Tag 0208](https://kerodon.net/tag/0208)

*03-straightening.html — 2. ∞ 圏を作る ∞ 圏：coherent nerve*

- ∞ 圏　／　Lean　／　単体的圏の対象　／　Hom（Kan 複体）　／　場所
- $`\mathcal S`　／　\`SpaceInfinity\`　／　小さい Kan 複体　／　関手単体集合　／　F1/CatInfinity
- Cat\<sub\>∞\</sub\>　／　\`CatInfinity\`　／　小さい quasicategory（\`QCat\`）　／　関手 ∞ 圏の core　／　F1/CatInfinity、F1/QCatSimplicial
- $`\mathrm{LFib}(B)`　／　\`LeftFibrationInfinity B\`　／　$`B` 上の小さい左 fibration　／　相対関手空間 $`\mathrm{Fun}_{/B}(X,Y)`　／　F1/LeftFibrationInfinity
- $`\mathrm{coCart}(B)`　／　\`CocartesianFibrationInfinity B\`　／　$`B` 上の cocartesian fibration　／　cocartesian 辺を保つ相対関手の空間の core　／　F1/CocartesianFibrationInfinity

\`\`\`text
def SpaceInfinity : SSet.\{u + 1\} := SimplicialNerve KanObject.\{u\}
noncomputable def CatInfinity : SSet.\{u + 1\} := SimplicialNerve QCat.\{u\}
def SpaceInfinityFunctor (C : SSet.\{u + 1\}) : SSet.\{u + 1\} := (ihom C).obj SpaceInfinity.\{u\}
\`\`\`

宇宙の扱い

対象が宇宙 $`u` の単体的集合なので、それらを集めた ∞ 圏は宇宙 $`u+1` に入る。関手 ∞ 圏 $`\mathrm{Fun}(B,\mathcal S)` を作るには、底 $`B` も同じ宇宙に持ち上げる必要がある。そのため主定理には \`(SSet.uliftFunctor.\{u + 1, u\}).obj B\` が現れる。宇宙の持ち上げと、その逆向きの「反映」（F1/Universe\*、26 ファイル）は、この層の目立たないが避けられない作業になっている。

*06-catinfty-ind-presentable.html — 1. Cat∞ の写像空間と極限*

Cat\<sub\>∞\</sub\> は coherent nerve として定義されていた（第 3 章）。その写像空間は関手 ∞ 圏の core と同値である。

\`\`\`text
def catInfinityMappingEquivalence (X Y : QCat.\{u\}) :
    QCatEquivalence ((SSet.uliftFunctor.\{u + 1, u\}).obj (catInfinityFunctorCore X Y))
      (catInfinityMappingSpace X Y)
\`\`\`

場所：F2/CatMappingSpace。coherent nerve の写像空間が元の単体的圏の Hom と同値であることの一般論（\`coherentHomEquivalence\`）の特殊化である。

*coherent-nerve-diagrams.html — 1. 定義 — 基本定理と $`\mathcal S`・$`\mathrm{Cat}_\infty`*

- $`\mathrm{Cat}_\infty=N^{hc}(\mathrm{QCat}^\Delta)`：$`\mathrm{Map}(\mathcal C,\mathcal D)=\mathrm{Fun}(\mathcal C,\mathcal D)^{\simeq}`。$`\mathrm{Fun}(\mathcal C,\mathcal D)` は Kan ではないので core を取る。そのため $`\mathrm{Cat}_\infty` は非可逆な自然変換を忘れており、補章 2 §2 で coslice の fiber が core にしかならなかった原因はここにある。

*f-c-spaces.html — 5. $`\mathcal S` と $`\mathrm{Cat}_\infty`*

- $`\mathcal S=N^{hc}(\mathcal Kan)` の単体　／　中身
- 対象　／　小さい Kan 複体
- 射　／　写像
- 2 単体　／　ホモトピー $`h\simeq gf`
- 高次　／　ホモトピーの間のホモトピー

- $`hN^{hc}(\mathcal C)` は Hom が $`\pi_0\mathcal C(x,y)` の圏（2 単体が $`h\Rightarrow gf` の道なので $`[h]=[gf]`）。よって $`\mathcal S` の同値はホモトピー同値。

- $`\mathcal S` 自身は一つ上の宇宙に入るが、局所小。形式化：\`SpaceInfinity := SimplicialNerve KanObject\`（F1/Categories/CatInfinity.lean）、関手 ∞ 圏 \`SpaceInfinityFunctor C\`。

- $`\mathrm{Cat}_\infty`：$`\mathcal{QC}at` の Hom を core $`\mathrm{Fun}(C,D)^{\simeq}`（Kan 複体）にして $`N^{hc}`。core にするのは 4.2 を使うため（4.3 の理由で $`\mathrm{Fun}(C,D)` 全体では局所 Kan でない）。

*route-6ff-definition.html — 5. まず $`\mathrm{Cat}_\infty` とその対称モノイダル構造*

- 段　／　内容　／　重い入力
- 1　／　$`\mathfrak C[\Delta^n]`（写像空間 $`N(P_{i,j})`、和集合による合成）と $`\Delta` 上の関手性、$`N^{hc}(\mathcal C)_n=\mathrm{Hom}_{\mathrm{sCat}}(\mathfrak C[\Delta^n],\mathcal C)`（補章 3）　／　なし（組合せ論）
- 2　／　$`\mathrm{QCat}^\Delta`：対象は（小さい）準圏（宇宙を固定し $`\mathrm{Cat}_\infty` は一段大きい）、$`\mathrm{Map}(\mathcal C,\mathcal D)=\mathrm{Fun}(\mathcal C,\mathcal D)^{\simeq}`（core は全ての辺が同値な単体からなる最大の部分）　／　$`\mathrm{Fun}(\mathcal C,\mathcal D)` が準圏（Joyal、内アノダインが積で閉じる）
- 3　／　単体的圏で Hom が Kan：合成は内部 Hom の合成の制限で結合律・単位律は厳密。準圏の写像は同値を保ち、積の準圏で成分ごとの同値は同値なので core は core に移る　／　Joyal の定理（ホモトピー圏が亜群の準圏は Kan）
- 4　／　Kan 豊穣ならナーブは準圏（Cordier–Porter、HTT Prop. 1.1.5.10）：内ホーンの持ち上げは立方体 $`(\Delta^1)^{n-1}` を空洞の立方体から埋める問題　／　空洞の立方体の包含がアノダイン
- 5（次の段）　／　有限積：$`\mathrm{QCat}^\Delta` で $`\mathcal C\times\mathcal D` は厳密な積（$`\mathrm{Fun}(X,\mathcal C\times\mathcal D)^{\simeq}=\mathrm{Fun}(X,\mathcal C)^{\simeq}\times\mathrm{Fun}(X,\mathcal D)^{\simeq}`）。ナーブでも積になる　／　写像空間の比較定理（$`N^{hc}(\mathcal C)` の写像空間は $`\mathcal C(x,y)`）

段 5 のあと、cartesian 構造の一般的構成（HA §2.4.1）で $`\mathrm{Cat}_\infty^\times` を得る（次に扱う）。

*route-6ff-definition.html — 6. $`\mathrm{QCat}^\Delta` の記号と core の有無*

流れは「一般論として $`N^{hc}` を定義し、それを $`\mathrm{QCat}^\Delta` に適用して $`\mathrm{Cat}_\infty` を定義する」。

*route-6ff-definition.html — 6. $`\mathrm{QCat}^\Delta` の記号と core の有無 — 6.1 上付きの $`\Delta`*

$`\Delta` は「単体的圏として見たもの」（Hom に単体的集合の構造を入れたもの、HTT の記法）。「小さい」は対象の大きさ、$`\Delta` は Hom の構造についての記号で独立。

- 記号　／　何か　／　Hom
- $`\mathrm{QCat}`　／　普通の圏　／　関手の集合
- $`\mathrm{QCat}^\Delta`　／　単体的圏　／　$`\mathrm{Fun}(\mathcal C,\mathcal D)^{\simeq}`（0 単体は関手、1 単体は自然同値、…）。0 単体だけ取ると $`\mathrm{QCat}`

*普通の圏では足りない*：$`N(\mathrm{QCat})` では、準圏の同値 $`F` は $`GF\simeq\mathrm{id}` が等号でないので可逆な辺にならず、自然変換の情報もない。$`\mathrm{QCat}^\Delta` では自然同値が Hom の 1 単体として入り、$`N^{hc}` で 2 単体（補章 3 の $`H_{012}`）になって $`F` が可逆な辺になる。同値を同値として扱うために Hom の高次構造が要る。同じ記法：$`\mathrm{Kan}`（$`\mathcal S=N^{hc}(\mathrm{Kan})`）、HTT の $`\mathrm{Cat}_\infty^\Delta`（Def. 3.0.0.1）。

*route-6ff-definition.html — 6. $`\mathrm{QCat}^\Delta` の記号と core の有無 — 6.2 $`\mathrm{Cat}_\infty` の射と写像空間*

- $`\mathrm{QCat}^\Delta` の Hom を $`\mathrm{Fun}^{\simeq}` にするのは*定義*。

- $`N^{hc}` の*辺*は単体的関手 $`\mathfrak C[\Delta^1]\to\mathrm{QCat}^\Delta` で、$`\mathrm{Map}(0,1)=\Delta^0` なので、二つの準圏と $`\mathrm{Fun}^{\simeq}` の 0 単体、すなわち*関手そのもの*（定義を計算した結果）。

- *写像空間* $`\mathrm{Map}_{\mathrm{Cat}_\infty}(\mathcal C,\mathcal D)`（pinched Hom など）は単体ごとには $`\mathrm{Fun}^{\simeq}` と一致しないが、ホモトピー同値（写像空間の比較定理、\`coherentHomEquivalence\`）。

- 低次元の確認：$`\mathrm{Map}_{\mathrm{Cat}_\infty}` の道 $`F\to G` は辺 $`\{1,2\}` が恒等な 2 単体で、データは $`f_{01}=F`、$`f_{12}=\mathrm{id}`、$`f_{02}=G` と $`\mathrm{Map}(0,2)` の辺 $`G\Rightarrow F`、つまり $`\mathrm{Fun}^{\simeq}` の 1 単体（自然同値）。

*route-6ff-definition.html — 6. $`\mathrm{QCat}^\Delta` の記号と core の有無 — 6.3 core を取るかどうか*

- 　／　core を取る　／　core を取らない
- Hom　／　$`\mathrm{Fun}^{\simeq}`（Kan 複体）　／　$`\mathrm{Fun}`（準圏）
- 関手の間の 2 射　／　可逆な自然変換だけ　／　全ての自然変換
- 得られるもの　／　$`\mathrm{Cat}_\infty`：$`(\infty,1)` 圏　／　$`\mathrm{Cat}_{(\infty,2)}`：$`(\infty,2)` 圏
- $`N^{hc}` が準圏か　／　なる　／　ならない（空洞の立方体の包含はアノダインだが内アノダインでなく、非可逆な辺を逆にたどれない）。scaled 単体的集合など別のモデルが要る
- 1 圏での類似　／　$`(2,1)` 圏としての $`\mathrm{Cat}`　／　2 圏としての $`\mathrm{Cat}`

*失われるもの*：$`\mathrm{Cat}_\infty` の中で非可逆な自然変換が高次の射として見えない。lax な構成（補章 2 で coslice の fiber が core になった）、lax 関手（補章 7 §1：$`B\to\mathrm{Cat}_\infty` は擬関手の ∞ 版）、随伴の単位・余単位。*残るもの*：$`\mathrm{Cat}_\infty` はデカルト閉で $`\mathrm{Fun}(\mathcal C,\mathcal D)` が内部 Hom として対象になるので、非可逆な自然変換はその中の射として取り出せる。随伴は $`\Delta^1` 上の両側 fibration（対象のレベル）で表され、lax な情報は fibration 側で扱う。

*六関手形式との関係*：基底変換・射影公式の比較写像は可逆でなければならないので、値は core を取った $`\mathrm{Cat}_\infty` で足りる。随伴まで一つの関手で書こうとすると $`(\infty,2)` 圏が現れる（Gaitsgory–Rozenblyum）。Mann・Scholze は右随伴の存在を性質として課して $`(\infty,2)` 圏を避ける。

*route-classification.html — 5. 段 3：$`\mathcal S=N^{hc}(\mathrm{Kan})` と写像空間の比較定理 — 5.5（3.5）$`\mathrm{Cat}_\infty` の場合*

$`\mathrm{Cat}_\infty=N^{hc}(\mathrm{QCat}^\Delta)`、Hom は $`\mathrm{Fun}(\mathcal C,\mathcal D)^{\simeq}`（Kan、3.3）。3.3 の定理から $`\mathrm{Map}_{\mathrm{Cat}_\infty}(\mathcal C,\mathcal D)\simeq\mathrm{Fun}(\mathcal C,\mathcal D)^{\simeq}`。合成は関手の合成（core が積を保つことを使う）、$`h\mathrm{Cat}_\infty` は準圏と自然同値類、同値は ∞ 圏の同値。

*core で失うもの*：$`\mathrm{Fun}(\mathcal C,\mathcal D)` は Kan でないので $`N^{hc}` が準圏にならず（3.1）、core を取ると非可逆な自然変換が消える。$`\mathrm{Cat}_\infty` は $`(\infty,2)` 圏の $`(\infty,1)` 部分。随伴・lax pullback・cocartesian の分類では $`\mathrm{Fun}(\Delta^1,-)` や fibration の持ち上げ性質で取り戻す。

*点で表現される関手は core*：$`\mathrm{Map}_{\mathrm{Cat}_\infty}(\Delta^0,\mathcal C)\simeq\mathcal C^{\simeq}`。$`(\mathrm{Cat}_\infty)_{\Delta^0/}\to\mathrm{Cat}_\infty` は fiber $`\mathcal C^{\simeq}` の左 fibration で、定理 II の普遍 cocartesian fibration $`\mathcal Z`（fiber は $`\mathcal C` そのもの）にはならない。coslice の射は「$`F` と同値 $`F(x)\simeq y`」で、$`\mathcal Z` では「$`F` と非可逆な射 $`F(x)\to y`」が要る（F1 の README にも明記）。

\*\*$`\mathcal S\subset\mathrm{Cat}_\infty`\*\*：Kan 複体では $`\mathrm{Fun}(K,L)^{\simeq}=\mathrm{Fun}(K,L)` なので充満忠実な包含。

- 　／　$`\mathcal S`　／　$`\mathrm{Cat}_\infty`
- 写像空間　／　$`\mathrm{Fun}(K,L)`　／　$`\mathrm{Fun}(\mathcal C,\mathcal D)^{\simeq}`
- core の必要　／　なし　／　あり
- 点で表現される関手　／　恒等　／　core
- 点の coslice　／　普遍左 fibration　／　左 fibration にしかならない

*Lean での扱い*：\`QCat\`、\`qCat\_sHom\_kanComplex\`（F1/Categories/QCatSimplicial）、\`CatInfinity\`、\`catInfinityFunctor\_quasicategory\`（F1/Categories/CatInfinity）、\`quasicategoryCoreProduct\`、\`quasicategoryCoreFunctor\_laxMonoidal\`（F1/Categories/CoreProduct）、比較定理 \`coherentHomEquivalence\`。

*route-classification.html — 5. 段 3：$`\mathcal S=N^{hc}(\mathrm{Kan})` と写像空間の比較定理 — 5.6（3.6）大きさ（宇宙）の扱い*

- 対象　／　大きさ
- Kan 複体、準圏　／　宇宙 $`u`
- $`\mathcal S_u=N^{hc}(\mathrm{Kan}_u)`、$`\mathrm{Cat}_{\infty,u}`　／　宇宙 $`u+1`
- $`\mathrm{Map}_{\mathcal S_u}(K,L)\simeq\mathrm{Fun}(K,L)`　／　宇宙 $`u`（局所的に小さい）
- $`\mathrm{LFib}(B)`（全空間が $`u`）　／　宇宙 $`u+1`

- *底が小さいとき*：$`\mathrm{Fun}(B,\mathcal S_u)` には $`B` を $`u+1` に持ち上げる（同型を保つだけ）。強い形は $`\mathrm{LFib}_u(B)\simeq\mathrm{Fun}(B,\mathcal S_u)`。

- *底が大きいとき*：普遍左 fibration $`\mathcal S_{u,*}\to\mathcal S_u` は fiber が $`u`、全空間は $`u+1`。一般の $`B` では「$`\mathcal S_u` は fiber が*本質的に* $`u`-小さい左 fibration を分類する」と述べる（fiber $`\mathrm{Hom}^L(\Delta^0,K)` は $`K` と同値だが等しくない）。

- *選択の独立性*：小さい代表を選ぶので、その選択によらないことも示す必要がある。

*Lean での扱い*：F1 の README に同じ規約（$`u` の対象の coherent nerve は $`u+1`、小さい底では宇宙持ち上げを明示、本質的に小さい場合は代表への同値と選択独立性を証明）。\`leftStraighteningInfinityEquivalence\` の型は \`QCatEquivalence (LeftFibrationInfinity B) (SpaceInfinityFunctor (SSet.uliftFunctor.obj B))\`。小ささ F1/Coherent/MapSmallness、本質的に小さい場合 \`essentiallySmallLeftStraighteningRepresentation\`、\`essentiallySmallLeftStraighteningComparison\_isPrecompositionEquivalence\`（F1/StraighteningLeft/EssentiallySmallStraightening）。

*段 3 で押さえること*：局所 Kan な単体的圏の $`N^{hc}` は準圏（内ホーンの延長は蓋のない箱から立方体への延長で、アノダイン）。$`hN^{hc}(D)=\pi_0D`。写像空間の比較定理：$`\mathrm{Hom}^L_{N^{hc}\mathcal C}(X,Y)` は $`\Phi(K)=\mathfrak C\Sigma K` の右随伴で、$`\Phi(\Delta^n)` は $`\Delta^n` を太らせたもの（$`\rho` が圏同値）なので $`\mathcal C(X,Y)` とホモトピー同値。よって $`\mathrm{Map}_{\mathcal S}(K,L)\simeq\mathrm{Fun}(K,L)`、合成も一致、$`\mathrm{Map}_{\mathcal S}(\Delta^0,-)` は恒等。$`\mathrm{Cat}_\infty` では $`\mathrm{Fun}(\mathcal C,\mathcal D)^{\simeq}` で、点で表現される関手は core（coslice は普遍 cocartesian fibration にならない）。大きさは宇宙 $`u` と $`u+1` で管理し、大きい底では本質的に小さい fiber を扱う。

:::definition "kerodon_5_5_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCat_sHom_kanComplex, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCore_kanComplex, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCat_simplicialCategory, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCat_sHom") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Construction 5.5.3.1（[Tag 0209](https://kerodon.net/tag/0209)）。対応表の状態：本体にある。

QuasicategoryObjectとQCatは小さい準圏を対象とし、qCat\_sHomはHomがFunctor空間のcoreに一致すると明示する。qCat\_simplicialCategoryはcore関手で合成を移送し、CatInfinityはそのcoherent nerve。原文の全構成を直接与える。

:::

:::proposition "kerodon_5_5_3_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinity_quasicategory, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCore_kanComplex, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCat_sHom_kanComplex")
Kerodon Proposition 5.5.3.3（[Tag 020B](https://kerodon.net/tag/020B)）。対応表の状態：本体にある。

仮定：小さい ∞ 圏の単体豊穣圏 QCat の coherent nerve（Kerodon と一致）。結論：CatInfinity が Quasicategory（一致）。

:::

:::proposition "kerodon_5_5_3_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCore_kanComplex") (uses := "kerodon_1_4_0_1, kerodon_4_4_3_1")
Kerodon Remark 5.5.3.9（[Tag 05Q1](https://kerodon.net/tag/05Q1)）。対応表の状態：一部。

quasicategoryCoreFunctorは原文のcoreの対象・通常の射への作用を直接与え、準圏上では値がKan。豊穣Hom上の作用とcoherent nerve間の射への組立ては含まない。

:::

:::definition "kerodon_5_5_3_11" (uses := "kerodon_1_4_0_1")
Kerodon Variant 5.5.3.11（[Tag 03UT](https://kerodon.net/tag/03UT)）。対応表の状態：なし。

CatInfinity.\{u\}は宇宙による小ささ。原文の指定κのκ-smallを満たす頂点で張るfull subcategoryとκ⁺の型への対応がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity`

:::

:::definition "kerodon_5_5_3_13" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1")
Kerodon Variant 5.5.3.13（[Tag 03UV](https://kerodon.net/tag/03UV)）。対応表の状態：なし。

SpaceInfinity.\{u\}は宇宙版であり、原文の数値κとκ⁺で指定したKan複体のfull subcategoryへの比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity`

:::

:::proposition "kerodon_5_5_3_15"
Kerodon Proposition 5.5.3.15（[Tag 06T5](https://kerodon.net/tag/06T5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：n＝0・通常圏の nerve・QC の対角・完全忠実性・切断と小ささを照合。QC の射としての n-truncation と対象対の写像空間の条件。CatInfinity の fully faithful は写像空間の同値に関する別述語。

:::

:::corollary "kerodon_5_5_3_16"
Kerodon Corollary 5.5.3.16（[Tag 06T6](https://kerodon.net/tag/06T6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：n＝0・通常圏の nerve・QC の対角・完全忠実性・切断と小ささを照合。QC 内の mono と、充満忠実性や像での同型の条件との同値。SSet.Mono は各次数での集合の単射。

:::

:::corollary "kerodon_5_5_3_17"
Kerodon Corollary 5.5.3.17（[Tag 04W6](https://kerodon.net/tag/04W6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：n＝0・通常圏の nerve・QC の対角・完全忠実性・切断と小ささを照合。充満忠実な F を QC の辺として見たときの ∞ 圏の mono 性。fully faithful は F 自体の写像空間だけに関する。

:::

:::corollary "kerodon_5_5_3_19"
Kerodon Corollary 5.5.3.19（[Tag 06T7](https://kerodon.net/tag/06T7)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：n＝0・通常圏の nerve・QC の対角・完全忠実性・切断と小ささを照合。QC の対象としての C の n-truncation と局所 n-truncation を結ぶ同値条件。通常の coskeletal や π 群の型では QC の写像空間を評価しない。

:::

:::corollary "kerodon_5_5_3_21"
Kerodon Corollary 5.5.3.21（[Tag 05EW](https://kerodon.net/tag/05EW)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：n＝0・通常圏の nerve・QC の対角・完全忠実性・切断と小ささを照合。QC の対象の n-truncation から局所 n-truncation への含意と条件付きの逆。局所条件だけを述べる補題では QC の対象としての述語がない。

:::

# 5.5.4 The ∞-Bicategory of ∞-Categories

%%%
number := false
tag := "kerodon-5-5-4"
%%%

Kerodon [Tag 020J](https://kerodon.net/tag/020J)

:::definition "kerodon_5_5_4_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryObject_enrichedCategory, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryObject_simplicialCategory, CategoryTheory.SimplicialNerve")
Kerodon Construction 5.5.4.1（[Tag 020K](https://kerodon.net/tag/020K)）。対応表の状態：本体にある。

仮定：小さな ∞ 圏を QuasicategoryObject として束ねる。SimplicialNerve は任意の単体豊穣圏を取れる（Kerodon と一致）。結論：quasicategoryObject\_enrichedCategory は Hom に内部 Hom Fun(C,D) を取り、SimplicialNerve をこの豊穣圏に適用すると太字 QC の単体集合を得る（一致）。

:::

:::proposition "kerodon_5_5_4_2" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_1_5_3_7, kerodon_5_4_8_1")
Kerodon Proposition 5.5.4.2（[Tag 020L](https://kerodon.net/tag/020L)）。対応表の状態：なし。

CatInfinityはHomのcoreを取った局所Kanな圏のnerve。原文の太字QCはcoreを取る前の関手準圏をHomに持つ別の対象であり、その∞-bicategory性ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity`

:::

:::definition "kerodon_5_5_4_9"
Kerodon Variant 5.5.4.9（[Tag 03UX](https://kerodon.net/tag/03UX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：局所 Kan・core の場合・濃度と universe lift・通常双圏と Duskinを照合。本質的 κ-small な対象で張る太字 QC\_\{\<κ\} の ∞-bicategory。宇宙上限の lift と、任意の濃度 κ での部分圏を区別した。

:::

# 5.5.5 ∞-Categories with a Distinguished Object

%%%
number := false
tag := "kerodon-5-5-5"
%%%

Kerodon [Tag 020S](https://kerodon.net/tag/020S)

*f-06-straightening.html — 6. 普遍 cocartesian fibration $`\mathcal Z` — 6.1 定義と役割*

- 対象は小さい ∞ 圏とその対象の組 $`(A,a)`。射 $`(A,a)\to(B,b)` は関手 $`F\colon A\to B` と $`B` の射 $`f\colon F(a)\to b` の組で、$`f` は可逆とは限らない。

- 射影 $`(A,a)\mapsto A`。cocartesian 辺は $`f` が可逆なもの。$`A` 上のファイバーは $`A`。

- $`\mathrm{Un}(G)=B\times_{\mathrm{Cat}_\infty}\mathcal Z`。すべての cocartesian fibration がこの形になることが straightening の本質的全射性。1 圏では恒等関手の Grothendieck 構成 $`\mathrm{Cat}^{\mathrm{lax}}_*\to\mathrm{Cat}`。

- 空間値の $`\mathcal S_*` では対応する射が $`F(a)\simeq b` で、これが「すべての辺が cocartesian」に対応する。単なる coslice $`(\mathrm{Cat}_\infty)_{*/}` のファイバーは core $`A^{\simeq}` にしかならない。

:::definition "kerodon_5_5_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex")
Kerodon Construction 5.5.5.1（[Tag 020T](https://kerodon.net/tag/020T)）。対応表の状態：本体にある。

仮定：小さな ∞ 圏の圏 CatInfinity と、その頂点としての Δ⁰（Kerodon と一致）。結論：sliceUnder は指定した図式を固定する join の延長を束ねる。Δ⁰ を表す pointKanObject の基礎単体集合を CatInfinity の頂点に取り、原文の QC の coslice を得る（一致）。

:::

:::proposition "kerodon_5_5_5_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinity_quasicategory, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderProjection_leftFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnder_quasicategory")
Kerodon Proposition 5.5.5.2（[Tag 020U](https://kerodon.net/tag/020U)）。対応表の状態：本体にある。

仮定：Quasicategory X と図式 p:K→X（Lean が弱い：CatInfinity の一点に限らず任意の図式）。結論：sliceUnder\_quasicategory は coslice の ∞ 圏性、sliceUnderProjection\_leftFibration は X への射影の左ファイブレーション性（一致）。

:::

:::proposition "kerodon_5_5_5_6"
Kerodon Proposition 5.5.5.6（[Tag 020Y](https://kerodon.net/tag/020Y)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：空間値に制限・一点の QC coslice と輸送・普通の双圏の Pithを照合。点付き QCat の hc nerve と QC\_\* の全空間を結ぶ比較の ∞ 圏同値。relativeHomCosliceComparison は left fibration 分類圏の固定対象上の比較。

:::

:::definition "kerodon_5_5_5_8"
Kerodon Construction 5.5.5.8（[Tag 0210](https://kerodon.net/tag/0210)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：空間値に制限・一点の QC coslice と輸送・普通の双圏の Pithを照合。太字 QC の Δ⁰ 上の coslice としての太字 QC\_Obj。通常の QC の coslice では 2-射の情報を落とす。

*f-06-straightening.html — 6. 普遍 cocartesian fibration $`\mathcal Z` — 6.3 Kerodon の構成：$`f` を 2 射に置く*

Kerodon Construction 5.5.5.8。Hom を関手 ∞ 圏 $`\mathrm{Fun}(A,B)` 全体とする単体的圏の coherent nerve（∞-bicategory）の中で、点 $`\Delta^0` の下の coslice（join スライス）をとり、底を pith（可逆な 2 射の部分、つまり $`\mathcal{QC}`）に制限する。$`f\colon F(a)\to b` は 2 射 $`F\circ a\Rightarrow b` として厳密な構造に入る。∞-bicategory の理論（豊穣化された coherent nerve が ∞-bicategory になること、その中のスライス）が前提になる。

:::

:::proposition "kerodon_5_5_5_9" (uses := "kerodon_1_1_0_6, kerodon_5_4_3_1, kerodon_5_4_3_4, kerodon_5_5_4_2")
Kerodon Proposition 5.5.5.9（[Tag 0211](https://kerodon.net/tag/0211)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：空間値に制限・一点の QC coslice と輸送・普通の双圏の Pithを照合。太字 QC\_Obj が ∞-bicategory で太字 QC への射が interior fibration。普通の coslice 射影は interior を述べない。

:::

:::definition "kerodon_5_5_5_10" (uses := "kerodon_5_4_5_1")
Kerodon Definition 5.5.5.10（[Tag 0212](https://kerodon.net/tag/0212)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：空間値に制限・一点の QC coslice と輸送・普通の双圏の Pithを照合。太字 QC\_Obj の Pith としての QC\_Obj。quasicategory core は Pith と違い可逆辺で切る。

:::

:::proposition "kerodon_5_5_5_11" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_4_5_6, kerodon_5_4_7_10, kerodon_5_4_7_11, kerodon_5_5_5_9")
Kerodon Proposition 5.5.5.11（[Tag 0213](https://kerodon.net/tag/0213)）。対応表の状態：なし。

pointedSpaceProjectionの全空間は空間のcoslice。原文はQCの対象を分類する全空間であり、空間側が指定四角のpullbackである比較なしには同じ射の特殊化ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection_leftFibration`

:::

:::proposition "kerodon_5_5_5_14" (uses := "kerodon_5_1_4_1, kerodon_5_2_8_9, kerodon_5_4_9_2, kerodon_5_5_5_11")
Kerodon Proposition 5.5.5.14（[Tag 02S5](https://kerodon.net/tag/02S5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：空間値に制限・一点の QC coslice と輸送・普通の双圏の Pithを照合。QC\_Obj→QC の homotopy transport と hQC→hQCat の指定した同値。一般の homotopyTransport はこの普遍 fibration を指定しない。

:::

