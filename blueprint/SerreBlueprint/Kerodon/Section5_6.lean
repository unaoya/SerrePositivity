import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Bicategory.Grothendieck
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import Mathlib.CategoryTheory.Grothendieck
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InitialParametrizedPointTransport
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.Isofibration
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RelativeFunctorInverse
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CovariantRepresentableInfinity
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.HomInfinityBifunctor
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningEssentialSurjectivity
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningInfinityEquivalence
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraightening
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningFiberIso
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianInnerAnodynePullback
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RepresentableUnstraighteningIdentity

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "5.6 Classification of Cocartesian Fibrations" =>
%%%
number := false
tag := "kerodon-5-6"
%%%

Kerodon の 5.6 節（[Tag 027M](https://kerodon.net/tag/027M)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

*定義 11.2 （小さいファイバー）*

単体的集合の射 $`q\colon E\to B` が小さいファイバーをもつとは、$`B` のすべての頂点 $`b` について、ファイバー $`E_b`（定義 6.2）が小さい（冒頭の規約）ことをいう。

*注意 （直観と大きさ）*

$`\mathrm{St}(q)` は頂点 $`b` をファイバー $`E_b` に、辺 $`b\to b'` を左 fibration の持ち上げで得られる $`E_b\to E_{b'}` に送る関手である。$`\mathcal S` の対象は小さい Kan 複体なので、値が $`\mathcal S` に入るためにファイバーが小さいことを仮定する。$`B` は quasicategory でなくてよく、大きさも問わない。

*03-straightening.html — 3. 主定理（空間値）*

\`\`\`text
def leftStraighteningInfinityMap (B : SSet.\{u\}) :
    LeftFibrationInfinity B ⟶ SpaceInfinityFunctor ((SSet.uliftFunctor.\{u + 1, u\}).obj B)

lemma leftStraighteningInfinityMap\_isQCatEquivalence (B : SSet.\{u\}) \[Quasicategory B\] :
    IsQCatEquivalence (leftStraighteningInfinityMap B)
\`\`\`

場所：F1/LeftStraighteningAllBases（構成）、F1/LeftStraighteningInfinityEquivalence（同値）。同値の証明には、第 2 章の判定「充満忠実かつ本質的全射」を使う。

*03-straightening.html — 4. 証明の経路 — 第二段：一般の底への帰着*

$`N(\Delta_{/B})` は通常の圏の nerve なので、第一段が使える。$`B` 上の左 fibration を $`\mathrm{fv}` で引き戻して straightening すると、$`W` を反転する関手 $`N(\Delta_{/B})\to\mathcal S` が得られる。これを局所化の普遍性で $`B` へ降ろしたもの（\`transportUliftFunctorDescent\`）が、一般の底の分類写像 \`leftStraighteningInfinityMap B\` である。

本質的全射性は上で見たとおり一般の底で示されているので、残るのは充満忠実性である。同値性は次の判定に帰着する（F1/LeftStraighteningFirstVertexCriterion）。

\`\`\`text
lemma leftStraighteningInfinityMap\_isQCatEquivalence\_iff\_firstVertexBaseChange (B : SSet.\{u\}) :
    IsQCatEquivalence (leftStraighteningInfinityMap B) ↔
      IsFullyFaithful (leftFibrationInfinityBaseChange (transportSimplexFirstVertexMap B))
\`\`\`

つまり、「左 fibration を $`\mathrm{fv}` で引き戻す操作が充満忠実」であればよい。これは相対関手空間への引き戻しの作用の同値性として示され（F1/LeftFibrationBaseChangeFullyFaithful）、宇宙を持ち上げた側で示したものを元の宇宙へ反映して閉じる（F1/LeftFibrationFirstVertexUlift、F1/UniverseRelativePullbackReflection）。

*f-06-straightening.html — 2. 空間値版の主経路（完成）*

主定理は、任意の小さい quasicategory $`B` について $`\mathrm{LFib}(B)\simeq\mathrm{Fun}(B,\mathcal S)`。HTT と違い、「fibration → 関手」の向きの写像を直接 ∞ 圏の射として作り、充満忠実かつ本質的全射で同値を示す。モデル構造は使わない。

- 部品　／　内容　／　Lean・場所（旧シリーズの記述）　／　状態
- 両辺の ∞ 圏　／　$`\mathcal S`、$`\mathrm{Cat}_\infty`、$`\mathrm{LFib}(B)` はすべて Kan 豊穣な単体的圏の coherent nerve。宇宙が一つ上がる　／　SpaceInfinity、CatInfinity、LeftFibrationInfinity（F1/CatInfinity ほか）　／　済
- 第一段：普通の圏の脈体 $`N(C)` の底　／　strict transport：$`c\mapsto\mathrm{Fun}_{/N(C)}(N(C_{c/}),X)`。$`\{c\}\hookrightarrow N(C_{c/})` は left anodyne なので、始対象への制限は trivial Kan fibration で、値は $`X_c` と同値。$`c` と $`X` について厳密に関手的なので、単体的関手から coherent nerve の写像を作る　／　leftStraighteningCoherentMap（F1/StrictTransport\*）　／　済
- 第一段の同値　／　充満忠実（豊穣関手の Hom 比較）と本質的全射（unstraightening の余単位）　／　leftStraighteningCoherentMap\_isQCatEquivalence　／　済
- 第二段：一般の底　／　最初の頂点への写像 $`\mathrm{fv}\colon N(\Delta_{/B})\to B` は始点を保つ辺での局所化（骨格に沿った帰納法、$`B` は quasicategory でなくてよい）。第一段の関手を局所化の普遍性で $`B` に降ろす　／　transportSimplexFirstVertexMap\_isLocalization、leftStraighteningInfinityMap　／　済
- 一般の底の同値　／　本質的全射性は一般の底で直接、充満忠実性は最初の頂点の底変換による判定に帰着　／　leftStraighteningInfinityMap\_isQCatEquivalence　／　済
- unstraightening　／　普遍左 fibration の引き戻し。ファイバー、底変換との厳密な可換性、写像空間の比較　／　leftUnstraightening ほか　／　済
- Map の関手性と Yoneda　／　$`\mathrm{Tw}(C)\to C^{\mathrm{op}}\times C` は左 fibration。これを straightening して Hom 関手を作る（Kerodon §8.2〜8.3 と同じ）　／　twistedArrowHomInfinity、yonedaInfinityMap\_isFullyFaithful　／　済

Map の関手性の三つの作り方

- 単体的圏 $`\mathfrak C[C]` の厳密な合成を使い、Kan 化して $`N(\mathcal Kan)` へ（HTT 5.1.3）。値が $`\mathrm{Hom}^R` と一致することに HTT §2.2 の比較が要る。

- twisted arrow を straightening する。いまの形式化はこれ。

- 関手にせず fibration のまま扱う（Cisinski の本）。$`\mathcal S` は普遍左 fibration の底として作る。

底が quasicategory でない一般の単体的集合の場合は、主張としては入っていない。quasicategory への置き換え $`B\hookrightarrow B'`（inner anodyne）で移れる。$`\mathrm{Fun}(B',\mathcal S)\to\mathrm{Fun}(B,\mathcal S)` は $`\mathcal S` が quasicategory なので同値で、$`\mathrm{LFib}(B')\to\mathrm{LFib}(B)` は分類写像の延長から同値（Kerodon 5.6.7 と同じ型の議論）。

*f-06-straightening.html — 3. Kerodon の方法との比較*

Kerodon（5.6 節）は Cat∞ 値を本命として扱い、空間値はその特殊な場合として得る。

1. 普遍 cocartesian fibration $`V\colon\mathcal{QC}_{\mathrm{Obj}}\to\mathcal{QC}` を用意する。

2. unstraightening $`\int_{\mathcal C}F=\mathcal C\times_{\mathcal{QC}}\mathcal{QC}_{\mathrm{Obj}}` が主役。

3. 主定理 5.6.0.2：表現と同値の組全体の Kan 複体 $`\mathrm{TW}(\mathcal E/\mathcal C)`（transport witness）が可縮。

4. 証明（5.6.9）は底の骨格に沿った帰納法。$`\mathrm{TW}(\mathcal E/-)` は骨格の pushout を Kan fibration に沿った引き戻しに送るので、単体の場合に帰着する。$`\Delta^0`、$`\Delta^1`（5.5.5.14 を使う）を直接示し、$`k\ge 2` は inner horn への制限が trivial fibration であることで低次元に帰着する。

5. まず同値類の全単射を得て、ホモトピー圏の同値（7.4.2）、∞ 圏の同値へと後で引き上げる。

- 　／　Kerodon　／　いまの形式化
- 本命　／　Cat∞ 値（空間値は特殊な場合）　／　空間値（Cat∞ 値は別系統で途中）
- 主役の向き　／　unstraightening　／　straightening
- 主定理の形　／　transport witness の空間が可縮　／　∞ 関手 $`\mathrm{LFib}(B)\to\mathrm{Fun}(B,\mathcal S)` が同値
- 一般の底への道　／　骨格帰納法で $`\Delta^0,\Delta^1` に帰着　／　脈体で示し、$`N(\Delta_{/B})\to B` の局所化で降ろす
- 最初に得る結論　／　同値類の全単射　／　一気に ∞ 圏の同値
- 底　／　任意の単体的集合　／　小さい quasicategory

*unstraightening-analogy.html — 4. straightening*

straightening は fibration $`p\colon E\to B` から関手を作る。見方は二つある。

- *(A) 分類写像*：$`\chi(b)=E_b`、$`\chi(u)=u_!`（輸送）。難しいのは整合的な関手にまとめること。

- *(B) 表現可能関手の Un からの写像*：
  $$`\mathrm{St}(E)(b)\ :=\ \mathrm{Hom}_{/B}\bigl(\mathrm{Un}(h^b),\,E\bigr),\qquad h^b=\mathrm{Hom}_B(b,-).`

- 段　／　(A) の結果　／　(B)
- 集合　／　そのまま関手　／　$`\mathrm{Un}(h^b)=\{b\}`、$`\mathrm{Hom}_{/B}(\{b\},E)=E_b`
- 離散 opfibration　／　厳密な関手（$`(uv)_!=u_!v_!`）　／　$`\mathrm{Un}(h^b)=b/B`、始対象 $`\mathrm{id}_b` により $`\mathrm{Hom}_{/B}(b/B,E)\cong E_b`
- cocartesian（1 圏）　／　cleavage の選択で擬関手止まり　／　$`b\mapsto\mathrm{Fun}^{\mathrm{cocart}}_{/B}(b/B,E)` は厳密な関手（古典的な厳密化）
- 左 fibration（∞）　／　整合性の選択が手に負えない　／　$`\mathrm{Map}_{/B}(B_{b/},E)\simeq E_b`

(B) の要点は、持ち上げを一本選ぶ代わりに「$`b` から出るすべての射に沿う持ち上げ全体」を一度に保持すること。$`\mathrm{Un}` は「普遍 fibration の引き戻し」、$`\mathrm{St}` は「表現可能関手の $`\mathrm{Un}`（$`B_{b/}`）からの写像」で、層の茎・断面を表現可能対象からの射として取るのと同じナーヴ型の構成である。

*注意*：準圏の模型では、辺 $`u\colon b\to b'` から $`B_{b'/}\to B_{b/}` を作るのに合成の選択が要るので、$`b\mapsto B_{b/}` は厳密には関手的でない。厳密にするには $`\mathfrak C[B]` 上の関手として扱うなどの手当てが必要である。

*往復*：$`\mathrm{St}(\mathrm{Un}F)(b)=\mathrm{Map}_{/B}(\mathrm{Un}\,h^b,\mathrm{Un}F)\simeq\mathrm{Map}(h^b,F)\simeq F(b)`（充満忠実性と関手版 Yoneda）。逆向きは、$`\mathrm{id}_b` での評価が $`\mathrm{Un}(\mathrm{St}E)\to E` を与え、fiber ごとの同値なので全体で同値（左 fibration の fiber ごとの判定）。

*unstraightening.html — 7. straightening との関係*

- 向き　／　内容　／　Lean
- $`\mathrm{St}(\mathrm{Un}F)\cong F`　／　余単位の成分。本質的全射性の証明　／　\`leftStraighteningInfinityCounit\`（F1/LeftStraighteningEssentialSurjectivity）
- $`\mathrm{Un}(\mathrm{St}\,p)\simeq p`　／　対象ごとの再構成（前合成同値）　／　\`leftStraighteningInfinityReconstruction\`（F1/LeftStraighteningInfinityReconstruction）

注意：Un は ∞ 関手としてはまとめられていない

straightening は ∞ 圏の射 \`leftStraighteningInfinityMap : LFib(B) → Fun(B, 𝒮)\` として作られ、同値定理もこの射について述べられている（第 3 章）。一方 unstraightening は、対象への作用（§2）、変換への作用（§4、同型を除く関手性）、写像空間への作用（§5）が個別に与えられているだけで、∞ 関手 $`\mathrm{Fun}(B,\mathcal S)\to\mathrm{LFib}(B)` としては定義されていない。F1/PresheafUnstraightening の docstring にも「前層全体の unstraightening ∞ 関手は主張しない」とある。St が同値である以上、Un はその逆として（選択を通して）得られるので、理論上の欠落ではない。ただ、Un の自然性を直接使いたい場面が出てきたら、そこで初めて必要になる。

*unstraightening.html — 7. straightening との関係 — どこで使われるか*

- *Yoneda の補題*：h₁（§5）、h₂（§3）、h₄（§2 の fiber）。表現可能前層の unstraightening が slice になること（h₃）には §7 の再構成を使う。

- \*\*$`\mathcal S` の極限・余極限\*\*（第 5 章 §3）：極限 = $`\mathrm{Un}(F)` の切断の空間、余極限 = $`\mathrm{Un}(F)` の全空間。

- *straightening の同値定理*：本質的全射性（§7 の余単位）。

:::theorem "kerodon_5_6_0_2" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_6_5_12, kerodon_5_6_5_15")
Kerodon Theorem 5.6.0.2（[Tag 028K](https://kerodon.net/tag/028K)）。対応表の状態：なし。

有限鎖上のcocartesianStraighteningCoherentMapの圏同値はあるが、原文の指定積分の構成と相対fibration同値類・Functor coreのπ₀の全単射へ比較する型がない。分類の模型の同値だけをそのまま数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningCoherentMap_finite_isQCatEquivalence`

:::

:::corollary "kerodon_5_6_0_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_isEssentiallySurjective") (uses := "kerodon_1_1_0_6")
Kerodon Corollary 5.6.0.6（[Tag 028T](https://kerodon.net/tag/028T)）。対応表の状態：一部。

底Cを準圏に強めればleftStraighteningInfinityMap\_isQCatEquivalenceはleft fibrationと空間値図式の同じ分類の∞圏同値を直接与える。従ってcoreの頂点の同型類の全単射を与える。非準圏の底の単射側は含まない。

*定義 11.3 （straightening）*

単体的集合 $`B` 上の左 fibration（定義 5.3）$`q\colon E\to B` で小さいファイバーをもつもの（定義 11.2）に、関手（定義 11.1）

$$`\mathrm{St}(q)\colon B\to\mathcal S`

を対応させる操作を straightening という（$`\mathcal S` は定義 3.7）。構成は後の章で与える。

:::

# 5.6.1 Elements of Category-Valued Functors

%%%
number := false
tag := "kerodon-5-6-1"
%%%

Kerodon [Tag 01R1](https://kerodon.net/tag/01R1)

*cocartesian-definition.html — 1. 1 圏：Grothendieck opfibration*

関手 $`p\colon E\to B` の射 $`f\colon e\to e'` が *cocartesian* とは、任意の $`g\colon e\to e''` と $`v\circ p(f)=p(g)` を満たす任意の $`v\colon p(e')\to p(e'')` について、
$$`h\circ f=g,\qquad p(h)=v`
を満たす $`h\colon e'\to e''` が*一意に*存在すること。$`p` が *opfibration* とは、任意の $`e` と $`u\colon p(e)\to b` について $`u` の上の cocartesian 射 $`e\to e'` が存在すること。$`f` は「$`e` を $`u` に沿って押し出した普遍的な行き先」で、輸送 $`u_!(e):=e'` が定まる。

*fibered-descent.html — 1. 擬関手 — 定義*

圏 $`\mathcal C` から $`\mathrm{Cat}` への擬関手 $`F` は次のデータと条件からなる。

- 各対象 $`X` に圏 $`F(X)`、各射 $`f\colon X\to Y` に関手 $`F(f)`。

- 合成可能な $`X\xrightarrow{f}Y\xrightarrow{g}Z` ごとに可逆な自然変換 $`\mu_{g,f}\colon F(g)\circ F(f)\xRightarrow{\sim}F(g\circ f)`、各 $`X` に可逆な $`\eta_X\colon\mathrm{id}\xRightarrow{\sim}F(\mathrm{id}_X)`。

- *結合性*：$`W\xrightarrow{f}X\xrightarrow{g}Y\xrightarrow{h}Z` について
  $$`\mu_{h,gf}\circ\bigl(F(h)\,\mu_{g,f}\bigr)\ =\ \mu_{hg,f}\circ\bigl(\mu_{h,g}\,F(f)\bigr).`

- *単位性*：$`\mu_{f,\mathrm{id}}\circ(F(f)\,\eta_X)=\mathrm{id}`、$`\mu_{\mathrm{id},f}\circ(\eta_Y\,F(f))=\mathrm{id}`。

- 種類　／　$`\mu,\eta`
- 厳密な関手　／　恒等変換
- 擬関手　／　可逆な自然変換
- lax 関手　／　可逆とは限らない自然変換

$`\mu` は「同型が存在する」という条件ではなく、*指定されたデータ*である。選び方が違えば一般に違う擬関手になる（補章 3 例 1 の loop と同じ現象、降下データの $`\varphi` を変えると貼り合わせの結果が変わる）。

*fibered-descent.html — 1. 擬関手 — 1 圏と ∞ 圏：どこで等式になるか*

- 列の長さ　／　擬関手（$`\mathrm{Cat}` 値）　／　∞ 版（$`\mathrm{Cat}_\infty` 値）
- 1　／　関手 $`F(f)`　／　関手 $`F(f)`
- 2　／　自然同型 $`\mu_{g,f}`（データ）　／　2 単体 $`F(gf)\simeq F(g)F(f)`（データ）
- 3　／　結合性の*等式*（条件）　／　正方形：二通りの同型を結ぶ高次の同型（データ）
- $`n`　／　なし　／　$`(n-1)` 次元の立方体（データ）

$`\mathrm{Cat}` は 2 圏で自然変換の間には等しいかどうかしかないので、長さ 3 で等式になって止まる。$`\mathrm{Cat}_\infty` の写像空間 $`\mathrm{Fun}(\mathcal C,\mathcal D)^{\simeq}` は空間なので、一致もまたデータになり無限に続く。*擬関手は ∞ 版の整合的図式を長さ 3 で切り詰めたもの*である。$`\mathrm{Cat}_\infty` の写像空間は core なので、関手 $`\mathcal C\to\mathrm{Cat}_\infty` は lax ではなく擬関手の ∞ 版にあたる。

*fibered-descent.html — 1. 擬関手 — 整合性の処理の三通り*

- 方法　／　1 圏　／　∞ 圏
- ① 全データを書く　／　$`\mu,\eta` を与えて等式を確かめる（手で可能）　／　$`N(\mathcal C)\to N^{hc}(\mathrm{QCat}^\Delta)` を書く（実際には不可能）
- ② fibration として作る　／　Grothendieck ファイバー圏（SGA1）　／　cocartesian／cartesian fibration と straightening
- ③ 厳密化　／　擬関手は厳密な関手と同値（split fibration への置き換え、Giraud・Street）　／　整合的図式は単体的圏への厳密な図式と同値（Vogt、HTT Prop. 4.2.4.4）

:::definition "kerodon_5_6_1_1" (lean := "CategoryTheory.Pseudofunctor.Grothendieck, CategoryTheory.Pseudofunctor.Grothendieck.category, CategoryTheory.Grothendieck")
Kerodon Definition 5.6.1.1（[Tag 025N](https://kerodon.net/tag/025N)）。対応表の状態：Mathlib にある。

仮定：通常の圏 C と LocallyDiscrete C から Cat への擬関手 F（Kerodon と一致）。結論：Grothendieck F は (c,x) を対象とし、射は (f:c→d, F(f)(x)→y)。通常の Cat 値関手の版もある（一致）。

:::

:::proposition "kerodon_5_6_1_3" (lean := "CategoryTheory.Pseudofunctor.Grothendieck.category")
Kerodon Proposition 5.6.1.3（[Tag 01R3](https://kerodon.net/tag/01R3)）。対応表の状態：Mathlib にある。

仮定：通常の圏 C と Cat 値擬関手 F（Kerodon と一致）。結論：指定された Grothendieck F の合成に対して恒等則と結合則を持つ Category instance（一致）。

:::

:::definition "kerodon_5_6_1_5" (lean := "CategoryTheory.Pseudofunctor.CoGrothendieck, CategoryTheory.Pseudofunctor.CoGrothendieck.category")
Kerodon Definition 5.6.1.5（[Tag 025P](https://kerodon.net/tag/025P)）。対応表の状態：Mathlib にある。

仮定：通常の圏 C の反対圏から Cat への擬関手 F（Kerodon と一致）。結論：CoGrothendieck F は (c,x) と (f:c→d, x→F(f)(y)) による圏（一致）。

:::

:::definition "kerodon_5_6_1_12" (lean := "CategoryTheory.Pseudofunctor.Grothendieck.forget, CategoryTheory.Pseudofunctor.CoGrothendieck.forget")
Kerodon Notation 5.6.1.12（[Tag 01RA](https://kerodon.net/tag/01RA)）。対応表の状態：Mathlib にある。

仮定：通常の圏 C から、または Cᵒᵖ からの Cat 値擬関手 F（Kerodon と一致）。結論：共変・反変の Grothendieck 構成に対して、対象と射を底の成分に送る forget 関手（一致）。

:::

:::proposition "kerodon_5_6_1_16"
Kerodon Proposition 5.6.1.16（[Tag 025S](https://kerodon.net/tag/025S)）。対応表の状態：なし。

Mathlibの型は反変CoGrothendieckの選んだcartesian lift。原文の共変Grothendieckの一般(f,u)のcocartesian性とuの同型性のiffとは別の射と述語。

宣言：`CategoryTheory.Pseudofunctor.CoGrothendieck.isStronglyCartesian_homCartesianLift`

:::

:::corollary "kerodon_5_6_1_17" (lean := "CategoryTheory.Pseudofunctor.CoGrothendieck.isStronglyCartesian_homCartesianLift")
Kerodon Corollary 5.6.1.17（[Tag 025T](https://kerodon.net/tag/025T)）。対応表の状態：一部。

MathlibのCoGrothendieck忘却のIsFibered instanceは原文後半の反変版射影がcartesian fibrationという結論そのもの。共変版は含まない。

:::

# 5.6.2 Elements of QC-Valued Functors

%%%
number := false
tag := "kerodon-5-6-2"
%%%

Kerodon [Tag 026H](https://kerodon.net/tag/026H)

*unstraightening-analogy.html — 3. Un は関手で、Hom を保つ*

どの段でも示したいことは次の形である。

1. $`\mathrm{Un}\colon\mathrm{Fun}(B,\mathcal V)\to(\text{fibration})_{/B}` が関手になる。

2. 充満忠実：$`\mathrm{Hom}(F,G)\simeq\mathrm{Hom}_{/B}(\mathrm{Un}F,\mathrm{Un}G)`。

3. 本質的全射で、同値になる。

*unstraightening-analogy.html — 3. Un は関手で、Hom を保つ — 射への作用は $`B\times[1]` 上の引き戻しと輸送*

変換 $`\alpha\colon F\Rightarrow G` を $`B\times[1]\to\mathcal V` とみなし、普遍 fibration を引き戻す。$`0` 側・$`1` 側の fiber が $`\mathrm{Un}F`・$`\mathrm{Un}G` で、$`0\to1` 方向の輸送が $`\mathrm{Un}F\to\mathrm{Un}G` を与える。1 圏では $`\int\alpha\colon(b,x)\mapsto(b,\alpha_b(x))`。∞ では $`E\to B\times\Delta^1\to\Delta^1` が左 fibration なので、輸送はホモトピーを除いて一意に定まる（離散の場合の一意な持ち上げの ∞ 版）。

*unstraightening-analogy.html — 3. Un は関手で、Hom を保つ — Hom の比較はエンドになる*

- 段　／　Hom 側　／　整合性　／　「cocartesian 射を保つ」条件
- 集合　／　$`\prod_b\mathrm{Hom}(X_b,Y_b)`　／　なし　／　不要
- 1 圏（離散 fiber）　／　$`\int_b\mathrm{Hom}(Fb,Gb)`　／　自然性の等式　／　一意持ち上げで自動
- 1 圏（圏 fiber）　／　擬自然変換の圏　／　同型と整合性　／　課す（lax 自然変換なら一般の $`B` 上の関手）
- ∞（左 fibration）　／　$`\int_b\mathrm{Map}(Fb,Gb)`　／　全次元のホモトピー　／　自動（すべての射が cocartesian）

離散 opfibration で手で確かめると、充満忠実性の中身が見える。$`B` 上の関手 $`\Phi\colon\int F\to\int G` は各 fiber で写像 $`\alpha_b` を与える。射 $`(b,x)\to(b',F(u)x)` は $`u` の上の射に移るので、行き先は一意持ち上げにより $`G(u)\alpha_b(x)` しかない。対象の行き先と比べて $`\alpha_{b'}(F(u)x)=G(u)\alpha_b(x)`、すなわち*自然性そのもの*が出る。どの段でも「$`B` 上の写像 = fiber ごとの写像 + 底の射に沿う輸送との整合性」で、それがちょうどエンドを与える。

本質的全射まで含めると、$`\mathcal S` は左 fibration を分類する：$`\mathrm{Map}(B,\mathcal S)\simeq\mathrm{LFib}(B)^{\simeq}`（$`B` について自然）。1 圏の類似 $`\mathrm{Fun}(B,\mathrm{Set})^{\cong}\simeq\mathrm{DOpFib}(B)^{\cong}` では、引き戻しが同型を除いてしか決まらないので、$`B` についての自然性は擬自然性になる。

*unstraightening.html — 2. 定義：引き戻し*

- *底についての関手性*：$`\alpha\colon C\to D` が $`G\circ\alpha=F` を満たせば、射 $`\mathrm{Un}(F)\to\mathrm{Un}(G)` が決まり、恒等則・合成則が*厳密に*成り立ち、四角形は引き戻しになる（\`leftUnstraighteningMap\`、\`\_id\`、\`\_comp\`、\`\_isPullback\`）。

この定義の利点

HTT §2.2.1 では unstraightening を、単体的圏の側の straightening の右随伴（モデル圏の右 Quillen 関手）として定義する。そのため、底変換との両立はホモトピーを除いてしか成り立たない。ここでは $`\mathcal S_*\to\mathcal S` の引き戻しで定義しているので、底変換との両立が厳密な同型になり、それ以後の議論（局所化による一般の底への降下、strict な図式との比較）で「同型を除いて」の管理が一段減る。

*unstraightening.html — 3. 宇宙と小ささ*

$`\mathcal S` は宇宙 $`u+1` にあるので、$`\mathrm{Un}(F)` も \`SSet.\{u+1\}\` になる。しかし $`B` 上の左 fibration の ∞ 圏 $`\mathrm{LFib}(B)`（第 3 章）の対象は宇宙 $`u` の単体的集合である。そこで二段の手当てをする。

1. *小ささ*：底が各次数で $`u`-小さければ、引き戻しの単体も $`u`-小さい（\`pullback\_simplex\_small\_of\_fibers\`、\`leftUnstraightening\_obj\_small\`、F1/LeftUnstraighteningSmallness）。fiber が $`u`-小さい Kan 複体だからである。

2. *縮小*：各次数を \`Shrink\` して宇宙 $`u` に戻したものが \`smallLeftUnstraightening F\`（F1/SmallLeftUnstraightening）。射影・左 fibration 性・fiber は縮小の同型で移す（\`smallLeftUnstraighteningFiberValueEquivalence\`）。相対関手空間も厳密に同型（\`smallLeftUnstraighteningRelativeFunctorIso\`。Yoneda の h₂）。

前層（$`C^{\mathrm{op}}` 上の関手）の場合は、$`C^{\mathrm{op}}` 上の左 unstraightening を反転して $`C` 上の右 fibration にする（\`smallRightUnstraightening\`、F1/PresheafUnstraightening）。

*unstraightening.html — 4. 変換への作用*

変換 $`H\colon F\Rightarrow G`（$`\Delta^1\times B\to\mathcal S` で両端が $`F`、$`G` のもの）から、$`B` 上の射 $`\mathrm{Un}(F)\to\mathrm{Un}(G)` を作る。次の持ち上げ問題を解く。

$$`\begin{array}{ccc} \{0\}\times\mathrm{Un}(F) & \xrightarrow{\ \text{標準の点}\ } & \mathcal S_*\\ \downarrow & \nearrow & \downarrow\\ \Delta^1\times\mathrm{Un}(F) & \xrightarrow{\ H\circ(\mathrm{id}\times p)\ } & \mathcal S \end{array}`

上の辺は引き戻しの第一射影（$`\mathrm{Un}(F)` の各点が持っている $`F(b)` の点）。左の包含 $`\{0\}\times X\hookrightarrow\Delta^1\times X` は left anodyne で、右は左 fibration なので、持ち上げが存在する。持ち上げを $`\{1\}` で評価すると $`G\circ p` の上の点つき空間、つまり $`\mathrm{Un}(G)` への射になる。

- 内容　／　Lean　／　場所
- 持ち上げの選択空間は可縮　／　\`leftUnstraighteningTransformationChoiceSpace\_isContractibleKan\`　／　F1/LeftUnstraighteningTransformation
- 変換は $`B` 上の射を与える　／　\`exists\_leftUnstraighteningTransformation\`　／　同上
- 恒等変換 ↦ 恒等射（相対写像空間で同型）　／　\`leftUnstraighteningTransformationMap\_identityIso\`　／　F1/LeftUnstraighteningIdentity
- 合成の三角形 ↦ 合成（同型）　／　\`leftUnstraighteningTransformationMap\_compositionIso\`　／　F1/LeftUnstraighteningComposition

第 3 章の cocartesian transport と同じ型の議論で、「選択空間が可縮」によって選び方の任意性を閉じ込めている。恒等則・合成則は厳密な等式ではなく、相対写像空間の中の同型として成り立つ。

:::definition "kerodon_5_6_2_1" (uses := "kerodon_1_1_0_6")
Kerodon Definition 5.6.2.1（[Tag 026J](https://kerodon.net/tag/026J)）。対応表の状態：なし。

leftUnstraighteningはSpaceInfinityとpointedSpaceProjectionのpullback。原文のN\^hc(Set\_Δ)とそのΔ⁰-cosliceのpullbackとは別の対象で、二つの普遍射影を比較する型がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening`

:::

:::proposition "kerodon_5_6_2_2" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_5_5_10, kerodon_5_5_5_11")
Kerodon Proposition 5.6.2.2（[Tag 026K](https://kerodon.net/tag/026K)）。対応表の状態：なし。

引用は空間の普遍left fibrationのpullback。原文のQC\_Objの普遍cocartesian fibrationとのpullback比較がなく、QC値の同じ積分の特殊形だと直接同定できない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection_leftFibration`

:::

:::corollary "kerodon_5_6_2_3"
Kerodon Corollary 5.6.2.3（[Tag 026L](https://kerodon.net/tag/026L)）。対応表の状態：なし。

leftUnstraightening\_quasicategoryは空間の普遍射影のpullbackの準圏性。原文のQC\_Objによる積分と同じ対象になる比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening_quasicategory`

:::

:::definition "kerodon_5_6_2_4"
Kerodon Definition 5.6.2.4（[Tag 026M](https://kerodon.net/tag/026M)）。対応表の状態：なし。

SpaceInfinityによるleftUnstraighteningは原文のQC値の積分の定義と値域・普遍射影が異なり、指定対象を同定する比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening`

:::

:::proposition "kerodon_5_6_2_5"
Kerodon Remark 5.6.2.5（[Tag 026N](https://kerodon.net/tag/026N)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Space 値・底辺ごとの比較・通常圏 Grothendieck と nerve・全図式の自然性を照合。通常圏上の strictly unital Cat 値図式の ∞ 版 Grothendieck 構成と通常の圏 of elements の nerve の標準同型。番号引用の base change や vertexFiberPullback はこの nerve 比較を述べない。

*unstraightening.html — 2. 定義：引き戻し*

- *底変換*：$`k\colon D\to C` について $`\mathrm{Un}(F\circ k)\cong D\times_C\mathrm{Un}(F)` は*同型*（同値ではない。\`leftUnstraighteningBaseChangeIso\`、F1/LeftUnstraighteningBaseChange、Kerodon Remark 5.6.2.5）。引き戻しの貼り合わせによる。

:::

:::proposition "kerodon_5_6_2_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection_leftFibration, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningFiberIso")
Kerodon Example 5.6.2.9（[Tag 026S](https://kerodon.net/tag/026S)）。対応表の状態：本体にある。

仮定：任意の単体集合 C と F:C→SpaceInfinity（Kerodon と一致）。結論：PointedSpaceInfinity→SpaceInfinity を F に沿って引き戻した leftUnstraightening とその左ファイブレーション射影（一致）。

*unstraightening.html — 2. 定義：引き戻し*

\`\`\`text
noncomputable def leftUnstraightening \{C : SSet.\{u + 1\}\} (F : C ⟶ SpaceInfinity.\{u\}) :
    SSet.\{u + 1\} := pullback pointedSpaceProjection F

instance leftUnstraighteningProjection\_leftFibration \{C : SSet.\{u + 1\}\} (F : C ⟶ SpaceInfinity.\{u\}) :
    LeftFibration (leftUnstraighteningProjection F)
\`\`\`

$$`\begin{array}{ccc} \mathrm{Un}(F) & \longrightarrow & \mathcal S_*\\ \downarrow & \lrcorner & \downarrow\\ C & \xrightarrow{\ F\ } & \mathcal S \end{array}`

場所：F1/LeftUnstraightening（Kerodon Example 5.6.2.9）。*単体的集合としての厳密な引き戻し*なので、次のことがほぼ定義から従う。

- *左 fibration*：左 fibration は引き戻しで保たれる。底 $`C` が quasicategory なら全空間も quasicategory。

- *fiber*：$`\mathrm{Un}(F)_c` は $`\mathcal S_*` の $`F(c)` 上の fiber そのものなので、§1 により $`F(c)` と同値（\`leftUnstraighteningFiberValueEquivalence\`）。

:::

:::proposition "kerodon_5_6_2_21" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_1_7_1, kerodon_5_1_7_11, kerodon_5_5_5_11")
Kerodon Proposition 5.6.2.21（[Tag 02S7](https://kerodon.net/tag/02S7)）。対応表の状態：なし。

leftUnstraighteningMapは図式の厳密等式で与えた底変換の射。原文のFunctor空間の同型から底上の相対逆を持つ比較を返す型ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap`

:::

:::proposition "kerodon_5_6_2_22" (uses := "kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_2_8_9, kerodon_5_5_5_14")
Kerodon Proposition 5.6.2.22（[Tag 02S8](https://kerodon.net/tag/02S8)）。対応表の状態：なし。

leftStraighteningInfinityCounitは分類図式間のFunctorIso。原文の指定した比較θ\_Cと豊穣homotopyTransportの自然同型に結ぶ型がなく、別のunit/counitだけを数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityCounit`

:::

:::corollary "kerodon_5_6_2_23"
Kerodon Corollary 5.6.2.23（[Tag 027K](https://kerodon.net/tag/027K)）。対応表の状態：なし。

引用はstraightening counitとfiber同値を束ねたLeftTransportRepresentation。原文の各辺の作用・任意の選んだ共変輸送と指定θ\_Cからなる四角の可換性の型はない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityCounit`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation`

:::

:::corollary "kerodon_5_6_2_24" (uses := "kerodon_1_1_0_6")
Kerodon Corollary 5.6.2.24（[Tag 027L](https://kerodon.net/tag/027L)）。対応表の状態：なし。

引用はFunctor空間の辺F→Gをunstraighteningの全空間射へ移し、その各bの作用をpointed-space輸送と比較する。原文の一つのFの底の辺C→DとhC上の自然性とは異なる図式。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningEdgeMap_pointedFiberTransportIso`

:::

# 5.6.3 Comparison with the Category of Elements

%%%
number := false
tag := "kerodon-5-6-3"
%%%

Kerodon [Tag 0273](https://kerodon.net/tag/0273)

:::proposition "kerodon_5_6_3_1"
Kerodon Proposition 5.6.3.1（[Tag 0274](https://kerodon.net/tag/0274)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Set 値の圏 of elements・普通の nerve 比較・Space 値の特例を照合。∞ 版 ∫\_C F から通常 Grothendieck 圏の nerve への指定 T の一意性。weighted nerve の射影にはこの通常圏への比較がない。

:::

:::proposition "kerodon_5_6_3_2"
Kerodon Proposition 5.6.3.2（[Tag 0275](https://kerodon.net/tag/0275)）。対応表の状態：なし。

grothendieckTypeToCatは通常圏の二つの構成の圏同値。原文の積分のホモトピー圏からの指定した厳密同型との比較がない。

宣言：`CategoryTheory.Grothendieck.grothendieckTypeToCat`

:::

:::corollary "kerodon_5_6_3_3"
Kerodon Corollary 5.6.3.3（[Tag 027Y](https://kerodon.net/tag/027Y)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Set 値の圏 of elements・普通の nerve 比較・Space 値の特例を照合。left covering を hC 上の通常圏 of elements で判定する二条件。LeftFibration の分類は離散ファイバーの厳密な covering 判定ではない。

:::

:::proposition "kerodon_5_6_3_4"
Kerodon Proposition 5.6.3.4（[Tag 0276](https://kerodon.net/tag/0276)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Set 値の圏 of elements・普通の nerve 比較・Space 値の特例を照合。通常圏上の strictly unital Cat 値図式で ∞ 版 ∫ の nerve 比較 T が同型。一般の weighted nerve の定値図式比較は任意の bicategorical 図式を扱わない。

:::

:::corollary "kerodon_5_6_3_5"
Kerodon Corollary 5.6.3.5（[Tag 0278](https://kerodon.net/tag/0278)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Set 値の圏 of elements・普通の nerve 比較・Space 値の特例を照合。通常の Cat の pith に由来する図式について ∫\_C F の射影の性質を強める結果。一般の cocartesian straightening の型にこの因子化がない。

:::

# 5.6.4 Comparison with the Weighted Nerve

%%%
number := false
tag := "kerodon-5-6-4"
%%%

Kerodon [Tag 0279](https://kerodon.net/tag/0279)

:::definition "kerodon_5_6_4_1" (uses := "kerodon_1_1_0_6")
Kerodon Construction 5.6.4.1（[Tag 027A](https://kerodon.net/tag/027A)）。対応表の状態：なし。

exists\_kanWeightedUnstraighteningUnitはKan値図式に対する選択された比較の存在、reversed比較は反転した係数。原文のmin(S\\\{x\})による指定θの単体上の公式との比較がなく、同じ構成の特殊形ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_kanWeightedUnstraighteningUnit`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallReversedWeightedKanUnstraighteningComparison`

:::

:::proposition "kerodon_5_6_4_8" (uses := "kerodon_1_4_0_1, kerodon_4_6_7_8, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_6_1, kerodon_5_3_3_16, kerodon_5_6_2_2")
Kerodon Proposition 5.6.4.8（[Tag 027J](https://kerodon.net/tag/027J)）。対応表の状態：なし。

strictKanUnstraighteningComparisonの始域係数はsHom(Δ⁰,F(c))の反転、原文はF(c)そのもの。原文の指定θとの比較式がないため、反転模型上の同値を同じ射の結論として数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictKanUnstraighteningComparison`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictKanUnstraighteningComparison_isPrecompositionEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictKanUnstraighteningComparison_projection`

:::

# 5.6.5 The Universality Theorem

%%%
number := false
tag := "kerodon-5-6-5"
%%%

Kerodon [Tag 028U](https://kerodon.net/tag/028U)

:::definition "kerodon_5_6_5_1" (uses := "kerodon_1_1_0_6, kerodon_5_1_4_1, kerodon_5_1_7_1")
Kerodon Definition 5.6.5.1（[Tag 028V](https://kerodon.net/tag/028V)）。対応表の状態：なし。

LeftTransportRepresentationはSpaceInfinity値とfiberごとの同値を束ねる。原文のQC\_Objによる四角と相対逆を持つ比較射の定義への同定がなく、類似の表現データにとどまる。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation`

:::

:::theorem "kerodon_5_6_5_12" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_2_7_2, kerodon_5_1_4_1, kerodon_5_6_8_3, kerodon_5_6_8_10")
Kerodon Theorem 5.6.5.12（[Tag 0293](https://kerodon.net/tag/0293)）。対応表の状態：なし。

引用はSpaceInfinity・pointed-spaceによるleft transport表現の厳密延長。原文のQC\_Objによる指定四角と同じ表現空間になる比較がない。任意の余デカルト表現をそのまま延長しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_coherentUnstraighteningRepresentation_extension`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_smallFiber_leftTransportRepresentation_extension`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentUnstraighteningWitnessRestriction_trivialKanFibration`

:::

:::corollary "kerodon_5_6_5_13" (uses := "kerodon_1_1_0_6, kerodon_5_1_4_1")
Kerodon Corollary 5.6.5.13（[Tag 0294](https://kerodon.net/tag/0294)）。対応表の状態：なし。

引用の延長は空間値のleft transport表現で、原文のQC値表現の指定射影との比較がない。left fibrationに制限しても、与えられたQC値表現が同じ空間値データとは限らない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_smallFiber_leftTransportRepresentation_extension`

:::

:::corollary "kerodon_5_6_5_14" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_6_5_13")
Kerodon Corollary 5.6.5.14（[Tag 0295](https://kerodon.net/tag/0295)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan/Space 値の分類・通常圏の Grothendieck・充満部分圏・各頂点を照合。全ファイバーに同値な代表を含む充満部分圏 Q へ分類関手を落とす存在。Space 値の small unstraightening は任意の Q への因子化を与えない。

:::

:::corollary "kerodon_5_6_5_15" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_4_4, kerodon_5_1_4_1, kerodon_5_6_5_13")
Kerodon Corollary 5.6.5.15（[Tag 0296](https://kerodon.net/tag/0296)）。対応表の状態：なし。

空間値のtransportWitnessSpaceが可縮という型は、原文の任意の二つのQC値表現の間のFunctorIsoを直接返さない。表現の値域・証人空間の比較を欠く。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallTransportWitnessSpace_isContractibleKan`

:::

:::definition "kerodon_5_6_5_16" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_6_5_14, kerodon_5_6_5_15")
Kerodon Notation 5.6.5.16（[Tag 019S](https://kerodon.net/tag/019S)）。対応表の状態：なし。

leftStraighteningInfinityMapと表現のnonemptyは空間値の構成。原文のQC値の表現の全同型類と、同型な任意候補も表現である条件への比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftTransportRepresentation_nonempty`

:::

:::corollary "kerodon_5_6_5_18" (uses := "kerodon_1_4_0_1, kerodon_5_3_5_6, kerodon_5_6_0_2")
Kerodon Corollary 5.6.5.18（[Tag 0387](https://kerodon.net/tag/0387)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan/Space 値の分類・通常圏の Grothendieck・充満部分圏・各頂点を照合。通常の小圏 C について hc nerve が原文の指定した図式の二集合の間に全単射を誘導する結論。coherentProduct の比較同値は指定集合の全単射を与えない。

:::

:::proposition "kerodon_5_6_5_20"
Kerodon Proposition 5.6.5.20（[Tag 029A](https://kerodon.net/tag/029A)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan/Space 値の分類・通常圏の Grothendieck・充満部分圏・各頂点を照合。inner covering と所定の Q を通る ∫\_C F の厳密同型による分類。内ファイブレーションの底上の ∞ 圏同値と、ここでの covering の厳密同型は区別した。

:::

:::corollary "kerodon_5_6_5_21"
Kerodon Corollary 5.6.5.21（[Tag 01SU](https://kerodon.net/tag/01SU)）。対応表の状態：なし。

Grothendieckの型と反変射影のfibered instanceだけでは、原文の与えられた共変fibrationを指定同型で復元するiffのいずれの方向も直接返さない。

宣言：`CategoryTheory.Pseudofunctor.Grothendieck`、`CategoryTheory.Pseudofunctor.CoGrothendieck.instIsFiberedForget`

:::

:::corollary "kerodon_5_6_5_22"
Kerodon Corollary 5.6.5.22（[Tag 01SZ](https://kerodon.net/tag/01SZ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan/Space 値の分類・通常圏の Grothendieck・充満部分圏・各頂点を照合。通常の groupoid opfibration と Cat 値図式の Grothendieck 構成に同型であることの同値。Mathlib の Grothendieck は分裂の構成を与えるがこの分類を述べない。

:::

# 5.6.6 Application: Corepresentable Functors

%%%
number := false
tag := "kerodon-5-6-6"
%%%

Kerodon [Tag 02HU](https://kerodon.net/tag/02HU)

*f-b-literature-yoneda.html — 8. 前層と、写像空間の相対関手空間としての読み替え — 8.1 前層の二つの定義*

- 　／　関手として　／　fibration として
- ∞ 圏　／　$`\mathcal P(C)=\mathrm{Fun}(C^{\mathrm{op}},\mathcal S)`、$`\mathcal S=N^{hc}(\mathcal Kan)`　／　$`\mathrm{RFib}(C)`：小さい右 fibration $`X\to C` を対象、$`\mathrm{Fun}_{/C}(X,Y)`（Kan 複体）を Hom とする単体的圏の coherent nerve
- 対象　／　$`C^{\mathrm{op}}\to\mathcal S`。$`\mathfrak C\dashv N^{hc}` で読むと単体的関手 $`\mathfrak C[C^{\mathrm{op}}]\to\mathcal Kan`（ホモトピー整合的な図式）　／　右 fibration（$`C^{\mathrm{op}}` 上の左 fibration）
- 射　／　自然変換 $`\Delta^1\times C^{\mathrm{op}}\to\mathcal S`　／　$`C` 上の写像
- 形式化　／　SpaceInfinityFunctor　／　LeftFibrationInfinity（$`C^{\mathrm{op}}` 上の左 fibration として）

$`\mathcal S` は小さい Kan 複体の全体なので $`\mathcal P(C)` は一つ上の宇宙に入る（形式化で $`C` を uliftFunctor で持ち上げる理由）。straightening は $`\mathcal P(C)\simeq\mathrm{LFib}(C^{\mathrm{op}})\cong\mathrm{RFib}(C)` を言う。1 圏では前層 $`F\colon C^{\mathrm{op}}\to\mathrm{Set}` と要素の圏 $`\int F\to C`（離散 fibration）が対応し、∞ 版では集合が空間に、離散 fibration が右 fibration になる。

*f-b-literature-yoneda.html — 8. 前層と、写像空間の相対関手空間としての読み替え — 8.2 主張*

$$`\mathrm{Map}_{\mathcal P(C)}(F,G)\;\simeq\;\mathrm{Fun}_{/C}(\mathrm{Un}\,F,\mathrm{Un}\,G)`

unstraightening が写像空間で充満忠実であることそのもので、形式化の Yoneda の証明の $`h_1`（最も重い入力。CoherentUnstraighteningMappingEquivalence、SmallCoherentMappingEquivalence）。1 圏では $`\alpha\colon F\Rightarrow G` から $`\int\alpha\colon(c,x)\mapsto(c,\alpha_c(x))` が得られ、$`C` 上にあることがちょうど自然性なので $`\mathrm{Nat}(F,G)\cong\mathrm{Fun}_{/C}(\int F,\int G)`。∞ 版はこれを空間のホモトピー同値に格上げしたもの。

*f-b-literature-yoneda.html — 8. 前層と、写像空間の相対関手空間としての読み替え — 8.3 両辺の中身と橋渡し*

- *左辺*（$`K=C^{\mathrm{op}}`）：写像空間の定義 (b) により $`\{F\}\times\mathrm{Fun}(\Delta^1,\mathrm{Fun}(K,\mathcal S))\times\{G\}`。点は両端が $`F,G` の自然変換 $`\alpha\colon\Delta^1\times K\to\mathcal S`。

- *右辺*：点は $`K` 上の写像 $`\mathrm{Un}\,F\to\mathrm{Un}\,G`。

- *橋渡し*：$`\mathrm{Un}(\alpha)` は $`\Delta^1\times K` 上の左 fibration で両端が $`\mathrm{Un}\,F,\mathrm{Un}\,G`。示すべきことは「$`\Delta^1\times K` 上の左 fibration で両端が $`X_0,X_1` のもの ↔ $`K` 上の写像 $`X_0\to X_1`」で、「$`\Delta^1` 上の左 fibration は写像柱」のパラメータ付き版（旧シリーズ「Yoneda への道」段 6 の univalence）。

左 fibration から写像へ（transport）

$`Y\to\Delta^1\times K` を左 fibration（両端 $`X_0,X_1`）とする。$`\{0\}\times X_0\to Y` を $`\Delta^1\times X_0\to\Delta^1\times K` の上に持ち上げる。$`\{0\}\times X_0\hookrightarrow\Delta^1\times X_0` は left anodyne（pushout-product の特別な場合）なので持ち上げ $`H` があり、部品 C と同じ理由で持ち上げ全体の空間は可縮。$`H|_{\{1\}\times X_0}` が $`K` 上の写像 $`X_0\to X_1`。covariant transport を $`K` 全体で一斉に行ったもの。

写像から左 fibration へ（写像柱）

$`\varphi\colon X_0\to X_1` に対し $`M_\varphi=(\Delta^1\times X_0)\sqcup_{\{1\}\times X_0}X_1\to\Delta^1\times K`。一般には左 fibration ではないので、両端を変えない相対的な left anodyne 置き換えで直す。その transport が $`\varphi` に戻ることは持ち上げの一意性から。

空間の同値にするには、すべての次元の単体で同じ対応を作る。$`n` 単体は $`\Delta^n` をパラメータに持つ同じ問題になる。

*f-b-literature-yoneda.html — 8. 前層と、写像空間の相対関手空間としての読み替え — 8.4 読み替えの役割*

- 場面　／　関手の言葉　／　fibration の言葉
- Yoneda　／　$`\mathrm{Map}(h_y,F)`　／　$`\mathrm{Fun}_{/C}(C_{/y},\mathrm{Un}\,F)`。fibration 版 Yoneda で $`F(y)`
- 極限　／　$`\lim F`　／　切断の空間 $`\mathrm{Fun}_{/C}(C,\mathrm{Un}\,F)`（Kerodon 7.4.1）
- 大域切断　／　$`\mathrm{Map}(\ast,F)`　／　同上（終対象の Un は $`C` 自身）
- 自然変換が同値か　／　各点で同値か　／　ファイバーごとの判定法

関手の言葉の問いを fibration に移すと、多くは持ち上げや切断の問題になり、left anodyne・pushout-product・始対象への制限で直接扱える。その入口が $`h_1`。前層を最初から $`\mathrm{RFib}(C)` と定義する流儀（Cisinski の本、∞-cosmos）では $`h_1` は定義から不要だが、前層を関手として扱う場面で straightening の同値定理が要る。どちらの流儀でもこの橋を一度は渡る。

*f-b-literature-yoneda.html — 9. straightening の構成と $`h_y` の関手性 — 9.8 $`h_y` の定義と、スライスとの比較*

- $`h_y=\mathrm{Map}(-,y)` は $`x` について反変なので $`C^{\mathrm{op}}\to\mathcal S`（$`C\to\mathcal S` にしたいなら $`h^x=\mathrm{Map}(x,-)`）。

- *定義（形式化）*：$`\mathrm{Tw}(C)\to C^{\mathrm{op}}\times C`（左 fibration）を straightening して Hom 関手 $`\mathrm{Map}\colon C^{\mathrm{op}}\times C\to\mathcal S`（twistedArrowHomInfinity）を作り、curry した Yoneda 埋め込み $`C\to\mathrm{Fun}(C^{\mathrm{op}},\mathcal S)`（yonedaInfinityMap）の $`y` での値を $`h_y` とする。関手であることは 9.3〜9.7 が保証し、$`y\mapsto h_y` も ∞ 関手として得られる。

- *スライスとの比較*：$`C_{/y}\to C` は右 fibration、$`C^{\mathrm{op}}_{y/}=(C_{/y})^{\mathrm{op}}\to C^{\mathrm{op}}` は左 fibration で、$`x` 上のファイバーは $`\mathrm{Hom}^R(x,y)\simeq\mathrm{Map}(x,y)`。$`h_y` の Un がこのスライスと同値であること（比較写像 $`C^{\mathrm{op}}_{y/}\to\mathrm{Un}(h_y)` が前合成同値、representableCosliceUnstraighteningComparison\_isPrecompositionEquivalence）を示す。中身は二つ：(1) St は底変換と整合するので、curry した関手の $`y` での値は $`\mathrm{Tw}(C)` を $`C^{\mathrm{op}}\times\{y\}` に引き戻した左 fibration の St。(2) $`\mathrm{Tw}(C)\times_C\{y\}` は fat スライスで、join スライス $`C^{\mathrm{op}}_{y/}` と同値。

- 　／　Hom 関手の値（定義）　／　スライスの St（比較）
- $`y` についての関手性　／　ある（Yoneda 埋め込み）　／　ない（$`y` ごと）
- fibration 側の記述　／　すぐにはわからない　／　定義から Un はスライス
- Yoneda で必要な場所　／　充満忠実性（Yoneda 写像そのものの Hom 作用）　／　値の計算 $`h_3`（fibration 版 Yoneda を適用する）

$`C` が普通の圏の脈体なら、スライスの St の値は $`\mathrm{Fun}_{/N(C^{\mathrm{op}})}(N(C^{\mathrm{op}}_{x/}),C^{\mathrm{op}}_{y/})\simeq\mathrm{Map}(x,y)` で、$`f\colon x'\to x` の作用は厳密な前合成に沿った制限（評価すれば $`f^*`）。$`f^*` を一つずつ選ばないので 9.2 の問題は起きない。他の作り方として、$`\mathfrak C[C]` の Hom を Kan 化する方法（HTT §5.1.3、比較定理が要るので不採用）、関手にせず $`C_{/y}` のまま扱う方法（∞-cosmos、Cisinski）がある。

- 段　／　整合性の処理
- fibration　／　transport と整合性は持ち上げ性質（Prop）
- 第一段　／　$`c\mapsto C_{c/}` の厳密な関手性と切断の制限。値の正しさは fibration 版 Yoneda
- 第二段　／　局所化 $`\mathrm{fv}` の普遍性
- $`h_y`　／　スライス $`C^{\mathrm{op}}_{y/}` を入れるだけ

*unstraightening.html — 5. 写像空間の比較（Yoneda の h₁）*

*定理.* 任意の底 $`B` と $`F,G\colon B\to\mathcal S` について、比較写像

$$`M\colon\ \mathrm{Map}_{\mathrm{Fun}(B,\mathcal S)}(F,G)\longrightarrow\mathrm{Fun}_{/B}\bigl(\mathrm{Un}(F),\mathrm{Un}(G)\bigr)`

は同値（\`leftUnstraighteningMappingSpaceMap\_isQCatEquivalence\`、F1/CoherentUnstraighteningMappingEquivalence）。底や高次のパラメーターの小ささは要らない。

*unstraightening.html — 5. 写像空間の比較（Yoneda の h₁） — 比較写像 $`M` の作り方*

§4 の持ち上げを、変換一本ずつではなく\*\*変換の空間 $`T` 全体に対して一度に\*\*行う（F1/LeftUnstraighteningFamilyLifts）。$`\{0\}\times\mathrm{Un}(F)\times T\hookrightarrow\Delta^1\times\mathrm{Un}(F)\times T` も left anodyne なので、族ごと持ち上げられる。終点で評価して相対的に curry したものが $`M`（F1/LeftUnstraighteningMappingSpaceMap）。

*unstraightening.html — 5. 写像空間の比較（Yoneda の h₁） — 同値性の証明：普遍的な族から逆を作る*

\`\`\`text
lemma leftUnstraighteningMappingSpaceMap\_isQCatEquivalence ... := by
  let Y := relativeFunctorSpace (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
  let T := leftUnstraighteningTransformationSpace F G
  let M := leftUnstraighteningMappingSpaceMap F G
  let f := relativeFunctorUncurry (𝟙 Y)                       -- Y 上の普遍的な族
  obtain ⟨t, W, hw₀, hw₁, hwp⟩ := exists\_coherentFamily\_recovery F G f hf   -- 族 → 変換の族
  ...
  have hleft : Nonempty (FunctorIso (M ≫ t) (𝟙 T)) := UnstraighteningFamilyWitness.unique ...
  have hright := unstraighteningFamilyComparisonIso F G t f hf W hw₀ hw₁ hwp  -- t ≫ M ≅ 𝟙 Y
  ...
  exact ⟨t, hleft, ⟨hright⟩⟩
\`\`\`

1. *普遍的な族*：相対関手空間 $`Y` の恒等射を uncurry すると、$`Y` をパラメーターとする相対射の族 $`\mathrm{Un}(F)\times Y\to\mathrm{Un}(G)` が得られる。「$`Y` の各点が表す射そのもの」の族である。

2. *族の復元*：この族から、$`Y` をパラメーターとする変換の族 $`t\colon Y\to T` を作る（\`exists\_coherentFamily\_recovery\`、F1/SmallCoherentFamilyRecovery）。方法は、族の始域と終域を写像円柱（collage）で貼り合わせた fibration を作り、*それを straightening の構成で分類する*、というもの（docstring：「指定した標準表現を両端に保つ collage を分類し curry する」）。

3. \*\*$`M\circ t\cong\mathrm{id}`\*\*：「変換の族が相対射の族を実現する」という証拠（\`UnstraighteningFamilyWitness\`：持ち上げの prism と、始点・終点・射影の三条件）は、同型を除いて一意である（\`UnstraighteningFamilyWitness.unique\`）。$`M` の定義に使った普遍的な持ち上げも、$`t` から作った持ち上げも、どちらも同じ族の証拠なので一致する。

4. \*\*$`t\circ M\cong\mathrm{id}`\*\*：復元した族を $`M` で戻すと元の普遍的な族と比較できる（\`unstraighteningFamilyComparisonIso\`）。普遍的な族は $`Y` の恒等射なので、これは $`t\circ M\cong\mathrm{id}_Y` を意味する。

Yoneda の議論と同じ「普遍元」の型の証明である。2 で straightening の*構成*（分類写像）を使っているので、この定理は straightening から独立ではないが、straightening の同値定理は使っていない。

*unstraightening.html — 5. 写像空間の比較（Yoneda の h₁） — 可逆性の保存と反映*

$`M` が変換 $`\alpha` に対応させる射 $`\mathrm{Un}(F)\to\mathrm{Un}(G)` が同値であることと、$`\alpha` が可逆であることは同値（\`leftUnstraighteningMappingVertexMap\_isQCatEquivalence\_iff\`、F1/LeftUnstraighteningReflectsEquivalences）。fiber に制限し、普遍射影の transport から各点での可逆性を回収して示す。

:::definition "kerodon_5_6_6_1" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1")
Kerodon Definition 5.6.6.1（[Tag 038A](https://kerodon.net/tag/038A)）。対応表の状態：なし。

IsCorepresentableSmallSpaceFunctorは共変Hom関手とのFunctorIsoの存在。原文は指定頂点xで評価した同じ写像空間作用の同値性であり、その頂点による同値との比較が型にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsCorepresentableSmallSpaceFunctor`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity`

:::

:::definition "kerodon_5_6_6_2" (uses := "kerodon_1_4_0_1, kerodon_5_6_6_1")
Kerodon Variant 5.6.6.2（[Tag 038B](https://kerodon.net/tag/038B)）。対応表の状態：なし。

representablePresheafInfinityはHom前層の構成。原文の指定頂点が表現を与える述語とその存在の定義は直接与えない。

*定義 14.3 （表現可能前層）*

小さい quasicategory $`C` の頂点 $`y` について、前層 $`h_y` を合成

$$`h_y\colon C^{\mathrm{op}}\cong C^{\mathrm{op}}\times\Delta^0\xrightarrow{\ \mathrm{id}\times y\ }C^{\mathrm{op}}\times C\xrightarrow{\ \mathrm{Map}_C\ }\mathcal S`

で定め、$`y` が表現する前層という（$`\mathrm{Map}_C` は定義 12.5）。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity`

:::

:::definition "kerodon_5_6_6_10" (uses := "kerodon_1_2_5_1, kerodon_3_1_5_10")
Kerodon Definition 5.6.6.10（[Tag 02FR](https://kerodon.net/tag/02FR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：点付き左ファイブレーションの特例・局所 Kan・通常の Yoneda・反対と輸送を照合。hKan 豊穣圏と反対圏での指定した表現可能関手の関係。通常の EnrichedCategory の Hom と op の定義だけでは hKan 値の比較がない。

:::

:::theorem "kerodon_5_6_6_13" (uses := "kerodon_1_4_0_1, kerodon_4_7_3_20, kerodon_5_1_7_1, kerodon_5_6_0_6, kerodon_5_6_6_19, kerodon_5_6_6_21")
Kerodon Theorem 5.6.6.13（[Tag 038J](https://kerodon.net/tag/038J)）。対応表の状態：なし。

共変Hom関手とcoslice分類の同型はあるが、原文の指定頂点でのcorepresentabilityとその存在・一意性を返す型へ比較されていない。関手があるだけを表現可能性の証明としない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantCosliceClassificationIso`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantHomIsoOfCosliceEquivalence`

:::

:::definition "kerodon_5_6_6_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity") (uses := "kerodon_1_4_0_1, kerodon_5_6_6_13")
Kerodon Notation 5.6.6.14（[Tag 038L](https://kerodon.net/tag/038L)）。対応表の状態：一部。

homInfinityCovariantとcovariantRepresentableInfinityは原文の共変Hom(X,−)の候補を具体的な図式として直接構成する。指定頂点によるcorepresentabilityと局所小な大きいC全体、二変数での比較は含まない。

:::

:::proposition "kerodon_5_6_6_17" (uses := "kerodon_1_2_5_1, kerodon_4_6_7_3, kerodon_4_6_7_5, kerodon_5_6_6_1")
Kerodon Proposition 5.6.6.17（[Tag 038P](https://kerodon.net/tag/038P)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：点付き左ファイブレーションの特例・局所 Kan・通常の Yoneda・反対と輸送を照合。hc nerve 上の Space 値関手を、指定点が representable にするための条件。Yoneda の普遍性や一点の評価だけではこの enriched 側の特徴付けが出ない。

:::

:::proposition "kerodon_5_6_6_19" (uses := "kerodon_1_4_0_1, kerodon_4_2_5_4, kerodon_4_7_3_1, kerodon_4_7_3_9, kerodon_4_7_3_20, kerodon_4_7_3_22, kerodon_5_1_7_5")
Kerodon Proposition 5.6.6.19（[Tag 038R](https://kerodon.net/tag/038R)）。対応表の状態：なし。

IsInitialVertex.exists\_cosliceLiftは始対象から任意A→XをXのcosliceへ持ち上げる型。原文のC\_\{X/\}→Dの相対同値・評価のtrivial Kan性・π₀全単射とは別の対象と射。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex.exists_cosliceLift`

:::

:::corollary "kerodon_5_6_6_20" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.QCatEquivalence.map_isInitialVertex") (uses := "kerodon_1_4_0_1, kerodon_4_7_3_9, kerodon_5_6_6_19")
Kerodon Corollary 5.6.6.20（[Tag 03J6](https://kerodon.net/tag/03J6)）。対応表の状態：一部。

QCatEquivalence.map\_isInitialVertexは原文のFが同値なら指定始対象の像も始対象となる方向を同じFについて直接返す。左ファイブレーションの仮定すら不要。逆は含まない。

:::

:::proposition "kerodon_5_6_6_21" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representableUnstraighteningIdentity_isInitialVertex, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.parametrizedFiberTransport_evaluate_isQCatEquivalence_of_initialVertex") (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_6_4_1, kerodon_4_7_3_20, kerodon_5_1_7_16, kerodon_5_2_8_1, kerodon_5_2_8_7, kerodon_5_2_8_12, kerodon_5_6_6_10, kerodon_5_6_6_19")
Kerodon Proposition 5.6.6.21（[Tag 02J8](https://kerodon.net/tag/02J8)）。対応表の状態：一部。

parametrizedFiberTransport\_evaluate\_isQCatEquivalence\_of\_initialVertexは原文(1)の始対象⇒同じパラメーター付き輸送を指定点で評価した射の同値、という方向を直接返す。逆・豊穣表現可能性の各iffは含まない。

:::

# 5.6.7 Application: Extending Cocartesian Fibrations

%%%
number := false
tag := "kerodon-5-6-7"
%%%

Kerodon [Tag 029B](https://kerodon.net/tag/029B)

:::lemma_ "kerodon_5_6_7_1" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_4_4_9, kerodon_4_4_5_8, kerodon_5_1_7_9, kerodon_5_1_7_13")
Kerodon Lemma 5.6.7.1（[Tag 029C](https://kerodon.net/tag/029C)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左ファイブレーション・アノダインの特例・指数化と底変換・ファイバーと宇宙の特例を照合。C の部分複体上の指定同型を延長する cocartesian fibration の四角。通常の底変換の pullback 同型は任意の部分複体からの延長ではない。

:::

:::proposition "kerodon_5_6_7_2" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_1_7_14, kerodon_5_5_3_3, kerodon_5_6_0_2, kerodon_5_6_2_2, kerodon_5_6_7_1")
Kerodon Proposition 5.6.7.2（[Tag 029E](https://kerodon.net/tag/029E)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左ファイブレーション・アノダインの特例・指数化と底変換・ファイバーと宇宙の特例を照合。部分複体上の cocartesian fibration とファイバーの条件を持つ引き戻しによる延長。指定した底上の分類の型では延長先を作らない。

:::

:::corollary "kerodon_5_6_7_3" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_1_3_3, kerodon_4_5_4_14, kerodon_5_1_4_1, kerodon_5_6_7_2")
Kerodon Corollary 5.6.7.3（[Tag 029F](https://kerodon.net/tag/029F)）。対応表の状態：なし。

引用は既に大きい底の上にあるleft fibrationの表現を延長する。原文は底と全空間のfibration自体をinner anodyneな底変更で拡張する存在であり、対象が異なる。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_leftTransportRepresentation_extension_innerAnodyne`

:::

:::corollary "kerodon_5_6_7_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianFibration_kanEquivalenceLifting, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianFibration_kanInvertibleTargetLifting") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_1_4_9, kerodon_5_6_7_3")
Kerodon Corollary 5.6.7.5（[Tag 029G](https://kerodon.net/tag/029G)）。対応表の状態：一部。

底を準圏に強めるとcocartesianFibration\_kanEquivalenceLiftingは同じUのequivalence liftingを直接与え、inner性と可逆辺の持ち上げというisofibration判定に一致する。

:::

:::corollary "kerodon_5_6_7_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianFibration_pullback_innerAnodyne_isPrecompositionEquivalence") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_8_10, kerodon_5_1_4_1, kerodon_5_3_6_1, kerodon_5_6_7_3")
Kerodon Corollary 5.6.7.6（[Tag 029H](https://kerodon.net/tag/029H)）。対応表の状態：一部。

底の圏同値をinner anodyneに制限するとcocartesianFibration\_pullback\_innerAnodyne\_isPrecompositionEquivalenceは同じpullback projectionの圏同値性を直接返す。任意の圏同値への一般化は含まない。

:::

:::corollary "kerodon_5_6_7_7" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_1_5_16, kerodon_5_6_7_3, kerodon_5_6_7_6")
Kerodon Corollary 5.6.7.7（[Tag 03TX](https://kerodon.net/tag/03TX)）。対応表の状態：なし。

HasSmallSimplexFibers.essentiallySmallは宇宙版の頂点fiberの小ささ。原文の数値κとcf(κ)、全空間のessentiallyκ-smallとのiffのいずれの方向も直接返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers.essentiallySmall`

:::

:::corollary "kerodon_5_6_7_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_relativeFunctorInverse_of_precompositionEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_iff_isQCatEquivalence")
Kerodon Corollary 5.6.7.8（[Tag 029K](https://kerodon.net/tag/029K)）。対応表の状態：一部。

底を準圏、U,Vをleft fibrationに強めれば、圏同値Fを前合成同値へ移しexists\_relativeFunctorInverse\_of\_precompositionEquivalenceで同じFの底上の相対逆と相対単位・余単位を直接得る。一般cocartesian版と逆は含まない。

:::

# 5.6.8 Transport Witnesses

%%%
number := false
tag := "kerodon-5-6-8"
%%%

Kerodon [Tag 02S9](https://kerodon.net/tag/02S9)

:::definition "kerodon_5_6_8_1"
Kerodon Notation 5.6.8.1（[Tag 02SA](https://kerodon.net/tag/02SA)）。対応表の状態：なし。

transportWitnessSpaceは空間値のleft transportの証人全体。原文TWはQC値表現の証人全体であり、Uがleft fibrationでも任意QC値表現を空間値データに同定する比較なしには同じ部分単体集合にならない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace`

:::

:::theorem "kerodon_5_6_8_3" (uses := "kerodon_1_1_0_6, kerodon_1_1_4_12, kerodon_1_2_5_1, kerodon_3_2_7_2, kerodon_5_1_4_1, kerodon_5_6_8_10, kerodon_5_6_9_1, kerodon_5_6_9_2")
Kerodon Theorem 5.6.8.3（[Tag 02SC](https://kerodon.net/tag/02SC)）。対応表の状態：なし。

可縮性の型は空間値のtransportWitnessSpace。原文のQC値表現全体のTWとの比較がないので、left fibrationに制限しても同じTWの可縮性とは言えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallTransportWitnessSpace_isContractibleKan`

:::

:::lemma_ "kerodon_5_6_8_5" (uses := "kerodon_1_1_0_6, kerodon_1_5_4_13, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_4_13")
Kerodon Lemma 5.6.8.5（[Tag 02SE](https://kerodon.net/tag/02SE)）。対応表の状態：なし。

引用のIsRepresentationは空間値left transportのfiber同値条件。原文のQC\_Objによる指定四角が表現になる条件との同定がない。頂点全射での検出は類似の判定。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SquareRepresentationRestriction.LeftTransportSquare.isRepresentation_iff_restrict_of_vertexSurjective`

:::

:::lemma_ "kerodon_5_6_8_6" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_1_5_3_7, kerodon_1_5_7_5, kerodon_4_1_4_3, kerodon_5_1_1_1, kerodon_5_1_1_9, kerodon_5_1_2_4, kerodon_5_1_4_1, kerodon_5_6_8_5")
Kerodon Lemma 5.6.8.6（[Tag 02SF](https://kerodon.net/tag/02SF)）。対応表の状態：なし。

引用は空間値LeftTransportSquareの表現条件を可逆辺に沿って保つ。原文のQC値の全四角のMとそのreplete部分TWは別の対象で、同定する比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare.isRepresentation_of_edge`

:::

:::lemma_ "kerodon_5_6_8_7" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_4_2_1, kerodon_4_4_3_19, kerodon_4_4_4_4, kerodon_5_1_1_1, kerodon_5_1_1_11, kerodon_5_1_4_1, kerodon_5_2_5_2, kerodon_5_6_8_6")
Kerodon Lemma 5.6.8.7（[Tag 02SG](https://kerodon.net/tag/02SG)）。対応表の状態：なし。

Kan性の型は空間値left transportの証人空間。原文のQC値の全表現のTWとの比較を欠くため、同じ対象の特殊形の結論ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace_kanComplex`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessEdge_isInvertible`

:::

:::definition "kerodon_5_6_8_9" (uses := "kerodon_1_1_0_6, kerodon_5_1_4_1")
Kerodon Notation 5.6.8.9（[Tag 02SJ](https://kerodon.net/tag/02SJ)）。対応表の状態：なし。

引用の制限写像は空間値TW間。原文のQC値TWの指定制限射との比較がなく、余極限から極限への保存の主張も含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction`

:::

:::lemma_ "kerodon_5_6_8_10" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_1_5_7_6, kerodon_4_4_5_1, kerodon_4_4_5_3, kerodon_4_5_6_18, kerodon_5_1_4_1, kerodon_5_3_6_6, kerodon_5_6_8_5, kerodon_5_6_8_6, kerodon_5_6_8_7, kerodon_5_6_8_9")
Kerodon Lemma 5.6.8.10（[Tag 02SK](https://kerodon.net/tag/02SK)）。対応表の状態：なし。

引用のfibration性とinner anodyneでのtrivial性は空間値TWの制限。原文のQC値のTWの制限と同じ射である比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportRepresentationInnerExtension_isContractibleKan`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction_trivialKanFibration_of_innerAnodyne`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.WitnessRestrictionFibration.transportWitnessRestriction_fibration`

:::

# 5.6.9 Proof of the Universality Theorem

%%%
number := false
tag := "kerodon-5-6-9"
%%%

Kerodon [Tag 02SM](https://kerodon.net/tag/02SM)

:::lemma_ "kerodon_5_6_9_1" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_2_7_2, kerodon_3_2_8_1, kerodon_3_3_7_6, kerodon_3_4_1_5, kerodon_3_4_1_11, kerodon_4_4_3_7, kerodon_4_4_5_1, kerodon_4_4_5_7, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_2_1_1, kerodon_5_2_1_3, kerodon_5_2_2_4, kerodon_5_2_2_8, kerodon_5_2_4_2, kerodon_5_2_8_1, kerodon_5_5_5_14, kerodon_5_6_8_10")
Kerodon Lemma 5.6.9.1（[Tag 02SN](https://kerodon.net/tag/02SN)）。対応表の状態：なし。

引用は一点上の空間値証人空間を関手空間として区間境界へ制限する射。原文のΔ¹上の一般cocartesian fibrationのQC値TWの制限への同定がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointWitnessIntervalBoundary_trivialKanFibration`

:::

:::lemma_ "kerodon_5_6_9_2" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_5_1_33, kerodon_5_6_8_7, kerodon_5_6_9_1")
Kerodon Lemma 5.6.9.2（[Tag 02SR](https://kerodon.net/tag/02SR)）。対応表の状態：なし。

引用は一点上のleft fibrationの空間値証人空間。原文の任意の準圏EのQC値TWと比較する型がなく、EがKanという制限だけでは同じ証人空間にならない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointTransportWitnessSpace_isContractibleKan`

:::

