-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberConnecting
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorSuspension
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFunctorCriterion
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorFiniteLimits
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorPullbackComparison
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorPullbackSquares
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.HomotopyBinaryBiproduct
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.HomotopyPreadditive
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopEquivalenceExcision
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopEquivalenceStability
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionEquivalence
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionEquivalenceOfLoopEquivalence
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TriangulatedInstance
import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.CoproductRealizationColimits
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.FiniteCoproductColimitGeneration
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.CoproductRealizationConditions
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.ExactFunctor
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.LocallySmall
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalVertices

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 1.4 Spectra and Stabilization" =>
%%%
number := false
tag := "ha-1-4"
%%%

HA 1.4 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 1.4.1 The Brown Representability Theorem

%%%
number := false
tag := "ha-1-4-1"
%%%

:::proposition "ha_1_4_1_3" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.preadditive_ho, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasBinaryBiproducts_ho")
*HA 例 1.4.1.3*　コンパクト生成な安定 ∞ 圏への Brown の定理の適用（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=135)）。対応表の状態：一部（component）。

*主張*　可提示安定 ∞ 圏の各対象はホモトピー圏で余群対象になり、コンパクト生成なら Brown 表現可能性の定理の仮定を満たす。

KB-W2型再照合：仮定：安定準圏（Lean が弱い：presentable 性は不要）。結論：ホモトピー圏の前加法性と双積があり、原典冒頭の加法性に対応する（Lean が弱い：各対象の余群構造と compactly generated な場合の Brown の全仮定の確認は含まれない）。

ホモトピー圏が加法的で、対角射を余積への余積構造として使える。したがってコンパクト生成の場合には、余群対象を生成に使う条件が成り立つ。

:::

:::definition "ha_1_4_1_6" (lean := "CategoryTheory.Functor.IsHomological, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isTriangulated_ho")
*HA 定義 1.4.1.6*　点付き ∞ 圏上のコホモロジー理論（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=135)）。対応表の状態：一部（special）。

*主張*　点付きで小余極限を持つ ∞ 圏上のコホモロジー理論は、懸垂で次数が一つずれる反変集合値関手の族で、余積を積に移し、余ファイバー列の中央で完全性を満たす。

Cを安定準圏とし、各HnがhCop上のAb値ホモロジー関手のunderlying Set関手として与えられる場合、cofiberTriangle\_memとIsHomological.exactは同じcofiber列に対する条件(2)のkernel-image完全性を直接返す。次数族全体・δと小余積保存の条件(1)は含まない。

零対象で一点になるので、各値には零元が定まる。余ファイバー列 $`C'\to C\to C''` に対して、$`H^n(C')` で零になる $`H^n(C)` の元が $`H^n(C'')` から来ることを要求する。

:::

:::proposition "ha_1_4_1_8" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension, CategoryTheory.Functor.map_distinguished_exact")
*HA 注意 1.4.1.8*　余ファイバー列に伴う長完全列（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=136)）。対応表の状態：一部（component）。

*主張*　コホモロジー理論を余ファイバー列に適用すると、懸垂への接続射を用いたアーベル群の長完全列を得る。

cofiberConnectingToSuspensionは原文最初の同じcofiber列のC″→ΣC′という境界射の構成を直接与える。Hnとδnから長完全列全体を組み立てる型は含まない。

接続射 $`C''\to\Sigma C'` と懸垂同型から $`H^n(C')\to H^{n+1}(C'')` が得られる。余ファイバー列を順に回転して定義の中央での完全性を適用すると、他の項でも完全性が従う。

:::

# 1.4.2 Spectrum Objects

%%%
number := false
tag := "ha-1-4-2"
%%%

*spectra-k-theory.html — 1. スペクトルの ∞ 圏 — 定義：安定化*

$$`\mathrm{Sp}:=\lim\bigl(\cdots\xrightarrow{\Omega}\mathcal S_*\xrightarrow{\Omega}\mathcal S_*\xrightarrow{\Omega}\mathcal S_*\bigr).`

対象は $`\Omega` スペクトル（列 $`(X_n)` と同値 $`X_n\simeq\Omega X_{n+1}`）。古典論の「圏を作ってから弱同値で局所化する」手順が要らず、最初からホモトピー的な対象として定義される。一般の有限極限を持つ $`\mathcal C` には $`\mathrm{Sp}(\mathcal C):=\mathrm{Exc}_*(\mathcal S^{\mathrm{fin}}_*,\mathcal C)`（reduced excisive 関手、Goodwillie 微積分の 1 階部分、HA §1.4）。

:::definition "ha_1_4_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices") (uses := "htt_1_1_2_4")
*HA 定義 1.4.2.1*　切除的関手と被約関手（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=141)）。対応表の状態：本体にある。

*主張*　押し出しを引き戻しに移す関手を切除的といい、終対象を終対象に移す関手を被約という。

同じFに∀R, IsPushoutSquare R→IsPullbackSquare(R≫F)を課し、指定終頂点\*にIsTerminalVertex(F(\*))を課せばexcisive/reducedの定義そのもの。functorVertexEquivとfullSubcomplexOnVerticesへその二条件・論理積を代入すれば三つの指定全部分準圏も直接構成できる。

押し出しと終対象が始域にある場合、切除的関手、被約関手、それら両方を満たす関手の充満部分圏を関手圏に取れる。

:::

:::proposition "ha_1_4_2_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesPushoutSquare, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesPullbackSquare, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_of_preservesFiber")
*HA 注意 1.4.2.2*　安定 ∞ 圏を始域または終域とする被約切除的関手（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=141)）。対応表の状態：一部（special）。

*主張*　点付き有限余完備な始域の場合、被約・切除的であることは、始域が安定なら左完全性、終域が安定なら右完全性と同値である。

KB-W2型再照合：仮定：両準圏が安定（Lean が強い：HA は始域のみ又は標的のみが安定な場合も述べる）。結論：完全関手が押し出し・引き戻しを保ち、零と fiber 列の保存から完全性が従う（Lean が弱い：片側だけが安定な場合を含めた左・右完全性との同値はこの型に含まれない）。

両方が安定なら完全性と同値になる。零対象が被約性に対応し、安定圏で引き戻しと押し出しが一致することを使う。

:::

:::proposition "ha_1_4_2_3" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_functorCategory, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPullbackSquare_functor_iff") (uses := "htt_1_1_2_4")
*HA 注意 1.4.2.3*　切除的関手の極限に対する閉性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=141)）。対応表の状態：一部（special）。

*主張*　終域が $`K`-型極限を持てば関手圏もそれらを持ち、切除関手と、始域に終対象がある場合の被約関手は、それぞれその極限で閉じている。

Kを有限形状に限りDに全有限極限も要求するとhasFiniteLimits\_functorCategoryは原文最初の同じFun(C,D)のK極限存在を直接返す。切除的・縮約関手の部分準圏の閉性は含まない。

極限を点ごとに計算する。切除性には極限と引き戻しの交換を、被約性には終対象の定値図式の極限が終対象であることを使う。

:::

:::definition "ha_1_4_2_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt")
*HA 記法 1.4.2.5*　点付き空間と有限空間（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=141)）。対応表の状態：一部（component）。

*主張*　$`\mathcal S_*` は終空間からの射で表す点付き空間の圏であり、有限空間は点から有限余極限で生成される。

同じSpaceの矢準圏にfullSubcomplexOnVerticesを使い、始点のIsTerminalVertexを頂点条件に入れれば原文のS\*の構成を直接与える。固定一点のcosliceという別模型への比較ではなく、その指定全部分圏を用いる。Sfinとそのpointed部分は含まない。

基礎空間が有限である点付き空間を集めると $`\mathcal S_*^{\mathrm{fin}}` となる。懸垂はこの部分圏を保ち、$`S^n` は点付き $`n` 次元球面の代表を指す。

:::

:::proposition "ha_1_4_2_11" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isStable_of_loopEquivalence, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_of_isPullback_of_loopEquivalence") (uses := "ha_1_1_1_1, ha_1_4_2_13, htt_1_1_2_4")
*HA 命題 1.4.2.11*　懸垂・ループの充満忠実性と正方形の極限・余極限（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=142)）。対応表の状態：一部（component）。

*主張*　有限極限・有限余極限を持つ点付き ∞ 圏で、懸垂が充満忠実なら押し出しは引き戻し、ループが充満忠実なら引き戻しは押し出しである。ループが同値なら圏は安定である。

KB-W2型再照合：仮定：点付き準圏に有限極限と loop 図式の切断を取り、その loop が同値（第3項では Lean が弱い：有限余極限は不要。第1・2項では Lean が強い：完全忠実性だけの条件に対して loop 同値を要求）。結論：安定性、および引き戻しなら押し出し（Lean が弱い：完全忠実な suspension または loop だけからの二方向をこの型は与えない）。

懸垂とループは随伴なので、それぞれの充満忠実性を単位または余単位の同値として使える。ループが同値なら、その随伴で懸垂も同値になる。

:::

:::definition "ha_1_4_2_12" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorPullbackComparisonEdge, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorPullbackComparisonFamily") (uses := "htt_1_1_2_4")
*HA 記法 1.4.2.12*　正方形および懸垂に付随する比較射（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=143)）。対応表の状態：一部（component）。

*主張*　四角形の関手像には左上から残りの三頂点の引き戻しへの標準比較があり、零対象を含む懸垂の四角形の場合は $`F(X)\to\Omega_DF(\Sigma_C X)` になる。

KB-W2型再照合：仮定：四角形の関手族とその右上・左下・右下の極限錐を選ぶ（HA と一致：有限極限は選択された錐を与える）。結論：元の左上頂点から引き戻しへの比較辺とその関手族（Lean が弱い：零角の場合の F(X)→ΩF(ΣX) との同定はこの型に含まれない）。

終域に有限極限を仮定して比較の標的を作る。二つの零対象とその像が零なら、引き戻しの項はループになる。

:::

:::proposition "ha_1_4_2_13" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sends_pushouts_to_pullbacks_of_suspensionSquares") (uses := "ha_1_1_1_1, ha_1_4_2_1, ha_1_4_2_11, ha_1_4_2_12, htt_1_1_2_4")
*HA 命題 1.4.2.13*　懸垂とループの比較による切除性の判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=143)）。対応表の状態：一部（stronger-hyp）。

*主張*　点付き有限余完備な圏から点付き有限完備な圏への被約関手が切除的であることは、各対象で $`F(X)\to\Omega_DF(\Sigma_C X)` が同値となることに等しい。

原文の縮約関手Fに、全suspension正方形の像がpullbackであるという入力も追加するとsends\_pushouts\_to\_pullbacks\_of\_suspensionSquaresは同じFのexcisive性を直接返す。指定ηXの可逆性だけからこの追加入力を得たとはしない。

切除性からこの判定は懸垂を定める押し出しに適用して得られる。逆向きは、その特殊な比較から任意の押し出し四角形の比較を復元する。

:::

:::corollary "ha_1_4_2_14" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExactFunctor.preservesSuspensionDiagramVertex, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sends_pushouts_to_pullbacks_of_suspensionSquares, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor")
*HA 系 1.4.2.14*　零対象と懸垂の保存による完全性の判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=143)）。対応表の状態：一部（component）。

*主張*　安定 ∞ 圏の間の関手の完全性は、零対象を保つことと、標準比較 $`\Sigma_DF(X)\to F(\Sigma_C X)` が各対象で同値であることで判定できる。

同じ完全関手FのIsExactFunctor.preservesZeroは原文の右辺(1)の零対象保存を直接返す。指定された標準比較ΣF(X)→FΣ(X)の可逆性と全iffはこの引用だけでは含まない。

零対象を保つと関手は被約である。懸垂比較をループとの随伴で移すと、前項の切除性の判定に一致する。

:::

:::corollary "ha_1_4_2_27" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isStable_of_loopEquivalence, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionQCatEquivalence, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctorOfLoopEquivalence_isQCatEquivalence")
*HA 系 1.4.2.27*　点付き ∞ 圏の安定性の同値条件（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=149)）。対応表の状態：一部（component）。

*主張*　点付き ∞ 圏の安定性は、有限余極限があり懸垂が同値であること、または有限極限がありループが同値であることのいずれでも判定できる。

KB-W2型再照合：仮定：点付き準圏に有限極限と選択 loop を置く場合、または既に安定な場合（HA と一致する方向別の仮定）。結論：loop 同値から安定性、安定性から互いに逆な suspension と loop、loop 同値から対応する suspension 同値（Lean が弱い：有限余極限と suspension 同値だけを入力する安定性の逆方向はこれらの型に現れない）。

安定圏では懸垂とループが互いに逆になる。逆向きには片方の存在と可逆性から、必要な双対の極限または余極限と四角形の条件を得る。

:::

# 1.4.3 The ∞-Category of Spectra

%%%
number := false
tag := "ha-1-4-3"
%%%

*spectra-k-theory.html — 1. スペクトルの ∞ 圏 — 普遍性*

- *自由安定化*：$`\Sigma^\infty_+\colon\mathcal S\to\mathrm{Sp}` は 1 点から生成される余極限で閉じた自由な安定 ∞ 圏。$`\mathrm{Pr}^L` では $`\mathrm{Sp}=\mathrm{colim}(\mathcal S_*\xrightarrow{\Sigma}\mathcal S_*\xrightarrow{\Sigma}\cdots)`（$`\mathrm{Pr}^R` での $`\Omega` に沿った極限と一致）。

- *冪等代数*：$`\mathrm{Sp}` は $`\mathrm{Pr}^L` の冪等可換代数で、$`\mathrm{Pr}^L_{\mathrm{st}}\simeq\mathrm{Mod}_{\mathrm{Sp}}(\mathrm{Pr}^L)`、$`\mathrm{Sp}\otimes\mathcal C\simeq\mathrm{Sp}(\mathcal C)`。安定性は構造でなく性質になる。

- *smash 積*：単位 $`\mathbb S`、各変数で余極限を保つ対称モノイダル構造は一意（HA §4.8.2）。symmetric/orthogonal spectra や EKMM の $`S`-modules が解こうとした問題（結合的・可換な smash 積）は普遍性から自動的に解ける。$`E_\infty` 環 $`=\mathrm{CAlg}(\mathrm{Sp})`。

*spectra-k-theory.html — 1. スペクトルの ∞ 圏 — 内在的に展開できるもの*

t 構造（heart $`\simeq\mathrm{Ab}`、Postnikov 塔）、Brown 表現定理（HA §1.4）、Bousfield 局所化、パラメータ付きスペクトル $`\mathrm{Fun}(X,\mathrm{Sp})` と Thom スペクトル（Ando–Blumberg–Gepner–Hopkins–Rezk）、THH/TC（Nikolaus–Scholze、Tate 構成と Frobenius）、同変スペクトル（$`S^V` の形式的逆元化、スペクトル的 Mackey 関手）、$`\mathrm{SH}(S)`（$`\mathbb P^1` の逆元化、Robalo）。

モデル圏がまだ関わるところ

- ∞ 圏論の基礎：HTT は擬圏を Joyal モデル構造で扱う（直線化、$`\mathcal S` の構成、$`\mathrm{Pr}^L` のテンソル積）。回避の試みとして Riehl–Verity の ∞-cosmos、Cisinski–Cnossen–Nguyen–Walde の合成的なアプローチがある（到達点は未確認）。

- 古典的な点集合モデルとの比較（Mandell–May–Schwede–Shipley）。

- 個別の構成：$`E_\infty` 構造の障害理論（Goerss–Hopkins–Miller）。∞ 的な構成（Lurie, Elliptic II）もあり、文献上は混在。

# 1.4.4 Presentable Stable ∞-Categories

%%%
number := false
tag := "ha-1-4-4"
%%%

:::proposition "ha_1_4_4_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.preservesSmallColimits_of_coproducts_finite, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.hasSmallColimits_iff_coproducts_geometricRealizations")
*HA 命題 1.4.4.1*　安定 ∞ 圏における小余極限と小余積（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=154)）。対応表の状態：一部（stronger-hyp）。

*主張*　安定 ∞ 圏での小余極限の存在は小余積の存在で判定でき、完全関手によるその保存も小余積の保存で判定できる。

原文(2)の同じFに全有限図式の保存余極限HasPreservedColimitも追加すれば、preservesSmallColimits\_of\_coproducts\_finiteは小余積保存⇒同じFの全小余極限保存を直接返す。安定性・exactだけからこの追加入力を供給したとはせず、(1)(3)と全iffは含まない。

さらに小余極限を持つ場合、$`X` がコンパクトであることは、$`X` から任意の小余積への射がホモトピーまで有限部分余積を経由することで特徴付けられる。

:::

:::corollary "ha_1_4_4_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsPresentable.isLocallySmall, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isPresentable_iff_cocompleteIndEquivalence, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallColimits.hasSmallCoproducts")
*HA 系 1.4.4.2*　安定 ∞ 圏の表示可能性の判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=155)）。対応表の状態：一部（component）。

*主張*　安定 ∞ 圏の可提示性は、小余積があり、ホモトピー圏が局所小で、ある正則基数でコンパクトな生成対象が存在することと同値である。

同じpresentableなCの全小余極限存在からHasSmallColimits.hasSmallCoproductsは原文右辺(1)の同じCの小余積存在を直接返す。hCの局所小性と単一κ-compact生成対象という残る条件、逆向きは含まない。

ここで生成対象 $`X` から $`Y` へのホモトピー類の集合が一点なら、$`Y` は零対象になる。小余積を安定性と組み合わせて小余極限を得る。

:::

:::definition "ha_1_4_4_12" (lean := "SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices, CategoryTheory.Triangulated.TStructure")
*HA 定義 1.4.4.12*　アクセシブルな t 構造（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=160)）。対応表の状態：本体にある。

*主張*　可提示安定 ∞ 圏の $`t` 構造は、非負部分 $`C_{\ge0}` が可提示なとき可到達と呼ぶ。

t.ge 0の頂点述語で張る同じC≥0をfullSubcomplexOnVerticesで取り、そのIsPresentableを課せば、原文のaccessibleなt-structureの定義全体に一致する。接続説明の小生成族からの存在定理まではこの定義の対応に含めない。

定義の判定は非負部分圏で行う。$`C_{\le0}` の濾過余極限に関する条件は別の両立性の定義に現れる。

:::

