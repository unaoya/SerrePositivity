import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex.MulStruct
import Mathlib.AlgebraicTopology.SimplicialSet.RelativeMorphism
import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakFiniteSubsetColimit
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AcyclicFiber
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AcyclicKanLifting
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryNormalization
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.Commutativity
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.F1PointedAcyclicFibrationLifting
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.F1PointedPointedHomotopy
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FiberComponents
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationBoundary
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationExactness
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationMultiplication
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSequence
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FilteredNullHomotopy
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FilteredPointwiseWeakEquivalences
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyDegreeZero
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyGroups
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyInvariance
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanWhiteheadComparison
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.NullHomotopyRestriction
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.PointedKanWhitehead
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence
import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.SphericalBoundaryMap
import SerrePositivity.Spectra.Pointed.Cofiber
import SerrePositivity.Spectra.PointedSimplicialSet.Basic

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "3.2 Homotopy Groups" =>
%%%
number := false
tag := "kerodon-3-2"
%%%

Kerodon の 3.2 節（[Tag 00V2](https://kerodon.net/tag/00V2)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 3.2.1 Pointed Kan Complexes

%%%
number := false
tag := "kerodon-3-2-1"
%%%

Kerodon [Tag 00V4](https://kerodon.net/tag/00V4)

:::definition "kerodon_3_2_1_1"
Kerodon Definition 3.2.1.1（[Tag 050N](https://kerodon.net/tag/050N)）。対応表の状態：なし。

B6：RelativeMorphism の生成同値の商と、原文の相対内部 Hom の頂点ファイバーの π₀ の同定がない。 候補：同じ K 上の制限を固定した写像を、K 上一定の円柱ホモトピーで生成する関係で割る。引用では原文の相対内部 Hom の頂点ファイバーの π₀ と直接同定していない。

宣言：`SSet.RelativeMorphism.HomotopyClass`

:::

:::definition "kerodon_3_2_1_3" (lean := "SSet.RelativeMorphism.Homotopy")
Kerodon Definition 3.2.1.3（[Tag 050Q](https://kerodon.net/tag/050Q)）。対応表の状態：Mathlib にある。

*主張*　ホモトピー $`\Delta^1\times X\to Y` が単体部分集合 $`K\subseteq X` に沿って一定とは、$`\Delta^1\times K` 上で射影 $`\Delta^1\times K\to K` を経由することである。

仮定：単体集合 X,Y、部分複体 K≤X と K 上で同じ写像に制限する二射（Kerodon と一致。Lean は像を含む標的の部分複体も指定でき、Y 全体に取れる）。結論：円柱ホモトピーで、K×Δ¹ 上は K への射影を経由して固定写像に一致するという条件（一致）。

:::

:::proposition "kerodon_3_2_1_4"
Kerodon Proposition 3.2.1.4（[Tag 00V9](https://kerodon.net/tag/00V9)）。対応表の状態：なし。

B6：引用の exists\_extension は既に指定された H の延長であり、原文の相対ホモトピー関係の有限鎖/一段との iff を直接述べない。 候補：一般の RelativeMorphism.HomotopyClass は相対ホモトピーの生成同値で割る。原文の写像空間の成分との比較と、Kan 標的で一段に縮める一般の相対同値は未確認。

宣言：`SSet.RelativeMorphism.HomotopyClass`、`SerrePositivity.SimplicialModel.KanMonoRelativeHomotopy.exists_extension`

:::

:::definition "kerodon_3_2_1_5" (lean := "SerrePositivity.PointedSimplicialSet")
Kerodon Definition 3.2.1.5（[Tag 00V5](https://kerodon.net/tag/00V5)）。対応表の状態：一部。

*主張*　基点付き単体集合は頂点を一つ選んだ単体集合であり、台が Kan 複体なら基点付き Kan 複体である。基点付き Kan 複体の圏の射は基点を保つ写像とする。

B6：PointedSimplicialSet は PointedObject SSet で、原文の点付き単体集合と基点を保つ射を直接与える。Kan の対象だけに絞る Kan\_\* の圏の構成は含まない。

:::

:::definition "kerodon_3_2_1_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedRelativeHomotopy")
Kerodon Definition 3.2.1.7（[Tag 00V7](https://kerodon.net/tag/00V7)）。対応表の状態：一部。

*主張*　基点付き写像の基点付きホモトピーは、始域の基点上で標的の基点に一定であるホモトピーである。基点付きでホモトピックであることは、基点に相対的なホモトピー関係をいう。

B6：pointedRelativeHomotopy は円柱が全時刻で基点を保つという原文の pointed homotopy のデータを直接構成する。生成した点付きホモトピー関係と写像空間の成分との iff は含まない。

:::

:::definition "kerodon_3_2_1_10"
Kerodon Notation 3.2.1.10（[Tag 00VC](https://kerodon.net/tag/00VC)）。対応表の状態：なし。

B6：一点の相対ホモトピー商と、原文の点付き写像空間の π₀ の比較がない。 候補：RelativeMorphism.HomotopyClass を一点の部分複体に特殊化すると、基点固定ホモトピーで生成した商を得る。原文の点付き写像空間の π₀ との同定は未確認。

宣言：`SSet.RelativeMorphism.HomotopyClass`

:::

:::definition "kerodon_3_2_1_12"
Kerodon Construction 3.2.1.12（[Tag 00VE](https://kerodon.net/tag/00VE)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。点付き単体集合の普通圏と相対ホモトピー類の型は別々にある。点付き Kan 複体を対象、基点固定ホモトピー類を射とする商圏は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_2_1_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_pointedHomotopyInverse, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfBasedHomotopyInverse, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_homotopyEquivalence") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_1_7_1, kerodon_3_2_1_14")
Kerodon Proposition 3.2.1.13（[Tag 00WW](https://kerodon.net/tag/00WW)）。対応表の状態：一部。

*主張*　基点付き Kan 複体の射が台の単体集合でホモトピー同値であることと、基点付きホモトピー同値であることは同値である。

B6：exists\_pointedHomotopyInverse は全基点・全次数の π 同型という強い仮定から、原文の基点固定の両側逆と二つのホモトピーを直接返す。kanPiIsomorphism\_of\_homotopyEquivalence も同じ f に対する一段の逆からこの仮定を返す。有限鎖だけの非点付き逆からの完全な iff は含めない。

:::

:::lemma_ "kerodon_3_2_1_14" (uses := "kerodon_1_2_5_1, kerodon_3_1_3_3")
Kerodon Lemma 3.2.1.14（[Tag 04GD](https://kerodon.net/tag/04GD)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。PointedKanWhitehead は全次数の π 同型から点付き両側逆を作る。任意に指定した片側の逆と非点付きホモトピーだけを基点固定へ直す宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_2_1_15"
Kerodon Proposition 3.2.1.15（[Tag 02LD](https://kerodon.net/tag/02LD)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。pointedRelativeHomotopy は既に基点を固定する円柱を受け取る。自由な null homotopy の存在から基点固定の null homotopy を得る宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.2.2 The Homotopy Groups of a Kan Complex

%%%
number := false
tag := "kerodon-3-2-2"
%%%

Kerodon [Tag 00VJ](https://kerodon.net/tag/00VJ)

:::definition "kerodon_3_2_2_1" (lean := "SerrePositivity.PointedObject.cofiber, SerrePositivity.PointedObject.cofiberQuotient, SerrePositivity.PointedObject.cofiberQuotient_condition")
Kerodon Notation 3.2.2.1（[Tag 00VK](https://kerodon.net/tag/00VK)）。対応表の状態：本体にある。

*主張*　単体部分集合 $`A\subseteq B` を一点へ潰す押し出しを $`B/A` と書き、その点を基点とする。

仮定：単体集合 B と部分複体 A≤B（Lean が弱い：カルテシアンモノイダル圏の任意の射 f と、終対象への押し出しがあればよい）。結論：B←A→\* の押し出しを \* からの射で点付けた B/A と、A を基点へ潰す商射（一致）。

:::

:::definition "kerodon_3_2_2_4"
Kerodon Construction 3.2.2.4（[Tag 00VN](https://kerodon.net/tag/00VN)）。対応表の状態：なし。

B6：球面からの点付き写像のホモトピー類との比較がなく、境界定値単体の別の商だけでは同じ π\_n の構成を得ない。 候補：KanHomotopy X n x は境界を x に固定した標準 n 単体の商で、n=0 と正次数を分ける。球面は cofiber で構成できるが、球面からの点付きホモトピー類との比較は未確認。

*f-01-simplicial-kan.html — 3. ホモトピー群（Kan） — 3.1 定義*

Kan 複体 $`X` と頂点 $`x` について、$`\pi_n(X, x)` は、境界を $`x` に送る $`n` 単体 $`\Delta^n \to X` のホモトピー類である。Mathlib はその材料（基点付きの単体 \`PtSimplex\`、関係 \`RelStruct\`、積の構造 \`MulStruct\`、π₀ \`SSet.π₀\`）を持つが、群そのものは持っていない。群は KST/Spectra で作られている。

- 宣言　／　意味　／　場所
- \`KanHomotopyGroup X n x\`　／　$`\pi_{n+1}(X, x)`（*添字が一つずれている*）。群で、$`n \ge 1`（$`\pi_{\ge 2}`）なら可換群　／　KST/Spectra/HomotopyGroups.lean:94、Commutativity.lean:447
- \`KanHomotopyZero X x\`　／　$`\pi_0` を基点付き集合とみたもの　／　KST/Spectra/HomotopyDegreeZero.lean:26
- \`KanHomotopy X n x\`　／　本来の添字の $`\pi_n`：$`0 \mapsto` \`KanHomotopyZero\`、$`n+1 \mapsto` \`KanHomotopyGroup X n\`　／　KST/Spectra/HomotopyIndexing.lean:25

*f-01-simplicial-kan.html — 3. ホモトピー群（Kan） — 3.2 写像、不変性、π\_\ 同型*

- Kan 複体の写像は、ホモトピー群の準同型を誘導する。基点付きホモトピーで移り合う写像は、同じ準同型を誘導する（\`KanHomotopyGroup.map\_eq\_of\_basedHomotopy\`）。

- \`KanPiIsomorphism f\`：すべての基点とすべての $`n` で $`\pi_n(f)` が全単射であること（KST/Spectra/HomotopyIsomorphism.lean:27）。

- 基点のないホモトピーで移り合う二つの写像は、同時に π\_\* 同型になるか、同時にならないか、のどちらか（\`kanPiIsomorphism\_iff\_of\_homotopy\`）。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk`

:::

:::definition "kerodon_3_2_2_5" (lean := "SSet.PtSimplex")
Kerodon Notation 3.2.2.5（[Tag 00VP](https://kerodon.net/tag/00VP)）。対応表の状態：一部。

*主張*　基点付き Kan 複体 $`(X,x)` への $`\Delta^n/\partial\Delta^n` からの基点付き射は、境界が $`x` に一定な $`n`-単体に対応する。二つの単体が $`\pi_n(X,x)` で同じ類を表すことは、境界に沿って $`x` に一定なホモトピーが一つ存在することと同値である。

B6：PtSimplex は境界が x に定値な標準単体という原文前半の代表データを直接与える。球面からの射との同定と、類の等式 iff 境界固定のホモトピーという後半は含まない。

:::

:::proposition "kerodon_3_2_2_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero")
Kerodon Example 3.2.2.6（[Tag 00VQ](https://kerodon.net/tag/00VQ)）。対応表の状態：本体にある。

*主張*　基点付き Kan 複体の $`\pi_0(X,x)` は連結成分の集合 $`\pi_0(X)` と同一視でき、一般に自然な群構造はない。

仮定：Kan 複体 X と頂点 x（Kerodon と一致）。結論：零次の KanHomotopyZero X x と基点を忘れた SSet.π₀ X の全単射を与える。零次数には正次数の群構造を要求しない（一致）。

:::

:::theorem "kerodon_3_2_2_10" (uses := "kerodon_1_1_0_6, kerodon_1_1_4_13, kerodon_1_2_4_7, kerodon_1_2_5_1, kerodon_3_2_3_4, kerodon_3_2_3_5, kerodon_3_2_3_6, kerodon_3_2_3_7, kerodon_3_2_3_8, kerodon_3_2_3_9")
Kerodon Theorem 3.2.2.10（[Tag 00VU](https://kerodon.net/tag/00VU)）。対応表の状態：なし。

B6：定義された群の台は独自の境界定値単体の商で、原文の球面からの写像の商との同一視がない。群構造の存在・可換性だけでも同じ対象の結論にする比較が要る。 候補：KanHomotopyGroup X n x は π\_(n+1) で群、n≥1 なら可換群。SphericalBoundary.boundary\_filler\_iff は面がすべて基点に境界固定のとき、π\_(n+2) の交代和零と充填の同値を与える。π₁ での順序付き交代積と、条件を満たす群構造の一意性は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.instGroup`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.instCommGroupKanHomotopyGroupHAddNatOfNat`、`SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.boundary_filler_iff`

:::

# 3.2.3 The Group Structure on π \_n(X,x)

%%%
number := false
tag := "kerodon-3-2-3"
%%%

Kerodon [Tag 00W3](https://kerodon.net/tag/00W3)

:::definition "kerodon_3_2_3_1" (lean := "SSet.PtSimplex, SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.boundary_filler_iff")
Kerodon Notation 3.2.3.1（[Tag 00W4](https://kerodon.net/tag/00W4)）。対応表の状態：一部。

*主張*　基点付き Kan 複体 $`(X,x)` で、境界が $`x` に一定な $`n`-単体を集めた集合を $`\Sigma` とし、定値単体を $`e` と書く。$`\Sigma` の $`n+2` 個の単体の列が境界をなすとは、それらを順に面とする $`(n+1)`-単体があることである。$`\Sigma\to\pi_n(X,x)` は全射で、同じ類を表すことは境界相対のホモトピーと同値である。

B6：PtSimplex は原文の Σ の定義を直接与える。SphericalBoundary の引用は高次の面族についてだが、全次数での bounds と π への全射の一式は含めない。

:::

:::lemma_ "kerodon_3_2_3_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_congr_left, SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.boundary_filler_iff")
Kerodon Lemma 3.2.3.2（[Tag 00W5](https://kerodon.net/tag/00W5)）。対応表の状態：一部。

*主張*　基点付き Kan 複体で、境界が基点に一定な $`n`-単体の $`n+2` 個の列が $`(n+1)`-単体の境界をなすかどうかは、各単体の $`\pi_n` における類だけで決まる。

B6：boundary\_filler\_iff では n+2 次元の全ての球面的面族の充填可能性が alternatingClass=0 のみで決まる。各代表の類を固定すればこの式は変わらず、原文の不変性が直接得られる。π₁ の一般の面族は含まない。

:::

:::lemma_ "kerodon_3_2_3_4" (uses := "kerodon_1_1_0_6, kerodon_1_2_4_7, kerodon_1_2_5_1, kerodon_3_1_3_6")
Kerodon Lemma 3.2.3.4（[Tag 00W7](https://kerodon.net/tag/00W7)）。対応表の状態：なし。

B6：MulStruct/FourStruct は特定の定数面を置く充填。任意の他の全ての面を与えたときの残る類の一意存在は直接返さない。 候補：三面の積の充填と特定の四面の充填がある。任意の i を欠いた全ての面族に対する残る類の一意存在の宣言は未確認。

宣言：`SSet.PtSimplex.MulStruct.nonempty`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.exists_fill`

:::

:::lemma_ "kerodon_3_2_3_5"
Kerodon Lemma 3.2.3.5（[Tag 00W8](https://kerodon.net/tag/00W8)）。対応表の状態：なし。

B6：mul\_unique\_at は同じ二つの MulStruct の出力の類が等しい命題。原文の任意の η の bounds iff η\_i=m\_i(...) と関数の一意存在は含まず材料。 候補：最後の三面で定まる群の積と、その充填での類の決定を確認。各 i の m\_i の一意性は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.instMul`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_unique_at`

:::

:::proposition "kerodon_3_2_3_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.degenerate_face") (uses := "kerodon_3_2_3_5")
Kerodon Example 3.2.3.6（[Tag 00W9](https://kerodon.net/tag/00W9)）。対応表の状態：一部。

*主張*　境界が基点に一定な $`n`-単体 $`\sigma` の退化 $`s_i\sigma` は、$`i,i+1` 番目の面が $`\sigma`、ほかが定値単体 $`e` になる。これにより $`1\leq i\leq n` の積 $`m_i` で $`[e]` は両側単位になる。

B6：degenerate\_face は原文に明記された二面が σ、他の面が e という退化単体の式そのもの。全ての m\_i についての両単位則まではこの宣言の結論にない。

:::

:::lemma_ "kerodon_3_2_3_7" (uses := "kerodon_1_1_0_6, kerodon_1_2_4_7, kerodon_1_2_5_1")
Kerodon Lemma 3.2.3.7（[Tag 00WA](https://kerodon.net/tag/00WA)）。対応表の状態：なし。

B6：FourReduction は特定の四面の式であり、任意の全ての面族が bounds のままであるという原文の結論ではない。 候補：最後の四面で充填を合成して類の等式を得る。全ての i で面二つを左から掛け直しても元の列が境界を成すという全体の主張は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.mulStruct`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.class_eq`

:::

:::lemma_ "kerodon_3_2_3_8" (uses := "kerodon_3_2_3_7")
Kerodon Lemma 3.2.3.8（[Tag 00WB](https://kerodon.net/tag/00WB)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。AdjacentProduct.flip は特定の隣接位置の二つの積を反転する。任意の i での m\_i と m\_(i−1) の三変数交換則は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::lemma_ "kerodon_3_2_3_9" (uses := "kerodon_3_2_3_6, kerodon_3_2_3_8")
Kerodon Lemma 3.2.3.9（[Tag 00WC](https://kerodon.net/tag/00WC)）。対応表の状態：なし。

B6：AdjacentProduct.flip は三つの非定数面の代表での充填を移す部品。原文の m\_i を全ての類の上で同定する宣言がない。 候補：隣接位置の特別な充填と高次群の可換性を確認。任意の i の m\_i を m\_(i−1) の引数交換と同定する命題は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.flip`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_comm`

:::

# 3.2.4 Contractibility

%%%
number := false
tag := "kerodon-3-2-4"
%%%

Kerodon [Tag 02L4](https://kerodon.net/tag/02L4)

:::definition "kerodon_3_2_4_1" (uses := "kerodon_1_1_0_6, kerodon_3_1_7_1")
Kerodon Definition 3.2.4.1（[Tag 04GH](https://kerodon.net/tag/04GH)）。対応表の状態：なし。

B6：IsContractibleKan は全境界充填で、原文は終射のホモトピー逆の存在。保存/反映の定理だけではこの定義の一致は直接得ない。 候補：IsContractibleKan はすべての境界の充填を要求する。Kan 複体間のホモトピー同値でこの性質を移せるが、原文の任意の単体集合で終射がホモトピー同値という定義には及ばない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsSimplicialHomotopyEquivalence.isContractibleKan_iff`

:::

:::theorem "kerodon_3_2_4_3" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_1_7_10, kerodon_3_2_4_13, kerodon_3_2_4_14")
Kerodon Theorem 3.2.4.3（[Tag 04GJ](https://kerodon.net/tag/04GJ)）。対応表の状態：なし。

B6：型の IsContractibleKan は境界充填の定義で、原文(1)の終射のホモトピー同値への比較がない。π による定理も独自商を用い、原文の三条件への同定が必要。 候補：非空で全基点・全次数のホモトピー類が一元なら終射は自明 Kan fibration、境界充填との同値もある。原文の三条件のうち、任意の正次数の π の消滅を返す向きと終射のホモトピー同値による表記を一緒に確認できていない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_iff_trivialKanFibration`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.terminal_rlp_of_homotopySubsingleton`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.isWeaklyContractible_iff_isContractibleKan`

:::

:::definition "kerodon_3_2_4_5" (lean := "SSet.Homotopy, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_nullHomotopy_of_isFilteredInfinity, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.nullHomotopyRestriction")
Kerodon Definition 3.2.4.5（[Tag 02L7](https://kerodon.net/tag/02L7)）。対応表の状態：一部。

*主張*　単体集合の射 $`X\to Y` は、$`Y` のある頂点への定値射にホモトピックなとき零ホモトピックである。

B6：exists\_nullHomotopy\_of\_isFilteredInfinity は有限な始域 K と filtered 準圏 C の任意の p を定値写像に結ぶ一段のホモトピーを直接与える。この範囲で原文の nullhomotopic が成立する。一般の判定述語は含まない。

:::

:::lemma_ "kerodon_3_2_4_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.homotopy") (uses := "kerodon_1_2_5_1")
Kerodon Lemma 3.2.4.11（[Tag 050V](https://kerodon.net/tag/050V)）。対応表の状態：一部。

*主張*　Kan 複体への正次元の任意の角 $`\Lambda_i^n\to X` は零ホモトピックである。

B6：LastHornContraction.homotopy を任意の σ₀ で後合成すると σ₀ から定値写像へのホモトピーになる。最後のホーン i=n\>0 に限った原文の同じ主張。他の番号は含まない。

:::

:::definition "kerodon_3_2_4_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_filler_of_homotopy") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1")
Kerodon Variant 3.2.4.12（[Tag 050W](https://kerodon.net/tag/050W)）。対応表の状態：一部。

*主張*　Kan 複体 $`X` と $`n\geq0` に対し、境界 $`\partial\Delta^n\to X` が零ホモトピックであることと、$`\Delta^n` に延長できることは同値である。延長から零ホモトピーを得る向きには Kan 条件を要しない。

B6：exists\_filler\_of\_homotopy の g と s を定値写像に取れば、原文の nullhomotopic⇒延長の向きを直接得る。有限鎖だけでなく一段のホモトピーを与えた場合。延長⇒nullhomotopic は含まない。

:::

:::lemma_ "kerodon_3_2_4_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_boundary_filler_of_homotopySubsingleton") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_2_2_10, kerodon_3_2_4_11")
Kerodon Lemma 3.2.4.13（[Tag 050X](https://kerodon.net/tag/050X)）。対応表の状態：一部。

*主張*　Kan 複体 $`X` と $`n\geq2` に対し、全ての $`\partial\Delta^n\to X` が $`\Delta^n` に延長できることと、全頂点 $`x` で $`\pi_{n-1}(X,x)` が自明であることは同値である。

B6：exists\_boundary\_filler\_of\_homotopySubsingleton は指定 n の境界写像の延長を直接返す。頂点 x₀ と全基点・全次数の消滅を仮定するので、一つの π\_(n−1) の消滅だけの原文より強い。逆向きは含まない。

:::

:::definition "kerodon_3_2_4_14" (uses := "kerodon_3_2_4_13")
Kerodon Variant 3.2.4.14（[Tag 050Y](https://kerodon.net/tag/050Y)）。対応表の状態：なし。

B6：全次数の消滅と指定頂点からの充填は、n=0/1にそれぞれ一つの π₀ 条件だけを使う iff の結論ではない。 候補：AcyclicKanLifting は指定頂点を零次の充填に使い、零次のホモトピー類の一元性を高次の充填の仮定に含める。n=0 の非空性と n=1 の連結性の個別の同値は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_boundary_filler_of_homotopySubsingleton`

:::

:::corollary "kerodon_3_2_4_15" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_2_4_3, kerodon_3_2_4_12")
Kerodon Corollary 3.2.4.15（[Tag 05NZ](https://kerodon.net/tag/05NZ)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。点ごとの弱同値を保つ filtered colimit 定理はある。各段の transition だけが零ホモトピックな列の余極限が可縮という宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::definition "kerodon_3_2_4_16" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible")
Kerodon Definition 3.2.4.16（[Tag 04GW](https://kerodon.net/tag/04GW)）。対応表の状態：本体にある。

*主張*　単体集合 $`X` は、射影 $`X\to\Delta^0` が弱ホモトピー同値であるとき弱可縮である。

仮定：任意の単体集合 X（Kerodon と一致）。結論：終対象への射が IsWeakHomotopyEquivalence であるという述語 IsWeaklyContractible（一致。終対象は Δ⁰ と同型）。

:::

# 3.2.5 The Connecting Homomorphism

%%%
number := false
tag := "kerodon-3-2-5"
%%%

Kerodon [Tag 00WD](https://kerodon.net/tag/00WD)

:::definition "kerodon_3_2_5_1" (uses := "kerodon_1_2_5_1")
Kerodon Definition 3.2.5.1（[Tag 00WE](https://kerodon.net/tag/00WE)）。対応表の状態：なし。

B6：BoundaryLift は最後の面の incidence。原文の第0面と逆順にする比較がなく、別の面を指定した型を partial としない。 候補：境界定値の底の単体を、最後の面以外が基点に定値となるよう持ち上げる型。Kerodon は最初の面以外を固定し、第0面を指定する incidence を定める。面の反転を含む比較は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.boundaryLift_nonempty`

:::

:::proposition "kerodon_3_2_5_2" (uses := "kerodon_1_1_4_13, kerodon_1_2_5_1, kerodon_3_2_5_1")
Kerodon Proposition 3.2.5.2（[Tag 00WF](https://kerodon.net/tag/00WF)）。対応表の状態：なし。

B6：connecting は最後の面の持ち上げで定める。原文の第0面の incidence iff との比較と一意性がなく、違う連結写像の構成だけでは不足。 候補：選んだ最後の面の持ち上げから連結写像を定め、選択に依存しない。本文の第0面を指定した incidence との双方向および写像の一意性は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift.boundary_class_eq`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting`

:::

:::definition "kerodon_3_2_5_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHom")
Kerodon Construction 3.2.5.3（[Tag 00WG](https://kerodon.net/tag/00WG)）。対応表の状態：本体にある。

*主張*　基点付き Kan 複体の Kan ファイブレーションの各 $`n\geq0` で、3.2.5.2 の写像 $`\pi_{n+1}(S,s)\to\pi_n(X_s,x)` を連結準同型と呼ぶ。

仮定：点付き Kan fibration p : E ⟶ B と基点 e、次数 n≥0（Lean が弱い：connecting の型は B の Kan 性を要求し、E の Kan 性は入力しない）。結論：π\_(n+1)(B,p(e)) から π\_n(fiber,e) への連結写像を定め、正次数で群準同型にする（一致。Lean の計算は最後のホーンを用いる）。

:::

:::proposition "kerodon_3_2_5_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting_mul, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHom")
Kerodon Proposition 3.2.5.4（[Tag 00WH](https://kerodon.net/tag/00WH)）。対応表の状態：本体にある。

*主張*　基点付き Kan 複体の Kan ファイブレーションの連結写像 $`\pi_{n+1}(S,s)\to\pi_n(X_s,x)` は、$`n\geq1` で群準同型である。

仮定：点付き Kan fibration p と正の標的次数（Kerodon と一致。Lean の connectingHom p e n は標的次数 n+1、始域次数 n+2）。結論：連結写像が積を保存する群準同型（一致。Lean の代表は最後のホーンを用いる）。

:::

:::definition "kerodon_3_2_5_5" (uses := "kerodon_1_2_5_1, kerodon_3_2_5_2")
Kerodon Variant 3.2.5.5（[Tag 00WJ](https://kerodon.net/tag/00WJ)）。対応表の状態：なし。

B6：componentConnecting も最後の面の連結写像で、全成分上の原文の作用と同一視されていない。作用の単位則・合成則を型に持たない。 候補：任意の指定ファイバー頂点から出発する π₁(B) → π₀(fiber) の連結写像はある。π₀(fiber) 全体で代表に依らない作用と単位・合成則は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting`

:::

# 3.2.6 The Long Exact Sequence of a Fibration

%%%
number := false
tag := "kerodon-3-2-6"
%%%

Kerodon [Tag 00WL](https://kerodon.net/tag/00WL)

*f-01-simplicial-kan.html — 3. ホモトピー群（Kan） — 3.3 Kan fibration の長完全列*

Kan fibration $`p : E \to B`（$`E, B` は Kan 複体）と、$`E` の頂点 $`e` について、fiber を $`F = p^{-1}(p(e))` とすると、次の長完全列がある。

$$`\cdots \to \pi_{n+1}(B) \xrightarrow{\ \partial\ } \pi_n(F) \to \pi_n(E) \to \pi_n(B) \to \cdots \to \pi_0(E) \to \pi_0(B)`

- \`fiberLongExact p e\`（KST/Spectra/FibrationSequence.lean:28）：fiber・全空間・底空間の各所での完全性を、すべての $`n` についてまとめた主張。fiber は \`KanFiber p b\`、包含は \`fiberι\`、連結準同型は \`connecting\`。

- 連結準同型は群準同型である：\`connectingHom p e n : π\_\{n+2\}(B) →\* π\_\{n+1\}(F)\`（添字は \`KanHomotopyGroup\` の流儀。FibrationMultiplication.lean:198）。

:::theorem "kerodon_3_2_6_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLongExact, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_connecting_fiber, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_total_base")
Kerodon Theorem 3.2.6.1（[Tag 00WM](https://kerodon.net/tag/00WM)）。対応表の状態：本体にある。

*主張*　基点付き Kan 複体の Kan ファイブレーションでは、ファイバー・全体・底のホモトピー群を連結写像でつないだ長列が $`\pi_0` まで基点付き集合として完全である。

仮定：Kan 複体間の Kan fibration p と e : E₀（Kerodon と一致。底の基点は p(e)）。結論：ファイバー、全空間、底の三位置で直前の射の像と次の射の基点の逆像が一致する。ファイバーと全空間は零次数を含み、底は正次数を扱う（一致。連結写像は最後のホーンの規約）。

:::

:::proposition "kerodon_3_2_6_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_fiber_total, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_fiber_total_all")
Kerodon Proposition 3.2.6.2（[Tag 00WN](https://kerodon.net/tag/00WN)）。対応表の状態：本体にある。

*主張*　基点付き Kan 複体の Kan ファイブレーションについて、任意の $`n\geq0` で $`\pi_n(X_s,x)\to\pi_n(X,x)\to\pi_n(S,s)` は基点付き集合の完全列である。

仮定：Kan 複体間の Kan fibration p、基点 e と次数 n≥0（Kerodon と一致）。結論：π\_n(E)→π\_n(B) で基点に写る類と π\_n(fiber)→π\_n(E) の像が一致する（一致）。

:::

:::corollary "kerodon_3_2_6_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_fiber_total_zero, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentFiber_exact") (uses := "kerodon_1_2_5_1")
Kerodon Corollary 3.2.6.3（[Tag 00WP](https://kerodon.net/tag/00WP)）。対応表の状態：一部。

*主張*　Kan 複体間の Kan ファイブレーション $`X\to S` で、頂点 $`s` 上のファイバーの成分が $`\pi_0(X)` に作る像は、$`\pi_0(X)\to\pi_0(S)` の $`[s]` 上のファイバーに等しい。

B6：componentFiber\_exact は s=p(e) とファイバーの頂点 e を指定した場合の、π₀(E) の底での像が \[s\] iff ファイバーの像に属する、という同じ結論。任意の s と空ファイバーの場合には及ばない。

:::

:::proposition "kerodon_3_2_6_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_connecting_fiber, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_connecting_fiber_all")
Kerodon Proposition 3.2.6.4（[Tag 00WQ](https://kerodon.net/tag/00WQ)）。対応表の状態：本体にある。

*主張*　基点付き Kan 複体の Kan ファイブレーションについて、任意の $`n\geq0` で $`\pi_{n+1}(S,s)\xrightarrow{\partial}\pi_n(X_s,x)\to\pi_n(X,x)` は基点付き集合の完全列である。

仮定：Kan 複体間の Kan fibration p、基点 e と次数 n≥0（Kerodon と一致）。結論：π\_n(fiber)→π\_n(E) で基点に写る類と連結写像 π\_(n+1)(B)→π\_n(fiber) の像が一致する（一致。連結写像は最後のホーンの規約）。

:::

:::corollary "kerodon_3_2_6_5" (uses := "kerodon_1_2_5_1, kerodon_3_2_5_5, kerodon_3_2_6_4")
Kerodon Corollary 3.2.6.5（[Tag 00WR](https://kerodon.net/tag/00WR)）。対応表の状態：なし。

B6：componentConnecting\_exact は原文の作用・軌道の同定の部品。最後の面で作る connecting を第0面の作用と比較する宣言が必要。 候補：componentConnecting\_exact は、指定頂点の成分と同じ全空間の成分に写るファイバー成分を、π₁(B) からの連結写像の像として特徴づける。π₁ の全成分上の作用・軌道集合との比較は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting_exact`

:::

:::proposition "kerodon_3_2_6_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_total_base, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_total_base_all")
Kerodon Proposition 3.2.6.6（[Tag 00WS](https://kerodon.net/tag/00WS)）。対応表の状態：本体にある。

*主張*　基点付き Kan 複体の Kan ファイブレーションについて、任意の $`n\geq0` で $`\pi_{n+1}(X,x)\to\pi_{n+1}(S,s)\xrightarrow{\partial}\pi_n(X_s,x)` は基点付き集合の完全列である。

仮定：Kan 複体間の Kan fibration p、基点 e と次数 n≥0（Kerodon と一致）。結論：連結写像 π\_(n+1)(B)→π\_n(fiber) で基点に写る類と π\_(n+1)(E) の像が一致する（一致。連結写像は最後のホーンの規約）。

:::

:::corollary "kerodon_3_2_6_7" (uses := "kerodon_1_2_5_1, kerodon_3_2_5_5, kerodon_3_2_6_6")
Kerodon Corollary 3.2.6.7（[Tag 00WT](https://kerodon.net/tag/00WT)）。対応表の状態：なし。

B6：componentConnecting\_kernel は最後の面の connecting の核であり、原文の第0面による作用の安定化群との比較が必要。 候補：componentConnecting\_kernel は、指定ファイバー成分に戻る底のループ類と全空間の基本群の像を同定する。π₁ の全成分上の作用としての安定化群は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting_kernel`

:::

:::corollary "kerodon_3_2_6_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberHomotopySubsingleton, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberHomotopy_eq_point") (uses := "kerodon_1_2_5_1")
Kerodon Corollary 3.2.6.8（[Tag 050Z](https://kerodon.net/tag/050Z)）。対応表の状態：一部。

*主張*　基点付き Kan 複体の Kan ファイブレーション $`f:X\to S` と $`n>0` に対し、ファイバーの $`\pi_n` が消えることは、$`\pi_n(f)` が単射で $`\pi_{n+1}(f)` が全射であることと同値である。

B6：fiberHomotopySubsingleton は同じ指定ファイバーの π\_n の消滅を直接返す。二つの隣接次数だけの単射/全射でなく全基点・全次数の π 同型を仮定。消滅からの逆方向は含まない。

:::

:::definition "kerodon_3_2_6_9" (uses := "kerodon_1_2_5_1")
Kerodon Variant 3.2.6.9（[Tag 0510](https://kerodon.net/tag/0510)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。連結写像の基点の逆像と、ファイバーから全空間への成分写像の像は計算する。指定底成分の逆像の一意性と π₁ の全射性によるファイバー連結性の同値は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.2.7 Whitehead's Theorem for Kan Complexes

%%%
number := false
tag := "kerodon-3-2-7"
%%%

Kerodon [Tag 00WU](https://kerodon.net/tag/00WU)

:::theorem "kerodon_3_2_7_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.homotopyEquivalence_of_kanPiIsomorphism_of_piZero_surjective, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_homotopyEquivalence")
Kerodon Theorem 3.2.7.1（[Tag 00WV](https://kerodon.net/tag/00WV)）。対応表の状態：本体にある。

*主張*　Kan 複体の射 $`f:X\to Y` は、$`\pi_0` で全単射を誘導し、すべての頂点 $`x` と正の次数 $`n` で $`\pi_n(X,x)\to\pi_n(Y,f(x))` が同型となるとき、かつそのときに限りホモトピー同値である。

仮定：Kan 複体間の射 f（Kerodon と一致）。結論：全基点の π\_n の全単射と π₀ の全射性から f のホモトピー同値を得て、逆向きには各 π\_n の全単射を得る。零次数の型は通常の π₀ と同定する（一致）。

*f-01-simplicial-kan.html — 3. ホモトピー群（Kan） — 3.4 Whitehead の定理*

Kan 複体の間の写像が π\_\* 同型なら、ホモトピー同値である。

- 基点付き版：\`exists\_pointedHomotopyInverse\`（KST/Spectra/PointedKanWhitehead.lean:80）。π\_\* 同型な基点付き写像は、基点付きのホモトピー逆を持つ。

- 基点なし版：\`homotopyEquivalence\_of\_kanPiIsomorphism\_of\_piZero\_surjective\`（InfinityCategories/Kerodon/KanComplexes/HomotopyGroups/KanWhiteheadComparison.lean:98）。π\_\* 同型（すべての基点で）かつ π₀ で全射なら、ホモトピー同値。逆も成り立つ（\`kanPiIsomorphism\_of\_homotopyEquivalence\`）。

§2 の結果と合わせると、Kan 複体の間の写像について、次の四つが同値になる。「π\_\* 同型」「ホモトピー同値」「∞ 圏としての同値」「（Kan fibration なら）自明 fibration」。

:::

:::proposition "kerodon_3_2_7_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fibration_rlp_of_piIsomorphism, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_homotopyEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration") (uses := "kerodon_1_2_5_1, kerodon_3_1_7_10, kerodon_3_2_4_3, kerodon_3_2_6_8, kerodon_3_2_6_9")
Kerodon Proposition 3.2.7.2（[Tag 00X1](https://kerodon.net/tag/00X1)）。対応表の状態：一部。

*主張*　Kan 複体間の Kan ファイブレーションについて、自明であること、ホモトピー同値であること、$`\pi_0` が全単射で全基点の正次数のホモトピー群が同型になること、全頂点ファイバーが可縮であることは同値である。

B6：fibration\_rlp\_of\_piIsomorphism は条件(3)の全 π 同型と全空間の頂点 e₀ を仮定して、条件(1)の全単射 RLP を直接与える。e₀ は原文より強い。四条件全体の iff は含まない。

*f-01-simplicial-kan.html — 3. ホモトピー群（Kan） — 3.5 弱同値の三つの見方*

単体的集合（Kan とは限らない）の間の写像 $`f : A \to B` が「弱同値」であることには、このリポジトリでは三つの言い方がある。

- 言い方　／　定義　／　宣言
- Kan 複体への写像で見る　／　すべての Kan 複体 $`Z` について、$`\pi_0\mathrm{Fun}(B, Z) \to \pi_0\mathrm{Fun}(A, Z)` が全単射　／　\`IsWeakHomotopyEquivalence\`（InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/WeakHomotopy.lean:42）
- anodyne 局所化で見る　／　単体的集合の圏を anodyne 射で局所化した 1 圏（空間のホモトピー圏）で、$`f` が同型になる　／　\`anodyneQ\`（HomotopicalAlgebra/Simplicial/AnodyneHomotopyLocalization.lean:101）
- Kan 置換してから π\_\* で見る　／　Kan 置換したものの間の写像が π\_\* 同型　／　§1.4 の置換と §3.2

関係を示す結果として、Kan 複体の間の anodyne 射は π\_\* 同型である（\`kanPiIsomorphism\_of\_anodyne\`、KST/Spectra/AnodyneHomotopyEquivalence.lean:98）。三つが一致することは、第 2 章で「モデル圏を使わない基礎」としてまとめる。

*f-02-model-free.html — 4. 弱同値の三つの見方が一致すること*

第 1 章 §3.5 で、単体的集合の写像 $`f : X \to Y` が「弱同値」であることの三つの言い方を挙げた。ここで、それらがモデル構造なしで一致することを確かめる。

- 見方　／　定義　／　宣言
- (a) anodyne 局所化　／　$`\texttt{anodyneQ}(f)` が同型　／　\`IsIso (anodyneQ.map f)\`
- (b) Kan 複体による判定　／　すべての Kan 複体 $`K` について、前合成 $`[Y, K] \to [X, K]`（ホモトピー類）が全単射　／　\`KanTestDetection.Tests f\`（HomotopicalAlgebra/Simplicial/KanTestDetection.lean:47）。\`IsWeakHomotopyEquivalence\`（Kerodon/KanComplexes）（$`\pi_0\mathrm{Fun}(-, Z)` で同じことを言う）もこの形
- (c) Kan 置換と π\_\*　／　$`Rf : RX \to RY` が π\_\* 同型　／　第 1 章 §3.2 の \`KanPiIsomorphism\`

*(a) ⇔ (b)*：\`anodyneQ\_isIso\_iff\_tests\`（KanTestDetection.lean:111）。証明の流れは次のとおり。

1. (a) ⇒ (b)：Kan 複体 $`K` へのホモトピー類 $`[-, K]` は、anodyne 射を全単射に送る（Kan 複体への写像は anodyne に沿って延び、延長はホモトピーを除いて一意）。したがって $`[-, K]` は anodyneQ を経由し、$`\texttt{anodyneQ}(f)` が同型なら全単射（\`tests\_of\_anodyneQ\_isIso\`）。

2. (b) ⇒ (a)：Kan 置換 $`X \to RX` は anodyne なので、anodyneQ の中で $`f` と $`Rf` は同型の違いしかない。Kan 複体の間では、(b) は米田の議論により「ホモトピー同値」を意味する。ホモトピー同値は §3.2 により anodyneQ で同型になる（\`replacement\_tests\`・\`map\_isIso\_of\_tests\`）。

*(b) ⇔ (c)*：Kan 複体の間の写像については、(b) はホモトピー同値と同じで、ホモトピー同値は Whitehead の定理により π\_\* 同型と同値である（第 1 章 §3.4）。
一般の $`f` については、Kan 置換を経由して (b) と (c) が比べられる。Kan 置換の単位 $`X \to RX` は anodyne なので、(b) の判定を変えない。

ポイント

「弱同値」を、モデル構造の公理から出すのではなく、Kan 複体へのホモトピー類（(b)）で定義してしまう。そうすれば、局所化（(a)）や π\_\*（(c)）との一致は、持ち上げ性質と small object argument だけで示せる。
これが「モデル圏を使わない基礎」の中心である。

:::

:::corollary "kerodon_3_2_7_4"
Kerodon Corollary 3.2.7.4（[Tag 03DZ](https://kerodon.net/tag/03DZ)）。対応表の状態：なし。

B6：単体加群の核型正規化の QuasiIso と弱同値の iff で、原文の指定 K(C) と整数次数の C への比較はない。 候補：単体加群写像を正規化した擬同型と、忘却した単体写像の弱ホモトピー同値の同値。原文の任意の整数次数の鎖写像に K を施し、非負次数ホモロジーと比較する形は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.moduleNormalizedMap_quasiIso_iff_isWeakHomotopyEquivalence`

:::

# 3.2.8 Closure Properties of Homotopy Equivalences

%%%
number := false
tag := "kerodon-3-2-8"
%%%

Kerodon [Tag 00XB](https://kerodon.net/tag/00XB)

:::proposition "kerodon_3_2_8_1" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_1_7_6, kerodon_3_2_5_5, kerodon_3_2_6_3, kerodon_3_2_6_5, kerodon_3_2_6_7, kerodon_3_2_7_1")
Kerodon Proposition 3.2.8.1（[Tag 00XC](https://kerodon.net/tag/00XC)）。対応表の状態：なし。

B6：fiberMap\_piIsomorphism は独自の π の全単射であって原文のホモトピー同値への比較が要る。切断空間の宣言は原文とは別の射。 候補：全空間と底の π 同型からファイバーの π 同型を得る方向がある。ファイバー同値からの逆方向として引用されていた宣言は切断空間の比較で、全空間の同値を直接返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberMap_piIsomorphism`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplicialSectionsMap_homotopyEquivalence_of_fibers`

:::

:::proposition "kerodon_3_2_8_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.filteredColimitMap_isWeakHomotopyEquivalence_of_pointwise")
Kerodon Proposition 3.2.8.3（[Tag 00XE](https://kerodon.net/tag/00XE)）。対応表の状態：本体にある。

*主張*　単体集合の弱ホモトピー同値からなる射圏の充満部分圏は、フィルター付き余極限で閉じている。

仮定：小さい filtered 圏 I、単体集合値図式 F,G と自然変換 η の各成分が弱ホモトピー同値（Kerodon と一致。図式の値の Kan 性は不要）。結論：colim.map η が弱ホモトピー同値、すなわち矢印圏の点ごとの filtered colimit で弱同値が保存される（一致）。

:::

:::corollary "kerodon_3_2_8_4" (lean := "SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.finiteSubsetColimit_isWeaklyContractible, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.filteredColimitMap_isWeakHomotopyEquivalence_of_pointwise") (uses := "kerodon_1_1_0_6")
Kerodon Corollary 3.2.8.4（[Tag 03PK](https://kerodon.net/tag/03PK)）。対応表の状態：一部。

*主張*　弱可縮な単体集合のフィルター付き余極限は弱可縮である。

B6：finiteSubsetColimit\_isWeaklyContractible は任意の型 Q の有限部分集合の圏を添字にした filtered colimit に対し、原文と同じ弱可縮性の結論を直接返す。任意の filtered 小圏は含まない。

:::

:::corollary "kerodon_3_2_8_5" (uses := "kerodon_3_2_8_4")
Kerodon Corollary 3.2.8.5（[Tag 03PL](https://kerodon.net/tag/03PL)）。対応表の状態：なし。

B6：filtered 準圏の定理には普通の線形順序の nerve の filtered 性の適用が必要。contractionSpan も任意の線形順序に対する T と自然変換を型で与えず材料。 候補：filtered 準圏の弱可縮性と、縮約の span が指定される普通圏の nerve の弱可縮性を確認。非空線形順序からの適用を一つにまとめた宣言は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isWeaklyContractible_of_isFilteredInfinity`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.nerve_isWeaklyContractible_of_contractionSpan`

:::

