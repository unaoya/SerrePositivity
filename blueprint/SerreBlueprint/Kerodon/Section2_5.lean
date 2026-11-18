import Verso
import VersoManual
import VersoBlueprint
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.AlgebraicTopology.DoldKan.Equivalence
import Mathlib.AlgebraicTopology.MooreComplex
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import SerrePositivity.DifferentialGraded.Category.Basic
import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWChainMap
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AlexanderWhitney
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ConnectiveHom
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DGNerveBasic
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DoldKanIso
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.EdgeClosedEquivalence
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedShuffle
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Quasicategory
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Shuffle
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleChainMap
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplicialCategory
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardVertices

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "2.5 Differential Graded Categories" =>
%%%
number := false
tag := "kerodon-2-5"
%%%

Kerodon の 2.5 節（[Tag 00ND](https://kerodon.net/tag/00ND)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::definition "kerodon_2_5_0_1" (lean := "HomologicalComplex, ChainComplex")
Kerodon Definition 2.5.0.1（[Tag 00NE](https://kerodon.net/tag/00NE)）。対応表の状態：Mathlib にある。

仮定：加法圏 A（Lean が弱い：基礎圏には HasZeroMorphisms で足りる）。結論：ChainComplex A ℤ は整数次数の対象と次数を 1 下げる微分を持ち、微分の二回の合成が零（一致）。

:::

:::definition "kerodon_2_5_0_2" (lean := "ChainComplex")
Kerodon Notation 2.5.0.2（[Tag 00NF](https://kerodon.net/tag/00NF)）。対応表の状態：Mathlib にある。

仮定：加法圏 A（Lean が弱い：ChainComplex の型は零射のある圏で定義される）。結論：整数次数に特殊化すると、各隣接次数を d\_n : C\_n → C\_(n−1) で結ぶ原文の図式を表す（一致）。

:::

:::definition "kerodon_2_5_0_3" (lean := "HomologicalComplex.Hom")
Kerodon Definition 2.5.0.3（[Tag 00NG](https://kerodon.net/tag/00NG)）。対応表の状態：Mathlib にある。

仮定：加法圏の二つの整数次数鎖複体 C,D（Lean が弱い：HomologicalComplex.Hom は零射のある圏で任意の共通 shape に定義される）。結論：各次数の射 f\_n : C\_n → D\_n が微分と可換という型（一致）。

:::

:::definition "kerodon_2_5_0_4" (lean := "ChainComplex")
Kerodon Notation 2.5.0.4（[Tag 00NH](https://kerodon.net/tag/00NH)）。対応表の状態：Mathlib にある。

仮定：可換環 k（Lean が弱い：ChainComplex は零射のある圏一般を取る）。結論：V = ModuleCat k、添字 ℤ に特殊化した鎖複体と鎖写像の圏が Ch(k) を表す（一致）。

:::

:::definition "kerodon_2_5_0_5" (lean := "Homotopy, HomotopyEquiv")
Kerodon Definition 2.5.0.5（[Tag 00NJ](https://kerodon.net/tag/00NJ)）。対応表の状態：Mathlib にある。

仮定：加法圏の整数次数鎖複体 C,D と平行な鎖写像 f,g（Lean が弱い：前加法圏および一般の複体の形でよい）。結論：次数を 1 上げる h で f−g=dh+hd を与えるホモトピーと、両側の合成を恒等へホモトープにする逆写像のデータ（一致）。

:::

:::definition "kerodon_2_5_0_9"
Kerodon Construction 2.5.0.9（[Tag 00NM](https://kerodon.net/tag/00NM)）。対応表の状態：Mathlib にある。

仮定：加法圏 A（Lean が弱い：前加法圏と任意の shape で定義される）。結論：shape を down ℤ とすると、対象は鎖複体、射は鎖写像の鎖ホモトピー類となる商圏（一致）。

宣言：`HomotopyCategory`

:::

:::definition "kerodon_2_5_0_10"
Kerodon Construction 2.5.0.10（[Tag 00NN](https://kerodon.net/tag/00NN)）。対応表の状態：なし。

B6：Cochain と linearHomComplex は余鎖規約、homComplex もその別名。鎖規約の符号付き微分との次数反転の比較がなく、原文の mapping chain complex を直接得ない。

宣言：`CochainComplex.HomComplex.Cochain`、`CochainComplex.linearHomComplex`、`SerrePositivity.DifferentialGraded.homComplex`

:::

# 2.5.1 Generalities on Chain Complexes

%%%
number := false
tag := "kerodon-2-5-1"
%%%

Kerodon [Tag 00NQ](https://kerodon.net/tag/00NQ)

:::definition "kerodon_2_5_1_1"
Kerodon Definition 2.5.1.1（[Tag 00NR](https://kerodon.net/tag/00NR)）。対応表の状態：なし。

B6：IsStrictlyGE/LE の引用は余鎖複体についての述語。鎖複体への再添字の比較を欠くため原文の二つの充満部分圏の直接の部分構成とは数えない。

宣言：`CochainComplex.IsStrictlyGE`、`CochainComplex.IsStrictlyLE`

:::

:::definition "kerodon_2_5_1_3"
Kerodon Notation 2.5.1.3（[Tag 00NT](https://kerodon.net/tag/00NT)）。対応表の状態：一部。

B6：HomologicalComplex.cycles は指定次数の outgoing 微分の核を直接構成し、鎖規約でも原文の Z\_n を与える。image による B\_n とその包含の一式は引用に含まない。

宣言：`HomologicalComplex.cycles`

:::

:::definition "kerodon_2_5_1_4" (lean := "HomologicalComplex.homology, HomologicalComplex.Acyclic, HomologicalComplex.exactAt_iff_isZero_homology")
Kerodon Definition 2.5.1.4（[Tag 00NU](https://kerodon.net/tag/00NU)）。対応表の状態：Mathlib にある。

仮定：アーベル圏の鎖複体 K と次数 i（Lean が弱い：零射のある圏で該当する短複体のホモロジーがあればよい）。結論：homology K i はサイクルを境界で割る対象。Acyclic は全次数で ExactAt を要求し、exactAt\_iff\_isZero\_homology が各次数でホモロジー零との同値を与える（一致）。

:::

:::definition "kerodon_2_5_1_5" (lean := "QuasiIso, QuasiIsoAt")
Kerodon Definition 2.5.1.5（[Tag 00NV](https://kerodon.net/tag/00NV)）。対応表の状態：Mathlib にある。

仮定：アーベル圏の複体 K,L と鎖写像 f（Lean が弱い：零射と各次数で HasHomology があればよい）。結論：QuasiIso f は各 i の homologyMap f i が同型であることを課す（一致）。

:::

:::proposition "kerodon_2_5_1_8" (lean := "Homotopy.homologyMap_eq")
Kerodon Proposition 2.5.1.8（[Tag 00NY](https://kerodon.net/tag/00NY)）。対応表の状態：Mathlib にある。

仮定：同じ二複体間の鎖写像 f,g と Homotopy f g、比較次数 n のホモロジー（Lean が弱い：前加法圏と該当次数の HasHomology で足りる）。結論：homologyMap f n = homologyMap g n（一致）。

:::

:::corollary "kerodon_2_5_1_9" (lean := "HomotopyEquiv.quasiIso_hom")
Kerodon Corollary 2.5.1.9（[Tag 00NZ](https://kerodon.net/tag/00NZ)）。対応表の状態：Mathlib にある。

仮定：鎖ホモトピー同値 e と両複体の全次数のホモロジー（Lean が弱い：アーベル性は要求せず前加法性と HasHomology でよい）。結論：e.hom が QuasiIso（一致）。

:::

:::proposition "kerodon_2_5_1_10"
Kerodon Proposition 2.5.1.10（[Tag 00P0](https://kerodon.net/tag/00P0)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。各項射影かつ有界の複体の K 射影性はあるが、非輪状の場合に複体圏の全エピに切断を与える宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::definition "kerodon_2_5_1_11" (lean := "HomologicalComplex.tensorObj")
Kerodon Notation 2.5.1.11（[Tag 00P1](https://kerodon.net/tag/00P1)）。対応表の状態：Mathlib にある。

仮定：整数で次数づけたアーベル群の族 C,D（Lean が弱い：任意のモノイダル前加法圏で必要な余積を取れる場合を含む。次数づけた族は微分を零にして適用）。結論：次数 n の成分は p+q=n の C\_p ⊗ D\_q の余積で、ιTensorObj は該当成分の包含（一致）。

:::

:::proposition "kerodon_2_5_1_12"
Kerodon Proposition 2.5.1.12（[Tag 00P2](https://kerodon.net/tag/00P2)）。対応表の状態：なし。

B6：tensorObj の複体性と d\_eq=D₁+D₂ だけでは、原文の任意の x,y 上の指定 Leibniz 式を満たすという存在の結論を直接述べない。一意性の証明部品でもあるため none。

宣言：`HomologicalComplex.tensorObj`、`HomologicalComplex.mapBifunctor.d_eq`

:::

:::definition "kerodon_2_5_1_13" (lean := "HomologicalComplex.tensorObj")
Kerodon Notation 2.5.1.13（[Tag 00P3](https://kerodon.net/tag/00P3)）。対応表の状態：Mathlib にある。

仮定：整数次数の鎖複体 C,D（Lean が弱い：基礎圏は必要な余積とテンソルの加法性を持つモノイダル前加法圏でよい）。結論：次数別のテンソルの直和に d⊗1+(-1)\^p 1⊗d を入れた鎖複体（一致）。

:::

:::definition "kerodon_2_5_1_17" (lean := "HomologicalComplex.monoidalCategory")
Kerodon Construction 2.5.1.17（[Tag 00P7](https://kerodon.net/tag/00P7)）。対応表の状態：Mathlib にある。

仮定：基礎圏はアーベル群の圏、添字は ℤ（Lean が弱い：所要の余積とテンソルの余積保存を持つモノイダル前加法圏へ一般化）。結論：符号付きテンソル複体、次数 0 に集中する単位複体、結合子と左右単位子を備えるモノイダル圏（一致）。

:::

# 2.5.2 Differential Graded Categories

%%%
number := false
tag := "kerodon-2-5-2"
%%%

Kerodon [Tag 00P9](https://kerodon.net/tag/00P9)

:::definition "kerodon_2_5_2_1" (lean := "SerrePositivity.DifferentialGraded.DGCategory")
Kerodon Definition 2.5.2.1（[Tag 00PA](https://kerodon.net/tag/00PA)）。対応表の状態：本体にある。

仮定：対象型 D と係数環 R（Lean が弱い：整数係数に限らず可換環 R 上で定義）。結論：各 Hom を複体とし、複体の射である結合的合成と単位を持つ dg 圏（一致。Lean の余鎖次数 k は原文の鎖次数 −k）。

:::

:::definition "kerodon_2_5_2_4" (lean := "SerrePositivity.DifferentialGraded.ClosedCategory")
Kerodon Construction 2.5.2.4（[Tag 00PD](https://kerodon.net/tag/00PD)）。対応表の状態：本体にある。

仮定：dg 圏 D（Lean が弱い：可換環 R 上の dg 圏も取れる）。結論：対象は D の対象、射は閉次数 0 の Hom の元、合成と恒等は dg 圏のものを制限した普通圏（一致）。

:::

:::definition "kerodon_2_5_2_8" (lean := "SerrePositivity.DifferentialGraded.DGFunctor")
Kerodon Definition 2.5.2.8（[Tag 00PH](https://kerodon.net/tag/00PH)）。対応表の状態：本体にある。

仮定：同じ係数環上の dg 圏二つ（Lean が弱い：整数係数を任意の可換環 R に一般化）。結論：対象関数と各 dg Hom の複体写像が合成・恒等を保存する dg 関手（一致）。

:::

# 2.5.3 The Differential Graded Nerve

%%%
number := false
tag := "kerodon-2-5-3"
%%%

Kerodon [Tag 00PK](https://kerodon.net/tag/00PK)

:::definition "kerodon_2_5_3_1"
Kerodon Construction 2.5.3.1（[Tag 00PL](https://kerodon.net/tag/00PL)）。対応表の状態：なし。

B6：Simplex/SimplexData は HA の余鎖符号規約。原文の削除項と合成項の符号方程式を満たす組への変換がなく、raw データの射影だけは原文の単体集合の構成成分としない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData`

:::

:::proposition "kerodon_2_5_3_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback")
Kerodon Proposition 2.5.3.5（[Tag 00PQ](https://kerodon.net/tag/00PQ)）。対応表の状態：本体にある。

仮定：dg nerve の単体と単調写像 \[m\] → \[n\]（Kerodon と一致。係数環は ℤ 以外にも取れる）。結論：頂点を引き戻し、成分は単射な像では元の対応成分、端点が潰れた辺では恒等、潰れた高次の成分では零（一致）。

:::

:::definition "kerodon_2_5_3_7"
Kerodon Definition 2.5.3.7（[Tag 00PT](https://kerodon.net/tag/00PT)）。対応表の状態：なし。

B6：dgNerve は HA 規約の Simplex の単体集合。原文の方程式に従う N\_n と各単体写像の比較がないため、別規約の nerve を直接の部分結論としない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve`

:::

:::theorem "kerodon_2_5_3_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.instQuasicategory, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.hornFilling")
Kerodon Theorem 2.5.3.10（[Tag 00PW](https://kerodon.net/tag/00PW)）。対応表の状態：本体にある。

仮定：dg 圏 D（Lean が弱い：任意の可換環 R 上でよい）。結論：dgNerve R D は任意の内角が充填できる Quasicategory（一致）。

:::

# 2.5.4 The Homotopy Category of a Differential Graded Category

%%%
number := false
tag := "kerodon-2-5-4"
%%%

Kerodon [Tag 00SW](https://kerodon.net/tag/00SW)

:::definition "kerodon_2_5_4_1" (lean := "SerrePositivity.DifferentialGraded.boundaryRelation, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeClosedEquiv")
Kerodon Definition 2.5.4.1（[Tag 00PZ](https://kerodon.net/tag/00PZ)）。対応表の状態：本体にある。

仮定：dg 圏の二対象間の閉次数 0 の射 f,g（Lean が弱い：係数環 R は任意の可換環）。結論：f と g の差が次数 −1 の元の微分である関係。鎖次数 1 に読み替えた原文の境界関係と一致する（一致）。

:::

:::proposition "kerodon_2_5_4_5" (lean := "SerrePositivity.DifferentialGraded.boundaryCongruence")
Kerodon Proposition 2.5.4.5（[Tag 00Q3](https://kerodon.net/tag/00Q3)）。対応表の状態：本体にある。

仮定：dg 圏 D（Lean が弱い：係数環 R は任意の可換環）。結論：閉次数 0 の射の境界関係を、左右の合成に関して安定な圏の合同関係にする（一致）。

:::

:::definition "kerodon_2_5_4_6" (lean := "SerrePositivity.DifferentialGraded.HomotopyCategory, SerrePositivity.DifferentialGraded.homotopyHomologyEquiv")
Kerodon Construction 2.5.4.6（[Tag 00Q4](https://kerodon.net/tag/00Q4)）。対応表の状態：本体にある。

仮定：dg 圏 D（Lean が弱い：係数環 R は任意の可換環）。結論：閉次数 0 の普通圏を境界関係で割ると Hom は次数 0 のホモロジーになる（一致）。

:::

:::proposition "kerodon_2_5_4_10"
Kerodon Proposition 2.5.4.10（[Tag 00Q8](https://kerodon.net/tag/00Q8)）。対応表の状態：なし。

B6：equivalence/toH0 は現行 HA 規約の dg nerve と H⁰ の比較。原文の符号規約での nerve と対応づける宣言を欠き、圏同値を圏同型の component と数える前に対象の比較が要る。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equivalence`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0`

:::

# 2.5.5 Digression: The Homology of Simplicial Sets

%%%
number := false
tag := "kerodon-2-5-5"
%%%

Kerodon [Tag 00Q9](https://kerodon.net/tag/00Q9)

:::definition "kerodon_2_5_5_1"
Kerodon Construction 2.5.5.1（[Tag 00QA](https://kerodon.net/tag/00QA)）。対応表の状態：一部。

B6：alternatingFaceMapComplex は全ての面の交代和を微分とする ChainComplex を直接構成する。半単体対象一般ではなく、退化も持つ単体アーベル群に入力を制限した場合。

宣言：`AlgebraicTopology.alternatingFaceMapComplex`

:::

:::definition "kerodon_2_5_5_2" (lean := "SSet.chainComplex, SSet.homology")
Kerodon Definition 2.5.5.2（[Tag 00QB](https://kerodon.net/tag/00QB)）。対応表の状態：Mathlib にある。

仮定：単体集合 S と整数係数（Lean が弱い：余積と加法性を持つ係数圏の係数対象を取れる）。結論：n 単体で添字づけた係数対象の余積と面写像の交代和の微分を持つ鎖複体、およびそのホモロジー（一致）。

:::

:::definition "kerodon_2_5_5_5"
Kerodon Notation 2.5.5.5（[Tag 00QE](https://kerodon.net/tag/00QE)）。対応表の状態：なし。

B6：degenerateIntegralChains は Q∞ の像という構成。原文の退化写像の像で生成した subgroup との同一視は annihilates\_iff だけでは直接の型の結論でなく、比較の議論が要る。

宣言：`SerrePositivity.KST.Comparison.degenerateIntegralChains`、`SerrePositivity.KST.Comparison.integralDegenerateProjection_annihilates_iff`

:::

:::proposition "kerodon_2_5_5_6"
Kerodon Proposition 2.5.5.6（[Tag 00QF](https://kerodon.net/tag/00QF)）。対応表の状態：なし。

B6：Q∞ の像が複体という事実はあるが、原文の指定部分群 D\_n の微分による保存と、像模型の比較がない。退化部分を表す別構成の複体性だけは数えない。

宣言：`SerrePositivity.KST.Comparison.integralDegenerateProjection`、`SerrePositivity.KST.Comparison.degenerateIntegralChains`

:::

:::definition "kerodon_2_5_5_7"
Kerodon Construction 2.5.5.7（[Tag 00QG](https://kerodon.net/tag/00QG)）。対応表の状態：なし。

B6：normalizedMooreComplex は高次面の核の共通部分を用いる第二構成。原文の指定の商 C/D と同じ対象とする宣言なしに第一構成の partial としない。

宣言：`AlgebraicTopology.normalizedMooreComplex`

:::

:::definition "kerodon_2_5_5_9" (lean := "SSet.normalizedChainComplex")
Kerodon Construction 2.5.5.9（[Tag 00QH](https://kerodon.net/tag/00QH)）。対応表の状態：Mathlib にある。

仮定：単体集合 S と整数係数（Lean が弱い：自由対象を取る係数圏で一般化）。結論：各次数では非退化単体を生成元とし、退化単体の寄与を零にした正規化鎖複体（一致）。

:::

:::proposition "kerodon_2_5_5_11"
Kerodon Proposition 2.5.5.11（[Tag 00QK](https://kerodon.net/tag/00QK)）。対応表の状態：なし。

B6：homotopyPInftyToId と正規化ホモトピー同値は核型正規化の模型についての結果。原文の商射 C→C/D と同一の射である比較がなく、その擬同型性の直接の一部ではない。

宣言：`AlgebraicTopology.DoldKan.homotopyPInftyToId`、`SSet.homotopyEquivNormalizedChainComplex`

:::

:::definition "kerodon_2_5_5_15"
Kerodon Variant 2.5.5.15（[Tag 00QP](https://kerodon.net/tag/00QP)）。対応表の状態：一部。

B6：SSetPair.chainComplexFunctor は原文の相対非正規化鎖複体 C(S,S′;Z) の構成成分を与える。核型の正規化相対複体とのホモロジー比較や商型の N の同定は含めない。

宣言：`SSetPair.chainComplexFunctor`、`SerrePositivity.KST.Comparison.relativeIntegralChains`、`SerrePositivity.KST.Comparison.relativeIntegralHomologyFunctor`

:::

# 2.5.6 The Dold-Kan Correspondence

%%%
number := false
tag := "kerodon-2-5-6"
%%%

Kerodon [Tag 00QQ](https://kerodon.net/tag/00QQ)

:::theorem "kerodon_2_5_6_1" (lean := "CategoryTheory.Abelian.DoldKan.equivalence, CategoryTheory.Abelian.DoldKan.N")
Kerodon Theorem 2.5.6.1（[Tag 00QR](https://kerodon.net/tag/00QR)）。対応表の状態：Mathlib にある。

仮定：単体アーベル群と非負次数のアーベル群の複体（Lean が弱い：任意のアーベル圏 C で成り立つ）。結論：正規化 Moore 複体を順関手とする SimplicialObject C と ChainComplex C ℕ の圏同値（一致）。

:::

:::definition "kerodon_2_5_6_3"
Kerodon Construction 2.5.6.3（[Tag 00QT](https://kerodon.net/tag/00QT)）。対応表の状態：なし。

B6：Γ は非負次数複体上の別の Dold–Kan 模型。StandardSimplex も dg Hom に限定した鎖写像模型であり、原文の任意 M に対する指定鎖写像 Hom からの K の構成との比較がない。

宣言：`CategoryTheory.Abelian.DoldKan.Γ`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex`

:::

:::definition "kerodon_2_5_6_9"
Kerodon Construction 2.5.6.9（[Tag 00QX](https://kerodon.net/tag/00QX)）。対応表の状態：一部。

B6：const は任意の集合 G に対して原文が明記する K(G,0) を、nerve(SingleObj G) は群 G に対して明記する K(G,1) を直接構成する。一般の可換群の全 n は含まない。

宣言：`CategoryTheory.Functor.const`、`CategoryTheory.nerve`、`CategoryTheory.SingleObj`

:::

:::definition "kerodon_2_5_6_10"
Kerodon Notation 2.5.6.10（[Tag 00R1](https://kerodon.net/tag/00R1)）。対応表の状態：なし。

B6：standardSimplexEquiv は dg Hom の単体の表現の同値。最上生成元の評価による v、退化の消滅、商への因子化という原文の余単位の結論を型に持たない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv`

:::

:::proposition "kerodon_2_5_6_11"
Kerodon Proposition 2.5.6.11（[Tag 00R2](https://kerodon.net/tag/00R2)）。対応表の状態：なし。

B6：DoldKan.equivalence の抽象 Hom 全単射は核型 N と Γ のもの。原文の指定 K・指定余単位 v と比較されていないので、非負次数への限定だけでは同じ θ の主張にならない。

宣言：`CategoryTheory.Abelian.DoldKan.equivalence`

:::

:::corollary "kerodon_2_5_6_12"
Kerodon Corollary 2.5.6.12（[Tag 00R3](https://kerodon.net/tag/00R3)）。対応表の状態：なし。

B6：DoldKan.equivalence は核型 N と Γ の同値。原文の鎖写像 Hom による K と一致させる宣言がなく、指定 K を右随伴とする主張の特殊化とは数えない。

宣言：`CategoryTheory.Abelian.DoldKan.equivalence`

:::

:::corollary "kerodon_2_5_6_13"
Kerodon Corollary 2.5.6.13（[Tag 00R4](https://kerodon.net/tag/00R4)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。単体集合の正規化鎖複体と Dold–Kan の部品はあるが、ℤ 次数の K を右随伴として組んだ宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::definition "kerodon_2_5_6_15" (lean := "AlgebraicTopology.normalizedMooreComplex")
Kerodon Construction 2.5.6.15（[Tag 00R6](https://kerodon.net/tag/00R6)）。対応表の状態：Mathlib にある。

仮定：単体アーベル群 A（Lean が弱い：任意のアーベル圏 C の単体対象を取れる）。結論：次数 n で d₁,…,d\_n の核の共通部分を取り、d₀ の制限を微分にする正規化 Moore 複体（一致）。

:::

:::lemma_ "kerodon_2_5_6_16"
Kerodon Lemma 2.5.6.16（[Tag 00R7](https://kerodon.net/tag/00R7)）。対応表の状態：なし。

B6：Γ₀.splitting の summand は構成から選んだ成分。原文の高次面の核 Ñ\_m とその包含を退化写像で送る特定 f との同一視が必要で、Splitting の型だけは別模型の材料。

宣言：`CategoryTheory.SimplicialObject.Splitting`、`AlgebraicTopology.DoldKan.Γ₀.splitting`

:::

:::proposition "kerodon_2_5_6_17"
Kerodon Proposition 2.5.6.17（[Tag 00R9](https://kerodon.net/tag/00R9)）。対応表の状態：なし。

B6：splitMonoInclusionOfMooreComplexMap は核型 Ñ→C の分裂単射。原文の指定の合成 Ñ→C→C/D が同型、あるいは C=Ñ⊕D という補空間の同定を直接述べない。

宣言：`AlgebraicTopology.DoldKan.splitMonoInclusionOfMooreComplexMap`

:::

:::proposition "kerodon_2_5_6_21"
Kerodon Proposition 2.5.6.21（[Tag 00RC](https://kerodon.net/tag/00RC)）。対応表の状態：一部。

B6：homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex は原文の核型 Ñ と C の包含を hom とするホモトピー同値。そこから包含のホモロジー同型という第二の結論成分が直接得られる。商射・一般の D の非輪状性は含まない。

宣言：`AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex`、`SerrePositivity.KST.Comparison.degenerateIntegralChains_homology_isZero`

:::

:::proposition "kerodon_2_5_6_23"
Kerodon Proposition 2.5.6.23（[Tag 00RE](https://kerodon.net/tag/00RE)）。対応表の状態：なし。

B6：equivalence と connectiveHomComplex の各次数同型は指定の余単位 v についての主張ではない。K の模型と v の比較を欠くため同型の存在だけを原文の component にしない。

宣言：`CategoryTheory.Abelian.DoldKan.equivalence`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_zeroCyclesIso`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_positiveIso`

:::

# 2.5.7 The Shuffle Product

%%%
number := false
tag := "kerodon-2-5-7"
%%%

Kerodon [Tag 00RF](https://kerodon.net/tag/00RF)

:::proposition "kerodon_2_5_7_1"
Kerodon Proposition 2.5.7.1（[Tag 00RG](https://kerodon.net/tag/00RG)）。対応表の状態：なし。

B6：normalizedShuffle は核型正規化での鎖写像。原文の商型正規化の指定の shuffle と比較されず、射の存在だけでは原文の一意性・自然性・次数0条件の一部を直接得ない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedShuffle`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.projectedRingShuffleProduct_assoc`

:::

:::definition "kerodon_2_5_7_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.left, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.right, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.inversions")
Kerodon Notation 2.5.7.2（[Tag 00RH](https://kerodon.net/tag/00RH)）。対応表の状態：本体にある。

仮定：非負整数 p,q（Kerodon と一致。Lean では n=p+q を明示）。結論：n 個のステップから p 個の左ステップを指定して \[n\]→\[p\] と \[n\]→\[q\] を作り、右ステップが先行する対の数で符号を得る（一致）。

:::

:::definition "kerodon_2_5_7_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleApp, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBidegree")
Kerodon Construction 2.5.7.3（[Tag 00RJ](https://kerodon.net/tag/00RJ)）。対応表の状態：本体にある。

仮定：単体 ℤ 加群 C,D と p+q=n（Kerodon と一致）。結論：次数 (p,q) のテンソル成分から、左右の shuffle の引き戻しを置換符号付きで加えた (C⊗D)\_n への射（一致）。

:::

:::proposition "kerodon_2_5_7_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffle_comm, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffle")
Kerodon Proposition 2.5.7.7（[Tag 00RN](https://kerodon.net/tag/00RN)）。対応表の状態：本体にある。

仮定：単体 ℤ 加群 C,D（Kerodon と一致）。結論：非正規化 shuffle がテンソル複体の微分と可換で、成分ごとには d(a⋄b)=(da)⋄b+(-1)\^p a⋄(db) になる（一致）。

:::

:::proposition "kerodon_2_5_7_8"
Kerodon Proposition 2.5.7.8（[Tag 00RP](https://kerodon.net/tag/00RP)）。対応表の状態：なし。

B6：σ\_rawBilinear\_left/right は単体集合由来の shuffle が正規化への射影後に消える式。原文の C(A⊗B) における退化部分群への所属を結論せず、対象と商の比較が必要。

宣言：`SerrePositivity.EInfinity.Shuffle.σ_rawBilinear_left`、`SerrePositivity.EInfinity.Shuffle.σ_rawBilinear_right`

:::

:::definition "kerodon_2_5_7_9"
Kerodon Construction 2.5.7.9（[Tag 00RQ](https://kerodon.net/tag/00RQ)）。対応表の状態：なし。

B6：normalizedShuffle は核型 Ñ に非正規化 shuffle を挟んだ射。商型 N と指定の商射の可換図式を比較する宣言がなく、同じ主張の部分構成とは数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedShuffle`

:::

:::proposition "kerodon_2_5_7_10"
Kerodon Proposition 2.5.7.10（[Tag 00RR](https://kerodon.net/tag/00RR)）。対応表の状態：なし。

B6：projectedRingShuffleProduct は shuffle を環の乗法で合成した内部積。原文の A⊗B への外部積の結合・対称・単位則を直接述べず、Barratt–Eccles の限られた対象の式も対象比較が必要。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.projectedRingShuffleProduct_assoc`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.projectedRingShuffleProduct_left_unit`、`SerrePositivity.EInfinity.BarrattEccles.shuffleBilinear_left_unit`

:::

:::definition "kerodon_2_5_7_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedShuffle")
Kerodon Notation 2.5.7.11（[Tag 00RS](https://kerodon.net/tag/00RS)）。対応表の状態：本体にある。

仮定：単体 ℤ 加群 C,D（Kerodon と一致）。結論：二つの正規化 Moore 複体のテンソルから点ごとのテンソルの正規化複体への shuffle 鎖写像（一致。記法 EZ が指す鎖写像の構成）。

:::

:::theorem "kerodon_2_5_7_14"
Kerodon Theorem 2.5.7.14（[Tag 00RV](https://kerodon.net/tag/00RV)）。対応表の状態：なし。

B6：normalizedEZHomotopy/ezHomotopy は AW≫shuffle の合成のホモトピー。一方の合成だけの式は指定 EZ 自身のホモロジー同型性を直接与えず、核型/商型の比較も必要。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedEZHomotopy`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezHomotopy`

:::

:::corollary "kerodon_2_5_7_15"
Kerodon Corollary 2.5.7.15（[Tag 00RW](https://kerodon.net/tag/00RW)）。対応表の状態：なし。

B6：chainMap は EZ の候補鎖写像の構成で、擬同型性の結論成分を持たない。原文の命題の証明部品にとどまる。

宣言：`SerrePositivity.EInfinity.Shuffle.chainMap`

:::

:::definition "kerodon_2_5_7_17"
Kerodon Variant 2.5.7.17（[Tag 00RY](https://kerodon.net/tag/00RY)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。相対鎖複体と絶対 shuffle はあるが、指定の積の対への相対 EZ 擬同型は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

# 2.5.8 The Alexander-Whitney Construction

%%%
number := false
tag := "kerodon-2-5-8"
%%%

Kerodon [Tag 00S0](https://kerodon.net/tag/00S0)

:::definition "kerodon_2_5_8_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFront, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBack")
Kerodon Notation 2.5.8.1（[Tag 00S1](https://kerodon.net/tag/00S1)）。対応表の状態：本体にある。

仮定：非負整数 n と p : Fin(n+1)（Kerodon と一致）。結論：\[p\]→\[n\] を i↦i、\[n−p\]→\[n\] を j↦p+j とする前半・後半の単体圏の射（一致）。

:::

:::definition "kerodon_2_5_8_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneyApp, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneySummand")
Kerodon Construction 2.5.8.2（[Tag 00S2](https://kerodon.net/tag/00S2)）。対応表の状態：本体にある。

仮定：単体 ℤ 加群 C,D と次数 n（Kerodon と一致）。結論：(C⊗D)\_n から、各切断位置 p の前半・後半への制限のテンソルを対応する (p,n−p) 成分へ入れた和（一致）。

:::

:::proposition "kerodon_2_5_8_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitney_comm, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitney")
Kerodon Proposition 2.5.8.3（[Tag 00S3](https://kerodon.net/tag/00S3)）。対応表の状態：本体にある。

仮定：単体 ℤ 加群 C,D（Kerodon と一致）。結論：各切断位置の和による非正規化 Alexander–Whitney 射が微分と可換で、C\_\*(C⊗D) から C\_\*(C)⊠C\_\*(D) への鎖写像（一致）。

:::

:::proposition "kerodon_2_5_8_4"
Kerodon Proposition 2.5.8.4（[Tag 00S4](https://kerodon.net/tag/00S4)）。対応表の状態：一部。

B6：alexanderWhitney\_naturality は単体 Z 加群の二変数に関する原文の非正規化 AW の自然性を直接述べる。colax 構造の自然性成分のみで、一般の余単位・余結合は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitney_naturality`、`SerrePositivity.EInfinity.AlexanderWhitney.rawComponent_coassoc`

:::

:::proposition "kerodon_2_5_8_5"
Kerodon Proposition 2.5.8.5（[Tag 00S5](https://kerodon.net/tag/00S5)）。対応表の状態：なし。

B6：aw\_degeneracy\_not\_mono は切断した単体写像のいずれかが退化する組合せ補題。restrictToNormalized も核型への制限であり、原文の指定 K\_\* への像の所属を直接述べない。

宣言：`SerrePositivity.EInfinity.AlexanderWhitney.aw_degeneracy_not_mono`、`SerrePositivity.EInfinity.AlexanderWhitney.restrictToNormalized`

:::

:::definition "kerodon_2_5_8_6"
Kerodon Construction 2.5.8.6（[Tag 00S6](https://kerodon.net/tag/00S6)）。対応表の状態：なし。

B6：normalizedAlexanderWhitney は核型正規化による射。原文の商射による可換図式とその一意性を述べず、商型 N への対象比較が必要。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedAlexanderWhitney`

:::

:::proposition "kerodon_2_5_8_7"
Kerodon Proposition 2.5.8.7（[Tag 00S7](https://kerodon.net/tag/00S7)）。対応表の状態：なし。

B6：normalizedAlexanderWhitney\_naturality は核型 Ñ での式、diagonal の余結合・余単位は対角を合成した別の射の式。原文の商型 N の一般の colax 構造の直接の成分とは数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedAlexanderWhitney_naturality`、`SerrePositivity.EInfinity.AlexanderWhitney.diagonal_coassoc`、`SerrePositivity.EInfinity.AlexanderWhitney.diagonal_left_counit`

:::

:::proposition "kerodon_2_5_8_9"
Kerodon Proposition 2.5.8.9（[Tag 00S9](https://kerodon.net/tag/00S9)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。原文は shuffle の後の AW が厳密に恒等。normalizedEZHomotopy は逆順の合成のホモトピーなので関連引用を除く。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::corollary "kerodon_2_5_8_11"
Kerodon Corollary 2.5.8.11（[Tag 00SB](https://kerodon.net/tag/00SB)）。対応表の状態：なし。

B6：normalizedEZHomotopy は合成 AW≫shuffle のホモトピーだけで、指定 AW 自身の擬同型性を直接述べない。別の合成の逆性と商型への比較が必要。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedEZHomotopy`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezHomotopy`

:::

# 2.5.9 Comparison with the Homotopy Coherent Nerve

%%%
number := false
tag := "kerodon-2-5-9"
%%%

Kerodon [Tag 00SC](https://kerodon.net/tag/00SC)

:::proposition "kerodon_2_5_9_1"
Kerodon Proposition 2.5.9.1（[Tag 00SD](https://kerodon.net/tag/00SD)）。対応表の状態：なし。

B6：standardAW と awData\_assoc/unit は dg Hom を合成先とする演算とその法則。原文の K(X)×K(Y)→K(X⊠Y) とは値域も異なり、任意の鎖複体の lax 構造の直接の部分結論ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_assoc`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_unit_left`

:::

:::definition "kerodon_2_5_9_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanSimplicialCategory, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomSpace, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardDoldKanModuleIso")
Kerodon Construction 2.5.9.2（[Tag 00SE](https://kerodon.net/tag/00SE)）。対応表の状態：本体にある。

仮定：dg 圏 D（Lean が弱い：任意の可換環 R 上でよい）。結論：dg Hom の非負鎖次数への切断に Dold–Kan を施した Hom 単体集合と、対角・AW・dg 合成からなる豊穣合成を持つ単体圏（一致）。

:::

:::proposition "kerodon_2_5_9_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanSimplicialCategory, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedStandardVertexEquiv, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedStandardVertexEquiv_id, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedStandardVertexEquiv_comp")
Kerodon Remark 2.5.9.3（[Tag 00SF](https://kerodon.net/tag/00SF)）。対応表の状態：本体にある。

仮定：dg 圏 D（Lean が弱い：任意の可換環 R 上でよい）。結論：Dold–Kan の単体圏構造を元の閉次数 0 射の普通圏 ClosedCategory R D に直接載せる。Hom の 0 単体との全単射で恒等・合成を保存することを構造の場で確認した（一致）。

:::

:::definition "kerodon_2_5_9_6"
Kerodon Construction 2.5.9.6（[Tag 00SJ](https://kerodon.net/tag/00SJ)）。対応表の状態：一部。

B6：cubeFlag は番号付けた有限集合で空集合から1点ずつ増やす最大旗の単体を直接構成する。原文に記された旗の構成成分のみで、正規化整数基本鎖と自由推移性の一式は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation`

:::

:::definition "kerodon_2_5_9_9"
Kerodon Notation 2.5.9.9（[Tag 00SM](https://kerodon.net/tag/00SM)）。対応表の状態：なし。

B6：coherentCubeHom/Component は包含順 path の Hom からの評価。原文の逆包含と補集合の座標での基本鎖の向きとの比較を欠き、同じ σ の評価とは直接いえない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeHom`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation`

:::

:::proposition "kerodon_2_5_9_10"
Kerodon Proposition 2.5.9.10（[Tag 00SN](https://kerodon.net/tag/00SN)）。対応表の状態：なし。

B6：coherentComparison は HA 符号規約の dg nerve と包含順 nerve の比較。原文の両模型への自然な比較を欠くため、対象の一致だけを指定 Z の一意存在の component としない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison_obj`

:::

:::definition "kerodon_2_5_9_12"
Kerodon Notation 2.5.9.12（[Tag 00SP](https://kerodon.net/tag/00SP)）。対応表の状態：一部。

B6：cubeFaceMap は指定座標を0/1に固定する原文の二つの面の包含を直接構成する。原文の基本鎖をこれで送った整数鎖としての比較は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag_boundary_sum`

:::

:::lemma_ "kerodon_2_5_9_13"
Kerodon Lemma 2.5.9.13（[Tag 00SQ](https://kerodon.net/tag/00SQ)）。対応表の状態：一部。

B6：cubeFlag\_boundary\_sum は任意の加法可換群値 F に対する符号和。F を正規化自由鎖への生成元写像に取ると原文の境界式が直接得られる。型の card=n+2、すなわち次元2以上に限り、0・1次元は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag_boundary_sum`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag_boundary_eq_outer_sum`

:::

:::lemma_ "kerodon_2_5_9_16"
Kerodon Lemma 2.5.9.16（[Tag 00ST](https://kerodon.net/tag/00ST)）。対応表の状態：なし。

B6：cubeEvaluation\_AW\_comp は dg 合成後の評価の等式。原文の普遍的な正規化整数鎖内の AW の等式と異なり、合成評価から元のテンソル鎖の等式を回収する宣言がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation_AW_comp`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval_AW_cubeSum_all_permutations`

:::

:::theorem "kerodon_2_5_9_18"
Kerodon Theorem 2.5.9.18（[Tag 00SV](https://kerodon.net/tag/00SV)）。対応表の状態：なし。

B6：coherentComparison の準圏同値・充満忠実性は HA/包含順模型の射についての主張。原文の特定の Z との比較が未確認で、自明 Kan fibration の部分としても数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparisonEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison_fullyFaithful`

:::

