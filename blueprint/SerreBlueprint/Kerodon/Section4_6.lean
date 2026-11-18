import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ConeFamily
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CosliceCoconeFamilyEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CosliceFixedDiagramIso
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CosliceLaxEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoin
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinComparison
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinComparisonGluing
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinGeneralComparison
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinStdComparison
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FullyFaithfulIntervalMapping
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingSpace
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinEquivalenceFunctor
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LaxPullback
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LaxPullbackProjections
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LaxSlice
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalComparison
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceLeft
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceModelEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceRightKan
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PreFiberKan
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RightIntervalEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SliceConeFamilyEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SliceFixedDiagramIso
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SliceLaxEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SliceLaxMap

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "4.6 Morphism Spaces" =>
%%%
number := false
tag := "kerodon-4-6"
%%%

Kerodon の 4.6 節（[Tag 01J3](https://kerodon.net/tag/01J3)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 4.6.1 Morphism Spaces

%%%
number := false
tag := "kerodon-4-6-1"
%%%

Kerodon [Tag 01J4](https://kerodon.net/tag/01J4)

:::definition "kerodon_4_6_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace")
Kerodon Construction 4.6.1.1（[Tag 01J5](https://kerodon.net/tag/01J5)）。対応表の状態：本体にある。

仮定：単体集合 X と頂点 x,y（Kerodon と一致）。結論：intervalMappingSpace x y は Fun(Δ¹,X) の境界制限を (x,y) 上で取ったファイバー（一致）。

:::

:::definition "kerodon_4_6_1_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace")
Kerodon Variant 4.6.1.3（[Tag 03X9](https://kerodon.net/tag/03X9)）。対応表の状態：本体にある。

仮定：∞ 圏の頂点 x（Lean が弱い：構成は任意の SSet）。結論：両端を同じ x にした intervalMappingSpace x x が自己写像空間（一致）。

:::

:::proposition "kerodon_4_6_1_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace_kanComplex, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHom_kanComplex")
Kerodon Proposition 4.6.1.10（[Tag 01JC](https://kerodon.net/tag/01JC)）。対応表の状態：本体にある。

仮定：Quasicategory X と任意の頂点 x,y（Kerodon と一致）。結論：intervalMappingSpace x y が KanComplex。右 pinched 版にも同じ結論がある（一致）。

:::

:::proposition "kerodon_4_6_1_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanComplex_preFiber_of_vertexSurjective")
Kerodon Proposition 4.6.1.11（[Tag 01P1](https://kerodon.net/tag/01P1)）。対応表の状態：本体にある。

仮定：Quasicategory X、頂点全射な単射 j:A→B、Fun(A,X) の頂点 p（Kerodon と一致）。結論：制限 (pre j).app X の p 上のファイバーが KanComplex（一致）。

:::

:::proposition "kerodon_4_6_1_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsQCatEquivalence.isFullyFaithful, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsFullyFaithful.intervalMappingPost_isQCatEquivalence")
Kerodon Proposition 4.6.1.14（[Tag 06QP](https://kerodon.net/tag/06QP)）。対応表の状態：本体にある。

仮定：∞ 圏間の圏同値 F、始域の頂点 x,y（Lean が弱い：写像空間の補題は充満忠実性で足りる）。結論：intervalMappingPost F x y は圏同値。ここで両辺は Kan 複体なのでホモトピー同値（一致）。

:::

:::definition "kerodon_4_6_1_16" (uses := "kerodon_1_1_0_6")
Kerodon Construction 4.6.1.16（[Tag 01P2](https://kerodon.net/tag/01P2)）。対応表の状態：なし。

引用に現れるのは右pinchedHomMapの頂点fiberで、原文の区間模型のHom\_C(X,Y)上の指定辺のfiberとの比較がない。定義の対象と相対写像の同一視が必要。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomMap_vertexFiber_kanComplex`

:::

:::proposition "kerodon_4_6_1_21"
Kerodon Proposition 4.6.1.21（[Tag 01P7](https://kerodon.net/tag/01P7)）。対応表の状態：なし。

右pinched模型の指定fiberのKan性で、原文の区間模型のfiberのKan性ではない。両模型の弱同値だけでもKan性は移らず、特定fiberの同型などの比較が要る。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomMap_vertexFiber_kanComplex`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomMap_rightFibration`

:::

:::proposition "kerodon_4_6_1_22" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_6_1_24")
Kerodon Proposition 4.6.1.22（[Tag 01P8](https://kerodon.net/tag/01P8)）。対応表の状態：なし。

pinchedHomMapのホーン持ち上げは別模型の射の性質。原文の区間模型のHomへの誘導射と厳密に比較する宣言を欠く。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomMap_hasLiftingProperty_horn`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomMap_rightFibration`

:::

:::proposition "kerodon_4_6_1_24" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_4_3_10, kerodon_4_4_5_11, kerodon_4_6_1_11")
Kerodon Proposition 4.6.1.24（[Tag 01PC](https://kerodon.net/tag/01PC)）。対応表の状態：一部。

kanComplex\_preFiber\_of\_vertexSurjective は底Dが終対象の場合の同じ、全頂点を含むAからの制限の指定fiberのKan性を直接返す。右pinched模型の候補は区間模型との比較がなく数えない。一般の相対底は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomMap_hasLiftingProperty_horn`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomMap_rightFibration`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanComplex_preFiber_of_vertexSurjective`

:::

# 4.6.2 Digression: Universal Property of the Join

%%%
number := false
tag := "kerodon-4-6-2"
%%%

Kerodon [Tag 01HM](https://kerodon.net/tag/01HM)

:::definition "kerodon_4_6_2_1"
Kerodon Construction 4.6.2.1（[Tag 01HN](https://kerodon.net/tag/01HN)）。対応表の状態：一部。

joinCylinderMap は原文の順序の切断による同じcollapseの写像を直接構成する。指定両端だけからの一意性は引用型に含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap`

:::

:::proposition "kerodon_4_6_2_2"
Kerodon Proposition 4.6.2.2（[Tag 01HP](https://kerodon.net/tag/01HP)）。対応表の状態：なし。

fatJoinComparisonの前合成同値性は関連する比較射の命題。原文の指定四角がcoreのホモトピーpullbackを与えることへの判定の比較がさらに必要で、同値な言い換えという説明だけではpartialにしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinComparison`

:::

:::definition "kerodon_4_6_2_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStage, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison")
Kerodon Notation 4.6.2.3（[Tag 01HR](https://kerodon.net/tag/01HR)）。対応表の状態：本体にある。

仮定：任意の単体集合 X,Y（Kerodon と一致）。結論：fatJoin X Y は円柱の両端をそれぞれ X,Y へ射影する押し出し。fatJoinComparison は通常の join への比較射（一致）。

:::

:::theorem "kerodon_4_6_2_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinComparison, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison")
Kerodon Theorem 4.6.2.8（[Tag 01HV](https://kerodon.net/tag/01HV)）。対応表の状態：本体にある。

仮定：任意の単体集合 X,Y（Kerodon と一致）。結論：fatJoinComparison X Y が前合成同値（Lean が強い：各試験対象で π₀ 全単射を含む）。

:::

:::corollary "kerodon_4_6_2_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsPrecompositionEquivalence.joinMap_left, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsPrecompositionEquivalence.joinMap_right")
Kerodon Corollary 4.6.2.9（[Tag 01HW](https://kerodon.net/tag/01HW)）。対応表の状態：本体にある。

仮定：f,g がそれぞれ前合成同値（Kerodon と一致）。結論：joinMap f (id \_) と joinMap (id \_) g が前合成同値。二つの合成が f⋆g（一致）。

:::

:::lemma_ "kerodon_4_6_2_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinComparison, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinComparison_of_pushout_left")
Kerodon Lemma 4.6.2.10（[Tag 01HX](https://kerodon.net/tag/01HX)）。対応表の状態：本体にある。

仮定：任意の単体集合 X,Y（Lean が弱い：Δ¹⋄Y での同値を事前には仮定しない）。結論：fatJoinComparison X Y が前合成同値（一致）。

:::

:::lemma_ "kerodon_4_6_2_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinComparison, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinComparison_stdSimplex")
Kerodon Lemma 4.6.2.11（[Tag 01HY](https://kerodon.net/tag/01HY)）。対応表の状態：本体にある。

仮定：X=Δ¹、Y=Δ⁰（Lean が弱い：任意の標準単体の組を扱う）。結論：fatJoinComparison Δ¹ Δ⁰ が前合成同値（一致）。

:::

:::proposition "kerodon_4_6_2_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinComparison")
Kerodon Proposition 4.6.2.12（[Tag 01HZ](https://kerodon.net/tag/01HZ)）。対応表の状態：本体にある。

仮定：X は任意、Y=Δ⁰（Lean が弱い：Y も任意）。結論：X⋄Δ⁰→X⋆Δ⁰ が前合成同値（一致）。

:::

:::corollary "kerodon_4_6_2_14" (uses := "kerodon_1_1_0_6, kerodon_4_3_6_4, kerodon_4_5_4_14, kerodon_4_5_5_9, kerodon_4_5_5_11, kerodon_4_6_2_8")
Kerodon Corollary 4.6.2.14（[Tag 01J0](https://kerodon.net/tag/01J0)）。対応表の状態：なし。

fatJoinComparisonは原文の相対pushoutからB◇Δ⁰へのθとは異なる射。通常joinとの比較の前合成同値性だけはθの同値性の直接の一部ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinComparison`

:::

# 4.6.3 Digression: Categorical Mapping Cylinders

%%%
number := false
tag := "kerodon-4-6-3"
%%%

Kerodon [Tag 01K2](https://kerodon.net/tag/01K2)

:::proposition "kerodon_4_6_3_1" (uses := "kerodon_1_4_0_1, kerodon_4_6_3_9")
Kerodon Proposition 4.6.3.1（[Tag 01K3](https://kerodon.net/tag/01K3)）。対応表の状態：一部。

可逆区間JによるB×Jの円柱に限ると、二つのEquivalenceCylinderFunctorIsoの型は同じ二端点を持つ延長とFunctorIsoを双方向に直接結ぶ。任意の分解B̄での三条件全部は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.exists_equivalenceCylinder_extension_of_functorIso`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.nonempty_functorIso_of_equivalenceCylinder_extension`

:::

:::definition "kerodon_4_6_3_3" (uses := "kerodon_1_1_0_6")
Kerodon Definition 4.6.3.3（[Tag 01K5](https://kerodon.net/tag/01K5)）。対応表の状態：一部。

relativeEquivalenceCylinderの二端点はA上で一致し、同じ射影への切断であることをendpoint\_fixed/projectionが直接返す。B∐\_A Bからの合わせた射のMono性と一般の円柱を束ねる型は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinder`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinderProjection`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinderEndpoint_projection`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinderEndpoint_fixed`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinderEndpoint_mono`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_relativeEquivalenceCylinderEndpoint`

:::

:::corollary "kerodon_4_6_3_7" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_6_3_1, kerodon_4_6_3_3")
Kerodon Corollary 4.6.3.7（[Tag 01K9](https://kerodon.net/tag/01K9)）。対応表の状態：一部。

exists\_relativeCylinder\_extension は元の二図式を結ぶ点ごとに可逆な実際の区間ホモトピーも入力すると、指定の単射円柱への同じ延長を直接返す。FunctorIsoだけからこの入力を作る方向と逆方向は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.exists_relativeCylinder_extension`

:::

:::theorem "kerodon_4_6_3_8" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_1_4_6, kerodon_4_4_3_15, kerodon_4_5_4_11")
Kerodon Theorem 4.6.3.8（[Tag 01KA](https://kerodon.net/tag/01KA)）。対応表の状態：一部。

S=Δ⁰、A=∅、B̄=B×Jの可逆区間円柱に限ると、二つのEquivalenceCylinderFunctorIsoの型が同じ延長とFunctorIsoを双方向に結ぶ。一般のisofibration上の相対版は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.exists_relativeCylinder_extension`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.exists_equivalenceCylinder_extension_of_functorIso`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.nonempty_functorIso_of_equivalenceCylinder_extension`

:::

:::corollary "kerodon_4_6_3_9" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_6_3_8")
Kerodon Corollary 4.6.3.9（[Tag 01KB](https://kerodon.net/tag/01KB)）。対応表の状態：一部。

exists\_relativeCylinder\_extension はA上で固定され点ごとに可逆な区間ホモトピーを追加入力すると、原文(3)の任意の単射円柱への同じ延長を直接返す。相対関手空間での同型だけからの入力の比較と逆方向は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinder`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.exists_relativeCylinder_extension`

:::

:::corollary "kerodon_4_6_3_10"
Kerodon Corollary 4.6.3.10（[Tag 01KC](https://kerodon.net/tag/01KC)）。対応表の状態：一部。

底Sを終対象にし、A上固定で点ごとに可逆な区間ホモトピーも与える場合、exists\_relativeCylinder\_extension は指定円柱への同じ延長を返す。一般の相対底の持ち上げとiffは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.exists_relativeCylinder_extension`

:::

:::corollary "kerodon_4_6_3_11"
Kerodon Corollary 4.6.3.11（[Tag 01KD](https://kerodon.net/tag/01KD)）。対応表の状態：一部。

exists\_relativeCylinder\_extension はA上で固定され点ごとに可逆な区間ホモトピーを追加入力すると、指定円柱への同じ延長を直接返す。相対関手空間での同型との比較・逆向きは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.exists_relativeCylinder_extension`

:::

# 4.6.4 Oriented Fiber Products

%%%
number := false
tag := "kerodon-4-6-4"
%%%

Kerodon [Tag 01KE](https://kerodon.net/tag/01KE)

:::definition "kerodon_4_6_4_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst")
Kerodon Definition 4.6.4.1（[Tag 01KF](https://kerodon.net/tag/01KF)）。対応表の状態：本体にある。

仮定：同じ標的 C を持つ単体集合の射 p:A→C と q:B→C（Kerodon と一致）。結論：laxPullback p q は Fun(Δ¹,C) の両端評価に沿い A×B から引き戻した単体集合（一致）。

:::

:::proposition "kerodon_4_6_4_2" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_5_3")
Kerodon Proposition 4.6.4.2（[Tag 01KG](https://kerodon.net/tag/01KG)）。対応表の状態：なし。

arrowEndpointPairのisofibration性は引き戻す前の射の性質。原文のlax pullbackの特定の射影θとの基底変換の同定が必要。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair_kanEquivalenceLifting`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair_innerFibration`

:::

:::corollary "kerodon_4_6_4_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback_quasicategory")
Kerodon Corollary 4.6.4.3（[Tag 01KH](https://kerodon.net/tag/01KH)）。対応表の状態：本体にある。

仮定：Quasicategory A,B,C と p:A→C、q:B→C（Kerodon と一致）。結論：laxPullback p q が Quasicategory（一致）。

:::

:::proposition "kerodon_4_6_4_13" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_6_2, kerodon_4_6_2_3, kerodon_4_6_2_14")
Kerodon Proposition 4.6.4.13（[Tag 01KQ](https://kerodon.net/tag/01KQ)）。対応表の状態：一部。

pointedConeProjectionをK=Δ⁰に取りjoinStdSimplexIso 0 0でΔ¹に移すと、原文の始点Xを固定した向き付き積の同じ射影のleft fibration性を直接得る。終点固定のright側は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedConeProjection_leftFibration`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedConeProjection`

:::

:::corollary "kerodon_4_6_4_14" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_6_4_13")
Kerodon Corollary 4.6.4.14（[Tag 01KR](https://kerodon.net/tag/01KR)）。対応表の状態：なし。

通常joinによるslice/coslice射影は原文の向き付き積の射影と別模型。sliceLaxMapの圏同値性だけではその射のleft/right fibration性は移らず、厳密な比較が必要。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverProjection_rightFibration`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderProjection_leftFibration`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_sliceLaxMap`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_cosliceLaxMap`

:::

:::definition "kerodon_4_6_4_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceLaxMap, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceLaxMap")
Kerodon Construction 4.6.4.15（[Tag 02GH](https://kerodon.net/tag/02GH)）。対応表の状態：本体にある。

仮定：任意の単体集合の射 F:K→X（Kerodon と一致）。結論：太い join から通常の join への前合成で slice→laxSlice と coslice→laxCoslice を構成。標的は端点の固定された向き付き引き戻しの模型（一致）。

:::

:::theorem "kerodon_4_6_4_19" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_sliceLaxMap, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_cosliceLaxMap, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSlice")
Kerodon Theorem 4.6.4.19（[Tag 01KU](https://kerodon.net/tag/01KU)）。対応表の状態：本体にある。

仮定：Quasicategory X と任意の図式 F:K→X（Kerodon と一致）。結論：sliceLaxMap F と cosliceLaxMap F が IsQCatEquivalence（一致）。

:::

:::corollary "kerodon_4_6_4_20" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_sliceLaxMap, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_cosliceLaxMap")
Kerodon Corollary 4.6.4.20（[Tag 02VT](https://kerodon.net/tag/02VT)）。対応表の状態：本体にある。

仮定：∞ 圏 X の頂点（Lean が弱い：任意の K と F:K→X を扱う）。結論：K=Δ⁰ の slice・coslice から点を固定する向き付き引き戻しへの対角射が圏同値（一致）。

:::

:::corollary "kerodon_4_6_4_21" (uses := "kerodon_1_4_0_1, kerodon_4_6_4_19")
Kerodon Corollary 4.6.4.21（[Tag 02GL](https://kerodon.net/tag/02GL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：片側を点とする場合・同値および厳密基底変換・左右と Kan ファイバーを照合。同値 G で基底図式を押し出した slice と coslice の双方の同値。図式制限や両者の op 比較は G による変換を扱わない。

:::

:::corollary "kerodon_4_6_4_22" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_3_21, kerodon_4_5_3_20, kerodon_4_5_3_24, kerodon_4_5_3_27, kerodon_4_5_3_28, kerodon_4_6_4_21")
Kerodon Corollary 4.6.4.22（[Tag 069H](https://kerodon.net/tag/069H)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：片側を点とする場合・同値および厳密基底変換・左右と Kan ファイバーを照合。categorical pullback を図式に沿う slice に移す比較四角。点上の pullback や pinched Hom の四角では slice 全体に及ばない。

:::

:::corollary "kerodon_4_6_4_23"
Kerodon Corollary 4.6.4.23（[Tag 06QQ](https://kerodon.net/tag/06QQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：片側を点とする場合・同値および厳密基底変換・左右と Kan ファイバーを照合。右ファイブレーションのファイバーと K の連結度から slice 射の連結度を見積もる型。右ファイブレーションの基底変換には n と k の次数がない。

:::

:::corollary "kerodon_4_6_4_24"
Kerodon Corollary 4.6.4.24（[Tag 05YA](https://kerodon.net/tag/05YA)）。対応表の状態：一部。

sliceOverPostcomp\_trivialKanFibration\_of\_rightFibration はK=Δ⁰の同じ射U\_/Fの自明Kan性を直接返す。この図式は全次数で連結で、任意の指定のfiber切断次数に依存しない。一般Kは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceOverPostcomp_trivialKanFibration_of_rightFibration`

:::

:::lemma_ "kerodon_4_6_4_25" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.nonempty_functorIso_iff_sliceOverFixedDiagramVertexIso, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.nonempty_functorIso_iff_sliceUnderFixedDiagramVertexIso")
Kerodon Lemma 4.6.4.25（[Tag 01KV](https://kerodon.net/tag/01KV)）。対応表の状態：本体にある。

仮定：Quasicategory X、固定図式 F:K→X、slice 内の二つの J 図式（Kerodon と一致）。結論：二図式の FunctorIso の存在と、対応する J⋆K 上の図式の相対関手空間での頂点同型の存在が同値（一致）。

:::

# 4.6.5 Pinched Morphism Spaces

%%%
number := false
tag := "kerodon-4-6-5"
%%%

Kerodon [Tag 01KW](https://kerodon.net/tag/01KW)

:::definition "kerodon_4_6_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft")
Kerodon Construction 4.6.5.1（[Tag 01KX](https://kerodon.net/tag/01KX)）。対応表の状態：本体にある。

仮定：単体集合 X と頂点 x,y（Kerodon と一致）。結論：右 pinched は X\_\{/y\} の x 上、左 pinched は X\_\{x/\} の y 上のファイバーに当たる模型（一致）。

:::

:::proposition "kerodon_4_6_5_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHom_kanComplex, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft_kanComplex")
Kerodon Proposition 4.6.5.5（[Tag 01L0](https://kerodon.net/tag/01L0)）。対応表の状態：本体にある。

仮定：Quasicategory X と頂点 x,y（Kerodon と一致）。結論：pinchedHom x y と pinchedHomLeft x y はともに KanComplex（一致）。

:::

:::definition "kerodon_4_6_5_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftToIntervalMappingSpace")
Kerodon Construction 4.6.5.7（[Tag 01L2](https://kerodon.net/tag/01L2)）。対応表の状態：本体にある。

仮定：単体集合 X と頂点 x,y（Kerodon と一致）。結論：左右の pinched 空間から区間模型 intervalMappingSpace x y への pinch inclusion を構成（一致）。

:::

:::proposition "kerodon_4_6_5_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftToIntervalMappingSpace_isQCatEquivalence")
Kerodon Proposition 4.6.5.10（[Tag 01L5](https://kerodon.net/tag/01L5)）。対応表の状態：本体にある。

仮定：Quasicategory X と頂点 x,y（Kerodon と一致）。結論：左右の pinch inclusion が IsQCatEquivalence。両端が Kan 複体なのでホモトピー同値（一致）。

:::

# 4.6.6 Digression: Diagrams in Slice ∞-Categories

%%%
number := false
tag := "kerodon-4-6-6"
%%%

Kerodon [Tag 04HY](https://kerodon.net/tag/04HY)

:::definition "kerodon_4_6_6_1"
Kerodon Notation 4.6.6.1（[Tag 04HZ](https://kerodon.net/tag/04HZ)）。対応表の状態：一部。

片方の図式が空の場合、sliceOverまたはsliceUnderが原文の両側sliceの一側だけを固定した構成を直接与える。二つの非空図式を同時に固定するtilde fと反復構成全体は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder`

:::

:::definition "kerodon_4_6_6_4"
Kerodon Construction 4.6.6.4（[Tag 04J1](https://kerodon.net/tag/04J1)）。対応表の状態：一部。

sliceConeFamilyMapはK₋=∅、K=Δ⁰のとき、原文の同じsliceからcone familyへの評価比較を直接構成する。両側の一般図式と一般Kは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyMap`

:::

:::theorem "kerodon_4_6_6_5"
Kerodon Theorem 4.6.6.5（[Tag 04J2](https://kerodon.net/tag/04J2)）。対応表の状態：一部。

sliceConeFamilyMapとcosliceCoconeFamilyMapの圏同値性は、それぞれ片側の図式が空、K=Δ⁰の場合の同じ比較射の結論。一般の両側slice・任意Kは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_sliceConeFamilyMap`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_cosliceCoconeFamilyMap`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_fatJoinComparison_fixedDiagram`

:::

:::lemma_ "kerodon_4_6_6_7"
Kerodon Lemma 4.6.6.7（[Tag 04J4](https://kerodon.net/tag/04J4)）。対応表の状態：一部。

isQCatEquivalence\_sliceConeFamilyMap はK=Δ⁰で同じslice→cone familyの比較が圏同値となる結論を直接返す。任意Kの関手空間版は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_sliceConeFamilyMap`

:::

:::proposition "kerodon_4_6_6_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_sliceConeFamilyMap, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamily, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_cosliceCoconeFamilyMap")
Kerodon Example 4.6.6.8（[Tag 04J5](https://kerodon.net/tag/04J5)）。対応表の状態：本体にある。

仮定：Quasicategory X と任意の図式 F:K→X（Kerodon と一致）。結論：sliceConeFamilyMap F が圏同値。coneFamily F は左錐図式を K 上で F に固定した関手空間（一致）。

:::

:::corollary "kerodon_4_6_6_9"
Kerodon Corollary 4.6.6.9（[Tag 04J6](https://kerodon.net/tag/04J6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：片側が空・点・両側の拡張・関手圏の点の版を照合。mixed slice に対する A⊂B の延長比較の持ち上げ性。片側の restriction の型には二端の固定がない。

:::

:::definition "kerodon_4_6_6_10"
Kerodon Variant 4.6.6.10（[Tag 02GN](https://kerodon.net/tag/02GN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：片側が空・点・両側の拡張・関手圏の点の版を照合。join で作る slice/coslice から Fun(K,C) の点上の slice/coslice への両比較。join と over の定義があってもこの比較射を扱う型がない。

:::

# 4.6.7 Morphism Spaces in the Homotopy Coherent Nerve

%%%
number := false
tag := "kerodon-4-6-7"
%%%

Kerodon [Tag 01LA](https://kerodon.net/tag/01LA)

:::definition "kerodon_4_6_7_1" (uses := "kerodon_1_1_0_6")
Kerodon Notation 4.6.7.1（[Tag 01LB](https://kerodon.net/tag/01LB)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一つの豊穣 Hom・二対象・局所 Kan の特例・次数を固定した解像を照合。二対象 x,y の simplicial category E\[K\] の一方向 Hom が K で逆向きは空。enriched pair object は積でこの自由構成ではない。

:::

:::definition "kerodon_4_6_7_3" (uses := "kerodon_1_1_0_6, kerodon_2_4_3_1, kerodon_2_4_4_15, kerodon_4_6_5_1")
Kerodon Construction 4.6.7.3（[Tag 01LD](https://kerodon.net/tag/01LD)）。対応表の状態：なし。

coherentHomComparison は右pinched写像空間への比較で、原文は左pinchedへの特定のθ。Pathの包含順の規約も異なり、指定射の比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison`

:::

:::theorem "kerodon_4_6_7_5" (uses := "kerodon_1_2_5_1, kerodon_4_6_7_3")
Kerodon Theorem 4.6.7.5（[Tag 01LE](https://kerodon.net/tag/01LE)）。対応表の状態：なし。

右pinchedのcoherentHomComparisonのホモトピー同値性であり、原文の左pinchedの指定θの同値性ではない。対象だけでなく比較射を同定する宣言が必要。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_isSimplicialHomotopyEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_isQCatEquivalence`

:::

:::theorem "kerodon_4_6_7_8" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_6_7_3, kerodon_4_6_7_22, kerodon_4_6_7_23, kerodon_4_6_7_25, kerodon_4_6_7_26")
Kerodon Theorem 4.6.7.8（[Tag 01LG](https://kerodon.net/tag/01LG)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。Hom が Kan 複体の場合（Thm 4.6.7.5）だけ。Hom が ∞ 圏のときの同値は未。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint_quasicategory`

:::

:::proposition "kerodon_4_6_7_9"
Kerodon Remark 4.6.7.9（[Tag 01LH](https://kerodon.net/tag/01LH)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。右 pinched で直接作っているので op 経由の主張はない。Kan の場合だけ。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_enriched_naturality`

:::

:::definition "kerodon_4_6_7_10" (uses := "kerodon_1_1_0_6, kerodon_2_4_4_2")
Kerodon Construction 4.6.7.10（[Tag 01LJ](https://kerodon.net/tag/01LJ)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。仮定：任意の単体集合 K（Kerodon と一致）。結論：coherentResolution は標準単体上の旗から拡張した関手（Lean が弱い：Path\[ΣK\] の指定二点間の Hom と同定する型がない）。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex`

:::

:::lemma_ "kerodon_4_6_7_15"
Kerodon Lemma 4.6.7.15（[Tag 01LP](https://kerodon.net/tag/01LP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一つの豊穣 Hom・二対象・局所 Kan の特例・次数を固定した解像を照合。E\[K\] からの対象固定 enriched functor と K から Hom(X,Y) への射の全単射。通常 nerve の完全忠実性はこの対応の型ではない。

:::

:::corollary "kerodon_4_6_7_16" (uses := "kerodon_1_1_0_6")
Kerodon Corollary 4.6.7.16（[Tag 01LQ](https://kerodon.net/tag/01LQ)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。仮定：任意の単体集合 K、単体豊穣圏 C と対象 X,Y（Kerodon と一致）。結論：右 pinched の R(Hom\_C(X,Y)) との同型と Φ⊣R が Hom 全単射を与える（Lean が弱い：原文の左 pinched 版との同定を欠く）。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedFlagIso`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction`

:::

:::corollary "kerodon_4_6_7_18" (uses := "kerodon_1_1_0_6, kerodon_4_6_7_1, kerodon_4_6_7_16")
Kerodon Corollary 4.6.7.18（[Tag 01LR](https://kerodon.net/tag/01LR)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。E\[B\] の構成がないので、随伴 Φ ⊣ R だけ。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction`

:::

:::corollary "kerodon_4_6_7_19"
Kerodon Corollary 4.6.7.19（[Tag 01LS](https://kerodon.net/tag/01LS)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。右随伴は抽象的に定義していて、Hom\^L\_\{N(E\[B\])\}(x,y) との同一視はない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint`

:::

:::corollary "kerodon_4_6_7_21" (uses := "kerodon_4_6_7_10")
Kerodon Corollary 4.6.7.21（[Tag 01LU](https://kerodon.net/tag/01LU)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。仮定：任意の単体集合の図式（Kerodon と一致）。結論：旗で定めた coherentResolution が余極限を保存（Lean が弱い：原文の Path\[ΣK\] の Φ との同定は未確認）。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution_preservesColimitsOfSize`

:::

:::definition "kerodon_4_6_7_22" (uses := "kerodon_1_1_0_6, kerodon_4_6_7_1, kerodon_4_6_7_3, kerodon_4_6_7_18")
Kerodon Construction 4.6.7.22（[Tag 01LV](https://kerodon.net/tag/01LV)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。仮定：任意の単体集合 K（Kerodon と一致）。結論：coherentResolutionProjectionAll は旗の解像から K への自然変換（Lean が弱い：原文の E\[K\] の左 pinched 比較を転置した射との一致は型にない）。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll`

:::

:::proposition "kerodon_4_6_7_23" (uses := "kerodon_1_1_0_6, kerodon_1_1_4_12, kerodon_4_5_5_9, kerodon_4_6_2_3, kerodon_4_6_2_12, kerodon_4_6_7_21, kerodon_4_6_7_22, kerodon_4_6_7_29, kerodon_4_8_8_11")
Kerodon Proposition 4.6.7.23（[Tag 01LW](https://kerodon.net/tag/01LW)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。仮定：任意の単体集合 K（Kerodon と一致）。結論：coherentResolutionProjectionAll.app K は前合成同値（Lean が弱い：原文の指定 ρ\_K と同じ射であることを引用先から確認できない）。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll_isPrecompositionEquivalence`

:::

:::corollary "kerodon_4_6_7_24" (uses := "kerodon_1_1_0_6, kerodon_4_6_7_23")
Kerodon Corollary 4.6.7.24（[Tag 01LX](https://kerodon.net/tag/01LX)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。仮定：K→K′ が前合成同値（Lean が強い：原文の π₀ 条件との橋渡しが引用にない）。結論：旗の解像による像は前合成同値（Lean が弱い：Path\[Σ−\] の関手との比較を欠く）。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution_map_isPrecompositionEquivalence`

:::

:::corollary "kerodon_4_6_7_25" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_6_2, kerodon_4_6_7_16, kerodon_4_6_7_24")
Kerodon Corollary 4.6.7.25（[Tag 01LY](https://kerodon.net/tag/01LY)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。仮定：単体豊穣圏 C の Hom\_C(X,Y) が ∞ 圏（Kerodon と一致）。結論：右随伴 R の値が ∞ 圏であり、右 pinched と同型（Lean が弱い：原文の左 pinched の模型との比較を欠く）。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint_quasicategory`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedFlagIso`

:::

:::corollary "kerodon_4_6_7_26" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_6_3_3, kerodon_4_6_3_7, kerodon_4_6_7_16, kerodon_4_6_7_21, kerodon_4_6_7_24")
Kerodon Corollary 4.6.7.26（[Tag 01LZ](https://kerodon.net/tag/01LZ)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。仮定：単体集合 K の解像に沿う豊穣比較。型は解像側の指定ホモトピーを仮定。結論：指定ホモトピーを随伴で移す方向がある。原文の一つの豊穣 Hom の準圏性で二つの像の同型を比較する iff は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionTransposeHomotopy`

:::

:::proposition "kerodon_4_6_7_27" (uses := "kerodon_1_1_0_6, kerodon_2_4_4_9")
Kerodon Example 4.6.7.27（[Tag 01M0](https://kerodon.net/tag/01M0)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。仮定：m,n が非負整数（Kerodon と一致）。結論：CoherentResolutionFlag n m は最小元から始まる増大旗（Lean が弱い：ΣΔⁿ の非退化単体と両端固定の減少旗による原文の集合との全単射が型にない）。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag`

:::

:::definition "kerodon_4_6_7_28" (uses := "kerodon_1_1_0_6, kerodon_4_6_7_27")
Kerodon Construction 4.6.7.28（[Tag 01M1](https://kerodon.net/tag/01M1)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一つの豊穣 Hom・二対象・局所 Kan の特例・次数を固定した解像を照合。部分集合鎖で定める Φ(Δⁿ)×Δ¹→Φ(Δⁿ⁺¹) の指定写像。rigidification の頂点鎖・necklace はこの二変数射を定めない。

:::

:::lemma_ "kerodon_4_6_7_29" (uses := "kerodon_1_1_0_6, kerodon_4_6_7_28")
Kerodon Lemma 4.6.7.29（[Tag 01M2](https://kerodon.net/tag/01M2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一つの豊穣 Hom・二対象・局所 Kan の特例・次数を固定した解像を照合。指定された Φ(Δⁿ)×Δ¹→Φ(Δⁿ⁺¹) の性質。通常の Δ¹ cylinder 比較には部分集合鎖モデル Φ の端点条件がない。

:::

# 4.6.8 Composition of Morphisms

%%%
number := false
tag := "kerodon-4-6-8"
%%%

Kerodon [Tag 01PF](https://kerodon.net/tag/01PF)

:::definition "kerodon_4_6_8_1" (uses := "kerodon_1_1_0_6")
Kerodon Notation 4.6.8.1（[Tag 01PG](https://kerodon.net/tag/01PG)）。対応表の状態：一部。

intervalMappingSpaceは頂点列が二つ、n=1の場合の原文と同じ区間関手空間の両端固定fiberを直接構成する。任意長の列は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace`

:::

:::proposition "kerodon_4_6_8_4" (uses := "kerodon_1_1_0_6, kerodon_4_1_4_4")
Kerodon Proposition 4.6.8.4（[Tag 01PK](https://kerodon.net/tag/01PK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：二端・1 圏・dg の特例・片方向の比較と基底変換・ホモトピー圏に降りる形を照合。内ファイブレーションが誘導する有限頂点列 Hom の Kan ファイブレーション。二点間の pinched Hom の比較だけでは任意列を固定できない。

:::

:::corollary "kerodon_4_6_8_5" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Corollary 4.6.8.5（[Tag 01PL](https://kerodon.net/tag/01PL)）。対応表の状態：なし。

compositionCorrespondenceFirstは第二辺gを固定したfiberからの射。原文の二つのHomがともに変動する積への制限射と異なり、全空間のRLPを直接返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFirst_trivialKanFibration`

:::

:::corollary "kerodon_4_6_8_8"
Kerodon Corollary 4.6.8.8（[Tag 01PP](https://kerodon.net/tag/01PP)）。対応表の状態：なし。

compositionCorrespondenceは第二辺を固定した別のfiber。原文の三頂点だけを固定したHom(X₀,X₁,X₂)全体のKan性と同一視する宣言がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondence_kanComplex`

:::

:::definition "kerodon_4_6_8_9" (uses := "kerodon_1_4_0_1, kerodon_4_6_8_5")
Kerodon Construction 4.6.8.9（[Tag 01PQ](https://kerodon.net/tag/01PQ)）。対応表の状態：なし。

compositionCorrespondenceとKanMappingCompositionは特定の辺・三角形を固定した対応。原文の二つの写像空間の積からhKanでの合成射を構成する型ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondence`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanMappingComposition`

:::

:::proposition "kerodon_4_6_8_11" (uses := "kerodon_1_1_0_6, kerodon_1_1_1_4, kerodon_1_1_2_1, kerodon_1_2_5_1, kerodon_1_4_0_1")
Kerodon Proposition 4.6.8.11（[Tag 01PS](https://kerodon.net/tag/01PS)）。対応表の状態：なし。

dg nerveの右pinchedのAW合成の単位則で、原文の区間模型のhKan合成と同定されていない。対象・合成の比較なしに類似の律だけをspecialにしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomComposition_unit_left`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomComposition_unit_right`

:::

:::proposition "kerodon_4_6_8_12" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_6_8_5")
Kerodon Proposition 4.6.8.12（[Tag 01PT](https://kerodon.net/tag/01PT)）。対応表の状態：なし。

dg nerveの右pinchedのAW合成の結合則で、原文の区間模型のhKan合成と同定されていない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomComposition_assoc`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily_assoc`

:::

:::definition "kerodon_4_6_8_13" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_2_1_7_1, kerodon_4_6_1_1, kerodon_4_6_8_9, kerodon_4_6_8_11, kerodon_4_6_8_12")
Kerodon Construction 4.6.8.13（[Tag 01PV](https://kerodon.net/tag/01PV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：二端・1 圏・dg の特例・片方向の比較と基底変換・ホモトピー圏に降りる形を照合。hKan の直積モノイダル構造上の enrichment としての hC。通常の HomotopyCategory は Hom 集合に π₀ を取る。

:::

:::definition "kerodon_4_6_8_15" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_6_8_9")
Kerodon Notation 4.6.8.15（[Tag 01TP](https://kerodon.net/tag/01TP)）。対応表の状態：なし。

固定辺のcompositionCorrespondenceの構成だけは、原文のhKanの前後合成の射とそのホモトピー類だけへの依存を結論しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondence`

:::

:::proposition "kerodon_4_6_8_16" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_6_5_7")
Kerodon Proposition 4.6.8.16（[Tag 02LL](https://kerodon.net/tag/02LL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：二端・1 圏・dg の特例・片方向の比較と基底変換・ホモトピー圏に降りる形を照合。f による合成と二種 Hom の比較が作る四角のホモトピー可換性。成分上の合成や単一の比較同値にはその四角がない。

:::

:::corollary "kerodon_4_6_8_18" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_3_6_12, kerodon_4_4_3_8, kerodon_4_6_5_5, kerodon_4_6_5_10, kerodon_4_6_8_16")
Kerodon Corollary 4.6.8.18（[Tag 02R3](https://kerodon.net/tag/02R3)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：二端・1 圏・dg の特例・片方向の比較と基底変換・ホモトピー圏に降りる形を照合。coslice の Hom と合成写像の指定値でのホモトピーファイバーの比較。coslice 全体の制限は f,g を固定した空間を計算しない。

:::

:::proposition "kerodon_4_6_8_19" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_4_6_8_9")
Kerodon Proposition 4.6.8.19（[Tag 02LN](https://kerodon.net/tag/02LN)）。対応表の状態：なし。

coherentCompositionCorrespondenceは射を一つ固定した対応への写像。原文の両因子が変動する積とhKan合成の可換正方形を直接返さず、canonicalなθの規約の比較も要る。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentCompositionCorrespondence`

:::

:::corollary "kerodon_4_6_8_20" (uses := "kerodon_2_4_6_9, kerodon_4_6_8_13")
Kerodon Corollary 4.6.8.20（[Tag 02LP](https://kerodon.net/tag/02LP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：二端・1 圏・dg の特例・片方向の比較と基底変換・ホモトピー圏に降りる形を照合。locally Kan enriched category と hc nerve の Hom 比較が合成と両立。hC の通常圏同型だけでは空間レベルの合成を扱わない。

:::

:::proposition "kerodon_4_6_8_21"
Kerodon Proposition 4.6.8.21（[Tag 03E0](https://kerodon.net/tag/03E0)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：二端・1 圏・dg の特例・片方向の比較と基底変換・ホモトピー圏に降りる形を照合。dg Hom のテンソル合成と dg nerve の写像空間合成のホモトピー可換性。Dold–Kan の比較や dg nerve の定義だけでは合成四角を与えない。

:::

