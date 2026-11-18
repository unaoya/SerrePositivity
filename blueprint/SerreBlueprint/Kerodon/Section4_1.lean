import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.RelativeFunctor
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalVertices

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "4.1 Inner Fibrations" =>
%%%
number := false
tag := "kerodon-4-1"
%%%

Kerodon の 4.1 節（[Tag 01B8](https://kerodon.net/tag/01B8)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 4.1.1 Inner Fibrations of Simplicial Sets

%%%
number := false
tag := "kerodon-4-1-1"
%%%

Kerodon [Tag 01B9](https://kerodon.net/tag/01B9)

:::definition "kerodon_4_1_1_1" (lean := "SSet.InnerFibration, SSet.innerFibrations")
Kerodon Definition 4.1.1.1（[Tag 01BA](https://kerodon.net/tag/01BA)）。対応表の状態：Mathlib にある。

仮定：単体集合の任意の射 q:X→S（Kerodon と一致）。結論：0\<i\<n の内ホーン包含すべてに対する右持ち上げ性を InnerFibration q とする（一致）。

*定義 5.3 （fibration）*

- 名前　／　包含
- inner fibration　／　$`\Lambda^n_i\subseteq\Delta^n`（$`0<i<n`）

:::

:::proposition "kerodon_4_1_1_10" (uses := "kerodon_1_1_0_6, kerodon_1_3_4_1, kerodon_1_4_0_1")
Kerodon Proposition 4.1.1.10（[Tag 01BK](https://kerodon.net/tag/01BK)）。対応表の状態：一部。

quasicategory\_of\_innerFibration を標的 nerve に適用すると q が inner fibration⇒X が準圏という原文の向きを直接得る。逆向きの引用は薄い圏に限る。

宣言：`SSet.quasicategory_of_innerFibration`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.thinNerve_innerFibration`

:::

:::corollary "kerodon_4_1_1_11"
Kerodon Corollary 4.1.1.11（[Tag 01NP](https://kerodon.net/tag/01NP)）。対応表の状態：一部。

thinNerve\_innerFibration は標的 D が薄い圏のとき、同じ nerveMap F の内ファイブレーション性を直接与える。任意の通常圏 D は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.thinNerve_innerFibration`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.posetSubtypeInclusion_nerveMap_innerFibration`

:::

# 4.1.2 Subcategories of ∞-Categories

%%%
number := false
tag := "kerodon-4-1-2"
%%%

Kerodon [Tag 01CD](https://kerodon.net/tag/01CD)

:::definition "kerodon_4_1_2_2" (uses := "kerodon_1_4_0_1")
Kerodon Definition 4.1.2.2（[Tag 01CF](https://kerodon.net/tag/01CF)）。対応表の状態：一部。

InnerFibration を部分複体の包含 A.ι に適用した型は原文のホーン持ち上げ条件そのもの。部分圏として束ねる専用の型は含まない。

宣言：`SSet.InnerFibration`

:::

:::proposition "kerodon_4_1_2_10" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Proposition 4.1.2.10（[Tag 01CP](https://kerodon.net/tag/01CP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の部分圏・ホモトピー圏・頂点指定または全可逆辺を照合。hC の任意の部分圏と C の部分複体の全単射。全部分複体の頂点指定は射集合を動かさない。

:::

:::corollary "kerodon_4_1_2_11" (uses := "kerodon_1_4_0_1, kerodon_1_4_5_4, kerodon_4_1_2_10")
Kerodon Corollary 4.1.2.11（[Tag 01CQ](https://kerodon.net/tag/01CQ)）。対応表の状態：なし。

posetFullSubcomplexNerveLift は一つの比較写像の構成だけ。部分圏の二集合の全単射やその制限版を直接返す型ではない。

宣言：`SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetFullSubcomplexNerveLift`

:::

:::corollary "kerodon_4_1_2_12"
Kerodon Corollary 4.1.2.12（[Tag 01CR](https://kerodon.net/tag/01CR)）。対応表の状態：一部。

fullSubcomplexOnVertices は T を選んだ S の頂点間の全ての辺とする場合の部分複体を直接作る。任意に指定する T の四条件による存在と一意性全体は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory`

:::

:::definition "kerodon_4_1_2_13"
Kerodon Definition 4.1.2.13（[Tag 01CS](https://kerodon.net/tag/01CS)）。対応表の状態：一部。

頂点条件による充満部分圏と全対象・可逆辺に限る core は、原文の S,T をこの二種類に制限した構成を直接与える。任意の S,T の構成は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCore_kanComplex`

:::

:::definition "kerodon_4_1_2_15" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Definition 4.1.2.15（[Tag 01CU](https://kerodon.net/tag/01CU)）。対応表の状態：一部。

fullSubcomplexOnVertices の次数別の条件から、この構成で得た部分複体は全頂点が入る単体を全て含む。任意の部分複体についての充満性の述語・包含の inner fibration 性の一般命題は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices`

:::

:::proposition "kerodon_4_1_2_16"
Kerodon Proposition 4.1.2.16（[Tag 01CV](https://kerodon.net/tag/01CV)）。対応表の状態：一部。

fullSubcomplexOnVertices の条件は全頂点の所属であり、頂点集合が S である充満部分複体の存在を直接与える。一意性は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex`

:::

:::definition "kerodon_4_1_2_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_innerFibration")
Kerodon Definition 4.1.2.17（[Tag 01CW](https://kerodon.net/tag/01CW)）。対応表の状態：本体にある。

仮定：単体集合 X と頂点述語 P。部分圏として使う場合は Quasicategory X（Kerodon と一致）。結論：全頂点が P を満たす単体の部分複体 fullSubcomplexOnVertices X P を取り、包含は内ファイブレーション。X が ∞ 圏なら結果も ∞ 圏（一致）。

:::

# 4.1.3 Inner Anodyne Morphisms

%%%
number := false
tag := "kerodon-4-1-3"
%%%

Kerodon [Tag 01BM](https://kerodon.net/tag/01BM)

:::proposition "kerodon_4_1_3_1" (lean := "SSet.innerAnodyneExtensions_eq_llp_rlp, CategoryTheory.MorphismProperty.rlp_llp_rlp, SSet.innerFibrations")
Kerodon Proposition 4.1.3.1（[Tag 01BN](https://kerodon.net/tag/01BN)）。対応表の状態：Mathlib にある。

仮定：任意の単体集合の射 q（Kerodon と一致）。結論：innerAnodyneExtensions = (innerHornInclusions.rlp).llp と rlp\_llp\_rlp により、内アノダイン全体に対する右持ち上げ性と内ホーンに対する右持ち上げ性が同値（一致）。

:::

:::proposition "kerodon_4_1_3_2" (uses := "kerodon_1_1_0_6, kerodon_3_1_8_1")
Kerodon Proposition 4.1.3.2（[Tag 01BP](https://kerodon.net/tag/01BP)）。対応表の状態：一部。

exists\_innerAnodyne\_innerFibration\_factorization は同じ f の指定二種類の射への分解の存在を直接返す。関手性・filtered colimit 保存は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.exists_innerAnodyne_innerFibration_factorization`、`SSet.instHasSmallObjectArgumentInnerHornInclusions`

:::

:::corollary "kerodon_4_1_3_3" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Corollary 4.1.3.3（[Tag 01BQ](https://kerodon.net/tag/01BQ)）。対応表の状態：一部。

exists\_quasicategory\_resolution\_over を終対象への射に適用すると原文の inner anodyne な準圏置換の存在を直接得る。関手性・filtered colimit 保存は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.exists_quasicategory_resolution_over`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.exists_innerAnodyne_innerFibration_factorization`

:::

:::corollary "kerodon_4_1_3_4" (lean := "SSet.innerAnodyneExtensions")
Kerodon Corollary 4.1.3.4（[Tag 01BR](https://kerodon.net/tag/01BR)）。対応表の状態：Mathlib にある。

仮定：任意の単体集合の射 i（Kerodon と一致）。結論：innerAnodyneExtensions i は内ファイブレーションに対する左持ち上げ性（一致）。

:::

# 4.1.4 Exponentiation for Inner Fibrations

%%%
number := false
tag := "kerodon-4-1-4"
%%%

Kerodon [Tag 01BS](https://kerodon.net/tag/01BS)

:::proposition "kerodon_4_1_4_1"
Kerodon Proposition 4.1.4.1（[Tag 01BT](https://kerodon.net/tag/01BT)）。対応表の状態：Mathlib にある。

仮定：単体集合の単射 i:A→B と内ファイブレーション p:X→S、比較先の引き戻しの選択（Kerodon と一致）。結論：Fun(B,X)→Fun(A,X)×\_\{Fun(A,S)\}Fun(B,S) に当たる π が InnerFibration（一致）。

宣言：`SSet.innerFibration_pullbackObjObjπ`

:::

:::corollary "kerodon_4_1_4_2"
Kerodon Corollary 4.1.4.2（[Tag 01BU](https://kerodon.net/tag/01BU)）。対応表の状態：Mathlib にある。

仮定：単体集合の単射 i:A→B と Quasicategory X（Kerodon と一致）。結論：(pre i).app X すなわち Fun(B,X)→Fun(A,X) が InnerFibration（一致）。

宣言：`SSet.instInnerFibrationAppPreOfMonoOfQuasicategory`

:::

:::corollary "kerodon_4_1_4_3"
Kerodon Corollary 4.1.4.3（[Tag 01BV](https://kerodon.net/tag/01BV)）。対応表の状態：Mathlib にある。

仮定：内ファイブレーション p:E→B と任意の単体集合 X（Kerodon と一致）。結論：(ihom X).map p すなわち Fun(X,E)→Fun(X,B) が InnerFibration（一致）。

宣言：`SSet.instInnerFibrationMapIhom`

:::

:::proposition "kerodon_4_1_4_4" (uses := "kerodon_1_1_0_6, kerodon_1_5_7_5, kerodon_4_1_3_1")
Kerodon Proposition 4.1.4.4（[Tag 01BW](https://kerodon.net/tag/01BW)）。対応表の状態：一部。

trivialKanFibration\_pre\_of\_innerAnodyne は底が終対象の場合に同じ制限射の自明 Kan 性を直接与える。一般の相対評価は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.trivialKanFibration_pre_of_innerAnodyne`、`SSet.innerAnodyneExtensions_pushoutObjObjι'`

:::

:::proposition "kerodon_4_1_4_5"
Kerodon Proposition 4.1.4.5（[Tag 01BX](https://kerodon.net/tag/01BX)）。対応表の状態：一部。

trivialKanFibration\_pre\_of\_innerAnodyne と内ホーン Λ²₁ の所属から、底が終対象・X が準圏の場合の同じ制限射の自明 Kan 性を直接得る。一般の底と逆向きは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.trivialKanFibration_pre_of_innerAnodyne`、`SSet.innerAnodyneExtensions.horn_ι`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFirst_trivialKanFibration`

:::

:::proposition "kerodon_4_1_4_6" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_1_3_7, kerodon_4_1_4_1, kerodon_4_1_4_4")
Kerodon Proposition 4.1.4.6（[Tag 01GQ](https://kerodon.net/tag/01GQ)）。対応表の状態：なし。

引用は相対内部Homの比較射の内ファイブレーション性と一般の頂点ファイバーの準圏性という部品。原文の特定の延長空間との同定を型に持たず、可縮性も結論しない。

宣言：`SSet.innerFibration_pullbackObjObjπ`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.innerFibration_vertexFiber_quasicategory`

:::

:::corollary "kerodon_4_1_4_7"
Kerodon Corollary 4.1.4.7（[Tag 01GR](https://kerodon.net/tag/01GR)）。対応表の状態：なし。

一般の頂点ファイバーと特定制限射を別々に扱う部品で、Fun\_\{A/\}(B,C) という指定延長空間の構成との同定がない。自明 Kan 性だけもそのファイバーの可縮性とは別。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.innerFibration_vertexFiber_quasicategory`、`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.trivialKanFibration_pre_of_innerAnodyne`

:::

:::corollary "kerodon_4_1_4_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.relativeFunctorSpace_quasicategory_of_innerFibration")
Kerodon Corollary 4.1.4.8（[Tag 01GS](https://kerodon.net/tag/01GS)）。対応表の状態：本体にある。

仮定：内ファイブレーション q:F→B と任意の p:E→B（Kerodon と一致）。結論：p 上の写像の相対関手空間 relativeFunctorSpace q p が Quasicategory（一致）。

:::

# 4.1.5 Inner Covering Maps

%%%
number := false
tag := "kerodon-4-1-5"
%%%

Kerodon [Tag 0226](https://kerodon.net/tag/0226)

:::definition "kerodon_4_1_5_1"
Kerodon Definition 4.1.5.1（[Tag 0227](https://kerodon.net/tag/0227)）。対応表の状態：なし。

strictSegal は spine の延長一意性で、原文は相対内ホーンの一意持ち上げ。nerve の特殊形でもホーンとspineの比較がさらに必要。

宣言：`CategoryTheory.Nerve.strictSegal`

:::

:::proposition "kerodon_4_1_5_10"
Kerodon Proposition 4.1.5.10（[Tag 022G](https://kerodon.net/tag/022G)）。対応表の状態：なし。

strictSegal だけは原文の inner covering のホーン持ち上げを直接返さない。始域がnerve・底が一点に限っても比較の議論が必要。

宣言：`CategoryTheory.Nerve.strictSegal`

:::

:::corollary "kerodon_4_1_5_11"
Kerodon Corollary 4.1.5.11（[Tag 022H](https://kerodon.net/tag/022H)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏・離散ファイバー・ホーン一意性・双対と底変換を照合。各 Δⁿ への底変換の nerve 表示による一意内ホーン充填の判定。引き戻しの補題は解の存在のみ。

:::

