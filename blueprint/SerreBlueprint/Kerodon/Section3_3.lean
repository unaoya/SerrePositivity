import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.SimplicialSet.Subdivision
import Mathlib.Order.NonemptyFiniteChains
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinity
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityAnodyne
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityFibrations
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityKan
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityLocalization
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExUnit
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExUnitAnodyne
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.FiniteChainGreatest
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionAnodyne
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionLastVertexMap
import SerrePositivity.KST.Comparison.ArbitraryBasePullback
import SerrePositivity.KST.Comparison.LocalizedHomotopyComparison
import SerrePositivity.KST.Fibration.WeakHomotopyAnodyneComparison

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "3.3 The Ex^∞ Functor" =>
%%%
number := false
tag := "kerodon-3-3"
%%%

Kerodon の 3.3 節（[Tag 00XF](https://kerodon.net/tag/00XF)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::theorem "kerodon_3_3_0_1"
Kerodon Theorem 3.3.0.1（[Tag 00XG](https://kerodon.net/tag/00XG)）。対応表の状態：一部。

B6：exInfinity の自然な単位・Kan 性・anodyne 性・Kan fibration 保存で、同じ置換正方形の (a),(b),(c) を直接与える。任意の指定ファイバーの比較がホモトピー同値という (d) は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_map_rlp`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit_anodyne`、`SerrePositivity.KST.Comparison.isHomotopyPullback_exInfinity_iff`

:::

# 3.3.1 Digression: Braced Simplicial Sets

%%%
number := false
tag := "kerodon-3-3-1"
%%%

Kerodon [Tag 00XT](https://kerodon.net/tag/00XT)

:::definition "kerodon_3_3_1_1"
Kerodon Definition 3.3.1.1（[Tag 00XU](https://kerodon.net/tag/00XU)）。対応表の状態：一部。

B6：nonDegenerate\_δ は Nonsingular X の非退化単体の各面も非退化と直接述べるので、原文の braced 条件を返す。単体の写像自体が Mono という強い仮定に限る。

宣言：`SSet.nonDegenerate_δ`

:::

:::definition "kerodon_3_3_1_4"
Kerodon Notation 3.3.1.4（[Tag 00XX](https://kerodon.net/tag/00XX)）。対応表の状態：一部。

B6：nonDegenerate は任意 X の原文の次数別部分集合を直接与える。nonDegenerate\_δ は Nonsingular の追加仮定で面閉性を返す。braced 一般の半単体集合の束ねた構造は含まない。

宣言：`SSet.nonDegenerate`、`SSet.nonDegenerate_δ`

:::

:::proposition "kerodon_3_3_1_5" (uses := "kerodon_1_1_0_6, kerodon_1_1_3_8")
Kerodon Proposition 3.3.1.5（[Tag 00XY](https://kerodon.net/tag/00XY)）。対応表の状態：なし。

B6：非退化面の余極限表示は半単体写像からの延長全単射と同じ宣言ではなく、原文との比較が要る。 候補：Nonsingular の X は非退化単体の順序圏の標準単体の余極限。braced 一般の半単体写像がただ一つの単体写像へ延長する形は確認できない。

宣言：`SSet.isColimitCoconeN'`

:::

:::definition "kerodon_3_3_1_6" (uses := "kerodon_1_1_0_6")
Kerodon Construction 3.3.1.6（[Tag 00XZ](https://kerodon.net/tag/00XZ)）。対応表の状態：なし。

B6：既存単体集合の fat realization の定義で、原文の半単体集合の全射/単射分解による作用との同定は引用の型にない。 候補：freeDegeneracies は単体集合の次数データを離散行から fat realization する。任意の半単体集合 S を直接受け取る自由退化関手は未確認。

宣言：`SerrePositivity.KST.Comparison.freeDegeneracies`

:::

:::proposition "kerodon_3_3_1_7" (uses := "kerodon_1_1_0_6, kerodon_3_3_1_6")
Kerodon Proposition 3.3.1.7（[Tag 00Y0](https://kerodon.net/tag/00Y0)）。対応表の状態：なし。

B6：freeDegeneracies と augmentation だけは、原文の η の単射性・braced 性・非退化像のいずれも結論しない。 候補：freeDegeneracies とその augmentation は既存の単体集合を受け取る。任意の半単体集合 S からの次数ごとの包含とその単射性、非退化像の主張は未確認。

宣言：`SerrePositivity.KST.Comparison.freeDegeneracies`、`SerrePositivity.KST.Comparison.freeDegeneraciesAugmentation`

:::

:::corollary "kerodon_3_3_1_8"
Kerodon Corollary 3.3.1.8（[Tag 00Y1](https://kerodon.net/tag/00Y1)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。SemiSimplexCategory は単射な単体圏の射を扱う添字圏。braced な単体集合と半単体集合の二つの圏の同値は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_3_1_9" (uses := "kerodon_1_1_0_6, kerodon_3_3_1_5, kerodon_3_3_1_7")
Kerodon Corollary 3.3.1.9（[Tag 00Y2](https://kerodon.net/tag/00Y2)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。freeDegeneraciesAugmentation は既存の単体集合を終域に取る。半単体集合 S からの任意の半単体写像を自由退化 S⁺ へ一意に延長する型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_3_1_10"
Kerodon Corollary 3.3.1.10（[Tag 00Y3](https://kerodon.net/tag/00Y3)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。SemiSimplexCategory の単体圏への包含と、単体集合の freeDegeneracies は別々にある。半単体集合への忘却の左随伴を与える宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_3_1_11" (uses := "kerodon_1_1_0_6, kerodon_3_3_1_5, kerodon_3_3_1_9")
Kerodon Corollary 3.3.1.11（[Tag 00Y4](https://kerodon.net/tag/00Y4)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Nonsingular の非退化単体での余極限表示はある。braced な X で非退化半単体集合への自由退化を施したものが X に同型という型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.3.2 The Subdivision of a Simplex

%%%
number := false
tag := "kerodon-3-3-2"
%%%

Kerodon [Tag 00XH](https://kerodon.net/tag/00XH)

:::definition "kerodon_3_3_2_1" (lean := "PartialOrder.NonemptyFiniteChains, PartOrd.nonemptyFiniteChainsFunctor")
Kerodon Notation 3.3.2.1（[Tag 00XJ](https://kerodon.net/tag/00XJ)）。対応表の状態：Mathlib にある。

仮定：半順序集合 P（Kerodon と一致）。結論：NonemptyFiniteChains P は P の非空有限全順序部分集合で、包含により順序づける。単調写像は像の鎖を与える（一致）。

:::

:::proposition "kerodon_3_3_2_3"
Kerodon Proposition 3.3.2.3（[Tag 00XL](https://kerodon.net/tag/00XL)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。標準単体の細分を鎖の nerve として作る宣言はある。重心に各頂点を送り各小単体でアフィンとなる幾何学的実現の同相は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::definition "kerodon_3_3_2_5" (lean := "SSet.ex, SimplexCategory.sd")
Kerodon Construction 3.3.2.5（[Tag 00XN](https://kerodon.net/tag/00XN)）。対応表の状態：Mathlib にある。

仮定：任意の単体集合 X（Kerodon と一致）。結論：SSet.ex の n 単体は SimplexCategory.sd.obj \[n\] から X への射で、sd.obj \[n\] は非空部分集合の鎖の nerve。単体圏の写像には細分写像で前合成する（一致）。

:::

:::definition "kerodon_3_3_2_10" (uses := "kerodon_1_1_0_6, kerodon_3_3_1_5, kerodon_3_3_2_5")
Kerodon Variant 3.3.2.10（[Tag 0102](https://kerodon.net/tag/0102)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。SSet.ex は Δᵒᵖ 全体の単体集合の関手。半単体集合への適用として Ex の次数と面の構成を与える宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.3.3 The Subdivision of a Simplicial Set

%%%
number := false
tag := "kerodon-3-3-3"
%%%

Kerodon [Tag 00Y5](https://kerodon.net/tag/00Y5)

:::definition "kerodon_3_3_3_1" (uses := "kerodon_1_1_0_6, kerodon_3_3_2_5")
Kerodon Definition 3.3.3.1（[Tag 00Y6](https://kerodon.net/tag/00Y6)）。対応表の状態：なし。

B6：sdExAdjunction は選ばれた unit の普遍性で、任意の u を判定する原文の述語との比較を欠く。 候補：sd ⊣ ex が表現対象と普遍写像を与える。原文の任意の u : X→Ex(Y) がこの普遍性を満たすという条件を独立の述語にはしていない。

宣言：`SSet.sdExAdjunction`

:::

:::definition "kerodon_3_3_3_2" (lean := "SSet.sd")
Kerodon Notation 3.3.3.2（[Tag 00Y7](https://kerodon.net/tag/00Y7)）。対応表の状態：Mathlib にある。

仮定：単体集合 X（Kerodon と一致）。結論：左 Kan 拡張で得る SSet.sd.obj X は Ex への射の関手を表現する選択済みの細分対象（一致）。

:::

:::proposition "kerodon_3_3_3_3" (lean := "SSet.sd, SSet.sdExAdjunction")
Kerodon Proposition 3.3.3.3（[Tag 00Y8](https://kerodon.net/tag/00Y8)）。対応表の状態：Mathlib にある。

仮定：任意の単体集合 X（Kerodon と一致）。結論：sd X と随伴の単位 X→Ex(sd X) が存在し、任意の Y に対し Hom(sd X,Y) ≃ Hom(X,Ex Y) を与える（一致）。

:::

:::corollary "kerodon_3_3_3_4" (lean := "SSet.sdExAdjunction")
Kerodon Corollary 3.3.3.4（[Tag 00Y9](https://kerodon.net/tag/00Y9)）。対応表の状態：Mathlib にある。

仮定：単体集合の圏（Kerodon と一致）。結論：sdExAdjunction は sd ⊣ ex の随伴データを返し、Ex が右随伴である（一致）。

:::

:::proposition "kerodon_3_3_3_7"
Kerodon Proposition 3.3.3.7（[Tag 00YB](https://kerodon.net/tag/00YB)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。標準単体やホーンの組合せ的な細分の比較はある。braced X について実現した 幾何学的実現 Sd X と X の標準同相は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::definition "kerodon_3_3_3_10"
Kerodon Construction 3.3.3.10（[Tag 04HN](https://kerodon.net/tag/04HN)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Subdivision の標準単体同型と、順序集合・ホーンでの比較はある。任意 X の単体の圏 Δ\_X の nerve から Sd X への比較写像 ψ\_X は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::definition "kerodon_3_3_3_12"
Kerodon Notation 3.3.3.12（[Tag 00YE](https://kerodon.net/tag/00YE)）。対応表の状態：なし。

B6：N は部分単体関係の順序集合で、原文の非退化単体の充満部分圏の全ての単体圏の射を保たない。 候補：X.N は非退化単体を部分単体関係で順序づける。原文の Δ\_X の充満部分圏であり得る複数の異なる単体圏の射まで保持しない。

宣言：`SSet.N`

:::

:::proposition "kerodon_3_3_3_17"
Kerodon Proposition 3.3.3.17（[Tag 00YL](https://kerodon.net/tag/00YL)）。対応表の状態：なし。

B6：HornFacePoset との比較は原文の非退化単体の充満部分圏を使う特定 ψ\_X と比較されていない。 候補：ホーンの細分から非退化面の順序集合の nerve への比較は同型。任意の braced X での原文の ψ\_X の同型性は確認できない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionComparison_isIso`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionComparison`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionNerveChains`

:::

:::lemma_ "kerodon_3_3_3_19"
Kerodon Lemma 3.3.3.19（[Tag 00YQ](https://kerodon.net/tag/00YQ)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Nonsingular の非退化面の表示はある。原文の半単体集合を対象とする関手についての充満忠実性の主張は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::definition "kerodon_3_3_3_20"
Kerodon Variant 3.3.3.20（[Tag 04HQ](https://kerodon.net/tag/04HQ)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。非退化単体の順序型と面写像の計算はある。半単体集合全体を対象とした変形版の関手と射の同定は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.3.4 The Last Vertex Map

%%%
number := false
tag := "kerodon-3-3-4"
%%%

Kerodon [Tag 00YR](https://kerodon.net/tag/00YR)

:::definition "kerodon_3_3_4_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainGreatest")
Kerodon Notation 3.3.4.1（[Tag 00YS](https://kerodon.net/tag/00YS)）。対応表の状態：本体にある。

仮定：半順序集合 P と非空有限鎖（Kerodon と一致）。結論：有限鎖の最大元を返し、鎖の包含順に単調な写像 finiteChainGreatest : NonemptyFiniteChains P →o P（一致）。

:::

:::definition "kerodon_3_3_4_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionLastVertexMap, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exUnitAt")
Kerodon Construction 3.3.4.3（[Tag 00YU](https://kerodon.net/tag/00YU)）。対応表の状態：本体にある。

仮定：任意の単体集合 X（Kerodon と一致）。結論：exUnitAt X は n 単体 σ に最大元写像を前合成したものを割り当て、subdivisionLastVertexMap.app X はその sd ⊣ ex の Hom 同値による逆像として一意に定める（一致）。

:::

:::proposition "kerodon_3_3_4_8"
Kerodon Proposition 3.3.4.8（[Tag 00YZ](https://kerodon.net/tag/00YZ)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。subdivisionLastVertexMap は λ\_X を定めるが、弱同値の定理 exUnitAt\_anodyne は随伴先の ρ\_X の性質。元の λ\_X の弱ホモトピー同値性を結論する宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.3.5 Comparison of X with Ex(X)

%%%
number := false
tag := "kerodon-3-3-5"
%%%

Kerodon [Tag 00Z1](https://kerodon.net/tag/00Z1)

:::theorem "kerodon_3_3_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exUnitAt_anodyne, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exUnitAt")
Kerodon Theorem 3.3.5.1（[Tag 00Z2](https://kerodon.net/tag/00Z2)）。対応表の状態：本体にある。

仮定：任意の単体集合 X（Kerodon と一致）。結論：exUnitAt X は anodyne（Lean が強い：全 Kan 標的で弱同値を検査できるほか、Kan fibration への左持ち上げ性を持つ）。

:::

:::corollary "kerodon_3_3_5_2" (uses := "kerodon_1_1_0_6, kerodon_3_3_5_1")
Kerodon Corollary 3.3.5.2（[Tag 0103](https://kerodon.net/tag/0103)）。対応表の状態：なし。

B6：Ex∞ についての iff は一段の Ex と異なる関手。exUnitAt\_anodyne は自然性による弱同値判定のための材料。 候補：Ex∞ 版の anodyne 局所化同型の同値と、単一の Ex の単位の anodyne 性を確認。単一の Ex による弱ホモトピー同値の両方向を述べる宣言は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_map_localized_isIso_iff`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exUnitAt_anodyne`

:::

:::proposition "kerodon_3_3_5_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivision_map_anodyne")
Kerodon Proposition 3.3.5.3（[Tag 00Z3](https://kerodon.net/tag/00Z3)）。対応表の状態：本体にある。

仮定：任意の anodyne 射 f : X ⟶ Y（Kerodon と一致）。結論：細分関手の SSet.sd.map f も anodyne（一致）。

:::

:::corollary "kerodon_3_3_5_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ex_map_rlp, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exIterate_map_rlp")
Kerodon Corollary 3.3.5.4（[Tag 00Z4](https://kerodon.net/tag/00Z4)）。対応表の状態：本体にある。

仮定：単体集合の射 p が J.rlp、すなわち Kan fibration（Kerodon と一致）。結論：Ex.map p も全ホーンに対する RLP を持つ（一致）。

:::

:::corollary "kerodon_3_3_5_5"
Kerodon Corollary 3.3.5.5（[Tag 00Z5](https://kerodon.net/tag/00Z5)）。対応表の状態：なし。

B6：ex\_map\_rlp は Ex.map p の J.rlp を返す。Ex の終対象保存との比較を使って終射に移す議論が必要で、KanComplex(Ex X) 自体は引用の型にない。 候補：ex\_map\_rlp は射の全ホーン RLP を保存する。終射に適用できるが、引用は Ex X の KanComplex インスタンスまたはその終射についての型を直接返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ex_map_rlp`

:::

:::proposition "kerodon_3_3_5_6"
Kerodon Proposition 3.3.5.6（[Tag 00Z6](https://kerodon.net/tag/00Z6)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。subdivisionHomEquiv\_app\_down は随伴の各単体の像を計算する。Kan 標的への二写像がホモトピックであることをこの転置が保存・反映する宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_3_5_7"
Kerodon Proposition 3.3.5.7（[Tag 00Z7](https://kerodon.net/tag/00Z7)）。対応表の状態：なし。

B6：kanHomotopyEquivOfLocalizedIso の結論は π の台の同値で、名から想像されるホモトピー逆ではない。ρ\_Y の anodyne 性だけは原文のホモトピー同値性の部品。 候補：ρ\_Y の anodyne 性と、両端が Kan のときの局所化同型のホモトピー逆がある。ρ\_Y に対する一体の命題と Ex Y の Kan 性は引用にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exUnitAt_anodyne`、`SerrePositivity.KST.Comparison.kanHomotopyEquivOfLocalizedIso`

:::

:::proposition "kerodon_3_3_5_8"
Kerodon Proposition 3.3.5.8（[Tag 00Z8](https://kerodon.net/tag/00Z8)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。exUnitAt\_naturality は射に関する自然性。ρ\_(Ex X) と Ex(ρ\_X) の間の円柱ホモトピーの存在は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::lemma_ "kerodon_3_3_5_9"
Kerodon Lemma 3.3.5.9（[Tag 00Z9](https://kerodon.net/tag/00Z9)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。orderSubtypeNerve\_anodyne は部分順序の指定点を通る上向きの変形を要求する。上面一枚を欠く立方体の補題もあるが、最大頂点だけを除いた部分順序集合の nerve の指定包含とは異なる。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.3.6 The Ex\^∞ Functor

%%%
number := false
tag := "kerodon-3-3-6"
%%%

Kerodon [Tag 00ZA](https://kerodon.net/tag/00ZA)

:::definition "kerodon_3_3_6_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit")
Kerodon Construction 3.3.6.1（[Tag 00ZB](https://kerodon.net/tag/00ZB)）。対応表の状態：本体にある。

仮定：任意の単体集合 X（Kerodon と一致）。結論：exIterate の n 段の値を ρ で結んだ列の余極限を exInfinity とし、零段からの射が exInfinityUnit（一致）。

:::

:::proposition "kerodon_3_3_6_2" (uses := "kerodon_1_1_0_6")
Kerodon Proposition 3.3.6.2（[Tag 00ZC](https://kerodon.net/tag/00ZC)）。対応表の状態：一部。

B6：exInfinityUnit\_anodyne と anodyne\_mono から同じ ρ\_X\^∞ の Mono を直接得る。零単体での全射性は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit_anodyne`、`SerrePositivity.KST.Spectra.anodyne_mono`

:::

:::proposition "kerodon_3_3_6_4" (uses := "kerodon_1_1_0_6")
Kerodon Proposition 3.3.6.4（[Tag 00ZE](https://kerodon.net/tag/00ZE)）。対応表の状態：一部。

B6：exInfinity\_preservesFiniteLimits は原文の二つの保存性のうち有限極限保存を直接述べる。入力の filtered colimit 保存を、有限始域からの段階因子化と取り違えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_preservesFiniteLimits`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_finite_factorization`

:::

:::corollary "kerodon_3_3_6_5" (uses := "kerodon_1_1_0_6, kerodon_3_3_6_2, kerodon_3_3_6_4")
Kerodon Corollary 3.3.6.5（[Tag 00ZF](https://kerodon.net/tag/00ZF)）。対応表の状態：なし。

B6：有限極限保存の一般instanceだけで、原文の指定した頂点を通じる比較写像の同型性は述べていない。Ex∞(1)と1を同定し自然な単位との整合を確かめる比較が必要。 候補：Ex∞ の有限極限保存はファイバーの引き戻しに適用できる。原文の Ex∞(X\_s)→Ex∞(X)\_s を同型とし、頂点と終対象の同定を明示する専用の型は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_preservesFiniteLimits`

:::

:::proposition "kerodon_3_3_6_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_map_rlp")
Kerodon Proposition 3.3.6.6（[Tag 00ZG](https://kerodon.net/tag/00ZG)）。対応表の状態：本体にある。

仮定：単体集合の射 p が J.rlp、すなわち Kan fibration（Kerodon と一致）。結論：Ex∞.map p も J.rlp（一致）。

:::

:::proposition "kerodon_3_3_6_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit_anodyne")
Kerodon Proposition 3.3.6.7（[Tag 00ZH](https://kerodon.net/tag/00ZH)）。対応表の状態：本体にある。

仮定：任意の単体集合 X（Kerodon と一致）。結論：exInfinityUnit.app X は anodyne（Lean が強い：弱同値性に加え Kan fibration に対する左持ち上げ性）。元の Ex∞ の Kan 性への引用を単位の宣言に訂正。

:::

:::corollary "kerodon_3_3_6_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_map_localized_isIso_iff, SerrePositivity.KST.Fibration.weakHomotopyEquivalence_anodyneQ_isIso")
Kerodon Corollary 3.3.6.8（[Tag 00ZJ](https://kerodon.net/tag/00ZJ)）。対応表の状態：本体にある。

仮定：任意の単体集合の射 f（Kerodon と一致）。結論：f が anodyne 局所化で同型となることと Ex∞.map f が同型となることが同値。両方向の弱ホモトピー同値との比較を加えると原文の述語で同じ同値を得る（一致）。

:::

:::proposition "kerodon_3_3_6_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex")
Kerodon Proposition 3.3.6.9（[Tag 00ZK](https://kerodon.net/tag/00ZK)）。対応表の状態：本体にある。

仮定：任意の単体集合 X（Kerodon と一致）。結論：Ex∞.obj X が KanComplex（一致）。元の単位の anodyne 性への引用を KanComplex のインスタンスに訂正。

:::

:::corollary "kerodon_3_3_6_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit_localized_isIso, SerrePositivity.KST.Comparison.kanHomotopyEquivOfLocalizedIso, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex")
Kerodon Corollary 3.3.6.10（[Tag 00ZL](https://kerodon.net/tag/00ZL)）。対応表の状態：本体にある。

仮定：Kan 複体 X（Kerodon と一致。Ex∞ X の Kan 性はインスタンスで供給）。結論：exInfinityUnit.app X の局所化同型と、Kan 複体間のその射の実ホモトピー逆の構成を確認（一致）。

:::

# 3.3.7 Application: Characterizations of Weak Homotopy Equivalences

%%%
number := false
tag := "kerodon-3-3-7"
%%%

Kerodon [Tag 00ZM](https://kerodon.net/tag/00ZM)

:::proposition "kerodon_3_3_7_1" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_2_8_1, kerodon_3_3_6_5, kerodon_3_3_6_6, kerodon_3_3_6_8, kerodon_3_3_6_9")
Kerodon Proposition 3.3.7.1（[Tag 00ZN](https://kerodon.net/tag/00ZN)）。対応表の状態：なし。

B6：left fibration と準圏同値の判定は一般の Kan fibration の弱同値判定と異なる。引き戻し局所化同型は特定の正方形だけの性質。 候補：left fibration のファイバー比較は準圏の底を要求し、底の弱同値を伴う一般の Kan fibration の正方形の同値条件ではない。基底変換の引き戻しが弱同値になる場合は確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_isQCatEquivalence_iff_fibers`、`SerrePositivity.KST.Comparison.pullback_localized_isIso`

:::

:::corollary "kerodon_3_3_7_4" (lean := "SerrePositivity.KST.Comparison.pullback_localized_isIso, SerrePositivity.KST.Fibration.weakHomotopyEquivalence_anodyneQ_isIso")
Kerodon Corollary 3.3.7.4（[Tag 0104](https://kerodon.net/tag/0104)）。対応表の状態：本体にある。

仮定：任意の底 S 上の Kan fibration p と弱ホモトピー同値 T→S（Kerodon と一致。Lean の型は全ホーン RLP と anodyne 局所化での同型で記述）。結論：選んだ引き戻し T×\_S X→X の局所化像も同型で、同じ射が弱ホモトピー同値（一致）。

:::

:::corollary "kerodon_3_3_7_5" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1")
Kerodon Corollary 3.3.7.5（[Tag 0105](https://kerodon.net/tag/0105)）。対応表の状態：一部。

B6：leftFibration\_isQCatEquivalence\_iff\_fibers は同じ三角形とファイバー射の iff。E,F,B を Kan 複体に強めると Kan fibration は left fibration で、引用の isWeakHomotopyEquivalence\_iff\_isQCatEquivalence と isSimplicialHomotopyEquivalence への比較をそのまま適用できる。任意の底 S については含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_isQCatEquivalence_iff_fibers`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_iff_isQCatEquivalence`

:::

:::proposition "kerodon_3_3_7_6" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_1_7_10, kerodon_3_1_7_13, kerodon_3_3_7_5, kerodon_3_5_2_1")
Kerodon Proposition 3.3.7.6（[Tag 00ZP](https://kerodon.net/tag/00ZP)）。対応表の状態：一部。

B6：rightFibration\_trivialKanFibration\_of\_contractible\_fibers は Kan fibration（特に right fibration）に全ファイバーの可縮性を仮定し、同じ f の自明 Kan 性を返す。(4)⇒(1)の向き。一般の弱同値からの逆方向は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.trivialKanFibration_of_fibration_of_simplicialHomotopyEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_trivialKanFibration_of_contractible_fibers`、`SerrePositivity.KST.SConstruction.map_isIso_of_trivialKanFibration`

:::

:::corollary "kerodon_3_3_7_7" (uses := "kerodon_1_1_0_6, kerodon_3_1_7_14, kerodon_3_1_8_1, kerodon_3_3_7_6")
Kerodon Corollary 3.3.7.7（[Tag 00ZQ](https://kerodon.net/tag/00ZQ)）。対応表の状態：一部。

B6：anodyne\_mono は条件(1)から条件(2)の単射性成分を直接返す。一般 ModelCategory SSet を要求する別宣言は根拠にせず、モデル圏のinstanceなしで逆向きや仮定なしの一致を主張しない。

宣言：`SerrePositivity.KST.Spectra.anodyne_mono`、`SerrePositivity.SimplicialModel.simplicial_anodyne_eq_trivialCofibrations`

:::

# 3.3.8 Application: Extending Kan Fibrations

%%%
number := false
tag := "kerodon-3-3-8"
%%%

Kerodon [Tag 00ZR](https://kerodon.net/tag/00ZR)

:::theorem "kerodon_3_3_8_1"
Kerodon Theorem 3.3.8.1（[Tag 00ZS](https://kerodon.net/tag/00ZS)）。対応表の状態：一部。

B6：trivialFibrationExtension は同じ q を p に沿う引き戻しで延長し、延長先にも全単射 RLP を返す。原文の Kan fibration を自明 Kan fibration に強める場合。p は任意の単射なので anodyne も含む。

宣言：`SerrePositivity.KST.Comparison.trivialFibrationExtension`

:::

:::lemma_ "kerodon_3_3_8_4"
Kerodon Lemma 3.3.8.4（[Tag 00ZV](https://kerodon.net/tag/00ZV)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。自明 Kan fibration の延長や相対持ち上げの宣言はある。指定の二部分集合とファイバー同値を仮定し、制限が X を通る単体だけを残した Y'→T の Kan fibration 性は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

