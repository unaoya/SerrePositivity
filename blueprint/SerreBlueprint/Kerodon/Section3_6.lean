import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.ComparisonWithTopologicalSpaces.FiniteInternalHomContinuity

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "3.6 Comparison with Topological Spaces" =>
%%%
number := false
tag := "kerodon-3-6"
%%%

Kerodon の 3.6 節（[Tag 012Y](https://kerodon.net/tag/012Y)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::theorem "kerodon_3_6_0_1"
Kerodon Theorem 3.6.0.1（[Tag 012Z](https://kerodon.net/tag/012Z)）。対応表の状態：なし。

B6：普通の実現/特異の随伴は原文のCW型を持つ空間のホモトピー圏との同値の部品。 候補：幾何学的実現 SSet.toTop と特異単体集合 TopCat.toSSet の随伴はある。両方の弱ホモトピー同値を反転した圏の同値は未確認。

宣言：`sSetTopAdj`

:::

# 3.6.1 Digression: Finite Simplicial Sets

%%%
number := false
tag := "kerodon-3-6-1"
%%%

Kerodon [Tag 0130](https://kerodon.net/tag/0130)

:::definition "kerodon_3_6_1_1" (lean := "SSet.Finite, SSet.hasDimensionLT_of_finite, SSet.finite_of_hasDimensionLT")
Kerodon Definition 3.6.1.1（[Tag 0131](https://kerodon.net/tag/0131)）。対応表の状態：Mathlib にある。

仮定：単体集合 X（Kerodon と一致）。結論：SSet.Finite は全非退化単体の有限性で定義し、次元上限と各次数の単体の有限性を得る。逆向きは次元上限と各次元の有限性から有限和の非退化単体を数える（一致）。

:::

:::proposition "kerodon_3_6_1_7" (lean := "SSet.Finite.exists_epi_from_isCardinalPresentable, SSet.finite_of_epi, SSet.finite_of_hasDimensionLT")
Kerodon Proposition 3.6.1.7（[Tag 0137](https://kerodon.net/tag/0137)）。対応表の状態：Mathlib にある。

仮定：単体集合 X（Kerodon と一致）。結論：非退化単体が有限なら対応する有限個の標準単体の余積からエピがあり、有限な始域のエピ像は有限。各次数の有限性と次元上限からも非退化単体が有限で、本文の三条件を与える（一致）。

:::

:::proposition "kerodon_3_6_1_9" (uses := "kerodon_1_1_0_6, kerodon_1_1_0_12, kerodon_3_6_1_7, kerodon_9_2_0_2")
Kerodon Proposition 3.6.1.9（[Tag 02LG](https://kerodon.net/tag/02LG)）。対応表の状態：一部。

B6：Finite.instIsFinitelyPresentable は X.Finite から Hom(X,−) が filtered colimit を保つという原文の向きを直接与える。逆向きの有限性は含まない。

宣言：`SSet.Finite.instIsFinitelyPresentable`

:::

:::corollary "kerodon_3_6_1_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.ComparisonWithTopologicalSpaces.finiteInternalHom_preservesFilteredColimits")
Kerodon Corollary 3.6.1.10（[Tag 03X6](https://kerodon.net/tag/03X6)）。対応表の状態：本体にある。

仮定：有限単体集合 K（Kerodon と一致）。結論：内部 Hom の関手 ihom K が filtered colimit を保存する（一致）。

:::

:::proposition "kerodon_3_6_1_11" (uses := "kerodon_1_1_0_6, kerodon_3_6_1_7, kerodon_3_6_1_13")
Kerodon Proposition 3.6.1.11（[Tag 0139](https://kerodon.net/tag/0139)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。有限単体集合と CW 部分複体の API はある。実現のコンパクト部分集合を有限単体部分複体の実現に含める判定は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_6_1_12" (uses := "kerodon_1_1_0_6")
Kerodon Corollary 3.6.1.12（[Tag 013A](https://kerodon.net/tag/013A)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。単体集合の有限性と CW の有限性は別々に定義される。幾何学的実現の CompactSpace との iff は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::lemma_ "kerodon_3_6_1_13" (uses := "kerodon_1_1_0_6, kerodon_1_1_3_8, kerodon_1_1_3_9")
Kerodon Lemma 3.6.1.13（[Tag 013B](https://kerodon.net/tag/013B)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。CW の閉性公理はある。指定の各非退化単体に対する条件から実現中の部分集合 S の閉性を得る宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.6.2 Exactness of Geometric Realization

%%%
number := false
tag := "kerodon-3-6-2"
%%%

Kerodon [Tag 013C](https://kerodon.net/tag/013C)

:::theorem "kerodon_3_6_2_1" (uses := "kerodon_1_1_0_6, kerodon_3_6_2_9")
Kerodon Theorem 3.6.2.1（[Tag 013D](https://kerodon.net/tag/013D)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。SSet.toTop は左随伴で余極限を保つ。有限極限を保つ便利な位相空間の実現の型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_6_2_2" (uses := "kerodon_1_1_0_6, kerodon_3_6_1_12, kerodon_3_6_2_1")
Kerodon Corollary 3.6.2.2（[Tag 013E](https://kerodon.net/tag/013E)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。標準単体の実現の同相と、一般の位相空間の積はある。片方が有限単体集合のとき実現の積比較が同相という宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::definition "kerodon_3_6_2_6"
Kerodon Construction 3.6.2.6（[Tag 013J](https://kerodon.net/tag/013J)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。通常の実現は標準単体からの左 Kan 拡張。有限分割 S に依存する 実現 X\_S の余極限模型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::definition "kerodon_3_6_2_8"
Kerodon Notation 3.6.2.8（[Tag 013L](https://kerodon.net/tag/013L)）。対応表の状態：一部。

B6：NonemptyFinLinOrd は原文の Lin\_\{≠∅\} の対象と単調写像を直接束ねる構成成分。\[0,1\]から有限集合を除いた成分集合の有限性・順序は含まない。

宣言：`NonemptyFinLinOrd`

:::

:::proposition "kerodon_3_6_2_9" (uses := "kerodon_1_1_0_6")
Kerodon Proposition 3.6.2.9（[Tag 013M](https://kerodon.net/tag/013M)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。標準単体の通常の実現は位相的単体と同相。有限分割模型の値を線形順序集合の Hom とする全単射は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.6.3 Weak Homotopy Equivalences in Topology

%%%
number := false
tag := "kerodon-3-6-3"
%%%

Kerodon [Tag 013P](https://kerodon.net/tag/013P)

:::definition "kerodon_3_6_3_1"
Kerodon Definition 3.6.3.1（[Tag 013Q](https://kerodon.net/tag/013Q)）。対応表の状態：なし。

B6：位相のπで定義した弱同値を Sing(f) のホモトピー同値と比較する宣言がない。 候補：位相空間の weakHomotopyEquivalences は π₀ と全基点・正次数の π\_n の全単射で定義する。Sing(f) の単体的な弱ホモトピー同値性との iff は未確認。

宣言：`SerrePositivity.TopologicalHomotopy.weakHomotopyEquivalences`

:::

:::proposition "kerodon_3_6_3_8"
Kerodon Proposition 3.6.3.8（[Tag 013X](https://kerodon.net/tag/013X)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。モデル圏一般の Whitehead 型と位相空間の弱ホモトピー同値の定義はある。CW の仮定で位相的ホモトピー逆を返す定理は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_6_3_10"
Kerodon Corollary 3.6.3.10（[Tag 013Z](https://kerodon.net/tag/013Z)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。位相的な全基点の π の全単射は弱同値の定義である。それを CW のホモトピー同値へ強める Whitehead の結論は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::lemma_ "kerodon_3_6_3_11"
Kerodon Lemma 3.6.3.11（[Tag 0140](https://kerodon.net/tag/0140)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。被覆写像のホモトピー持ち上げはある。弱ホモトピー同値に沿う CW の任意写像のホモトピーまでの持ち上げは見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.6.4 The Unit Map u: X → Sing\_• (\|X\|)

%%%
number := false
tag := "kerodon-3-6-4"
%%%

Kerodon [Tag 0141](https://kerodon.net/tag/0141)

:::theorem "kerodon_3_6_4_1" (uses := "kerodon_1_1_0_6, kerodon_1_1_4_12, kerodon_3_2_8_3, kerodon_3_4_1_11, kerodon_3_4_2_9, kerodon_3_4_2_10, kerodon_3_4_2_11, kerodon_3_4_6_1, kerodon_3_6_1_11")
Kerodon Theorem 3.6.4.1（[Tag 0142](https://kerodon.net/tag/0142)）。対応表の状態：なし。

B6：随伴のunitの存在は原文のunitの弱同値性の直接の部分結論ではなく、その対象射の構成だけ。 候補：実現と特異単体集合の随伴の単位 u\_X を確認。u\_X の弱ホモトピー同値性を述べる Milnor の定理は未確認。

宣言：`sSetTopAdj`

:::

:::corollary "kerodon_3_6_4_2"
Kerodon Corollary 3.6.4.2（[Tag 0143](https://kerodon.net/tag/0143)）。対応表の状態：なし。

B6：随伴のcounitの存在はその弱同値性を結論しない。 候補：実現と特異単体集合の随伴の余単位 v\_X はある。位相空間での v\_X の弱ホモトピー同値性は未確認。

宣言：`sSetTopAdj`

:::

:::corollary "kerodon_3_6_4_3"
Kerodon Corollary 3.6.4.3（[Tag 03X7](https://kerodon.net/tag/03X7)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。実現関手と弱ホモトピー同値は別々に定義される。f の弱同値性、実現した写像の弱同値性とホモトピー同値性を結ぶ三条件は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.6.5 Comparison of Homotopy Categories

%%%
number := false
tag := "kerodon-3-6-5"
%%%

Kerodon [Tag 0147](https://kerodon.net/tag/0147)

:::definition "kerodon_3_6_5_1"
Kerodon Construction 3.6.5.1（[Tag 0148](https://kerodon.net/tag/0148)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。実現は普通の関手として定義される。Top の豊穣 Hom を特異単体集合としたときの実現の豊穣構造は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_6_5_2"
Kerodon Proposition 3.6.5.2（[Tag 0149](https://kerodon.net/tag/0149)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。実現と特異単体集合の随伴は普通の Hom の全単射。Kan 標的で二つの豊穣 Hom の比較の弱同値性は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_6_5_3"
Kerodon Proposition 3.6.5.3（[Tag 014A](https://kerodon.net/tag/014A)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。CWComplex と実現関手はある。CW 型を持つことと本文の四つの特徴づけを結ぶ宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_6_5_4"
Kerodon Corollary 3.6.5.4（[Tag 04HV](https://kerodon.net/tag/04HV)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。普通の Hom の随伴全単射はある。CW 型の位相空間に対する本文の四条件とホモトピー類での普遍性は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_6_5_6"
Kerodon Corollary 3.6.5.6（[Tag 014C](https://kerodon.net/tag/014C)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。実現の左随伴性と弱同値を反転する局所化の API はある。本文で指定する二つの関手圏を結ぶ圏同値は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.6.6 Serre Fibrations

%%%
number := false
tag := "kerodon-3-6-6"
%%%

Kerodon [Tag 021Q](https://kerodon.net/tag/021Q)

:::definition "kerodon_3_6_6_1"
Kerodon Definition 3.6.6.1（[Tag 021R](https://kerodon.net/tag/021R)）。対応表の状態：一部。

B6：IsCoveringMap.liftHomotopy と liftHomotopy\_lifts/zero は任意の位相空間 A に対し初時刻の持ち上げを直接返す。q を被覆写像に強め、A を標準単体の実現（3.6.6.8では任意 B の実現）に取ると、原文の区間持ち上げ条件が直接成立。一般の Serre fibration と相対条件全体の iff は含まない。

宣言：`IsCoveringMap.liftHomotopy`、`IsCoveringMap.liftHomotopy_lifts`、`IsCoveringMap.liftHomotopy_zero`

:::

:::proposition "kerodon_3_6_6_5"
Kerodon Proposition 3.6.6.5（[Tag 021V](https://kerodon.net/tag/021V)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。特異単体集合と単体の Kan fibration はそれぞれ定義される。位相の Serre fibration と Sing(q) の Kan fibration 性の同値は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_6_6_8"
Kerodon Corollary 3.6.6.8（[Tag 021Y](https://kerodon.net/tag/021Y)）。対応表の状態：一部。

B6：IsCoveringMap.liftHomotopy と liftHomotopy\_lifts/zero は任意の位相空間 A に対し初時刻の持ち上げを直接返す。q を被覆写像に強め、A を標準単体の実現（3.6.6.8では任意 B の実現）に取ると、原文の区間持ち上げ条件が直接成立。一般の Serre fibration と相対条件全体の iff は含まない。

宣言：`IsCoveringMap.liftHomotopy`、`IsCoveringMap.liftHomotopy_lifts`、`IsCoveringMap.liftHomotopy_zero`

:::

:::proposition "kerodon_3_6_6_10"
Kerodon Proposition 3.6.6.10（[Tag 0221](https://kerodon.net/tag/0221)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。位相の被覆写像の持ち上げと局所同相の API はある。本文の局所条件を満たす一般の q が Serre fibration になる宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_6_6_11"
Kerodon Corollary 3.6.6.11（[Tag 0224](https://kerodon.net/tag/0224)）。対応表の状態：一部。

B6：IsCoveringMap.liftHomotopy と lifts/zero は全空間が離散ファイバーの被覆である場合、任意のパラメータ（特に実現した標準単体）で初時刻を固定する区間持ち上げを直接返す。一般のファイバー束の全体は含まない。

宣言：`IsCoveringMap.liftHomotopy`、`IsCoveringMap.liftHomotopy_lifts`、`IsCoveringMap.liftHomotopy_zero`

:::

