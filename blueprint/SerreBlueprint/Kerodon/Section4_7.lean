import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.EquivalenceTerminal
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialTerminalWeakContractibility
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialVerticesContractible
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IntervalMappingContractible
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalMappingSpace
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalTransport
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalVertices

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "4.7 Truncated Objects and Higher Homotopy Categories" =>
%%%
number := false
tag := "kerodon-4-7"
%%%

Kerodon の 4.7 節（[Tag 05EA](https://kerodon.net/tag/05EA)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 4.7.1 Truncated Objects

%%%
number := false
tag := "kerodon-4-7-1"
%%%

Kerodon [Tag 05EB](https://kerodon.net/tag/05EB)

:::definition "kerodon_4_7_1_1" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1")
Kerodon Definition 4.7.1.1（[Tag 05EC](https://kerodon.net/tag/05EC)）。対応表の状態：一部。

n=−2では全ての入射Homの境界充填による可縮性を要求する。terminalとpinchedHom可縮性のiffを、区間比較の圏同値と可縮Kan性の保存/反映で移せば、同じ入射intervalMappingSpaceの可縮性という条件を直接得る。任意nと離散空間の一般の述語は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_pinchedHom_isContractibleKan`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Is0TruncatedSpace`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_postOfEq`

:::

:::definition "kerodon_4_7_1_4"
Kerodon Variant 4.7.1.4（[Tag 06Y3](https://kerodon.net/tag/06Y3)）。対応表の状態：一部。

isInitialVertex\_iff\_intervalMappingSpace\_isContractibleKan はn=−2で原文の全ての出射Homの可縮Kan性の条件を直接表す。任意の整数nのcotruncated条件は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_iff_intervalMappingSpace_isContractibleKan`

:::

:::proposition "kerodon_4_7_1_16" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_3_6_1, kerodon_4_4_1_11, kerodon_4_4_5_8")
Kerodon Proposition 4.7.1.16（[Tag 05ET](https://kerodon.net/tag/05ET)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝-2 の端対象・空間の 0 切断・双対・境界を照合。n+3 以上の単体に対する指定端点付き境界条件と対象 n-truncation の同値。coskeleton の一意延長は指定端点の存在条件ではない。

:::

# 4.7.2 Truncated Morphisms

%%%
number := false
tag := "kerodon-4-7-2"
%%%

Kerodon [Tag 05F8](https://kerodon.net/tag/05F8)

:::definition "kerodon_4_7_2_1" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1")
Kerodon Definition 4.7.2.1（[Tag 05F9](https://kerodon.net/tag/05F9)）。対応表の状態：なし。

通常圏のMonoはHom集合の合成単射性。原文のnerveの区間写像空間への合成作用と(n=−1の)truncationの比較を欠く。

宣言：`CategoryTheory.Mono`

:::

:::proposition "kerodon_4_7_2_7" (uses := "kerodon_1_4_0_1, kerodon_3_5_9_12, kerodon_4_6_8_18, kerodon_4_7_1_1, kerodon_4_7_2_1")
Kerodon Proposition 4.7.2.7（[Tag 05FF](https://kerodon.net/tag/05FF)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝-2 の同値・n＝-1 の単射・通常圏の mono の合成・取消し・ファイバー・左右ホーンを照合。射 f の n-truncation と slice の対象としての n-truncation の同値。slice の構成と制限の型だけではこの二つの述語を結ばない。

:::

:::corollary "kerodon_4_7_2_8"
Kerodon Corollary 4.7.2.8（[Tag 05FG](https://kerodon.net/tag/05FG)）。対応表の状態：なし。

可逆辺の保存/反映の型は、原文の各写像空間への合成作用のn-truncationの保存/反映ではない。n=−2への特殊化にもこの特徴づけとの比較が必要。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge.map`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful.reflects_isInvertibleEdge`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsQCatEquivalence.isFullyFaithful`

:::

:::corollary "kerodon_4_7_2_9"
Kerodon Corollary 4.7.2.9（[Tag 05FJ](https://kerodon.net/tag/05FJ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝-2 の同値・n＝-1 の単射・通常圏の mono の合成・取消し・ファイバー・左右ホーンを照合。右ファイブレーションに沿う truncated 射の保存と反映。右ファイブレーションの pullback 安定性は射の切断度を比較しない。

:::

:::corollary "kerodon_4_7_2_10"
Kerodon Corollary 4.7.2.10（[Tag 05FL](https://kerodon.net/tag/05FL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝-2 の同値・n＝-1 の単射・通常圏の mono の合成・取消し・ファイバー・左右ホーンを照合。指定外ホーンに沿う持ち上げと f の n-truncation の同値。右ファイブレーションはすべての右ホーンに対する別の性質。

:::

:::proposition "kerodon_4_7_2_11"
Kerodon Proposition 4.7.2.11（[Tag 05FM](https://kerodon.net/tag/05FM)）。対応表の状態：なし。

通常圏の終対象へのmonoからsubterminalという定理であり、原文のnerveの写像空間での切断条件との同定がない。

宣言：`CategoryTheory.isSubterminal_of_mono_isTerminal_from`

:::

:::corollary "kerodon_4_7_2_12"
Kerodon Corollary 4.7.2.12（[Tag 05FN](https://kerodon.net/tag/05FN)）。対応表の状態：なし。

通常圏でのmonoとsubterminalの片側で、原文のn-truncated対象・射の定義への比較がない。

宣言：`CategoryTheory.isSubterminal_of_mono_isTerminal_from`

:::

:::corollary "kerodon_4_7_2_14"
Kerodon Corollary 4.7.2.14（[Tag 05FQ](https://kerodon.net/tag/05FQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝-2 の同値・n＝-1 の単射・通常圏の mono の合成・取消し・ファイバー・左右ホーンを照合。2-単体における n-truncated な射の合成と取消し。Mono の同型・合成や内ホーン充填は任意次数の取消しを述べない。

:::

# 4.7.3 Initial and Final Objects

%%%
number := false
tag := "kerodon-4-7-3"
%%%

Kerodon [Tag 02H6](https://kerodon.net/tag/02H6)

:::definition "kerodon_4_7_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_pinchedHom_isContractibleKan, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_iff_intervalMappingSpace_isContractibleKan")
Kerodon Definition 4.7.3.1（[Tag 02H7](https://kerodon.net/tag/02H7)）。対応表の状態：本体にある。

仮定：∞ 圏 X と頂点 x（Kerodon と一致）。結論：終対象は全ての y から x への右 pinched Hom が可縮 Kan、始対象は x から全ての y への intervalMappingSpace が可縮 Kan と同値（一致）。

*定理 8.2 （始対象の写像空間による特徴づけ）*

quasicategory $`C` の頂点 $`x` について、次は同値である。

- $`x` は始対象である（定義 8.1）。

- すべての頂点 $`y` について $`\mathrm{Hom}^L_C(x,y)`（定義 7.1）は可縮である（定義 5.4）。

*定理 8.4 （終対象の写像空間による特徴づけ）*

quasicategory $`C` の頂点 $`y` について、次は同値である。

- $`y` は終対象である（定義 8.3）。

- すべての頂点 $`x` について $`\mathrm{Hom}^R_C(x,y)`（定義 7.1）は可縮である（定義 5.4）。

:::

:::proposition "kerodon_4_7_3_6"
Kerodon Example 4.7.3.6（[Tag 02HB](https://kerodon.net/tag/02HB)）。対応表の状態：なし。

coherentHomComparisonは包含順nerveの右pinchedへの射。原文の逆包含coherent nerveでの指定対象と豊穣Homへの同定を欠き、terminal判定と組み合わせる前にこの比較が要る。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_pinchedHom_isContractibleKan`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_isSimplicialHomotopyEquivalence`

:::

:::proposition "kerodon_4_7_3_8"
Kerodon Proposition 4.7.3.8（[Tag 02HE](https://kerodon.net/tag/02HE)）。対応表の状態：なし。

dgNerve\_contractingElement\_isTerminalVertexはHA余鎖符号のdg nerveについての型。原文のdg nerveの符号規約に移す比較がなく、同じ対象の(3)⇒(2)とは確認できない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.dgNerve_contractingElement_isTerminalVertex`

:::

:::proposition "kerodon_4_7_3_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.QCatEquivalence.isTerminalVertex_iff, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.QCatEquivalence.isInitialVertex_iff")
Kerodon Proposition 4.7.3.9（[Tag 02HS](https://kerodon.net/tag/02HS)）。対応表の状態：本体にある。

仮定：∞ 圏の圏同値 e:X≃Y と頂点 x（Kerodon と一致）。結論：x が始対象または終対象であることと e(x) が同じ性質を持つことは同値（一致）。

:::

:::corollary "kerodon_4_7_3_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.QCatEquivalence.map_isTerminalVertex, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.QCatEquivalence.map_isInitialVertex")
Kerodon Corollary 4.7.3.10（[Tag 02MY](https://kerodon.net/tag/02MY)）。対応表の状態：本体にある。

仮定：∞ 圏の圏同値 e:X≃Y（Kerodon と一致）。結論：始対象・終対象は e で保たれる。逆向きにも e の逆同値で同じ保存を適用して、存在を比較（一致）。

:::

:::proposition "kerodon_4_7_3_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex")
Kerodon Proposition 4.7.3.11（[Tag 06R1](https://kerodon.net/tag/06R1)）。対応表の状態：本体にある。

仮定：∞ 圏 X と頂点 x（Lean が弱い：境界充填の定義自体は任意の単体集合）。結論：IsTerminalVertex x は最終頂点 x の任意の正次元境界を充填できること（一致）。

:::

:::corollary "kerodon_4_7_3_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_iff_trivialKanFibration")
Kerodon Corollary 4.7.3.12（[Tag 06R2](https://kerodon.net/tag/06R2)）。対応表の状態：本体にある。

仮定：∞ 圏 X と頂点 x（Lean が弱い：任意の単体集合で成立）。結論：始対象⇔coslice の射影が自明 Kan ファイブレーション、終対象⇔slice の射影が自明 Kan ファイブレーション（一致）。

*定義 8.1 （始対象）*

quasicategory $`C` の頂点 $`x` が始対象であるとは、コスライスの射影 $`C_{x/}\to C`（定義 4.7）が trivial Kan fibration（定義 5.3）であることをいう。

*定義 8.3 （終対象）*

quasicategory $`C` の頂点 $`y` が終対象であるとは、スライスの射影 $`C_{/y}\to C`（定義 4.7）が trivial Kan fibration（定義 5.3）であることをいう。

:::

:::corollary "kerodon_4_7_3_13"
Kerodon Corollary 4.7.3.13（[Tag 02HJ](https://kerodon.net/tag/02HJ)）。対応表の状態：一部。

IsContractibleKan.isTerminalVertex/isInitialVertexは、原文(3)の可縮Kan複体の任意の頂点について(1),(2)を直接返す。initial/finalから可縮性へ戻す方向は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan.isTerminalVertex`、`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan.isInitialVertex`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex.isWeaklyContractible`

:::

:::corollary "kerodon_4_7_3_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertices_isContractibleKan, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertices, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.initialVertices_isContractibleKan")
Kerodon Corollary 4.7.3.14（[Tag 02HM](https://kerodon.net/tag/02HM)）。対応表の状態：本体にある。

仮定：始対象または終対象を持つ ∞ 圏 X（Lean が弱い：両可縮性補題は Quasicategory を仮定しない）。結論：始対象を頂点とする全部分複体および終対象を頂点とする全部分複体が、それぞれ該当する対象が存在すれば可縮 Kan（一致）。

:::

:::definition "kerodon_4_7_3_15"
Kerodon Notation 4.7.3.15（[Tag 02HP](https://kerodon.net/tag/02HP)）。対応表の状態：なし。

通常圏の選ばれたinitial/terminalとその記法で、原文の準圏の頂点と一意な可縮選択空間の記法への比較がない。

宣言：`CategoryTheory.Limits.initialIsoIsInitial`、`CategoryTheory.Limits.terminal`

:::

:::corollary "kerodon_4_7_3_16" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_7_3_14")
Kerodon Corollary 4.7.3.16（[Tag 02HN](https://kerodon.net/tag/02HN)）。対応表の状態：一部。

isTerminalVertex\_iff\_of\_vertexIsoは、Xが終対象でYがXに同型ならYも終対象という原文の向きを直接返す。二つの終対象から頂点同型を作る逆方向は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_of_vertexIso`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex.nonempty_split`

:::

:::corollary "kerodon_4_7_3_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex.isTerminalHo, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_of_isTerminalHo")
Kerodon Corollary 4.7.3.17（[Tag 02HQ](https://kerodon.net/tag/02HQ)）。対応表の状態：本体にある。

仮定：Quasicategory X と頂点 x。逆向きは既知の終対象を仮定（Kerodon と一致）。結論：終対象は hX でも終対象。hX の終対象は既知の終対象があれば X でも終対象（一致）。

:::

:::corollary "kerodon_4_7_3_19" (uses := "kerodon_1_4_0_1, kerodon_4_7_3_12")
Kerodon Corollary 4.7.3.19（[Tag 02HG](https://kerodon.net/tag/02HG)）。対応表の状態：一部。

IsTerminalVertex.exists\_sliceLiftはK→C\_/Xという錐を直接与え、sliceのjoin転置で同じ図式f上のcosliceの頂点となり頂点Xへの射影を保つ。原文(1)の存在成分のみで、その頂点のcosliceでの終対象性は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex.exists_sliceLift`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex.exists_pointJoinBoundary_extension`

:::

:::proposition "kerodon_4_7_3_20" (uses := "kerodon_1_4_0_1, kerodon_1_4_6_1, kerodon_4_6_4_20, kerodon_4_7_2_7, kerodon_4_7_3_9")
Kerodon Proposition 4.7.3.20（[Tag 02J2](https://kerodon.net/tag/02J2)）。対応表の状態：一部。

cosliceIdentityCone\_isInitialVertexはf=id\_Xの場合、同じcosliceの恒等錐が始対象という原文(1)⇒(3)の特殊形を直接返す。任意の同型fと他の同値条件は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone_isInitialVertex`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnder_isWeaklyContractible`

:::

:::corollary "kerodon_4_7_3_21" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_7_3_12, kerodon_4_7_3_20")
Kerodon Corollary 4.7.3.21（[Tag 02J4](https://kerodon.net/tag/02J4)）。対応表の状態：一部。

exists\_fixed\_slice\_sectionは終対象から同じprojectionの切断でXをid\_Xに送るものの存在を直接返す。(1)の順方向だけで、逆向きとinitial側は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.exists_fixed_slice_section`

:::

:::corollary "kerodon_4_7_3_22" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_3_6_4, kerodon_4_3_7_8, kerodon_4_7_3_21")
Kerodon Corollary 4.7.3.22（[Tag 02J5](https://kerodon.net/tag/02J5)）。対応表の状態：一部。

terminalPoint\_rightAnodyneは終対象Xからその一点包含がright anodyneという原文(1)⇒(3)を直接返す。錐上のFの構成と逆方向は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.terminalPoint_rightAnodyne`

:::

:::corollary "kerodon_4_7_3_23" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex.isWeaklyContractible, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex.isWeaklyContractible")
Kerodon Corollary 4.7.3.23（[Tag 02P2](https://kerodon.net/tag/02P2)）。対応表の状態：本体にある。

仮定：始対象または終対象を持つ ∞ 圏（Lean が弱い：任意の単体集合に適用）。結論：それぞれ IsWeaklyContractible X を得る（一致）。

:::

# 4.7.4 Discrete and Subterminal Objects

%%%
number := false
tag := "kerodon-4-7-4"
%%%

Kerodon [Tag 04UX](https://kerodon.net/tag/04UX)

:::definition "kerodon_4_7_4_1"
Kerodon Definition 4.7.4.1（[Tag 04UY](https://kerodon.net/tag/04UY)）。対応表の状態：なし。

IsSubterminalは通常圏のHom集合の高々一元性。原文のnerveの区間写像空間が空または可縮という条件への比較がない。

宣言：`CategoryTheory.IsSubterminal`

:::

:::proposition "kerodon_4_7_4_8"
Kerodon Proposition 4.7.4.8（[Tag 06R3](https://kerodon.net/tag/06R3)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：空間の 0 切断・離散化・通常圏の subterminal・heart の代わりに hC と nerveを照合。slice 射がその像の充満部分圏上で自明 Kan ファイブレーションとなる subterminal の判定。slice の右ファイブレーション性だけでは弱い。

:::

:::definition "kerodon_4_7_4_9"
Kerodon Notation 4.7.4.9（[Tag 04V9](https://kerodon.net/tag/04V9)）。対応表の状態：なし。

通常圏のSubterminalsとMonoOverの圏同値・Subobjectの順序であり、原文の準圏のsubterminal性からの同型類と2単体による順序との同定がない。

宣言：`CategoryTheory.subterminalsEquivMonoOverTerminal`、`CategoryTheory.Subobject`

:::

:::proposition "kerodon_4_7_4_11"
Kerodon Proposition 4.7.4.11（[Tag 06R5](https://kerodon.net/tag/06R5)）。対応表の状態：なし。

通常圏の薄さとThinSkeletonとの圏同値だけは、原文の指定の\[X\]への射の自明Kan性を返さない。

宣言：`CategoryTheory.subterminals_thin`、`CategoryTheory.ThinSkeleton.equivalence`

:::

:::corollary "kerodon_4_7_4_12"
Kerodon Corollary 4.7.4.12（[Tag 06R6](https://kerodon.net/tag/06R6)）。対応表の状態：なし。

ThinSkeletonとの通常圏の圏同値はあるが、原文の写像空間のsubterminal条件とnerve上の準圏同値とを直接結ぶ型がない。

宣言：`CategoryTheory.ThinSkeleton.equivalence`

:::

:::definition "kerodon_4_7_4_13"
Kerodon Definition 4.7.4.13（[Tag 05EY](https://kerodon.net/tag/05EY)）。対応表の状態：なし。

Is0TruncatedSpaceは空間の∞圏で離散模型と同値という述語。原文の任意のCからの写像空間の成分の可縮性を直接述べない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Is0TruncatedSpace`

:::

:::definition "kerodon_4_7_4_21"
Kerodon Notation 4.7.4.21（[Tag 05F6](https://kerodon.net/tag/05F6)）。対応表の状態：なし。

discreteSpaceInclusionは選んだ離散模型の像。原文の全てのdiscrete objectsの充満部分圏との同定がなく、任意の圏のheartの構成ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.discreteSpaceInclusion`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.discreteSpaceInclusion_isFullyFaithful`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Is0TruncatedSpace`

:::

:::proposition "kerodon_4_7_4_22"
Kerodon Proposition 4.7.4.22（[Tag 06RD](https://kerodon.net/tag/06RD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：空間の 0 切断・離散化・通常圏の subterminal・heart の代わりに hC と nerveを照合。heart からそのホモトピー圏の nerve への自明 Kan ファイブレーション。一般の homotopy category 比較には discrete 対象への制限がない。

:::

:::corollary "kerodon_4_7_4_23"
Kerodon Corollary 4.7.4.23（[Tag 06RE](https://kerodon.net/tag/06RE)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：空間の 0 切断・離散化・通常圏の subterminal・heart の代わりに hC と nerveを照合。通常圏の nerve と同値であることと全対象の discrete 性などの同値。nerve が ∞ 圏という一方向とは異なる。

:::

# 4.7.5 Monomorphisms

%%%
number := false
tag := "kerodon-4-7-5"
%%%

Kerodon [Tag 04VD](https://kerodon.net/tag/04VD)

:::definition "kerodon_4_7_5_1"
Kerodon Definition 4.7.5.1（[Tag 04VE](https://kerodon.net/tag/04VE)）。対応表の状態：なし。

通常圏のMonoのHom集合の単射性は、nerveの写像空間への合成が直和因子へのホモトピー同値という結論に移す比較を要する。

宣言：`CategoryTheory.Mono`

:::

:::definition "kerodon_4_7_5_2"
Kerodon Notation 4.7.5.2（[Tag 04VG](https://kerodon.net/tag/04VG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の mono/epi と subobject・同値・充満忠実の特例・左右反転と sliceを照合。∞ 圏の mono を鉤付き矢印で記す規約。通常圏の Mono はこの表記を導入しない。

:::

:::definition "kerodon_4_7_5_3"
Kerodon Variant 4.7.5.3（[Tag 04VS](https://kerodon.net/tag/04VS)）。対応表の状態：なし。

通常圏のEpiのHom集合の単射性は、nerveの写像空間への前合成が直和因子へのホモトピー同値という原文の条件への比較を要する。

宣言：`CategoryTheory.Epi`

:::

:::definition "kerodon_4_7_5_19"
Kerodon Definition 4.7.5.19（[Tag 04W8](https://kerodon.net/tag/04W8)）。対応表の状態：なし。

MonoOverは通常圏のmonoの充満部分圏。原文の準圏のslice内のsubterminal性との同定がない。

宣言：`CategoryTheory.MonoOver`

:::

:::definition "kerodon_4_7_5_20"
Kerodon Notation 4.7.5.20（[Tag 04W9](https://kerodon.net/tag/04W9)）。対応表の状態：なし。

通常圏のMonoOverのThinSkeletonと順序。原文の準圏のsliceのsubterminal objectsの商と2単体での順序の同定がない。

宣言：`CategoryTheory.Subobject`

:::

# 4.7.6 Locally Truncated ∞-Categories

%%%
number := false
tag := "kerodon-4-7-6"
%%%

Kerodon [Tag 0583](https://kerodon.net/tag/0583)

:::definition "kerodon_4_7_6_1"
Kerodon Definition 4.7.6.1（[Tag 0584](https://kerodon.net/tag/0584)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝0/1 の通常圏・groupoid・空間の切断と cosk・普遍性の片方向を照合。各 X,Y の Hom(X,Y) の n-truncation としての局所 n-truncation。単体集合自体の coskeletal 性を述べる型と区別した。

:::

:::definition "kerodon_4_7_6_9"
Kerodon Variant 4.7.6.9（[Tag 058A](https://kerodon.net/tag/058A)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝0/1 の通常圏・groupoid・空間の切断と cosk・普遍性の片方向を照合。dg nerve の局所 n-truncation と dg Hom のホモロジー消滅の同値。dg Hom の複体と nerve の定義には消滅の次数比較がない。

:::

:::definition "kerodon_4_7_6_13"
Kerodon Definition 4.7.6.13（[Tag 058C](https://kerodon.net/tag/058C)）。対応表の状態：なし。

nerveAdjunctionは普通のHomの随伴全単射で、原文の任意Fのlocal n-truncationを判定する関手∞圏の同値と局所切断条件を直接与えない。

宣言：`CategoryTheory.nerveAdjunction`

:::

:::proposition "kerodon_4_7_6_15" (uses := "kerodon_1_4_0_1, kerodon_3_5_3_18")
Kerodon Proposition 4.7.6.15（[Tag 06RM](https://kerodon.net/tag/06RM)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝0/1 の通常圏・groupoid・空間の切断と cosk・普遍性の片方向を照合。C の局所 (n−2)-truncation と coskₙ 比較の条件の同値。coskeleton adjunction 自体は写像空間の次数を判定しない。

:::

:::corollary "kerodon_4_7_6_16" (uses := "kerodon_1_4_0_1")
Kerodon Corollary 4.7.6.16（[Tag 06RN](https://kerodon.net/tag/06RN)）。対応表の状態：なし。

cosk₂Isoは通常圏のnerveの2-coskeletal性を表す同型。原文の結論の局所(n−2)-truncationを型に持たず、n=2の特殊形でも写像空間の比較が要る。

宣言：`CategoryTheory.Nerve.cosk₂Iso`

:::

:::corollary "kerodon_4_7_6_17" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_3_5_3_23, kerodon_4_7_6_16")
Kerodon Corollary 4.7.6.17（[Tag 06RP](https://kerodon.net/tag/06RP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝0/1 の通常圏・groupoid・空間の切断と cosk・普遍性の片方向を照合。coskₙ(C) 自身の局所 (n−2)-truncation と ∞ 圏性。truncated simplicial set からの右随伴の型は両性質を主張しない。

:::

:::corollary "kerodon_4_7_6_18" (uses := "kerodon_1_4_0_1, kerodon_4_5_4_12, kerodon_4_7_6_15, kerodon_4_7_6_16, kerodon_4_7_6_17")
Kerodon Corollary 4.7.6.18（[Tag 058L](https://kerodon.net/tag/058L)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝0/1 の通常圏・groupoid・空間の切断と cosk・普遍性の片方向を照合。局所 (n−2)-truncation と C→coskₙ(C) の圏同値の判定。coskeleton 反射の同型判定は圏同値より強い別条件。

:::

:::proposition "kerodon_4_7_6_19" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_3_5_3_17, kerodon_3_5_3_18, kerodon_4_7_6_17, kerodon_4_7_6_18")
Kerodon Proposition 4.7.6.19（[Tag 058G](https://kerodon.net/tag/058G)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝0/1 の通常圏・groupoid・空間の切断と cosk・普遍性の片方向を照合。C→coskₙ(C) が局所 (n−2)-truncation を表示する普遍性。骨格との随伴では標的が局所 truncated な ∞ 圏とは限らない。

:::

:::corollary "kerodon_4_7_6_20"
Kerodon Corollary 4.7.6.20（[Tag 058N](https://kerodon.net/tag/058N)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝0/1 の通常圏・groupoid・空間の切断と cosk・普遍性の片方向を照合。hQCat 上で局所 n-truncated な対象への反射。通常の hC や coskeleton の随伴の圏が異なる。

:::

:::corollary "kerodon_4_7_6_22"
Kerodon Corollary 4.7.6.22（[Tag 06RR](https://kerodon.net/tag/06RR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝0/1 の通常圏・groupoid・空間の切断と cosk・普遍性の片方向を照合。Kan 複体を始域とする局所 n-truncation と空間の truncation の比較。C の Kan 性だけを運ぶ比較は局所普遍性を与えない。

:::

:::corollary "kerodon_4_7_6_24" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_5_2_2, kerodon_3_5_7_20, kerodon_4_6_5_10, kerodon_4_7_6_19")
Kerodon Corollary 4.7.6.24（[Tag 06RT](https://kerodon.net/tag/06RT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝0/1 の通常圏・groupoid・空間の切断と cosk・普遍性の片方向を照合。局所 n-truncation が各 Hom 上で誘導する n-truncation。pinched Hom の比較同値は次数付き切断射ではない。

:::

:::corollary "kerodon_4_7_6_25" (uses := "kerodon_1_4_0_1, kerodon_4_7_6_24")
Kerodon Corollary 4.7.6.25（[Tag 0590](https://kerodon.net/tag/0590)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝0/1 の通常圏・groupoid・空間の切断と cosk・普遍性の片方向を照合。各 f における Hom の πₙ が一元となる局所 truncation 判定。Kan 複体の連結度や π 群単体の補題だけでは全 f を結ばない。

:::

# 4.7.7 n-Categories

%%%
number := false
tag := "kerodon-4-7-7"
%%%

Kerodon [Tag 057D](https://kerodon.net/tag/057D)

:::definition "kerodon_4_7_7_1"
Kerodon Definition 4.7.7.1（[Tag 057E](https://kerodon.net/tag/057E)）。対応表の状態：なし。

StrictSegalはspineからの一意延長で、原文の内ホーンの存在・高次一意性とは異なる条件。nerveの場合にもホーンとの比較が必要。

宣言：`CategoryTheory.Nerve.strictSegal`

:::

:::proposition "kerodon_4_7_7_8"
Kerodon Proposition 4.7.7.8（[Tag 057L](https://kerodon.net/tag/057L)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve と n＝0 の薄い圏・Kan の特例と次数付き骨格・閉性の一部を照合。正次数 n-category と weak n-coskeletal かつ次元 n で minimal の同値。一般の minimal モデルの型には次元の制限がない。

:::

:::definition "kerodon_4_7_7_9"
Kerodon Definition 4.7.7.9（[Tag 057M](https://kerodon.net/tag/057M)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve と n＝0 の薄い圏・Kan の特例と次数付き骨格・閉性の一部を照合。負次数も含め weak coskeleton と次数付き minimality で定める n-category。全次元の coskeletal や minimal で代用できない。

:::

:::proposition "kerodon_4_7_7_16"
Kerodon Proposition 4.7.7.16（[Tag 057U](https://kerodon.net/tag/057U)）。対応表の状態：一部。

thinNerve\_hom\_ext\_hornは半順序Qのnerveで次数2以上の同じホーンに一致する二充填の等式を直接返す。この特殊形の高次充填の一意性成分のみで、0-category全体のiffは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.thinNerve_innerFibration`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.thinNerve_hom_ext_horn`

:::

:::proposition "kerodon_4_7_7_20"
Kerodon Proposition 4.7.7.20（[Tag 057Y](https://kerodon.net/tag/057Y)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve と n＝0 の薄い圏・Kan の特例と次数付き骨格・閉性の一部を照合。n-category の左右 pinched Hom が (n−1)-groupoid となる次数降下。左右比較同値や Kan 性だけには次数がない。

:::

:::proposition "kerodon_4_7_7_22"
Kerodon Proposition 4.7.7.22（[Tag 0581](https://kerodon.net/tag/0581)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve と n＝0 の薄い圏・Kan の特例と次数付き骨格・閉性の一部を照合。n-category の Fun(K,C) による閉性。Fun(K,C) の ∞ 圏性を導く型には高次ホーンの一意性がない。

:::

:::corollary "kerodon_4_7_7_23"
Kerodon Corollary 4.7.7.23（[Tag 0582](https://kerodon.net/tag/0582)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve と n＝0 の薄い圏・Kan の特例と次数付き骨格・閉性の一部を照合。oriented と homotopy fiber product の n-category 性。既存 pullback の ∞ 圏性からは次数 n を保持する型を得ない。

:::

:::corollary "kerodon_4_7_7_24"
Kerodon Corollary 4.7.7.24（[Tag 06RV](https://kerodon.net/tag/06RV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の nerve と n＝0 の薄い圏・Kan の特例と次数付き骨格・閉性の一部を照合。slice と coslice の n-category 性。join から得る ∞ 圏性・ファイブレーション性には一意充填の次数がない。

:::

# 4.7.8 Minimality Conditions

%%%
number := false
tag := "kerodon-4-7-8"
%%%

Kerodon [Tag 058P](https://kerodon.net/tag/058P)

:::proposition "kerodon_4_7_8_1"
Kerodon Proposition 4.7.8.1（[Tag 058Q](https://kerodon.net/tag/058Q)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan 最小性・0-reduced・通常の coskeleton と nerve・有限次数での比較を照合。非空条件を含む (n+1)-coskeletal の判定と n-category 性の関係。通常 coskeletal だけの型では負次数と weak 条件を扱わない。

:::

:::corollary "kerodon_4_7_8_2"
Kerodon Corollary 4.7.8.2（[Tag 058R](https://kerodon.net/tag/058R)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan 最小性・0-reduced・通常の coskeleton と nerve・有限次数での比較を照合。minimal ∞ 圏で n-category と局所 (n−1)-truncation が同値。minimal Kan fibration の一意性には任意の ∞ 圏の局所次数がない。

:::

:::corollary "kerodon_4_7_8_3"
Kerodon Corollary 4.7.8.3（[Tag 058S](https://kerodon.net/tag/058S)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan 最小性・0-reduced・通常の coskeleton と nerve・有限次数での比較を照合。局所 (n−1)-truncation と n-category に同値であることの同値。minimal モデルの比較だけでは n-category への次数評価がない。

:::

:::corollary "kerodon_4_7_8_4"
Kerodon Corollary 4.7.8.4（[Tag 058T](https://kerodon.net/tag/058T)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan 最小性・0-reduced・通常の coskeleton と nerve・有限次数での比較を照合。weak (n−1)-coskeletal な ∞ 圏から n-category 性を得る含意。通常 coskeleton と内ホーンの一意充填の次数が異なる。

:::

:::corollary "kerodon_4_7_8_5"
Kerodon Corollary 4.7.8.5（[Tag 058U](https://kerodon.net/tag/058U)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan 最小性・0-reduced・通常の coskeleton と nerve・有限次数での比較を照合。n-category の Hom が weak (n−1)-coskeletal となる結論。interval Hom の Kan 性だけでは weak coskeleton の次数を与えない。

:::

:::proposition "kerodon_4_7_8_6"
Kerodon Proposition 4.7.8.6（[Tag 0592](https://kerodon.net/tag/0592)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan 最小性・0-reduced・通常の coskeleton と nerve・有限次数での比較を照合。m-単体から (m−1)-骨格への制限 θₘ による n-category 判定。sk/cosk の随伴には一意充填を反映するこの判定がない。

:::

:::corollary "kerodon_4_7_8_8"
Kerodon Corollary 4.7.8.8（[Tag 0594](https://kerodon.net/tag/0594)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan 最小性・0-reduced・通常の coskeleton と nerve・有限次数での比較を照合。n-reduced の次数 ≤n での単体一意性の同値条件。Reduced は頂点一意の特別な場合。

:::

:::corollary "kerodon_4_7_8_9"
Kerodon Corollary 4.7.8.9（[Tag 0595](https://kerodon.net/tag/0595)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan 最小性・0-reduced・通常の coskeleton と nerve・有限次数での比較を照合。minimal Kan で n-reduced と (n+1)-connective の同値。π による連結度の型に n 以下の単体の一意性はない。

:::

:::proposition "kerodon_4_7_8_10"
Kerodon Proposition 4.7.8.10（[Tag 058V](https://kerodon.net/tag/058V)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan 最小性・0-reduced・通常の coskeleton と nerve・有限次数での比較を照合。weak coskₙ の ∞ 圏性と局所 truncation の表示。通常 coskₙ を取る右随伴とは対象も普遍性も異なる。

:::

# 4.7.9 Higher Homotopy Categories

%%%
number := false
tag := "kerodon-4-7-9"
%%%

Kerodon [Tag 0596](https://kerodon.net/tag/0596)

:::definition "kerodon_4_7_9_1"
Kerodon Definition 4.7.9.1（[Tag 0597](https://kerodon.net/tag/0597)）。対応表の状態：なし。

hoFunctorとnerveAdjunctionはcanonicalなホモトピー圏の普遍性。原文の任意のFのn-category性と全てのn-category標的についての条件を直接判定しない。

宣言：`SSet.hoFunctor`、`CategoryTheory.nerveAdjunction`

:::

:::definition "kerodon_4_7_9_2"
Kerodon Notation 4.7.9.2（[Tag 0598](https://kerodon.net/tag/0598)）。対応表の状態：なし。

随伴の単位はC→N(hC)の射を構成するが、n-categoryの型・原文の普遍性と同定されていないので、ホモトピーn-categoryの同じ構成の特殊形とは数えない。

宣言：`CategoryTheory.nerveAdjunction`

:::

:::proposition "kerodon_4_7_9_7"
Kerodon Proposition 4.7.9.7（[Tag 059D](https://kerodon.net/tag/059D)）。対応表の状態：なし。

随伴は選んだunitの普通のHom全単射。原文の任意のFの前合成での集合全単射と関手∞圏の同型という二条件の含意を型に持たない。

宣言：`CategoryTheory.nerveAdjunction`

:::

:::corollary "kerodon_4_7_9_8"
Kerodon Corollary 4.7.9.8（[Tag 059E](https://kerodon.net/tag/059E)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の普遍性・n＝0 の成分と n＝∞ の恒等・骨格・相対化の片側を照合。homotopy n-category の表示から局所 (n−1)-truncation の表示へ移す含意。通常 hC の Hom の定義にこの次数付き普遍性がない。

:::

:::definition "kerodon_4_7_9_9"
Kerodon Construction 4.7.9.9（[Tag 059F](https://kerodon.net/tag/059F)）。対応表の状態：なし。

原文は弱coskeletonの相対同型の商からの特定比較射。hoFunctorの別構成とそのunitはその商・射と比較されていない。

宣言：`SSet.hoFunctor`、`CategoryTheory.nerveAdjunction`

:::

:::proposition "kerodon_4_7_9_11"
Kerodon Proposition 4.7.9.11（[Tag 059H](https://kerodon.net/tag/059H)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の普遍性・n＝0 の成分と n＝∞ の恒等・骨格・相対化の片側を照合。skₙ(A) からの指定射に対する h≤n の比較写像の性質。通常の sk/cosk 随伴は h≤n の商との比較ではない。

:::

:::corollary "kerodon_4_7_9_13"
Kerodon Corollary 4.7.9.13（[Tag 059K](https://kerodon.net/tag/059K)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の普遍性・n＝0 の成分と n＝∞ の恒等・骨格・相対化の片側を照合。weak coskₙ から h≤n への比較射の単体ごとの性質。普通の coskeleton の unit と h≤n への商射は別の射。

:::

:::corollary "kerodon_4_7_9_14"
Kerodon Corollary 4.7.9.14（[Tag 059M](https://kerodon.net/tag/059M)）。対応表の状態：なし。

strictSegalとhoFunctorは別構成のnerveについての結果。原文の弱coskeletonの指定商のn-category性を直接返さない。

宣言：`CategoryTheory.Nerve.strictSegal`、`SSet.hoFunctor`

:::

:::proposition "kerodon_4_7_9_15"
Kerodon Proposition 4.7.9.15（[Tag 059N](https://kerodon.net/tag/059N)）。対応表の状態：なし。

nerveAdjunctionはcanonicalなunitの普遍性で、原文の弱coskeletonからの商への指定比較射と同定する宣言がない。

宣言：`CategoryTheory.nerveAdjunction`

:::

:::corollary "kerodon_4_7_9_16"
Kerodon Corollary 4.7.9.16（[Tag 059P](https://kerodon.net/tag/059P)）。対応表の状態：なし。

unitの存在だけは、原文のhomotopy n-categoryの普遍性・低次全単射・因子化・自明Kan性・局所切断・isofibrationのいずれも直接結論しない。

宣言：`SSet.hoFunctor`、`CategoryTheory.nerveAdjunction`

:::

:::corollary "kerodon_4_7_9_17"
Kerodon Corollary 4.7.9.17（[Tag 059Q](https://kerodon.net/tag/059Q)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の普遍性・n＝0 の成分と n＝∞ の恒等・骨格・相対化の片側を照合。dim B≤n+1 とそれ以下で区別される h≤n 比較の持ち上げ。一般の内アノダイン持ち上げに次元上限とこの比較射がない。

:::

:::proposition "kerodon_4_7_9_20"
Kerodon Proposition 4.7.9.20（[Tag 059T](https://kerodon.net/tag/059T)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の普遍性・n＝0 の成分と n＝∞ の恒等・骨格・相対化の片側を照合。n-category を底とする pullback と h≤n の比較四角。一般の simplicial pullback は切断を施した四角を保証しない。

:::

:::corollary "kerodon_4_7_9_21"
Kerodon Corollary 4.7.9.21（[Tag 06RW](https://kerodon.net/tag/06RW)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の普遍性・n＝0 の成分と n＝∞ の恒等・骨格・相対化の片側を照合。下辺が homotopy n-category を表示する pullback から得る h≤n の同型。通常の pullback の比較同型では表示条件が異なる。

:::

:::proposition "kerodon_4_7_9_22"
Kerodon Proposition 4.7.9.22（[Tag 05K2](https://kerodon.net/tag/05K2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の普遍性・n＝0 の成分と n＝∞ の恒等・骨格・相対化の片側を照合。X 上の slice と homotopy n-category の比較射。slice の op や基底制限の構成に h≤n が現れない。

:::

:::corollary "kerodon_4_7_9_23"
Kerodon Corollary 4.7.9.23（[Tag 05K4](https://kerodon.net/tag/05K4)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：n＝1 の普遍性・n＝0 の成分と n＝∞ の恒等・骨格・相対化の片側を照合。(n−1)-truncated な X における slice の h≤n と h≤n の slice の比較。一般 slice 同値の型には対象の切断度がない。

:::

