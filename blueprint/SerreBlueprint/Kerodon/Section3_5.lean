import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.F1PointedAcyclicFibrationLifting

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "3.5 Truncations and Postnikov Towers" =>
%%%
number := false
tag := "kerodon-3-5"
%%%

Kerodon の 3.5 節（[Tag 0513](https://kerodon.net/tag/0513)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::proposition "kerodon_3_5_0_1"
Kerodon Proposition 3.5.0.1（[Tag 0514](https://kerodon.net/tag/0514)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Kan の Whitehead 判定は既にある比較写像の同値を判定する。ホモトピー群が一つの次数に集中する X から比較先 K(G,n) と同値を作る分類は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.5.1 Connectivity

%%%
number := false
tag := "kerodon-3-5-1"
%%%

Kerodon [Tag 0517](https://kerodon.net/tag/0517)

:::definition "kerodon_3_5_1_1" (lean := "SSet.IsConnected") (uses := "kerodon_1_2_5_1")
Kerodon Definition 3.5.1.1（[Tag 04GL](https://kerodon.net/tag/04GL)）。対応表の状態：一部。

*主張*　$`n\geq0` に対し、Kan 複体は空でなく、全頂点 $`x` と $`0\leq m<n` で $`\pi_m(X,x)` が一点集合であるとき $`n`-connective である。

B6：IsConnected は π₀ が一元かつ頂点が存在する条件を直接表し、原文の n=1 の連結性を与える。任意 n の高次群消滅を含む述語は与えない。

:::

:::definition "kerodon_3_5_1_6"
Kerodon Variant 3.5.1.6（[Tag 04GQ](https://kerodon.net/tag/04GQ)）。対応表の状態：なし。

B6：anodyne Kan 置換の存在は証明部品。n-connective の定義や置換からの独立性を述べない。 候補：連続 Kan 置換と Ex∞ の単位が弱同値であることは確認。置換を通じた任意 n の連結性を定義し、置換からの独立性を示す型は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit_anodyne`

:::

:::proposition "kerodon_3_5_1_12" (uses := "kerodon_1_1_0_6, kerodon_1_1_3_6, kerodon_1_1_4_12, kerodon_1_2_5_1, kerodon_3_2_4_12, kerodon_3_2_4_13, kerodon_3_2_4_14")
Kerodon Proposition 3.5.1.12（[Tag 04GV](https://kerodon.net/tag/04GV)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。SkeletalSphericalRealization は球面的 cochain の指定条件での実現。低次元の任意の A から n-connective Kan 複体への全写像を零ホモトピックとする宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::definition "kerodon_3_5_1_13" (uses := "kerodon_1_2_5_1")
Kerodon Definition 3.5.1.13（[Tag 04GZ](https://kerodon.net/tag/04GZ)）。対応表の状態：なし。

B6：KanPiIsomorphism は各頂点における全単射で、空の始域では π₀ の全射性も返さず、有限範囲の n-connective の定義とは異なる。 候補：KanPiIsomorphism はすべての基点・次数で同型を要求。低次数で同型、境界次数で全射という有限段の条件は型にない。

宣言：`SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism`

:::

:::definition "kerodon_3_5_1_15" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_1_8_1, kerodon_3_5_1_13")
Kerodon Variant 3.5.1.15（[Tag 04H1](https://kerodon.net/tag/04H1)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Ex∞ と弱同値の保存・反映はある。任意の射を Kan 置換の正方形で n-connective と判定する述語と選択独立性は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_5_1_22" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_1_8_1, kerodon_3_2_6_3, kerodon_3_2_6_8, kerodon_3_2_6_9, kerodon_3_3_6_2, kerodon_3_3_7_1, kerodon_3_5_1_1, kerodon_3_5_1_15")
Kerodon Proposition 3.5.1.22（[Tag 04H7](https://kerodon.net/tag/04H7)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。全次数の π 同型でファイバーが acyclic となる方向はある。有限次数の n-connective と各頂点ファイバーの連結性との同値は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_1_24"
Kerodon Corollary 3.5.1.24（[Tag 051E](https://kerodon.net/tag/051E)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。任意の底で Kan fibration に沿う引き戻しの弱同値性はある。n-connectivity の基底変換での保存と、底の π₀ 全射性による反映は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_1_25"
Kerodon Corollary 3.5.1.25（[Tag 051F](https://kerodon.net/tag/051F)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Kan fibration の通常ファイバーとホモトピー引き戻しの比較はある。任意の射の n-connectivity をホモトピーファイバーごとに特徴づける型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_5_1_26" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1")
Kerodon Proposition 3.5.1.26（[Tag 04H6](https://kerodon.net/tag/04H6)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。弱同値での可縮性移送や K 理論のファイバーの負次数消滅はある。n-connective な射の両端の連結度を比較する三条件は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_1_27" (uses := "kerodon_1_1_0_6")
Kerodon Corollary 3.5.1.27（[Tag 051G](https://kerodon.net/tag/051G)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。π₀ の連結性と頂点は扱える。非空 Kan 複体の連結度を基点包含の (n−1)-connectivity と比較する型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_1_28" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_1_8_1, kerodon_3_5_1_22, kerodon_3_5_1_26")
Kerodon Corollary 3.5.1.28（[Tag 04H9](https://kerodon.net/tag/04H9)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。弱ホモトピー同値の合成・消去は全次数の同値の結果。n と n+1 の連結度を混ぜて合成を判定する三条件は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_1_29" (uses := "kerodon_1_1_0_6, kerodon_3_2_6_3, kerodon_3_5_1_22, kerodon_3_5_1_28")
Kerodon Corollary 3.5.1.29（[Tag 04HA](https://kerodon.net/tag/04HA)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Kan ファイバーと対角の pullback の比較はある。相対対角でちょうど一つ下がる連結度の iff は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::definition "kerodon_3_5_1_30"
Kerodon Variant 3.5.1.30（[Tag 051H](https://kerodon.net/tag/051H)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。pinchedHom や端点を固定した path 空間の構成はある。各頂点対の path 空間の連結度から射の n-connectivity を判定する型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_1_31" (uses := "kerodon_1_1_0_6, kerodon_3_5_1_29")
Kerodon Corollary 3.5.1.31（[Tag 04HL](https://kerodon.net/tag/04HL)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。mono・左 fibration のファイバー判定は別条件。π₀ 全射を仮定した相対対角の弱同値性による一般の弱同値判定は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_1_32" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_1_7_23, kerodon_3_1_8_2, kerodon_3_5_1_31")
Kerodon Corollary 3.5.1.32（[Tag 04HB](https://kerodon.net/tag/04HB)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。π₀ による連結性と対角の pullback の API はある。非空性と絶対対角の (n−1)-connectivity で X の連結度を特徴づける型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_1_33" (uses := "kerodon_1_1_0_6, kerodon_3_5_1_32")
Kerodon Corollary 3.5.1.33（[Tag 02LF](https://kerodon.net/tag/02LF)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。終射による弱可縮性と弱同値での移送はある。非空性と絶対対角の弱ホモトピー同値性による判定は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.5.2 Connectivity as a Lifting Property

%%%
number := false
tag := "kerodon-3-5-2"
%%%

Kerodon [Tag 051J](https://kerodon.net/tag/051J)

:::proposition "kerodon_3_5_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fibration_rlp_of_piIsomorphism") (uses := "kerodon_1_1_0_6, kerodon_1_1_4_12, kerodon_1_2_5_1, kerodon_3_5_1_12, kerodon_3_5_1_22")
Kerodon Proposition 3.5.2.1（[Tag 04HC](https://kerodon.net/tag/04HC)）。対応表の状態：一部。

*主張*　Kan ファイブレーションが $`n`-connective であることは、全頂点ファイバーが $`n`-connective であることと同値である。これは次元 $`\leq n` の単体集合の部分集合包含すべてに対する右持ち上げ性と同値で、$`0\leq m\leq n` の境界包含 $`\partial\Delta^m\subseteq\Delta^m` だけで検査できる。

B6：fibration\_rlp\_of\_piIsomorphism は全基点・全次数の π 同型と頂点 e₀ を加えた場合、原文(3),(4)の持ち上げを全ての単射に対して直接与える。指定次数以下の連結度だけからの一般の iff は含まない。

:::

:::corollary "kerodon_3_5_2_2" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_1_8_12, kerodon_3_5_1_22")
Kerodon Corollary 3.5.2.2（[Tag 051L](https://kerodon.net/tag/051L)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。全境界に対する持ち上げ性による自明 Kan fibration はある。次数を上から制限した境界だけで一般の射の n-connectivity を結論する宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_2_4" (uses := "kerodon_1_1_0_6, kerodon_3_5_1_28, kerodon_3_5_2_1, kerodon_3_5_2_2")
Kerodon Corollary 3.5.2.4（[Tag 051N](https://kerodon.net/tag/051N)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。ホーンの小対象論法による分解は全次元を使う。低次単体の全単射を保ちながら指定の連結度を得る分解条件は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_2_5"
Kerodon Corollary 3.5.2.5（[Tag 051Q](https://kerodon.net/tag/051Q)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。単体集合を Kan 置換する自然射はある。次数の閾値まで全単射で、行き先を n-connective にする置換は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_2_6"
Kerodon Corollary 3.5.2.6（[Tag 051R](https://kerodon.net/tag/051R)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。標準単体の境界と次元上限は定義される。境界が (n−1)-connective であることをホモトピー群で保証する宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_2_7"
Kerodon Corollary 3.5.2.7（[Tag 051S](https://kerodon.net/tag/051S)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。anodyne の押し出し閉性は全ホーンの弱飽和の結果。任意の n-connective 射の指定押し出しで連結度を保つ型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::definition "kerodon_3_5_2_8"
Kerodon Definition 3.5.2.8（[Tag 051U](https://kerodon.net/tag/051U)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。SSet.sk は骨格関手を与える。sk\_n X が Δ⁰ と同型である n-reduced の述語と API は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_5_2_9" (uses := "kerodon_1_1_0_6, kerodon_3_1_8_1, kerodon_3_4_2_10, kerodon_3_5_1_26, kerodon_3_5_1_27, kerodon_3_5_2_2, kerodon_3_5_2_4")
Kerodon Proposition 3.5.2.9（[Tag 051V](https://kerodon.net/tag/051V)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Kan 置換と骨格の関手は独立にある。所定の連結度と n-reduced な弱同値模型の存在を同値にする宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_5_2_11"
Kerodon Proposition 3.5.2.11（[Tag 051Y](https://kerodon.net/tag/051Y)）。対応表の状態：なし。

B6：相対内部Homのfibration性は n-connective 性という結論の成分ではない。 候補：相対内部 Hom の比較射が Kan fibration になる定理はある。骨格を含む条件や n-connectivity の下限を比較射に移す結論は含まれない。

宣言：`SSet.fibration_pullbackObjObjπ`

:::

:::corollary "kerodon_3_5_2_12"
Kerodon Corollary 3.5.2.12（[Tag 04HF](https://kerodon.net/tag/04HF)）。対応表の状態：なし。

B6：制限射のfibration性は有限次数の連結度の結論を含まない。 候補：Kan 標的への単射沿いの前合成は fibration。原文で要求する制限写像の有限次数の連結度は未確認。

宣言：`SSet.instFibrationAppPreOfMonoOfKanComplex`

:::

:::corollary "kerodon_3_5_2_13"
Kerodon Corollary 3.5.2.13（[Tag 04HG](https://kerodon.net/tag/04HG)）。対応表の状態：なし。

B6：内部Homのfibration保存は n-connective 性の保存を結論しない。 候補：Kan fibration による内部 Hom の後合成が fibration になる。f の有限次数の連結度がそのまま保たれる結論は未確認。

宣言：`SSet.instFibrationMapIhom`

:::

:::corollary "kerodon_3_5_2_14"
Kerodon Corollary 3.5.2.14（[Tag 04HH](https://kerodon.net/tag/04HH)）。対応表の状態：なし。

B6：写像空間のKan性だけは n-connective 性という主結論を含まない。 候補：任意の B への写像空間は標的が Kan なら Kan。標的の連結度と B の次元を用いた写像空間の連結度の主張は確認できない。

宣言：`SSet.instKanComplexObjIhom`

:::

# 3.5.3 Coskeletal Simplicial Sets

%%%
number := false
tag := "kerodon-3-5-3"
%%%

Kerodon [Tag 051Z](https://kerodon.net/tag/051Z)

:::definition "kerodon_3_5_3_1"
Kerodon Definition 3.5.3.1（[Tag 0520](https://kerodon.net/tag/0520)）。対応表の状態：なし。

B6：右Kan拡張によるIsCoskeletalと原文の全高次境界の一意充填との比較がない。 候補：Mathlib の IsCoskeletal は自然数 n に対する切断からの右 Kan 拡張。Kerodon の整数 n で、m\>n の全境界の一意な延長という定義との比較は未確認。

宣言：`CategoryTheory.SimplicialObject.IsCoskeletal`

:::

:::proposition "kerodon_3_5_3_9"
Kerodon Proposition 3.5.3.9（[Tag 0528](https://kerodon.net/tag/0528)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Dold–Kan の正規化と coskeleton の構成はある。単体アーベル群の coskeletal 性を正規化鎖群の消滅と n-サイクルへの境界射の像で判定する型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_5_3_10" (uses := "kerodon_1_1_0_6, kerodon_1_1_4_12")
Kerodon Proposition 3.5.3.10（[Tag 0529](https://kerodon.net/tag/0529)）。対応表の状態：なし。

B6：次数切断からの右Kan拡張の普遍性は原文の sk\_n(S) からの制限との iff の直接の型ではない。 候補：IsCoskeletal.isUniversalOfIsRightKanExtension は次数切断への右 Kan 拡張の普遍性を与える。任意の S と sk\_n S の間の制限の全単射を用いた原文の iff は未確認。元の 2-coskeletal な nerve の引用は対象が違う。

宣言：`CategoryTheory.SimplicialObject.IsCoskeletal.isUniversalOfIsRightKanExtension`

:::

:::corollary "kerodon_3_5_3_12" (uses := "kerodon_1_1_0_6, kerodon_1_5_3_2, kerodon_3_5_3_10")
Kerodon Corollary 3.5.3.12（[Tag 052B](https://kerodon.net/tag/052B)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。内部 Hom と右 Kan 拡張の coskeleton は定義される。任意 K について X の coskeletal 性を Fun(K,X) に移す宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_3_13"
Kerodon Corollary 3.5.3.13（[Tag 052C](https://kerodon.net/tag/052C)）。対応表の状態：なし。

B6：cosk単位の同型性のiffは原文の単体圏の極限の特定 θ\_m と比較されていない。 候補：自然数 n での右 Kan 拡張とその単位の同型性を確認。原文の各 m での単体の圏による極限と、境界一意充填による定義からの iff は引用で確認できない。

宣言：`CategoryTheory.SimplicialObject.IsCoskeletal`、`CategoryTheory.SimplicialObject.isCoskeletal_iff_isIso`

:::

:::definition "kerodon_3_5_3_15"
Kerodon Definition 3.5.3.15（[Tag 052E](https://kerodon.net/tag/052E)）。対応表の状態：なし。

B6：選んだcoskAdjのunitだけでは原文の任意の f の二条件を述べる型は得られない。 候補：自然数 n の cosk への選択済み単位はある。任意の f が低次全単射で n-coskeleton を与えるという条件の型は未確認。

宣言：`SSet.coskAdj`

:::

:::proposition "kerodon_3_5_3_16" (uses := "kerodon_1_1_0_6, kerodon_1_1_4_9")
Kerodon Proposition 3.5.3.16（[Tag 052F](https://kerodon.net/tag/052F)）。対応表の状態：なし。

B6：自然数次数の右Kan拡張coskはあるが、原文の境界充填と低次全単射という定義との比較がない。 候補：自然数 n では cosk\_n X と随伴の単位が存在する。整数 n を許す本文に対し負次数の coskeleton と境界による性質は引用にない。

宣言：`SSet.cosk`、`SSet.coskAdj`

:::

:::proposition "kerodon_3_5_3_17" (uses := "kerodon_1_1_0_6, kerodon_3_5_3_10, kerodon_3_5_3_12, kerodon_3_5_3_16")
Kerodon Proposition 3.5.3.17（[Tag 052G](https://kerodon.net/tag/052G)）。対応表の状態：なし。

B6：coskeletalな対象のunitの同型は、原文の任意 f についての三条件のどの含意でもない。 候補：coskeletal なら標準の cosk への単位が同型。任意の f と coskeletal な標的について、低次全単射・内部 Hom の同型・Hom の全単射の三条件は未確認。

宣言：`CategoryTheory.SimplicialObject.isCoskeletal_iff_isIso`、`CategoryTheory.SimplicialObject.isoCoskOfIsCoskeletal`

:::

:::definition "kerodon_3_5_3_18" (uses := "kerodon_1_1_0_6, kerodon_3_5_3_16, kerodon_3_5_3_17")
Kerodon Notation 3.5.3.18（[Tag 052H](https://kerodon.net/tag/052H)）。対応表の状態：なし。

B6：右Kan拡張のcoskという模型と、原文のHom(sk\_nΔ\[m\],X)の式との比較を直接述べる型がない。 候補：SSet.cosk は自然数 n の選択済み coskeleton を与える。本文の任意の整数 n のうち負次数はこの型に含まれない。

宣言：`SSet.cosk`

:::

:::corollary "kerodon_3_5_3_19"
Kerodon Corollary 3.5.3.19（[Tag 052J](https://kerodon.net/tag/052J)）。対応表の状態：なし。

B6：Truncated.coskの本質像を原文の境界一意充填の充満部分圏と同定する宣言が必要。 候補：Truncated.cosk n は自然数 n で充満忠実な右随伴として reflective。原文の整数 n と、境界一意充填で指定した充満部分圏への左随伴の形は未確認。

宣言：`SSet.Truncated.coskAdj.reflective`、`SSet.Truncated.cosk.fullyFaithful`

:::

:::proposition "kerodon_3_5_3_23" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1")
Kerodon Proposition 3.5.3.23（[Tag 052N](https://kerodon.net/tag/052N)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。cosk₂Iso は普通圏の nerve の coskeleton 表示で、群oid の nerve には Kan の結果がある。任意 Kan 複体の任意 n の cosk の Kan 性は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.5.4 Weakly Coskeletal Simplicial Sets

%%%
number := false
tag := "kerodon-3-5-4"
%%%

Kerodon [Tag 052Q](https://kerodon.net/tag/052Q)

:::definition "kerodon_3_5_4_1"
Kerodon Definition 3.5.4.1（[Tag 052R](https://kerodon.net/tag/052R)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。IsCoskeletal は切断からの右 Kan 拡張で、存在しない充填を許す「存在すれば一意」の weakly coskeletal とは異なる。該当述語は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_5_4_12"
Kerodon Proposition 3.5.4.12（[Tag 0532](https://kerodon.net/tag/0532)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。通常の coskeleton の普遍性ではすべての制限写像が延長する。弱い版で制限の像を延長可能な写像に絞る型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_4_13"
Kerodon Corollary 3.5.4.13（[Tag 0533](https://kerodon.net/tag/0533)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。SSet の内部 Hom の Kan 性の保存はある。weakly coskeletal の制限写像の単射性を内部 Hom に移す宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::definition "kerodon_3_5_4_14"
Kerodon Definition 3.5.4.14（[Tag 0534](https://kerodon.net/tag/0534)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。通常の cosk の選択済みの単位と低次の切断はある。低次全単射に加え次の次数での全射を要求する弱 coskeleton の写像の型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_5_4_17"
Kerodon Proposition 3.5.4.17（[Tag 0537](https://kerodon.net/tag/0537)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。通常の cosk\_n への単位はある。cosk\_(n+1) から像で定める弱 cosk\_n への全射とその合成の性質は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_5_4_18"
Kerodon Proposition 3.5.4.18（[Tag 0538](https://kerodon.net/tag/0538)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。通常の右 Kan 拡張には Hom の普遍性がある。弱 coskeletal の標的に限定した三条件の同値は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::definition "kerodon_3_5_4_19"
Kerodon Notation 3.5.4.19（[Tag 0539](https://kerodon.net/tag/0539)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。単体写像の像の部分複体はある。cosk\_(n+1)→cosk\_n の像により弱 coskeleton を定義する宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_4_20"
Kerodon Corollary 3.5.4.20（[Tag 053A](https://kerodon.net/tag/053A)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。通常の Truncated.cosk の反射性はある。弱 coskeletal 単体集合の充満部分圏の包含の左随伴は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_5_4_22"
Kerodon Proposition 3.5.4.22（[Tag 053C](https://kerodon.net/tag/053C)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。cosk の間の切断と一般の Kan fibration は別々にある。通常の cosk\_(n+1) から弱 cosk\_n への比較の持ち上げ性は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_4_23"
Kerodon Corollary 3.5.4.23（[Tag 053E](https://kerodon.net/tag/053E)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。通常の cosk と Kan 置換はある。任意の Kan X の弱 cosk\_n が Kan である宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_4_24"
Kerodon Corollary 3.5.4.24（[Tag 053F](https://kerodon.net/tag/053F)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。IsCoskeletal の単位の同型性はある。弱 cosk と通常の cosk が一致する条件を比較する三条件は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_5_4_26"
Kerodon Proposition 3.5.4.26（[Tag 053H](https://kerodon.net/tag/053H)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。anodyne–Kan 分解はあるが、指定の X→弱 cosk\_n X 自体が Kan fibration という宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.5.5 Higher Groupoids

%%%
number := false
tag := "kerodon-3-5-5"
%%%

Kerodon [Tag 053L](https://kerodon.net/tag/053L)

:::definition "kerodon_3_5_5_1"
Kerodon Definition 3.5.5.1（[Tag 053M](https://kerodon.net/tag/053M)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。KanComplex は全角の存在を要求する。次数 n を超える角の一意な充填も要求する n-groupoid の型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_5_5_7"
Kerodon Proposition 3.5.5.7（[Tag 053T](https://kerodon.net/tag/053T)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。discrete と KanObject への包含はある。角の一意性で定義した 0-groupoid と定値単体集合との iff は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_5_5_8"
Kerodon Proposition 3.5.5.8（[Tag 053U](https://kerodon.net/tag/053U)）。対応表の状態：なし。

B6：groupoidNerve\_kanComplex は(1)を特定nerveに限ったときの(3)のKan性のみで、原文の1-groupoidや特定の基本亜群への射との同定がない。 候補：亜群の nerve が Kan であることを確認。高次角が一意である 1-groupoid の条件と、基本亜群の nerve への標準写像が同型という特徴づけは未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.groupoidNerve_kanComplex`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalGroupoidNerve_kanComplex`

:::

:::proposition "kerodon_3_5_5_9"
Kerodon Proposition 3.5.5.9（[Tag 053V](https://kerodon.net/tag/053V)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。正規化 Moore 複体は定義される。単体アーベル群の角の高次一意性と次数 m\>n の鎖群の消滅を比較する型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_5_5_10"
Kerodon Proposition 3.5.5.10（[Tag 053W](https://kerodon.net/tag/053W)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。普通圏の nerve について 2-coskeletal の結果がある。任意 n の n-groupoid から弱 n-coskeletal を導く宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_5_11"
Kerodon Corollary 3.5.5.11（[Tag 053X](https://kerodon.net/tag/053X)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。通常の nerve には 2-coskeletal のインスタンスがある。n-groupoid の一般の (n+1)-coskeletal 性は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_5_5_12"
Kerodon Proposition 3.5.5.12（[Tag 053Y](https://kerodon.net/tag/053Y)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。StrictSegal の nerve での単体の外延性はある。一般の n-groupoid で指定の面の一致から二つの単体の等式を導く型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_5_13"
Kerodon Corollary 3.5.5.13（[Tag 053Z](https://kerodon.net/tag/053Z)）。対応表の状態：なし。

B6：Kan性の保存だけでは高次ホーン充填の一意性を結論しない。 候補：標的が Kan なら写像空間が Kan になる。高次の角充填の一意性を保つ n-groupoid の主張は未確認。

宣言：`SSet.instKanComplexObjIhom`

:::

:::corollary "kerodon_3_5_5_14"
Kerodon Corollary 3.5.5.14（[Tag 0540](https://kerodon.net/tag/0540)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Whitehead 判定はすべての π 同型でホモトピー同値を得る。n-groupoid の間での低次数の条件による三条件の比較は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_5_16"
Kerodon Corollary 3.5.5.16（[Tag 0541](https://kerodon.net/tag/0541)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。単体写像の同型性は全次数の全単射で判定できる。n-groupoid の間で m\<n に限った全単射から同型を導く型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_5_5_17"
Kerodon Proposition 3.5.5.17（[Tag 0542](https://kerodon.net/tag/0542)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Dold–Kan は非負次数の複体を単体アーベル群に戻す。一点の低次単体を持つ n-groupoid を K(G,n) と同定する型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.5.6 Higher Fundamental Groupoids

%%%
number := false
tag := "kerodon-3-5-6"
%%%

Kerodon [Tag 0543](https://kerodon.net/tag/0543)

:::definition "kerodon_3_5_6_1"
Kerodon Definition 3.5.6.1（[Tag 0544](https://kerodon.net/tag/0544)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。KanHomotopy は固定境界の代表を割る。低次単体を保ち n 単体だけを相対ホモトピーで割る homotopy n-groupoid の写像の条件は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_5_6_5"
Kerodon Proposition 3.5.6.5（[Tag 0548](https://kerodon.net/tag/0548)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。基本圏と nerve の普通の Hom の転置がある。任意 n の n-groupoid 標的で Fun(Y,Z)→Fun(X,Z) の単体同型を与える型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::definition "kerodon_3_5_6_6"
Kerodon Notation 3.5.6.6（[Tag 0549](https://kerodon.net/tag/0549)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。SSet.truncation n は添字の切断であり、n 次元のホモトピー類で割る π\_\{≤n\}(X) は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::definition "kerodon_3_5_6_10"
Kerodon Construction 3.5.6.10（[Tag 054D](https://kerodon.net/tag/054D)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。cosk と部分複体の像の API はある。弱 cosk\_n から π\_\{≤n\} への相対ホモトピーによる商写像は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_5_6_12"
Kerodon Proposition 3.5.6.12（[Tag 054F](https://kerodon.net/tag/054F)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。相対ホモトピーの商は二写像の類を同定する。弱 cosk\_n の写像の像が同じという条件との比較は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_6_14"
Kerodon Corollary 3.5.6.14（[Tag 054H](https://kerodon.net/tag/054H)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。普通の coskeleton と一般の自明 fibration はある。弱 cosk\_n からホモトピー n-groupoid への q について本文の持ち上げ性は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_6_15"
Kerodon Corollary 3.5.6.15（[Tag 054K](https://kerodon.net/tag/054K)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。任意の単射への RLP で自明 Kan fibration を表す型はある。cosk\_(n+1) の指定商がその RLP を持つ宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_6_16"
Kerodon Corollary 3.5.6.16（[Tag 054L](https://kerodon.net/tag/054L)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。基本亜群の nerve は Kan。任意 n の π\_\{≤n\}(X) の Kan 性と高次の角の一意性は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::theorem "kerodon_3_5_6_17"
Kerodon Theorem 3.5.6.17（[Tag 054M](https://kerodon.net/tag/054M)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Kan 置換の存在と、相対ホモトピーの商はある。指定の v が任意次数の homotopy n-groupoid を与える一般の定理は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.5.7 Truncated Kan Complexes

%%%
number := false
tag := "kerodon-3-5-7"
%%%

Kerodon [Tag 054N](https://kerodon.net/tag/054N)

:::definition "kerodon_3_5_7_1" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1")
Kerodon Definition 3.5.7.1（[Tag 054P](https://kerodon.net/tag/054P)）。対応表の状態：なし。

B6：Is0TruncatedSpace は離散対象への準圏同型で、原文の境界充填と同定されていない別の定義。 候補：Is0TruncatedSpace は空間の準圏の頂点が離散空間と同型である条件。全 m≥n+2 の境界を埋める任意 n の定義ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Is0TruncatedSpace`

:::

:::proposition "kerodon_3_5_7_7"
Kerodon Proposition 3.5.7.7（[Tag 06QJ](https://kerodon.net/tag/06QJ)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。ホモトピー retract での可縮性移送はある。n-truncated の境界条件を指定の写像と片側逆の条件で移す型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_7_8" (uses := "kerodon_1_2_5_1")
Kerodon Corollary 3.5.7.8（[Tag 0550](https://kerodon.net/tag/0550)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。弱可縮性や π 同型のホモトピー不変性はある。任意 n の truncation の iff は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_5_7_9"
Kerodon Proposition 3.5.7.9（[Tag 054V](https://kerodon.net/tag/054V)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。AcyclicKanLifting は全基点・全次数の消滅から全境界を埋める。m\>n の消滅だけで高次境界を判定する iff は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_7_14"
Kerodon Corollary 3.5.7.14（[Tag 0551](https://kerodon.net/tag/0551)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Whitehead の全次数版はある。n-truncated の始域・終域で (n+1)-connectivity だけを用いる型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_7_15"
Kerodon Corollary 3.5.7.15（[Tag 0552](https://kerodon.net/tag/0552)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。cosk は関手である。所定の連結度の射に cosk\_n をかけると同値となるという宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_5_7_16"
Kerodon Proposition 3.5.7.16（[Tag 0553](https://kerodon.net/tag/0553)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。coskeletal なら cosk への単位は同型。n-truncated、n-groupoid 模型、cosk\_(n+1) へのホモトピー同値の四条件は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::definition "kerodon_3_5_7_17"
Kerodon Variant 3.5.7.17（[Tag 0554](https://kerodon.net/tag/0554)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。切断関手と Whitehead 判定はある。π\_\{≤n\}(X) への標準写像のホモトピー同値性による特徴づけは見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_7_19"
Kerodon Corollary 3.5.7.19（[Tag 0556](https://kerodon.net/tag/0556)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。単体アーベル群の Dold–Kan はある。n-connective かつ n-truncated な任意の Kan 複体を K(G,n) と特徴づける型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::definition "kerodon_3_5_7_20" (uses := "kerodon_1_2_5_1")
Kerodon Definition 3.5.7.20（[Tag 0557](https://kerodon.net/tag/0557)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。骨格と添字切断はある。n-truncated な標的への比較の存在により対象の n-truncation を定義する型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_5_7_30"
Kerodon Proposition 3.5.7.30（[Tag 055H](https://kerodon.net/tag/055H)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。全 Kan 標的への写像空間で弱同値を判定する型はある。n-truncated 標的に限る Hom の全単射による n-truncation の普遍性は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_7_31"
Kerodon Corollary 3.5.7.31（[Tag 055J](https://kerodon.net/tag/055J)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。普通の cosk は reflective。n-truncated Kan 複体のホモトピー圏の包含への左随伴は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.5.8 The Postnikov Tower of a Kan Complex

%%%
number := false
tag := "kerodon-3-5-8"
%%%

Kerodon [Tag 055K](https://kerodon.net/tag/055K)

:::definition "kerodon_3_5_8_1"
Kerodon Definition 3.5.8.1（[Tag 055L](https://kerodon.net/tag/055L)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Kan fibration の塔の極限と dg 代数の Postnikov はある。任意 Kan 複体の n-truncation を各段に指定する Postnikov tower の定義は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_5_8_7"
Kerodon Proposition 3.5.8.7（[Tag 055T](https://kerodon.net/tag/055T)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Kan ファイバーの高次ホモトピーと dg Hom の Dold–Kan 模型はある。弱 cosk の特定のファイバーと Eilenberg–MacLane 空間の同型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_8_9"
Kerodon Corollary 3.5.8.9（[Tag 055V](https://kerodon.net/tag/055V)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。fibration tower の極限と標準射はある。Postnikov 塔の各段のファイバーを K(π\_n,n) とする標準ホモトピー同値は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::definition "kerodon_3_5_8_10"
Kerodon Variant 3.5.8.10（[Tag 055W](https://kerodon.net/tag/055W)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。任意の指定した Kan fibration の塔の極限はある。弱 cosk の transition が Kan fibration であるという型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

# 3.5.9 Truncated Morphisms

%%%
number := false
tag := "kerodon-3-5-9"
%%%

Kerodon [Tag 055Y](https://kerodon.net/tag/055Y)

:::definition "kerodon_3_5_9_1" (uses := "kerodon_1_2_5_1")
Kerodon Definition 3.5.9.1（[Tag 055Z](https://kerodon.net/tag/055Z)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Is0TruncatedSpace は対象の零次の場合。負次数も含む任意の射の truncation を π の単射・全射で定義する型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_5_9_8" (uses := "kerodon_1_2_5_1, kerodon_3_2_6_3, kerodon_3_2_6_8, kerodon_3_2_6_9, kerodon_3_5_7_1, kerodon_3_5_9_1")
Kerodon Proposition 3.5.9.8（[Tag 0566](https://kerodon.net/tag/0566)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。ファイバーが可縮なら自明 Kan fibration という全次数の結果はある。任意 n の相対 truncation を各ファイバーで判定する iff は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::definition "kerodon_3_5_9_10"
Kerodon Variant 3.5.9.10（[Tag 0568](https://kerodon.net/tag/0568)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。片脚の Kan 置換によるホモトピー引き戻しはある。一般の写像の n-truncation をホモトピーファイバーに移す型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_9_11" (uses := "kerodon_1_2_5_1, kerodon_3_1_8_1, kerodon_3_5_7_8, kerodon_3_5_9_8")
Kerodon Corollary 3.5.9.11（[Tag 0569](https://kerodon.net/tag/0569)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。基底変換での弱同値保存はある。n-truncated な射の引き戻しでの保存と π₀ 全射による反映は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_9_12" (uses := "kerodon_1_2_5_1, kerodon_3_4_0_7, kerodon_3_4_0_9, kerodon_3_5_9_8, kerodon_3_5_9_11")
Kerodon Corollary 3.5.9.12（[Tag 056B](https://kerodon.net/tag/056B)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Kan 置換と通常ファイバーによる判定は全次数の弱同値に限る。ホモトピーファイバーの n-truncation と原文の三条件の比較は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_5_9_13"
Kerodon Proposition 3.5.9.13（[Tag 056C](https://kerodon.net/tag/056C)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。全次数の π 同型や π₀ 全射に基づく Whitehead 判定はある。始域の n-truncation と (n−1)-truncated な射から終域へ移す型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_9_14"
Kerodon Corollary 3.5.9.14（[Tag 06QK](https://kerodon.net/tag/06QK)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。ホモトピー引き戻しの模型と弱同値保存はある。四頂点の異なる切断次数から残りの頂点の n-truncation を得る型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_9_15"
Kerodon Corollary 3.5.9.15（[Tag 056D](https://kerodon.net/tag/056D)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。弱同値の二対三性はある。n と n−1 を混ぜた相対 truncation の合成・消去の三条件は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::proposition "kerodon_3_5_9_16"
Kerodon Proposition 3.5.9.16（[Tag 056E](https://kerodon.net/tag/056E)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。任意の Kan fibration のホーン持ち上げ性はある。k と n+2 の大小で境界条件から相対 truncation を回収する条件は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_9_17"
Kerodon Corollary 3.5.9.17（[Tag 056G](https://kerodon.net/tag/056G)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。全境界に対する自明 Kan fibration の判定はある。k≥n+2 の指定次元で境界充填の有無を相対 truncation に結び付ける宣言は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_9_18"
Kerodon Corollary 3.5.9.18（[Tag 056H](https://kerodon.net/tag/056H)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。相対対角の pullback とファイバー比較はある。対角が (n−1)-truncated であることによる相対 n-truncation の再帰判定は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::definition "kerodon_3_5_9_20"
Kerodon Variant 3.5.9.20（[Tag 056K](https://kerodon.net/tag/056K)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。fibration の高次境界充填を全 π 同型から得る結果はある。原文の有限次元での相対 truncation の特徴づけは見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_9_21"
Kerodon Corollary 3.5.9.21（[Tag 056L](https://kerodon.net/tag/056L)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。境界包含に対する相対内部 Hom の比較は fibration になる。指定の写像空間の正方形のホモトピー引き戻し性による truncation 判定は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_9_23"
Kerodon Corollary 3.5.9.23（[Tag 056N](https://kerodon.net/tag/056N)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。境界からの内部 Hom はある。定値写像を送る対角の弱同値性と X の n-truncation の iff は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_9_24"
Kerodon Corollary 3.5.9.24（[Tag 056P](https://kerodon.net/tag/056P)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。骨格と部分複体に沿う制限の fibration 性はある。所定骨格を含む場合の弱同値性を相対 n-truncation と比較する四条件は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_9_25"
Kerodon Corollary 3.5.9.25（[Tag 06QM](https://kerodon.net/tag/06QM)）。対応表の状態：なし。

B6：極限への射のfibration性は指定の n-truncation の保存を結論しない。 候補：FibrationTower.projection\_zero\_fibration は Kan fibration の塔の極限から初項への射が fibration と示す。transition の有限次数の truncation が保たれる結論は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection_zero_fibration`

:::

:::corollary "kerodon_3_5_9_26"
Kerodon Corollary 3.5.9.26（[Tag 06QN](https://kerodon.net/tag/06QN)）。対応表の状態：なし。

B6：極限のKan性は n-truncation の保存という結論ではない。 候補：Kan fibration の塔で初項が Kan なら極限も Kan となるインスタンスはある。各段の n-truncation を極限へ移す結論は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit_kanComplex`

:::

:::proposition "kerodon_3_5_9_27"
Kerodon Proposition 3.5.9.27（[Tag 056Q](https://kerodon.net/tag/056Q)）。対応表の状態：なし。

B6：比較射のfibration性は (n−k)-truncation の結論ではない。 候補：相対内部 Hom の比較が Kan fibration になる。入力の n-truncation と包含の次元を用いた比較の (n−k)-truncation は未確認。

宣言：`SSet.fibration_pullbackObjObjπ`

:::

:::corollary "kerodon_3_5_9_28"
Kerodon Corollary 3.5.9.28（[Tag 056R](https://kerodon.net/tag/056R)）。対応表の状態：なし。

B6：制限射のfibration性は (n−k)-truncation の結論ではない。 候補：Kan 標的と単射に沿う制限写像の fibration 性はある。次元 k によって truncation が n−k になる主張は未確認。

宣言：`SSet.instFibrationAppPreOfMonoOfKanComplex`

:::

:::corollary "kerodon_3_5_9_29"
Kerodon Corollary 3.5.9.29（[Tag 05P3](https://kerodon.net/tag/05P3)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。内部 Hom への定値写像はある。A の連結度に応じて対角 X→Fun(A,X) の truncation を n−k とする型は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_9_30"
Kerodon Corollary 3.5.9.30（[Tag 056S](https://kerodon.net/tag/056S)）。対応表の状態：なし。

B6：内部Homのfibration保存は n-truncation の結論ではない。 候補：内部 Hom の後合成が Kan fibration を保存する。有限次数の n-truncation を保つ型は未確認。

宣言：`SSet.instFibrationMapIhom`

:::

:::corollary "kerodon_3_5_9_31"
Kerodon Corollary 3.5.9.31（[Tag 056T](https://kerodon.net/tag/056T)）。対応表の状態：なし。

B6：内部HomのKan性は n-truncation の結論ではない。 候補：任意の単体集合 B から Kan X への Fun(B,X) の Kan 性はある。X の n-truncation を保つ型は未確認。

宣言：`SSet.instKanComplexObjIhom`

:::

:::corollary "kerodon_3_5_9_32"
Kerodon Corollary 3.5.9.32（[Tag 056U](https://kerodon.net/tag/056U)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。境界での相対内部 Hom の Kan fibration 性はある。対象の truncation と境界への定値写像の比較図式を結ぶ三条件は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

:::corollary "kerodon_3_5_9_33"
Kerodon Corollary 3.5.9.33（[Tag 056V](https://kerodon.net/tag/056V)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。全 Kan 標的への前合成による弱同値の判定はある。n-truncated 標的と (n+1)-connective 射の間の直交性を述べる五条件は見つからない。 一般API・証明部品だけを同じ主張のpartialにはしない。

:::

