import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.CatPullbackReplacementCone
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.EquivalenceSmallLimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.ExactFunctor
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.FibrationTower
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.FilteredKanCocone
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.FilteredKanColimit
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.FiniteLimitGeneration
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PullbackPasting
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.RepresentableLimitEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.SiftedColimitPreservation
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.SpacePullbacks
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.SpaceTowers
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.StrictHomotopyLimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanConeComparisonCriterion
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.QCatPullbackLimit
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FiniteLimitsColimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeLimit
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CatPullbackCone
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.CatPullback

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "7.6 Examples of Limits and Colimits" =>
%%%
number := false
tag := "kerodon-7-6"
%%%

Kerodon の 7.6 節（[Tag 03E8](https://kerodon.net/tag/03E8)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 7.6.1 Products and Coproducts

%%%
number := false
tag := "kerodon-7-6-1"
%%%

Kerodon [Tag 03E9](https://kerodon.net/tag/03E9)

*02-mapping-limits.html — 5. 極限 — 通常の圏との整合性*

Core/LimitExamples では、順序圏 $`0\to1` の二項積が nerve の極限と一致する、という小さな例を検算している（\`topPair\_limit\_agreement\`）。一般の圏 $`C` について $`N(C)` の極限が $`C` の極限と一致することは、ここではまだ示されていない（古典 nerve との比較は F1B 側、第 4 章）。

:::definition "kerodon_7_6_1_1"
Kerodon Definition 7.6.1.1（[Tag 03EA](https://kerodon.net/tag/03EA)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：空間圏の離散図式の積錐と余積余錐は構成される。任意の h Kan 豊穣圏で各 Hom の積への同型を条件にする積・余積の述語は見つからない。

:::

:::definition "kerodon_7_6_1_3"
Kerodon Definition 7.6.1.3（[Tag 03EC](https://kerodon.net/tag/03EC)）。対応表の状態：なし。

HasSmallCoproductsと離散形状のIsLimitConeは原文の指定射族が誘導する全写像空間の積比較そのものを型に含まない。hCの二項余積はπ₀だけであり、hKan豊穣普遍性の直接の成分とはしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallCoproducts`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spaceProductCone_isLimitCone`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.binaryColimit_isColimit`

:::

:::definition "kerodon_7_6_1_7"
Kerodon Notation 7.6.1.7（[Tag 03EG](https://kerodon.net/tag/03EG)）。対応表の状態：なし。

引用は全小余積の存在またはhCの二項余積。原文の指定Y\_iに対する写像空間の普遍性を持つ積・余積の対象の記法と一意性への比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallCoproducts`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.binaryColimit_isColimit`

:::

:::definition "kerodon_7_6_1_13"
Kerodon Notation 7.6.1.13（[Tag 03EK](https://kerodon.net/tag/03EK)）。対応表の状態：なし。

spaceProductCone\_isLimitConeは選んだ離散図式の極限錐。原文の任意の射対の全写像空間の比較とその記法を同定する型はこの引用にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spaceProductCone_isLimitCone`

:::

:::definition "kerodon_7_6_1_15"
Kerodon Notation 7.6.1.15（[Tag 04K4](https://kerodon.net/tag/04K4)）。対応表の状態：なし。

通常圏のprod.liftと射影の等式はあるが、原文の∞圏の指定積をhCのその二項積へ同定する型を引用に持たない。

宣言：`CategoryTheory.Limits.prod.lift`、`CategoryTheory.Limits.prod.lift_fst`、`CategoryTheory.Limits.prod.lift_snd`、`CategoryTheory.Limits.prod.hom_ext`

:::

:::proposition "kerodon_7_6_1_16"
Kerodon Proposition 7.6.1.16（[Tag 05FS](https://kerodon.net/tag/05FS)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の相対対角が同型であることと元の射が単射であることを比較する。一般の n と∞圏の対象の n-truncation を絶対対角の (n−1)-truncation と比較する型は見つからない。

:::

:::proposition "kerodon_7_6_1_17"
Kerodon Proposition 7.6.1.17（[Tag 04Q7](https://kerodon.net/tag/04Q7)）。対応表の状態：なし。

Over.forgetAdjStarは通常圏の随伴。∞圏の同じslice忘却関手の右随伴への比較がなく、nerveで自動的に同じ随伴と数えない。

宣言：`CategoryTheory.Over.forgetAdjStar`、`CategoryTheory.Over.star`

:::

:::proposition "kerodon_7_6_1_23"
Kerodon Proposition 7.6.1.23（[Tag 03ES](https://kerodon.net/tag/03ES)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：離散形状上の対象族の積はある。各 Kᵢ の図式の極限を先に取り、その積を Kᵢ の単体的余積上の図式の極限とする型は見つからない。

:::

:::corollary "kerodon_7_6_1_25"
Kerodon Corollary 7.6.1.25（[Tag 03EU](https://kerodon.net/tag/03EU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：小さい全形状の極限存在・保存を述べる述語はある。Kᵢ の極限と I-積だけで余積形状の極限存在・保存を得る型は見つからない。本文の保存条件には Kᵢ-indexed colimits とある。

:::

:::corollary "kerodon_7_6_1_26"
Kerodon Corollary 7.6.1.26（[Tag 03EV](https://kerodon.net/tag/03EV)）。対応表の状態：なし。

Mathlibの有限積生成は通常圏の極限。原文の∞圏の有限積とのnerve比較の型がなく、同じ存在のiffへの直接適用はできない。

宣言：`CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal`

:::

# 7.6.2 Pullback and Pushout Squares

%%%
number := false
tag := "kerodon-7-6-2"
%%%

Kerodon [Tag 03FE](https://kerodon.net/tag/03FE)

*02-mapping-limits.html — 5. 極限 — 引き戻し*

引き戻しの四角形は $`\Delta^1\times\Delta^1\to X` として扱う。鍵は同型 $`\Delta^0\star\Lambda^2_2\cong\Delta^1\times\Delta^1`（\`cospanConeSquareIso\`、Core/Square）で、両辺とも対角線に沿って二つの 2 単体を貼り合わせたものとして表示して比較する。これで四角形を cospan 上の錐とみなせる。

\`\`\`text
def IsPullbackSquare \{X : SSet.\{u\}\} (F : Δ\[1\] ⊗ Δ\[1\] ⟶ X) : Prop
\`\`\`

規約：右辺と上辺が cospan で、座標 $`(0,0)` が錐の頂点（Core/Pullback）。

:::definition "kerodon_7_6_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare")
Kerodon Definition 7.6.2.1（[Tag 03FF](https://kerodon.net/tag/03FF)）。対応表の状態：本体にある。

仮定：Δ¹×Δ¹→X の指定正方形。述語の形成には X の Quasicategory は不要（Lean が弱い）。結論：span 上の余錐の余極限性と cospan 上の錐の極限性（四角形の押し出し・引き戻しの定義と一致）。

:::

:::proposition "kerodon_7_6_2_6"
Kerodon Proposition 7.6.2.6（[Tag 05FR](https://kerodon.net/tag/05FR)）。対応表の状態：なし。

mono\_snd\_of\_monoは通常圏のMono。原文の∞圏のn-truncated射（写像空間による定義）との比較を引用に持たず、n=−1としても同じ述語ではない。

宣言：`CategoryTheory.IsPullback.mono_snd_of_mono`

:::

:::definition "kerodon_7_6_2_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeLimitCone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone")
Kerodon Variant 7.6.2.8（[Tag 048C](https://kerodon.net/tag/048C)）。対応表の状態：一部。

同じσのpullbackCone σにIsRelativeLimitCone Uを適用することで、原文のU-pullbackという定義の極限側を直接表す。専用のIsRelativePullbackSquareという名前の欠如は不足としない。余極限側は含まない。

:::

:::definition "kerodon_7_6_2_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.catPullbackDiagram_hasLimit")
Kerodon Notation 7.6.2.13（[Tag 03FS](https://kerodon.net/tag/03FS)）。対応表の状態：一部。

CをQC、二脚のfiber productをcatPullbackで指定するとcatPullbackDiagram\_hasLimitとその錐の頂点が原文の存在するfiber productの対象の成分を直接与える。一般Cとpushout側の記法・一意性は含まない。

:::

:::definition "kerodon_7_6_2_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hasFiniteLimits_of_terminal_pullbacks, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesPullbackSquare, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare")
Kerodon Definition 7.6.2.14（[Tag 03FT](https://kerodon.net/tag/03FT)）。対応表の状態：一部。

IsPullbackSquare σ=IsLimitCone(pullbackCone σ)を用い、全cospanにその錐の存在を要求すること、および全σでIsPullbackSquare σ→IsPullbackSquare(σ≫F)を要求することで、原文のpullback存在・保存の定義部分を直接表す。pushout側はこの行の根拠に含まない。

:::

:::proposition "kerodon_7_6_2_16"
Kerodon Proposition 7.6.2.16（[Tag 03FU](https://kerodon.net/tag/03FU)）。対応表の状態：なし。

terminalTargetPullback\_isBinaryProductの結論はhCの通常の二項積。原文のslice準圏のhKan豊穣積との比較がなく、終対象に限っても同じ結論は直接得られない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.terminalTargetPullback_isBinaryProduct`

:::

:::definition "kerodon_7_6_2_18"
Kerodon Variant 7.6.2.18（[Tag 05YF](https://kerodon.net/tag/05YF)）。対応表の状態：なし。

通常圏のMonoによるpullback錐の保存は、原文の∞圏のmonoと指定squareの極限性のiffへの比較を含まない。

宣言：`CategoryTheory.Limits.pullbackIsPullbackOfCompMono`

:::

:::proposition "kerodon_7_6_2_19"
Kerodon Proposition 7.6.2.19（[Tag 05K6](https://kerodon.net/tag/05K6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：∞圏の指定引き戻し正方形の述語はある。底 X が離散な場合に hC へ送った四角形の通常圏の引き戻し性を得る型は見つからない。

:::

:::proposition "kerodon_7_6_2_20"
Kerodon Proposition 7.6.2.20（[Tag 05G0](https://kerodon.net/tag/05G0)）。対応表の状態：なし。

Mathlibのpreserves\_mono\_of\_preservesLimitは通常圏のMonoを結論する。原文の∞圏の写像空間で定めるmonoとの同定がなく、同じFの結論として使えない。

宣言：`CategoryTheory.preserves_mono_of_preservesLimit`

:::

:::definition "kerodon_7_6_2_22"
Kerodon Notation 7.6.2.22（[Tag 04K5](https://kerodon.net/tag/04K5)）。対応表の状態：なし。

通常圏のpullback.diagonalは厳密なpullback対象への射。原文の∞圏の指定相対対角と同じ射・指定ホモトピーを構成する比較を持たない。

宣言：`CategoryTheory.Limits.pullback.diagonal`、`CategoryTheory.Limits.pullback.diagonal_fst`、`CategoryTheory.Limits.pullback.diagonal_snd`

:::

:::definition "kerodon_7_6_2_23"
Kerodon Variant 7.6.2.23（[Tag 04K7](https://kerodon.net/tag/04K7)）。対応表の状態：なし。

通常圏のpushout.codiagonalは原文の∞圏の指定homotopy pushoutでの相対余対角と同じ対象・射への比較を含まない。

宣言：`CategoryTheory.Limits.pushout.codiagonal`、`CategoryTheory.Limits.pushout.inl_codiagonal`、`CategoryTheory.Limits.pushout.inr_codiagonal`

:::

:::corollary "kerodon_7_6_2_24"
Kerodon Corollary 7.6.2.24（[Tag 03FV](https://kerodon.net/tag/03FV)）。対応表の状態：なし。

通常圏のOverの積と引き戻しの対応は、原文の同じ∞圏のslice準圏との比較がない。両辺に類似の存在があるだけでは数えない。

宣言：`CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback`、`CategoryTheory.Over.over_hasTerminal`、`CategoryTheory.Limits.IsLimit.pullbackConeEquivBinaryFanInverse`

:::

:::corollary "kerodon_7_6_2_27"
Kerodon Corollary 7.6.2.27（[Tag 05FT](https://kerodon.net/tag/05FT)）。対応表の状態：なし。

isIso\_diagonal\_iffは通常圏のMonoとIsIsoの判定。原文のn-truncatedと(n−1)-truncatedの写像空間の条件への比較がなく、n=−1の特殊化としても直接使えない。

宣言：`CategoryTheory.Limits.pullback.isIso_diagonal_iff`

:::

:::corollary "kerodon_7_6_2_29"
Kerodon Corollary 7.6.2.29（[Tag 05FU](https://kerodon.net/tag/05FU)）。対応表の状態：なし。

通常圏のMono保存は原文の∞圏のn-truncated射の保存への型の比較がない。任意nの結果の一部とは数えない。

宣言：`CategoryTheory.preserves_mono_of_preservesLimit`

:::

:::corollary "kerodon_7_6_2_30"
Kerodon Corollary 7.6.2.30（[Tag 03FX](https://kerodon.net/tag/03FX)）。対応表の状態：なし。

終対象上のpullbackから得るのはhCのBinaryFan.IsLimit。原文は同じ二射が∞圏のhKan豊穣積であることのiffであり、写像空間の積比較を引用の型に持たない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.terminalTargetPullback_isBinaryProduct`

:::

:::proposition "kerodon_7_6_2_31"
Kerodon Proposition 7.6.2.31（[Tag 05S7](https://kerodon.net/tag/05S7)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：四角形の引き戻し述語とファイブレーションの引き戻しで cartesian 辺を移す補題はある。ev₁ 上の指定辺で引き戻し・cartesian・locally cartesian を比較する型は見つからない。

:::

:::definition "kerodon_7_6_2_33"
Kerodon Definition 7.6.2.33（[Tag 04Q9](https://kerodon.net/tag/04Q9)）。対応表の状態：なし。

Over.pullbackは通常のslice圏の関手で、原文の指定∞圏のslice後合成のQCatAdjunctionによる右随伴の定義とは比較されていない。

宣言：`CategoryTheory.Over.pullback`

:::

:::definition "kerodon_7_6_2_34"
Kerodon Variant 7.6.2.34（[Tag 05S9](https://kerodon.net/tag/05S9)）。対応表の状態：なし。

MathlibのmapPullbackAdjは通常圏のsliceの随伴。原文の向き付きfiber product上の輸送関手とpinch同値を含む可換図式への比較がない。

宣言：`CategoryTheory.Over.mapPullbackAdj`

:::

:::proposition "kerodon_7_6_2_35"
Kerodon Proposition 7.6.2.35（[Tag 04QB](https://kerodon.net/tag/04QB)）。対応表の状態：なし。

通常圏のmapPullbackAdjは原文の四つの∞圏条件の同じslice関手やev₁のcartesian性を結論しない。

宣言：`CategoryTheory.Over.mapPullbackAdj`

:::

:::corollary "kerodon_7_6_2_37"
Kerodon Corollary 7.6.2.37（[Tag 05SA](https://kerodon.net/tag/05SA)）。対応表の状態：なし。

通常圏の全Over.map fの右随伴は、原文の∞圏のsliceおよび向き付きfiber productとの比較を含まない。ev₁の局所・大域cartesian性も型にない。

宣言：`CategoryTheory.Over.mapPullbackAdj`

:::

:::proposition "kerodon_7_6_2_38" (uses := "kerodon_1_4_0_1, kerodon_7_2_2_5, kerodon_7_3_8_1")
Kerodon Proposition 7.6.2.38（[Tag 048E](https://kerodon.net/tag/048E)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単体集合の厳密引き戻しの比較では cocartesian 辺の iff がある。∞圏の内在的 U-pullback または U-pushout 四角形を、その上下辺の U-(co)cartesian 性で判定する型は見つからない。

:::

:::corollary "kerodon_7_6_2_39" (uses := "kerodon_1_4_0_1, kerodon_5_1_1_4, kerodon_7_6_2_38")
Kerodon Corollary 7.6.2.39（[Tag 048F](https://kerodon.net/tag/048F)）。対応表の状態：なし。

通常圏のIsPullback/IsPushoutとIsIsoのiffはあるが、原文の同じ∞圏の指定正方形と可逆辺の条件への比較がない。

宣言：`CategoryTheory.IsPullback.of_horiz_isIso`、`CategoryTheory.IsPullback.isIso_fst_of_isIso`、`CategoryTheory.IsPushout.of_horiz_isIso`、`CategoryTheory.IsPushout.isIso_inr_of_isIso`

:::

:::proposition "kerodon_7_6_2_40" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isPullbackSquare_pasting_iff") (uses := "kerodon_1_4_0_1, kerodon_7_2_2_2, kerodon_7_2_3_7, kerodon_7_3_8_1")
Kerodon Proposition 7.6.2.40（[Tag 03FZ](https://kerodon.net/tag/03FZ)）。対応表の状態：一部。

Uを終対象への射に限るとisPullbackSquare\_pasting\_iffは同じΔ²×Δ¹図式の右squareを仮定した左squareと外周のiff、すなわち原文(1)を直接返す。相対一般Uとpushout側は含まない。

:::

:::proposition "kerodon_7_6_2_41" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_5_8_5, kerodon_7_5_8_13")
Kerodon Proposition 7.6.2.41（[Tag 03G1](https://kerodon.net/tag/03G1)）。対応表の状態：なし。

引用のpushout形状の余極限は原文の極限ではなく、opで反転したshape・cone・指定pushoutの比較が必要。有限極限生成だけも任意K₀₁の極限の存在を直接与えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hasColimit_pushout_shape_of_pointSpan`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hasPreservedColimit_pushout_shape`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hasFiniteLimits_of_terminal_pullbacks`

:::

:::corollary "kerodon_7_6_2_42" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hasFiniteLimits_of_terminal_pullbacks, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits") (uses := "kerodon_1_1_0_6, kerodon_1_1_4_12, kerodon_1_4_0_1, kerodon_7_2_2_12, kerodon_7_6_2_41")
Kerodon Corollary 7.6.2.42（[Tag 03G2](https://kerodon.net/tag/03G2)）。対応表の状態：一部。

HasFiniteLimitsの全有限形状への存在を終対象とcospanへ特殊化する向きと、hasFiniteLimits\_of\_terminal\_pullbacksの逆向きにより、原文の存在のiffを直接得る。任意の関手の有限極限保存のiffは含まない。

:::

# 7.6.3 Examples of Pullback and Pushout Squares

%%%
number := false
tag := "kerodon-7-6-3"
%%%

Kerodon [Tag 03G3](https://kerodon.net/tag/03G3)

:::proposition "kerodon_7_6_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_iff_cospan_representableComparison, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_cospan_homLimit, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanCone_isLimit_iff_bousfieldKanComparison")
Kerodon Proposition 7.6.3.1（[Tag 03G4](https://kerodon.net/tag/03G4)）。対応表の状態：一部。

全Homの指定一脚をKan fibrationに強めると、strictCoherentConeのBK Hom比較のiffとKan錐のhomotopy pullback判定から、原文の同じstrict squareの引き戻し性と全Hom squareのhomotopy pullback性を直接比較できる。一般の一脚fibrationでない場合は含まない。

:::

:::proposition "kerodon_7_6_3_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.qCatPullbackInfinityCone_isLimit, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.catPullbackReplacementCone_isLimit, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_3_21, kerodon_4_5_3_23, kerodon_4_5_3_24, kerodon_4_5_3_28, kerodon_4_5_3_29, kerodon_4_5_3_33, kerodon_7_1_3_18")
Kerodon Proposition 7.6.3.8（[Tag 06TN](https://kerodon.net/tag/06TN)）。対応表の状態：一部。

指定squareを一脚がEquivalenceLiftingなstrict pullback錐に限ると、qCatPullbackInfinityCone\_isLimitは同じsquareのQC内のpullback性（原文(1)）を直接返す。一般squareの指定Gの圏同値性とのiffは含まない。

:::

:::corollary "kerodon_7_6_3_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.catPullbackReplacementCone_isLimit, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.catPullbackCone_isLimit, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.catPullbackCone_vertex") (uses := "kerodon_1_4_0_1, kerodon_4_5_3_1, kerodon_4_5_3_21, kerodon_4_5_3_23, kerodon_7_6_3_8")
Kerodon Corollary 7.6.3.9（[Tag 03GF](https://kerodon.net/tag/03GF)）。対応表の状態：一部。

catPullbackCone\_isLimitとcatPullbackCone\_vertexは元の同じ二脚p,qの図式についてhomotopy fiber productそのものがQC内のfiber product対象となるという最後の結論を直接与える。指定αを備えるsquareの二脚の照合は含まない。

:::

:::corollary "kerodon_7_6_3_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spacePullbackCone_isLimitCone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_iff_cospan_representableComparison")
Kerodon Corollary 7.6.3.10（[Tag 03GG](https://kerodon.net/tag/03GG)）。対応表の状態：一部。

squareを一脚がKan fibrationなstrict pullback錐に指定すると、spacePullbackCone\_isLimitConeは同じsquareのSpace内でのpullback性（原文(1)）を直接返す。任意のsquareの指定gによるiffは含まない。

:::

:::corollary "kerodon_7_6_3_11"
Kerodon Corollary 7.6.3.11（[Tag 05E5](https://kerodon.net/tag/05E5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan 複体の厳密引き戻しを空間圏の引き戻し錐とする型はある。任意の n の二種類の連結性条件を引き戻しで移す型は見つからない。

:::

:::corollary "kerodon_7_6_3_14"
Kerodon Corollary 7.6.3.14（[Tag 03GK](https://kerodon.net/tag/03GK)）。対応表の状態：なし。

strictCoherentConeの判定の終域はBK holimで、原文の指定α₀,α₁で作る二重homotopy fiber productへの比較ではない。その自然な比較が引用にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_iff_cospan_representableComparison`

:::

# 7.6.4 Equalizers and Coequalizers

%%%
number := false
tag := "kerodon-7-6-4"
%%%

Kerodon [Tag 03GL](https://kerodon.net/tag/03GL)

:::definition "kerodon_7_6_4_1"
Kerodon Notation 7.6.4.1（[Tag 03GM](https://kerodon.net/tag/03GM)）。対応表の状態：なし。

MathlibのparallelPairは通常圏の二射の図式。原文の指定した単体集合のpushout形状と任意の準圏への射との全単射への比較がない。

宣言：`CategoryTheory.Limits.parallelPair`

:::

:::definition "kerodon_7_6_4_4"
Kerodon Definition 7.6.4.4（[Tag 03GQ](https://kerodon.net/tag/03GQ)）。対応表の状態：なし。

通常圏のWalkingParallelPairに対するequalizerとHasEqualizersは、原文の指定pushout単体形状の∞圏の極限・余極限との比較がない。

宣言：`CategoryTheory.Limits.equalizer`、`CategoryTheory.Limits.HasEqualizers`

:::

:::definition "kerodon_7_6_4_5"
Kerodon Notation 7.6.4.5（[Tag 03GR](https://kerodon.net/tag/03GR)）。対応表の状態：なし。

通常圏のequalizerという対象は原文の∞圏のEq(f₀,f₁)との比較を含まない。同じ表記だけでは数えない。

宣言：`CategoryTheory.Limits.equalizer`

:::

:::definition "kerodon_7_6_4_9"
Kerodon Variant 7.6.4.9（[Tag 03GV](https://kerodon.net/tag/03GV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左余終な制限の極限から元の極限を得る一般の向きはある。自由一生成モノイドの nerve への単体円の包含の inner anodyne 性と、その制限の（余）等化子表示は見つからない。

:::

:::definition "kerodon_7_6_4_10"
Kerodon Definition 7.6.4.10（[Tag 03GW](https://kerodon.net/tag/03GW)）。対応表の状態：なし。

通常圏のForkは原文の単体的な平行射形状のjoinからの極限図式と比較されていない。

宣言：`CategoryTheory.Limits.Fork`

:::

:::proposition "kerodon_7_6_4_14"
Kerodon Proposition 7.6.4.14（[Tag 03H3](https://kerodon.net/tag/03H3)）。対応表の状態：なし。

isPullback\_equalizer\_prodは通常圏の等化子のstrict pullback。原文のQC内のequalizer diagramとcategorical pullbackの同じ二条件への比較がない。

宣言：`CategoryTheory.Limits.isPullback_equalizer_prod`

:::

:::corollary "kerodon_7_6_4_15"
Kerodon Corollary 7.6.4.15（[Tag 03H5](https://kerodon.net/tag/03H5)）。対応表の状態：なし。

通常の等化子とSpaceのstrict pullback錐の極限性だけでは、原文の同じ平行射図式の∞等化子性とhomotopy pullback性のiffへ直接接続しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spacePullbackCone_isLimitCone`、`CategoryTheory.Limits.isPullback_equalizer_prod`

:::

:::corollary "kerodon_7_6_4_16"
Kerodon Corollary 7.6.4.16（[Tag 03H6](https://kerodon.net/tag/03H6)）。対応表の状態：なし。

一般のstrictCoherentConeのBK Hom比較は、原文の指定平行二射のHom squareのhomotopy pullback条件と同じ射とする比較がない。通常圏の対角表示だけで代用しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_isLimit_iff_general_representableComparison`、`CategoryTheory.Limits.isPullback_equalizer_prod`

:::

:::proposition "kerodon_7_6_4_18"
Kerodon Proposition 7.6.4.18（[Tag 03H8](https://kerodon.net/tag/03H8)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の等化子と対角の引き戻しは対応する。指定 E から categorical homotopy pullback への T が同値であることと QC での等化子性を比較する型は見つからない。

:::

:::definition "kerodon_7_6_4_19"
Kerodon Construction 7.6.4.19（[Tag 03H9](https://kerodon.net/tag/03H9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：準圏の同値辺の空間と端点評価、写像の path replacement の inner fibration 性はある。二関手の組 D→C×C に沿って両端点を引き戻す homotopy equalizer の指定構成は見つからない。

:::

:::corollary "kerodon_7_6_4_20"
Kerodon Corollary 7.6.4.20（[Tag 03HA](https://kerodon.net/tag/03HA)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の等化子から対角引き戻しへの型はある。同値辺空間を使った指定 hEq が QC で等化子となる型は見つからない。

:::

:::corollary "kerodon_7_6_4_21"
Kerodon Corollary 7.6.4.21（[Tag 03HB](https://kerodon.net/tag/03HB)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：片脚がファイブレーションである Kan 複体の引き戻しは空間圏の引き戻しになる。hEq の具体的 path モデルを指定し、その Kan 性と平行射の等化子性を結ぶ型は見つからない。

:::

:::proposition "kerodon_7_6_4_22"
Kerodon Proposition 7.6.4.22（[Tag 03HC](https://kerodon.net/tag/03HC)）。対応表の状態：なし。

Mathlibの通常圏のequalizerConeIsLimitは原文の∞圏の指定二射の等化子対象とfiber product対象のiffへの比較を欠く。

宣言：`CategoryTheory.Limits.HasEqualizersOfHasPullbacksAndBinaryProducts.equalizerConeIsLimit`、`CategoryTheory.Limits.hasEqualizers_of_hasPullbacks_and_binary_products`

:::

:::proposition "kerodon_7_6_4_23"
Kerodon Proposition 7.6.4.23（[Tag 03HD](https://kerodon.net/tag/03HD)）。対応表の状態：なし。

通常圏のcospan極限を積と等化子で作る型は、原文の同じ∞圏の対象と指定二射の極限性との比較を含まない。

宣言：`CategoryTheory.Limits.hasLimit_cospan_of_hasLimit_pair_of_hasLimit_parallelPair`、`CategoryTheory.Limits.hasPullbacks_of_hasBinaryProducts_of_hasEqualizers`

:::

:::corollary "kerodon_7_6_4_25"
Kerodon Corollary 7.6.4.25（[Tag 03HF](https://kerodon.net/tag/03HF)）。対応表の状態：なし。

通常圏の有限極限生成と保存は原文の∞圏の同じ積・等化子条件への比較を含まない。本体の終対象とpullbackによる生成も等化子からの方向には直接適用できない。

宣言：`CategoryTheory.Limits.hasFiniteLimits_of_hasEqualizers_and_finite_products`、`CategoryTheory.Limits.preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts`

:::

# 7.6.5 Sequential Limits and Colimits

%%%
number := false
tag := "kerodon-7-6-5"
%%%

Kerodon [Tag 03HG](https://kerodon.net/tag/03HG)

*f-01-simplicial-kan.html — 4. 塔と lim¹（Kan）*

Kan fibration の塔 $`\cdots \to X_2 \to X_1 \to X_0` の極限を考える。スペクトラムのホモトピー群の計算や、filtered な状況の比較で使う。

:::definition "kerodon_7_6_5_1"
Kerodon Definition 7.6.5.1（[Tag 03HH](https://kerodon.net/tag/03HH)）。対応表の状態：なし。

spaceTowerCone\_isLimitConeは一つのstrict towerの選んだ錐の極限性。原文の任意の∞圏のtowerおよび全towerの存在・保存の定義と同じ型を直接構成する根拠ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spaceTowerCone_isLimitCone`

:::

:::definition "kerodon_7_6_5_2"
Kerodon Notation 7.6.5.2（[Tag 03HJ](https://kerodon.net/tag/03HJ)）。対応表の状態：なし。

ofSequence/ofOpSequenceは通常圏の関手を構成する型。原文の準圏のnerve図式から同じ頂点と辺を読み出す記法の型との比較がない。

宣言：`CategoryTheory.Functor.ofSequence`、`CategoryTheory.Functor.ofOpSequence`

:::

:::definition "kerodon_7_6_5_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictNativeCocone_isColimit_of_filtered_forget, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.filteredColimit_kanComplex")
Kerodon Variant 7.6.5.9（[Tag 03HS](https://kerodon.net/tag/03HS)）。対応表の状態：本体にある。

仮定：小さい通常圏 I の filtered 図式で各値が Kan、通常圏の余錐が台で IsColimit。I=ℕ が原文（Lean が弱い）。結論：通常の余極限が Kan で、同じ頂点を持つ strictNativeCocone は標準 coherent 図式上の余極限（原文と一致）。

:::

:::definition "kerodon_7_6_5_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spaceTowerCone_isLimitCone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection_zero_fibration, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit_kanComplex")
Kerodon Variant 7.6.5.11（[Tag 03HU](https://kerodon.net/tag/03HU)）。対応表の状態：本体にある。

仮定：ℕᵒᵖ 上の Kan 図式で隣接遷移が Fibration。Kan 性の補題には初段の Kan 性だけが必要（Lean が弱い）。結論：通常の塔極限の Kan 性と、同じ塔の coherent 図式での spaceTowerCone の IsLimitCone（原文と一致）。

*f-01-simplicial-kan.html — 4. 塔と lim¹（Kan）*

- *極限は Kan 複体*：各 $`X_{n+1} \to X_n` が Kan fibration で、$`X_0` が Kan 複体なら、$`\lim X_n` は Kan 複体で、射影 $`\lim X_n \to X_0` は Kan fibration（\`FibrationTower.limit\_kanComplex\`・\`projection\_zero\_fibration\`、KST/Spectra/FibrationTower.lean。InfinityCategories/Kerodon/LimitsAndColimits/HomotopyLimitsAndColimits/KanLimits.lean にも \`towerLimit\_kanComplex\` がある）。

:::

:::definition "kerodon_7_6_5_12"
Kerodon Variant 7.6.5.12（[Tag 03HV](https://kerodon.net/tag/03HV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan 値で遷移がファイブレーションの塔の空間極限と、一写像の path replacement の inner fibration 性がある。任意の準圏の塔を指定した反復ホモトピー引き戻しで置換して QC の極限とする型は見つからない。

:::

:::proposition "kerodon_7_6_5_13"
Kerodon Proposition 7.6.5.13（[Tag 03HX](https://kerodon.net/tag/03HX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：既に与えられた Kan 値の塔の極限と、左余終な形状制限による極限性の iff はある。形状の逐次余極限から各段の極限をつなぐ塔を構成する型は見つからない。

:::

:::corollary "kerodon_7_6_5_14"
Kerodon Corollary 7.6.5.14（[Tag 03HY](https://kerodon.net/tag/03HY)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：小形状全体の極限存在と、左余終な写像に沿う極限性の制限はある。逐次完備性と各 K(n) 上の極限から余極限形状 K での存在・保存を得る型は見つからない。本文の存在の箇所には K-indexed colimits とある。

:::

:::proposition "kerodon_7_6_5_16"
Kerodon Proposition 7.6.5.16（[Tag 03J0](https://kerodon.net/tag/03J0)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Kan 値の塔の極限と、通常圏の等化子の対角引き戻し表示はある。任意の∞圏の塔で指定積上の shift をホモトピーまで一意に構成し、その恒等射との等化子で塔極限を判定する型は見つからない。

:::

# 7.6.6 Completeness and Cocompleteness

%%%
number := false
tag := "kerodon-7-6-6"
%%%

Kerodon [Tag 03UC](https://kerodon.net/tag/03UC)

:::definition "kerodon_7_6_6_1" (lean := "SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallLimits, SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits")
Kerodon Definition 7.6.6.1（[Tag 06B7](https://kerodon.net/tag/06B7)）。対応表の状態：本体にある。

仮定：単体集合 C を固定。述語形成には Quasicategory を要求しない（Lean が弱い）。結論：HasSmallLimits と HasSmallColimits は宇宙で小さい K の全図式の HasLimit・HasColimit（原文と一致）。

:::

:::definition "kerodon_7_6_6_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits, SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits")
Kerodon Definition 7.6.6.4（[Tag 06BA](https://kerodon.net/tag/06BA)）。対応表の状態：本体にある。

仮定：単体写像 F:C→D。定義自体は両端の∞圏性を要求しない（Lean が弱い）。結論：小さい K 上の全極限錐・余極限錐について、写した錐の極限性・余極限性を要求（原文と一致）。

:::

:::definition "kerodon_7_6_6_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits, SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits")
Kerodon Notation 7.6.6.5（[Tag 06BB](https://kerodon.net/tag/06BB)）。対応表の状態：一部。

PreservesSmallLimitsとPreservesSmallColimitsは原文のcontinuous/cocontinuousな頂点の条件を直接与える。専用のFunᶜᵒⁿᵗという名前の欠如は不足としないが、大きさの異なる全形状と全部分準圏の構成全体は含まない。

:::

:::definition "kerodon_7_6_6_6"
Kerodon Definition 7.6.6.6（[Tag 03UD](https://kerodon.net/tag/03UD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：宇宙で小さい全形状の完備性・余完備性と κ-small の濃度条件は別々にある。任意の κ を取ってその全 κ-small 形状に量化する四つの述語は見つからない。

:::

:::definition "kerodon_7_6_6_7"
Kerodon Notation 7.6.6.7（[Tag 04BC](https://kerodon.net/tag/04BC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：全頂点が張る部分複体を作る一般の構成はある。κ-small な形状の極限・余極限を保存する関手の充満部分圏としての指定定義は見つからない。

:::

:::proposition "kerodon_7_6_6_15"
Kerodon Proposition 7.6.6.15（[Tag 03UL](https://kerodon.net/tag/03UL)）。対応表の状態：なし。

通常圏の積・等化子による完備性生成は原文の∞圏のκ完備性と比較する型を持たない。本体の終対象とpullbackによる有限極限生成だけでは、右辺の小積と有限極限から一般κ完備という同じ結論は直接得られない。

宣言：`CategoryTheory.Limits.has_limits_of_hasEqualizers_and_products`、`CategoryTheory.Limits.hasEqualizers_of_hasPullbacks_and_binary_products`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hasFiniteLimits_of_terminal_pullbacks`

:::

:::corollary "kerodon_7_6_6_18"
Kerodon Corollary 7.6.6.18（[Tag 03UN](https://kerodon.net/tag/03UN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：宇宙で小さい全極限の述語と濃度制限はある。特異 λ で全 κ\<λ にわたる完備性から λ⁺-完備性を得る同値は見つからない。

:::

:::proposition "kerodon_7_6_6_19" (lean := "CategoryTheory.Functor.pointwiseRightKanExtension, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRightExtension_iff_local_limits") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_3_6_1, kerodon_4_6_5_10, kerodon_5_6_7_7, kerodon_7_3_5_1")
Kerodon Proposition 7.6.6.19（[Tag 03UP](https://kerodon.net/tag/03UP)）。対応表の状態：一部。

Kを準圏とし同じrightKanDiagram δ F₀ cの全てに極限があることも仮定すれば、exists\_kanRightExtension\_iff\_local\_limitsは原文の同じF₀の右Kan拡張存在を直接返す。局所κ-small性から各形状の小性を得る議論は含まない。

:::

:::definition "kerodon_7_6_6_20" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits, SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallLimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallSiftedColimits")
Kerodon Definition 7.6.6.20（[Tag 06BD](https://kerodon.net/tag/06BD)）。対応表の状態：一部。

𝕂を宇宙内の全小形状またはsifted小形状に限ればHasSmallLimits/HasSmallSiftedColimitsは、原文の各Kでの同じHasLimit/HasColimitの全称条件そのもの。任意の形状集合𝕂は含まない。

:::

:::definition "kerodon_7_6_6_22" (lean := "SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits")
Kerodon Definition 7.6.6.22（[Tag 06BE](https://kerodon.net/tag/06BE)）。対応表の状態：一部。

𝕂を宇宙内の全小形状に限ればPreservesSmallLimitsとPreservesSmallColimitsが原文の同じ図式の極限・余極限保存の条件を直接表す。任意𝕂およびそれを張る全部分関手準圏は含まない。

:::

:::proposition "kerodon_7_6_6_24"
Kerodon Proposition 7.6.6.24（[Tag 06BG](https://kerodon.net/tag/06BG)）。対応表の状態：なし。

引用は余極限保存関手のstrict pullbackの小余完備性。原文は極限とK-continuityであり、反対化した図式・coneの比較を持たない。双対に似た主張だけでは数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pullback_hasSmallColimits`

:::

:::definition "kerodon_7_6_6_26"
Kerodon Notation 7.6.6.26（[Tag 060V](https://kerodon.net/tag/060V)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：対象の完備性と関手の保存性の述語はある。指定形状集合に対応し、それぞれを対象条件・辺条件とする QC\_\{\<λ\} の部分圏は見つからない。

:::

:::proposition "kerodon_7_6_6_27"
Kerodon Proposition 7.6.6.27（[Tag 06BJ](https://kerodon.net/tag/06BJ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏 Cat の小極限と、既に頂点が属する充満部分複体への極限性移送はある。濃度境界つき QC の完備・余完備部分圏で κ-極限が存在し包含で保つ型は見つからない。

:::

:::definition "kerodon_7_6_6_28"
Kerodon Definition 7.6.6.28（[Tag 05KC](https://kerodon.net/tag/05KC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：全空間の相対余極限性を coslice 上で定義する。各ファイバーの図式に edgewise U-余極限余錐が存在することを全 K で量化した述語は見つからない。

:::

:::definition "kerodon_7_6_6_29"
Kerodon Variant 7.6.6.29（[Tag 06BK](https://kerodon.net/tag/06BK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対余極限と κ-small の述語はある。κ-small、有限、宇宙で小さい形状に対する edgewise 余極限付きファイブレーションの三種類の定義は見つからない。

:::

:::proposition "kerodon_7_6_6_39"
Kerodon Proposition 7.6.6.39（[Tag 06BT](https://kerodon.net/tag/06BT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定 U に対する相対余極限は定義される。二つの edgewise 余完備なファイブレーションの合成で、上側が cocartesian のとき余完備性を保つ型は見つからない。

:::

:::proposition "kerodon_7_6_6_40"
Kerodon Proposition 7.6.6.40（[Tag 06BU](https://kerodon.net/tag/06BU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：全空間の小余極限存在と射影の保存を別々に書く述語はある。底の余完備性の下で、それらの連言を edgewise なファイブレーションの余完備性と比較する iff は見つからない。

:::

:::proposition "kerodon_7_6_6_41"
Kerodon Proposition 7.6.6.41（[Tag 06BV](https://kerodon.net/tag/06BV)）。対応表の状態：なし。

isColimitCone\_of\_pointwiseは全関手準圏の余錐についての型。原文の一般のファイブレーションのsection準圏との比較を欠き、積射影へ限るだけで同じ指定section余錐の結論と数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isColimitCone_of_pointwise`

:::

