import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.HA.Section5_2_2.ClassifiedConeLimit
import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.SmallConstantSource
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningAllBases
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningInfinityEquivalence
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.InitialSectionLifting
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalCoconeRestriction
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalLimitTransfer
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalWeakEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.InitialSectionEvaluation
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenA
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.PullbackColimitConeExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.PullbackSquareCoconeCriterion
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CanonicalCoconeWeakEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CoconeFiberColimitCriterion
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CoherentTotalColimit
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.DiagramSectionsCone
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportConeRestriction
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.PullbackConeComponentCriterion
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.PullbackLimitConeExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.PullbackSquareConeCriterion
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RepresentationFamilyRecovery
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RepresentationFamilyUniqueness
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RepresentationFamilyWitness
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RepresentationMappingEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RepresentationMappingSpaceMap
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SigmaElementsConeRestriction
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SimplicialSections
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SpacePointLimitDetection
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SpaceSmallLimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TensorCoconeComponentCriterion
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TensorColimitConeExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TensorConeComponentCriterion
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TensorLimitConeExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportSectionsLimit
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.YonedaEvaluationLimits

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "7.4 Limits and Colimits of Spaces" =>
%%%
number := false
tag := "kerodon-7-4"
%%%

Kerodon の 7.4 節（[Tag 02SX](https://kerodon.net/tag/02SX)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 7.4.1 Limits of Spaces

%%%
number := false
tag := "kerodon-7-4-1"
%%%

Kerodon [Tag 05QM](https://kerodon.net/tag/05QM)

*05-gamma-bridges.html — 3. γ3：𝒮 の極限・余極限*

空間の ∞ 圏 $`\mathcal S` が完備かつ余完備であることは、二つの経路で示されている。

*05-gamma-bridges.html — 3. γ3：𝒮 の極限・余極限 — (a) 一般の coherent 図式：straightening 経由（無条件）*

- 内容　／　Lean　／　場所
- 任意の小さい coherent 図式 $`B\to\mathcal S` は極限を持つ。極限は unstraightening の*切断の空間*　／　\`hasLimit\_coherentSpaceDiagram\`　／　F1/CoherentSpaceSmallLimits
- 同じく余極限を持つ。余極限は unstraightening の*全空間*の Kan 模型　／　\`hasColimit\_coherentSpaceDiagram\`　／　F2/CoherentTotalColimit
- 系：前層 ∞ 圏は小さい極限・余極限を持ち、評価で保存・検出される　／　\`presheafInfinity\_hasLimit\`、\`presheafInfinity\_hasColimit\`　／　F1/PresheafAllSmallLimits、F1/PresheafPointwiseColimits

これは「$`\lim F=` 左 fibration $`\mathrm{Un}(F)\to B` の切断の空間、$`\mathrm{colim}\,F=\mathrm{Un}(F)` の全空間（を Kan 化したもの）」という Kerodon 流の記述そのものである。第 3 章の straightening が完成していることがこの経路の前提になっている。

:::proposition "kerodon_7_4_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramSectionsCone_isLimit") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_7_1_0_1, kerodon_7_1_8_3")
Kerodon Proposition 7.4.1.1（[Tag 05QN](https://kerodon.net/tag/05QN)）。対応表の状態：一部。

*主張*　単体集合 $`C` 上の空間値図式 $`\mathscr F` と Kan 複体 $`Y` の錐 $`\beta:\underline Y\to\mathscr F` を取る。$`\beta` が極限を与えることは、一点からの射空間 $`\operatorname{Hom}_S(\Delta^0,Y)` から $`\operatorname{Hom}(\underline{\Delta^0},\mathscr F)` への合成がホモトピー同値であることと同値である。

Cを宇宙で小さく、βとYをcoherentDiagramSectionsCone Fの標準錐と切断空間に指定すると、coherentDiagramSectionsCone\_isLimitは原文(1)を同じβについて直接返す。任意のβに対する(1)⇔(2)の判定は含まない。

:::

:::corollary "kerodon_7_4_1_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentSmallConstantSourceMap_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramSectionsCone_isLimit")
Kerodon Corollary 7.4.1.2（[Tag 05QP](https://kerodon.net/tag/05QP)）。対応表の状態：一部。

*主張*　単体集合 $`C` 上の空間値図式 $`\mathscr F` への一点の定数図式からの射空間が本質的に小さいなら、その射空間は $`\mathscr F` の極限を与える。

Cが宇宙で小さい場合、coherentSmallConstantSourceMap\_isQCatEquivalenceを点に適用すると原文のMは同じ小さい全切断空間と同値。その切断錐の極限性を同値に沿って移せばMが極限と直接得る。任意の大きなCは含まない。

:::

:::corollary "kerodon_7_4_1_3" (lean := "SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.space_hasSmallLimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.hasLimit_coherentSpaceDiagram")
Kerodon Corollary 7.4.1.3（[Tag 05QQ](https://kerodon.net/tag/05QQ)）。対応表の状態：本体にある。

*主張*　空間の無限圏はすべての小さい極限を持つ。

仮定：小さい単体集合 B から SpaceInfinity への図式。原文と同じく B に Quasicategory を要求しない（Kerodon と一致）。結論：space\_hasSmallLimits と各図式の HasLimit（原文と一致）。

:::

:::definition "kerodon_7_4_1_4"
Kerodon Variant 7.4.1.4（[Tag 05QR](https://kerodon.net/tag/05QR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：宇宙で小さい図式の極限と定値始域比較はある。非可算 κ を固定して Hom の本質的 κ-small 性を必要十分とし、さらに λ への包含が極限を保つ主張は見つからない。

:::

:::proposition "kerodon_7_4_1_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramSectionsCone_isLimit, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportSectionsConeIsLimit")
Kerodon Proposition 7.4.1.6（[Tag 05QS](https://kerodon.net/tag/05QS)）。対応表の状態：一部。

*主張*　小さい単体集合 $`C` 上の左ファイブレーション $`U:E\to C` の空間値共変移送表現の極限は、切断の単体集合 $`\operatorname{Fun}_{/C}(C,E)` で与えられる。この単体集合は Kan 複体である。

UをFの標準leftUnstraighteningProjectionに指定すると、全切断のKan性のinstanceとcoherentDiagramSectionsCone\_isLimitは同じ全切断空間がFの極限であると直接返す。任意の与えた輸送表現Uは含まない。

:::

:::corollary "kerodon_7_4_1_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.hasLimit_coherentSpaceDiagram, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramSectionsCone")
Kerodon Corollary 7.4.1.7（[Tag 02VD](https://kerodon.net/tag/02VD)）。対応表の状態：本体にある。

*主張*　小さい単体集合 $`C` 上の空間値図式 $`\mathscr F` の極限は、その元の左ファイブレーション $`\int_C\mathscr F\to C` の切断の無限圏で与えられる。

仮定：小さい B と空間値 F（Kerodon と一致）。結論：HasLimit F と、F の標準 unstraightening の切断から構成する coherentDiagramSectionsCone（原文の切断モデルと一致）。

:::

:::definition "kerodon_7_4_1_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation")
Kerodon Definition 7.4.1.8（[Tag 05QT](https://kerodon.net/tag/05QT)）。対応表の状態：本体にある。

*主張*　左ファイブレーション $`U:E\to C` と空間値図式 $`\mathscr F:C\to S` について、$`\alpha:\underline{\Delta^0}_E\to\mathscr F|_E` が共変移送表現を示すとは、各頂点 $`c` への制限が $`E_c\to\operatorname{Hom}_S(\Delta^0,\mathscr F(c))` のホモトピー同値になることである。

仮定：左ファイブレーション p と空間値図式（Kerodon と一致）。結論：LeftTransportRepresentation の comparison は底上で指定 unstraightening へ写し、全頂点のファイバーで圏同値。各ファイバーは Kan で、点付き空間模型でファイバーごとのホモトピー同値を得る（原文と一致）。

:::

:::proposition "kerodon_7_4_1_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation.isPrecompositionEquivalence") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_6_4_20, kerodon_5_1_7_16, kerodon_5_6_5_1, kerodon_7_4_1_8")
Kerodon Proposition 7.4.1.9（[Tag 05QU](https://kerodon.net/tag/05QU)）。対応表の状態：一部。

*主張*　左ファイブレーション $`U:E\to C` の共変移送表現が空間値図式 $`\mathscr F:C\to S` であることは、一点の定数図式から $`\mathscr F|_E` への自然変換で、各ファイバー上の比較がホモトピー同値になるものの存在と同値である。これは $`U` が $`\mathscr F` に沿う向き付きファイバー積 $`\{\Delta^0\}\vec\times_S C\to C` に同値であることとも同値である。

Space値の比較データLeftTransportRepresentationを仮定すると、そのcomparisonはLeftTransportRepresentation.isPrecompositionEquivalenceにより同じUからFの標準leftUnstraighteningへの底上の同値を直接与える。(1)から(3)のこの成分だけで、指定αと全三条件のiffは含まない。

:::

:::definition "kerodon_7_4_1_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections") (uses := "kerodon_1_1_0_6")
Kerodon Construction 7.4.1.13（[Tag 05QY](https://kerodon.net/tag/05QY)）。対応表の状態：一部。

*主張*　単体集合の射 $`E\to C`、空間値図式 $`\mathscr F:C\to S`、自然変換 $`\underline{\Delta^0}_E\to\mathscr F|_E` を取る。この変換を切断の評価 $`\operatorname{Fun}_{/C}(C,E)\times C\to E` に沿って引き戻すと、切断の単体集合から $`\operatorname{Hom}(\underline{\Delta^0}_C,\mathscr F)` への比較写像を得る。

simplicialSectionsは原文のFun\_/C(C,E)という構成の始域を、同じUについて指定pullbackで直接構成する。αからHom空間への比較射Tの構成は含まない。

:::

:::proposition "kerodon_7_4_1_14" (uses := "kerodon_1_1_0_6, kerodon_1_1_4_12, kerodon_1_2_5_1, kerodon_3_4_1_13, kerodon_4_2_4_11, kerodon_4_2_5_2, kerodon_4_2_5_4, kerodon_4_4_3_8, kerodon_7_3_6_7, kerodon_7_4_1_8, kerodon_7_4_1_13")
Kerodon Proposition 7.4.1.14（[Tag 05QZ](https://kerodon.net/tag/05QZ)）。対応表の状態：なし。

極限錐の存在とconeRestrictionの同値は、原文の指定αで定義される比較Tのホモトピー同値ではない。始域と終域だけ似た別の比較を数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramSectionsCone_isLimit`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation.coneRestriction_iff`

:::

:::definition "kerodon_7_4_1_15" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_9_8_11")
Kerodon Variant 7.4.1.15（[Tag 03UB](https://kerodon.net/tag/03UB)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定宇宙で次数ごとの関手空間小性と空間圏の小極限を確認した。ecf(λ) の形状境界から切断の本質的 λ-small 性を出す濃度条件は見つからない。

:::

:::proposition "kerodon_7_4_1_16" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.spaceCone_isLimit_iff_pointRestriction_of_hasLimit, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.smallLeftConeRestriction_isQCatEquivalence_of_map_isLimit, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation.coneRestriction_iff") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_7_4_1_1, kerodon_7_4_1_9, kerodon_7_4_1_13, kerodon_7_4_1_14")
Kerodon Proposition 7.4.1.16（[Tag 05R3](https://kerodon.net/tag/05R3)）。対応表の状態：一部。

*主張*　単体集合 $`C^{\triangleleft}` 上の本質的に小さい左ファイブレーション $`\bar E` と、その $`C` への引き戻し $`E` を取る。$`\bar E` の空間値共変移送表現が極限図式であることは、$`\bar E` の切断から $`E` の切断への制限が Kan 複体のホモトピー同値であることと同値である。

Ūを普遍pointed-space左fibrationの指定F̄によるpullback、Fの極限存在も仮定する場合、spaceCone\_isLimit\_iff\_pointRestriction\_of\_hasLimitは同じ点からの切断制限の同値と極限性のiffを直接返す。任意の与えた表現Ūは含まない。

:::

:::corollary "kerodon_7_4_1_18"
Kerodon Corollary 7.4.1.18（[Tag 06MF](https://kerodon.net/tag/06MF)）。対応表の状態：なし。

coneRestriction\_iffはU側と普遍pointed-space側の切断制限の同値を比較する。指定した持ち上げのIsRelativeLimitConeを結論する型が引用にないため、原文(2)の解の存在と全解の相対極限性は直接得られない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation.coneRestriction_iff`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.leftFibrationConeRestriction`

:::

:::corollary "kerodon_7_4_1_19"
Kerodon Corollary 7.4.1.19（[Tag 06MH](https://kerodon.net/tag/06MH)）。対応表の状態：なし。

切断制限の同値を表現間で移すだけでは、原文の同じ持ち上げF̃が全空間で極限という結論との比較を欠く。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation.coneRestriction_iff`

:::

:::corollary "kerodon_7_4_1_20" (lean := "SerrePositivity.InfinityCategories.HA.Section5_2_2.exists_classifiedLimitCone")
Kerodon Corollary 7.4.1.20（[Tag 06MK](https://kerodon.net/tag/06MK)）。対応表の状態：一部。

*主張*　無限圏の左ファイブレーション $`U:E\to C` と極限を持つ図式 $`F:K\to C` を取る。共変移送表現が $`F` の極限を保つことは、$`F` の $`E` への任意の持ち上げが $`U` で保たれる極限を持つことと同値である。

Uを標準smallLeftUnstraighteningProjection Fに指定するとexists\_classifiedLimitConeは、同じFの底の極限の保存(1)から、任意のliftに射影で保たれる極限を直接与える。(2)⇒(1)および任意の表現Uは含まない。

:::

:::corollary "kerodon_7_4_1_21" (lean := "SerrePositivity.InfinityCategories.HA.Section5_2_2.hasLimit_smallLeftUnstraightening_of_finiteProducts, SerrePositivity.InfinityCategories.HA.Section5_2_2.exists_classifiedLimitCone")
Kerodon Corollary 7.4.1.21（[Tag 06ML](https://kerodon.net/tag/06ML)）。対応表の状態：一部。

*主張*　無限圏の左ファイブレーション $`U:E\to C` で $`C` が $`K` 添字の極限を持つとする。その共変移送表現がこの形の極限を保つことは、$`E` が $`K` 添字の極限を持ち $`U` がそれを保つことと同値である。

Uを標準smallLeftUnstraighteningProjection F、Kを有限離散形状に限りFに全有限積保存を課せば、exists\_classifiedLimitConeは任意の同じliftに射影で保たれる極限を直接作り(1)⇒(2)を与える。逆向き・一般Kは含まない。

:::

:::proposition "kerodon_7_4_1_22" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_6_4_13, kerodon_4_7_3_20, kerodon_5_6_6_14, kerodon_5_6_6_21, kerodon_7_1_6_19, kerodon_7_4_1_16")
Kerodon Proposition 7.4.1.22（[Tag 039L](https://kerodon.net/tag/039L)）。対応表の状態：なし。

引用はCᵒᵖ上の図式と反変representablePresheafInfinityによる判定。原文のC上の同じFと共変h\^Xによる判定ではない。反対圏で類似の結果というだけでは同じ極限の結論に移せない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.isLimitCone_iff_representablePresheafInfinity`

:::

:::corollary "kerodon_7_4_1_23" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.yonedaInfinityMap_evaluation_isLimit")
Kerodon Corollary 7.4.1.23（[Tag 039M](https://kerodon.net/tag/039M)）。対応表の状態：一部。

*主張*　非可算基数 $`\kappa` に関して局所的に $`\kappa`-小さい無限圏 $`C` の各対象について、$`\kappa`-小さい空間に値を取る余表現関手と表現関手は、任意の単体集合を添字とする極限を保つ。

Cを宇宙で小さく取るとyonedaInfinityMap\_evaluation\_isLimitは同じ共変Hom(x,−)について原文h\^Xの極限保存を直接返す。反変h\_X側および任意の局所κ-smallな大きなCは含まない。

:::

# 7.4.2 Digression: Functoriality of Covariant Transport

%%%
number := false
tag := "kerodon-7-4-2"
%%%

Kerodon [Tag 05R5](https://kerodon.net/tag/05R5)

:::definition "kerodon_7_4_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObject_enrichedCategory, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObject_sHom_kanComplex")
Kerodon Notation 7.4.2.1（[Tag 05R6](https://kerodon.net/tag/05R6)）。対応表の状態：一部。

*主張*　単体集合 $`C` 上の本質的に小さい左ファイブレーションで張るスライス圏の充満部分圏を $`\operatorname{LFib}(C)` と書く。単体射空間を $`C` 上の写像の単体集合 $`\operatorname{Fun}_{/C}(E,E')` とすると局所 Kan な単体圏になる。

宇宙で小さいCと小さい全空間のleft fibrationsに限れば、LeftFibrationObject、leftFibrationObject\_enrichedCategory、sHom\_kanComplexが原文と同じ対象・底上のHom・局所Kanな豊穣圏を直接構成する。単にcoherent nerveの写像があるという根拠から置き換えた。

:::

:::definition "kerodon_7_4_2_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness")
Kerodon Definition 7.4.2.2（[Tag 05R7](https://kerodon.net/tag/05R7)）。対応表の状態：本体にある。

*主張*　同じ底 $`C` 上の左ファイブレーション間の射 $`\Gamma:E\to E'` と共変移送表現の自然変換 $`\gamma:\mathscr F\to\mathscr F'` の両立性を定める。移送を示す定数一点からの自然変換 $`\alpha,\alpha'` に対して、$`\gamma|_E` と $`\alpha` の合成が $`\Gamma` で引き戻した $`\alpha'` にホモトピックであることをいう。

仮定：同じ底 B の二つの左ファイブレーションと輸送表現 R,S、二変換の族を取る。原文はパラメータ K=Δ⁰（Lean が弱い）。結論：TransportRepresentationFamilyWitness は底上の Γ と輸送の変換の適合を指定するデータ（一点の族が原文と一致）。

:::

:::theorem "kerodon_7_4_2_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_isQCatEquivalence")
Kerodon Theorem 7.4.2.4（[Tag 05R9](https://kerodon.net/tag/05R9)）。対応表の状態：一部。

*主張*　任意の単体集合 $`C` で、空間値図式を対応する左ファイブレーション $`\int_C\mathscr F\to C` に送る操作は $`h\operatorname{Fun}(C,S)\to h\operatorname{LFib}(C)` の圏同値を与える。自然変換の類は、それに両立する $`C` 上の射の類に送る。

Cを宇宙で小さい準圏に限ればleftStraighteningInfinityMap\_isQCatEquivalenceからh Funとh LFibの同値そのものを直接得る。指定γとΓの適合を保つという射の指定まではこの型に含まない。

:::

:::proposition "kerodon_7_4_2_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportRepresentationMappingSpaceMap_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportRepresentationMappingSpaceMap, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportRepresentationMappingFamilyWitness")
Kerodon Proposition 7.4.2.6（[Tag 05RB](https://kerodon.net/tag/05RB)）。対応表の状態：一部。

*主張*　無限圏 $`C` 上の左ファイブレーションの共変移送表現間の自然変換に対し、それと両立する $`C` 上の左ファイブレーション間の射が存在する。そのホモトピー類は一意である。

両left fibrationsにHasSmallSimplexFibersも仮定すると、transportRepresentationMappingSpaceMapの同値と同じ射に対するMappingFamilyWitnessは指定γに適合するΓの存在とホモトピー類の一意性を直接与える。表現だけから小性を得たとはしない。

:::

:::proposition "kerodon_7_4_2_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportRepresentationFamilyWitness_nonempty, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness.unique")
Kerodon Proposition 7.4.2.11（[Tag 05RH](https://kerodon.net/tag/05RH)）。対応表の状態：一部。

*主張*　単体集合 $`C` 上の左ファイブレーション間の射に対し、それと両立する共変移送表現間の自然変換がホモトピーを除いて一意に存在する。

両射にHasSmallSimplexFibersを加えると、familyWitness\_nonemptyのK=Δ⁰とuniqueは同じΓに適合するγの存在とFunctorIsoによるホモトピー一意性を直接返す。一般の小性のない場合は含まない。

:::

:::proposition "kerodon_7_4_2_13" (uses := "kerodon_1_4_0_1, kerodon_7_3_1_5, kerodon_7_3_4_1, kerodon_7_4_1_8")
Kerodon Proposition 7.4.2.13（[Tag 03LT](https://kerodon.net/tag/03LT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：輸送表現の比較のデータと、指定左 Kan 変換が Hom 全単射を与える型はある。指定 α の輸送表現性を定値点の左 Kan 拡張性と比較する iff は見つからない。

:::

:::definition "kerodon_7_4_2_14" (uses := "kerodon_1_4_0_1")
Kerodon Variant 7.4.2.14（[Tag 05RK](https://kerodon.net/tag/05RK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：輸送表現のデータは宇宙で小さい空間圏に値を取る。順序集合 nerve の濃度評価もあるが、U の本質的 κ-small 性の下で指定 α の二種類の普遍性を比較する型は見つからない。

:::

:::corollary "kerodon_7_4_2_15" (uses := "kerodon_1_4_0_1, kerodon_5_6_5_1")
Kerodon Corollary 7.4.2.15（[Tag 03LV](https://kerodon.net/tag/03LV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：各局所余極限を入力に指定左 Kan 変換を構成する補題と、輸送表現のデータはある。本質的 κ-small な U で、α を選ばず F の表現性と点の左 Kan 拡張性を比較する iff は見つからない。

:::

:::corollary "kerodon_7_4_2_17"
Kerodon Corollary 7.4.2.17（[Tag 05RM](https://kerodon.net/tag/05RM)）。対応表の状態：なし。

引用の比較は二つの全空間の底上の写像から二表現の変換空間への射。原文の指定αによるE上の定値点からのHomへの前合成とは違う射で、その自然な比較を型に含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportRepresentationMappingSpaceMap_isQCatEquivalence`

:::

# 7.4.3 Colimits of Spaces

%%%
number := false
tag := "kerodon-7-4-3"
%%%

Kerodon [Tag 05RN](https://kerodon.net/tag/05RN)

:::proposition "kerodon_7_4_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramTotalCocone_isColimit, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentTotalCoconeFiber_isWeakHomotopyEquivalence") (uses := "kerodon_1_1_0_6, kerodon_5_6_5_1")
Kerodon Proposition 7.4.3.1（[Tag 02VE](https://kerodon.net/tag/02VE)）。対応表の状態：一部。

*主張*　小さい単体集合 $`C` 上の左ファイブレーション $`U:E\to C` の空間値共変移送表現に対し、空間 $`X` がその余極限であることは、弱ホモトピー同値 $`E\to X` が存在することと同値である。

Uを標準leftUnstraighteningProjection、XをcoherentDiagramTotalCoconeの頂点に限ると、その余極限性とcoherentTotalCoconeFiber\_isWeakHomotopyEquivalenceは同じ全空間からXへの標準射の弱同値性を直接返す。任意X・任意の輸送表現のiffは含まない。

:::

:::corollary "kerodon_7_4_3_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.hasColimit_coherentSpaceDiagram, SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.space_hasSmallColimits")
Kerodon Corollary 7.4.3.3（[Tag 02VF](https://kerodon.net/tag/02VF)）。対応表の状態：一部。

*主張*　小さい単体集合 $`C` 上の任意の空間値図式 $`\mathscr F` は余極限を持つ。Kan 複体 $`X` がその余極限であることは、弱ホモトピー同値 $`\int_C\mathscr F\to X` が存在することと同値である。

hasColimit\_coherentSpaceDiagramとspace\_hasSmallColimitsは原文前半の全小図式の余極限存在を直接返す。任意Xについて全空間からの弱同値で特徴付ける後半は含まない。

:::

:::corollary "kerodon_7_4_3_4"
Kerodon Corollary 7.4.3.4（[Tag 039K](https://kerodon.net/tag/039K)）。対応表の状態：なし。

引用はBousfield–Kanの選んだ余錐の余極限性。原文が指定するweighted nerveとその頂点との弱同値をこの型だけでは得られず、任意Xについてのiffの一部とは数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.bousfieldKanCoherentCocone_isColimit`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.kanDiagramCoherentNerve_hasColimit`

:::

:::proposition "kerodon_7_4_3_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.isColimitCone_of_coconeFiberMap_weakEquivalence, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramTotalCocone_isColimit, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentTotalCoconeFiber_isWeakHomotopyEquivalence") (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_5_6_7_2, kerodon_7_1_2_11, kerodon_7_3_8_26, kerodon_7_4_2_15")
Kerodon Proposition 7.4.3.6（[Tag 05RR](https://kerodon.net/tag/05RR)）。対応表の状態：一部。

*主張*　非可算基数 $`\kappa` と、全体 $`E` が本質的に $`\kappa`-小さい左ファイブレーション $`E\to C` を取る。その $`\kappa`-小さい空間に値を取る共変移送表現の余極限を Kan 複体 $`X` が与えることは、$`E\to X` の弱ホモトピー同値があることと同値である。

Uを標準leftUnstraighteningProjectionに限り、指定Xへの射がある余錐cのcoconeFiberMapとして与えられる場合、isColimitCone\_of\_coconeFiberMap\_weakEquivalenceはその同じ射が弱同値ならXが余極限という向きを直接返す。任意の全空間射から余錐を構成する議論は含まない。

:::

:::corollary "kerodon_7_4_3_8" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_9_8_10, kerodon_5_6_2_1, kerodon_7_4_3_6")
Kerodon Corollary 7.4.3.8（[Tag 05RT](https://kerodon.net/tag/05RT)）。対応表の状態：なし。

space\_hasSmallColimitsは宇宙内の小図式についての存在。原文の特定λで切ったS\_\<λのcf(λ)-小形状の閉性およびS\_\<μへの保存への型の比較がなく、濃度を宇宙で代用しない。

宣言：`SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.space_hasSmallColimits`

:::

:::corollary "kerodon_7_4_3_10"
Kerodon Corollary 7.4.3.10（[Tag 05RV](https://kerodon.net/tag/05RV)）。対応表の状態：なし。

固定宇宙の余完備性だけでは、原文の任意の正則基数κに対するS\_\<κの存在と包含による保存の一部を直接与えない。

宣言：`SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.space_hasSmallColimits`

:::

:::proposition "kerodon_7_4_3_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_iff_weaklyContractible_coslices") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_6_6_13, kerodon_5_6_6_21, kerodon_7_2_1_1, kerodon_7_2_2_11, kerodon_7_2_3_1, kerodon_7_4_3_6")
Kerodon Proposition 7.4.3.11（[Tag 04K3](https://kerodon.net/tag/04K3)）。対応表の状態：一部。

*主張*　無限圏 $`C` への単体集合の射 $`F:C'\to C` が右共終であることは、任意の無限圏への余極限を持つ図式で $`F` に沿って制限しても同じ対象が余極限であることと同値である。任意の非可算正則基数 $`\kappa` の $`\kappa`-小空間値図式に限ってもよく、さらに余表現関手の制限が可縮な余極限を持つことだけを課してもよい。

isColimitCone\_iff\_restrict\_rightCofinalは、原文(1)⇒(2)の同じ極限対象Xを保つ制限余錐を直接与える。空間値の試験から共終性を検出する逆向きは含まない。

:::

:::corollary "kerodon_7_4_3_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLimitCone_iff_restrict_of_leftCofinal")
Kerodon Corollary 7.4.3.12（[Tag 03E7](https://kerodon.net/tag/03E7)）。対応表の状態：一部。

*主張*　単体集合の射 $`F:C'\to C` で、両端がある非可算正則基数 $`\kappa` に関して本質的に $`\kappa`-小さく、$`\lambda` の指数共終数が $`\kappa` 以上とする。$`F` が左共終であることは、任意の無限圏への極限図式を $`F^{\triangleleft}` で制限しても極限図式になることと同値であり、$`\lambda`-小空間を値域とする図式だけで検査してもよい。

Cを準圏に強めればisLimitCone\_iff\_restrict\_of\_leftCofinalは原文(1)⇒(2)を同じ指定極限錐の制限として直接返す。一般の単体集合Cおよび試験から共終性を得る逆向きは含まない。

:::

:::proposition "kerodon_7_4_3_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.isColimitCone_of_coconeFiberMap_weakEquivalence, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentTotalCoconeFiber_isWeakHomotopyEquivalence") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_6_7_3, kerodon_7_1_2_11, kerodon_7_3_8_26, kerodon_7_4_1_8, kerodon_7_4_2_14")
Kerodon Proposition 7.4.3.13（[Tag 05RW](https://kerodon.net/tag/05RW)）。対応表の状態：一部。

*主張*　非可算 $`\kappa` と全体が本質的に $`\kappa`-小さい左ファイブレーション $`E\to C` に対し、$`\mathscr F:C\to S_{<\kappa}` を $`\alpha:\underline{\Delta^0}_E\to\mathscr F|_E` が示す共変移送表現とする。余錐 $`\beta:\mathscr F\to\underline X_C` が余極限を与えることは、$`\alpha` と $`\beta|_E` の合成で定まる $`E\to\operatorname{Hom}_{S_{<\kappa}}(\Delta^0,X)` が弱ホモトピー同値であることと同値である。

Uを標準leftUnstraighteningProjection、γを指定余錐cのcoconeFiberMapとした場合、isColimitCone\_of\_coconeFiberMap\_weakEquivalenceは同じγについて(2)⇒(1)を直接返す。任意の表現αの比較と逆向きは含まない。

:::

:::corollary "kerodon_7_4_3_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal.isWeakHomotopyEquivalence") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_4_1_5, kerodon_4_1_3_3, kerodon_4_3_6_6, kerodon_4_5_3_12, kerodon_4_5_3_28, kerodon_4_6_4_1, kerodon_5_3_7_3, kerodon_5_6_7_2, kerodon_5_6_7_6, kerodon_7_2_1_5, kerodon_7_2_1_22, kerodon_7_2_3_1, kerodon_7_2_3_11, kerodon_7_4_3_13")
Kerodon Corollary 7.4.3.14（[Tag 02VJ](https://kerodon.net/tag/02VJ)）。対応表の状態：一部。

*主張*　$`C^{\triangleright}` 上の左ファイブレーション $`\bar E` と $`C` への引き戻し $`E` を取り、その引き戻しと $`C` が本質的に $`\kappa`-小さいよう非可算正則基数 $`\kappa` を選ぶ。$`E\to\bar E` が弱ホモトピー同値であること、左共終であること、$`\bar E` の $`\kappa`-小空間値共変移送表現が余極限図式であることは同値である。

IsLeftCofinal.isWeakHomotopyEquivalenceを同じ引き戻し包含E→Ēへ適用すると原文(2)⇒(1)を直接得る。輸送表現の余極限条件(3)や逆向きは含まない。

:::

:::corollary "kerodon_7_4_3_15"
Kerodon Corollary 7.4.3.15（[Tag 05JA](https://kerodon.net/tag/05JA)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左余終性の slice による判定と左輸送表現のデータはある。E⁰↪E の左余終性と C⁰ からの輸送表現の左 Kan 性の iff は見つからない。

:::

# 7.4.4 Limits of ∞-Categories

%%%
number := false
tag := "kerodon-7-4-4"
%%%

Kerodon [Tag 02T0](https://kerodon.net/tag/02T0)

:::proposition "kerodon_7_4_4_1" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_6_5_13, kerodon_7_4_4_6, kerodon_7_4_4_12")
Kerodon Proposition 7.4.4.1（[Tag 05RX](https://kerodon.net/tag/05RX)）。対応表の状態：なし。

QC内のpullback錐の極限性は原文のcocartesian切断準圏を頂点とする錐ではない。Space内の全切断の極限性もQC内への保存の比較を含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.catPullbackCone_isLimit`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.qCatPullbackInfinityCone_isLimit`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramSectionsCone_isLimit`

:::

:::corollary "kerodon_7_4_4_2"
Kerodon Corollary 7.4.4.2（[Tag 02TK](https://kerodon.net/tag/02TK)）。対応表の状態：なし。

原文は任意のQC値図式のcocartesian切断準圏そのものの極限性。引用のCat内のpullbackとSpace内の切断極限は別対象で、同じ錐への比較を欠く。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.catPullbackCone_isLimit`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramSectionsCone_isLimit`

:::

:::corollary "kerodon_7_4_4_3"
Kerodon Corollary 7.4.4.3（[Tag 02TL](https://kerodon.net/tag/02TL)）。対応表の状態：なし。

MathlibのHasLimits Catは通常圏の極限。原文のQCというcoherent nerve内の極限と比較する型がなく、そのまま小完備性と数えない。

宣言：`CategoryTheory.Cat.instHasLimits`

:::

:::theorem "kerodon_7_4_4_6" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_6_5_16, kerodon_5_6_6_17, kerodon_7_4_1_16, kerodon_7_4_1_22")
Kerodon Theorem 7.4.4.6（[Tag 02T8](https://kerodon.net/tag/02T8)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：始頂点での切断の評価は同値になる。二つの底にまたがる切断制限の同値と、輸送表現の QC\_\{\<κ\} 内の極限性を比較する iff は見つからない。

:::

:::definition "kerodon_7_4_4_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.exists_kanCocartesianSectionsEvaluate_section, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.InitialSectionLifting.cocartesianSectionsEvaluate_trivialKanFibration") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_3_1_23")
Kerodon Construction 7.4.4.9（[Tag 02TD](https://kerodon.net/tag/02TD)）。対応表の状態：一部。

*主張*　左錐 $`C^{\triangleleft}` 上の余デカルトファイブレーション $`\bar E` とその $`C` への引き戻し $`E` を取る。余デカルト切断の錐頂点評価の切断を選び、その後で $`C` に制限して、頂点ファイバーから $`E` の余デカルト切断への共変回折関手を得る。この関手は同型を除いて定まる。

底C◁を準圏に強めるとcocartesianSectionsEvaluate\_trivialKanFibrationとexists\_kanCocartesianSectionsEvaluate\_sectionは原文の指定evとその切断を直接構成する。θとの合成は書けるが、選択によらないFunctorIsoという残りの結論は含まない。

:::

:::proposition "kerodon_7_4_4_12" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_2_5_3, kerodon_4_3_6_5, kerodon_4_3_7_8, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_4_8, kerodon_5_2_3_1, kerodon_5_2_3_17, kerodon_5_3_1_21, kerodon_5_3_1_23, kerodon_5_6_7_2")
Kerodon Proposition 7.4.4.12（[Tag 02TG](https://kerodon.net/tag/02TG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：引き戻し後の切断の同定と始頂点評価の同値はある。任意の U を C◁ に延長し、C への切断制限を同値にする拡張の存在は見つからない。

:::

:::definition "kerodon_7_4_4_14" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_7_4_4_1")
Kerodon Variant 7.4.4.14（[Tag 05S1](https://kerodon.net/tag/05S1)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏 Cat の小極限と、始頂点での cocartesian 切断の評価同値を確認した。ecf(λ) の図式で QC\_\{\<λ\} の極限を切断で実現し、μ への包含で保つ型は見つからない。

:::

:::proposition "kerodon_7_4_4_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_of_isPullback_of_components, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.isLimitCone_of_isPullback_of_components, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.isLimitCone_pullback_of_components, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.isColimitCone_tensor_of_components, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.isLimitCone_tensor_of_components")
Kerodon Proposition 7.4.4.15（[Tag 06B4](https://kerodon.net/tag/06B4)）。対応表の状態：一部。

*主張*　無限圏値図式 $`\mathscr F` が無限圏の無限圏で極限を持つとする。その極限への右錐が、$`\mathscr F` の各値への射影で余極限図式になるなら、もとの右錐は極限圏で余極限図式である。

極限を二項積X⊗Yで表示する場合、isColimitCone\_tensor\_of\_componentsは同じ余錐q̄の二射影の余極限性からq̄の余極限性を直接返す。一般のQC値図式の極限は含まない。

:::

:::proposition "kerodon_7_4_4_16" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_colimitCone_pullback_with_snd, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.exists_limitCone_pullback_with_snd, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.exists_colimitCone_tensor_with_components, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.exists_limitCone_tensor_with_components")
Kerodon Proposition 7.4.4.16（[Tag 06B5](https://kerodon.net/tag/06B5)）。対応表の状態：一部。

*主張*　無限圏値図式 $`\mathscr F` の極限圏への図式 $`q` が各値への射影で余極限を持ち、$`\mathscr F` の全遷移関手が対応する余極限を保つとする。このとき $`q` に余極限があり、右錐が余極限図式であることは各射影で判定できる。

極限を二項積で表示する場合、exists\_colimitCone\_tensor\_with\_componentsは同じqの余極限を指定された成分余錐から直接構成し、tensor\_of\_componentsは原文の成分条件⇒余極限性を与える。任意の極限形状と逆向きは含まない。

:::

:::corollary "kerodon_7_4_4_17"
Kerodon Corollary 7.4.4.17（[Tag 06B6](https://kerodon.net/tag/06B6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：関手圏で点ごとの余極限性を判定する型と、通常圏 Cat の小極限の型はある。各遷移が K-余極限を保つ∞圏図式の極限内で K-余完備性と点ごとの判定を同時に得る型は見つからない。

:::

# 7.4.5 Colimits of ∞-Categories

%%%
number := false
tag := "kerodon-7-4-5"
%%%

Kerodon [Tag 02UN](https://kerodon.net/tag/02UN)

:::proposition "kerodon_7_4_5_1" (uses := "kerodon_1_1_0_6, kerodon_5_1_1_1, kerodon_5_1_4_1")
Kerodon Proposition 7.4.5.1（[Tag 05S2](https://kerodon.net/tag/05S2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：辺の局所化の述語と通常圏 Cat の余完備性はある。輸送表現の余極限を U-cocartesian 辺の局所化と特徴付ける iff は見つからない。

:::

:::corollary "kerodon_7_4_5_2"
Kerodon Corollary 7.4.5.2（[Tag 02V0](https://kerodon.net/tag/02V0)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：空間値図式には全空間の Kan 置換を用いた余極限がある。任意の QC 値図式で全空間の cocartesian 辺だけを反転する局所化を余極限とする型は見つからない。

:::

:::corollary "kerodon_7_4_5_3"
Kerodon Corollary 7.4.5.3（[Tag 02V1](https://kerodon.net/tag/02V1)）。対応表の状態：なし。

通常圏CatのHasColimitsは原文のQC内の∞圏的な小余完備性を直接結論しない。coherent nerveの余極限比較が必要。

宣言：`CategoryTheory.Cat.instHasColimits`

:::

:::corollary "kerodon_7_4_5_5"
Kerodon Corollary 7.4.5.5（[Tag 039J](https://kerodon.net/tag/039J)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：空間値の全空間による余極限はある。通常圏添字の QCat 値厳密図式の weighted nerve を cocartesian 辺で局所化し、QC 内の余極限に同定する型は見つからない。

:::

:::definition "kerodon_7_4_5_8" (uses := "kerodon_1_1_0_6, kerodon_5_1_1_1, kerodon_5_1_4_1")
Kerodon Definition 7.4.5.8（[Tag 02UP](https://kerodon.net/tag/02UP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：cocartesian な成分を持つ円柱の持ち上げを構成する。C▷ の終点ファイバーへの指定 Rf がこの形の円柱を持つことを、Rf 自体の性質として表す定義は見つからない。

:::

:::proposition "kerodon_7_4_5_10" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_2_2_13, kerodon_7_4_5_8")
Kerodon Proposition 7.4.5.10（[Tag 02UR](https://kerodon.net/tag/02UR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：指定底円柱に対する cocartesian な持ち上げの存在を確認した。終点ファイバーへの Rf の条件を定義し、同じ関手圏の同型類でその条件を特徴付ける型は見つからない。

:::

:::theorem "kerodon_7_4_5_13" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_1_3_3, kerodon_4_3_6_4, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_6_0_2, kerodon_5_6_5_13, kerodon_5_6_7_3, kerodon_7_2_1_3, kerodon_7_4_5_8, kerodon_7_4_5_10, kerodon_7_4_5_18, kerodon_7_4_6_2, kerodon_7_4_6_3")
Kerodon Theorem 7.4.5.13（[Tag 02UU](https://kerodon.net/tag/02UU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：局所化の述語と空間値の全空間モデルを確認した。QC\_\{\<λ\} での指定輸送余錐の余極限性と refraction の局所化性を比較し、逆向きだけに cf(λ) を課す型は見つからない。

:::

:::corollary "kerodon_7_4_5_17"
Kerodon Corollary 7.4.5.17（[Tag 039P](https://kerodon.net/tag/039P)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：局所化からの関手の延長と左 Kan 性の述語を確認した。QC 内の輸送余錐の余極限性と cocartesian 辺の反転から、E からの左 Kan 性を得る型は見つからない。

:::

:::proposition "kerodon_7_4_5_18" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_2_3_1, kerodon_5_2_3_17, kerodon_6_3_2_1")
Kerodon Proposition 7.4.5.18（[Tag 02UX](https://kerodon.net/tag/02UX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：既存のファイブレーション上の円柱は持ち上げられ、局所化は別に定義される。底を C▷ へ延長し、新しい頂点ファイバーへの refraction が局所化となる同時存在は見つからない。

:::

:::proposition "kerodon_7_4_5_20"
Kerodon Proposition 7.4.5.20（[Tag 05S5](https://kerodon.net/tag/05S5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：辺の局所化と通常圏 Cat の小余極限はある。濃度境界つきの QC 値輸送表現に対し局所化を余極限とし、任意の μ≥λ への包含で保つ型は見つからない。

:::

:::corollary "kerodon_7_4_5_22" (uses := "kerodon_1_4_0_1")
Kerodon Corollary 7.4.5.22（[Tag 03U9](https://kerodon.net/tag/03U9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏 Cat の小余完備性と CatInfinity の準圏性は別々にある。cf(λ) の形状の余完備性を QC\_\{\<λ\} に与え、より大きい濃度への包含で保つ型は見つからない。

:::

:::corollary "kerodon_7_4_5_23"
Kerodon Corollary 7.4.5.23（[Tag 03U8](https://kerodon.net/tag/03U8)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏 Cat の小余完備性はある。本質的 κ-small な準圏に制限した QC の小余完備性と、λ への包含による保存を同時に述べる型は見つからない。

:::

# 7.4.6 Proof of the Refraction Criterion

%%%
number := false
tag := "kerodon-7-4-6"
%%%

Kerodon [Tag 02V2](https://kerodon.net/tag/02V2)

:::lemma_ "kerodon_7_4_6_1" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_6_8_18, kerodon_4_7_3_11")
Kerodon Lemma 7.4.6.1（[Tag 02V3](https://kerodon.net/tag/02V3)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：CatInfinity の inner horn 充填性と辺の局所化の述語はある。0番目の外ホーンで、0→1 の局所化と他の辺の反転を仮定した充填は見つからない。

:::

:::proposition "kerodon_7_4_6_2" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_4_1_5, kerodon_4_6_8_15, kerodon_5_1_1_1, kerodon_5_1_2_1, kerodon_5_1_2_3, kerodon_5_1_4_1, kerodon_5_1_4_14, kerodon_5_2_3_17, kerodon_5_6_5_13, kerodon_5_6_7_1, kerodon_7_4_5_10, kerodon_7_4_6_1")
Kerodon Proposition 7.4.6.2（[Tag 02V4](https://kerodon.net/tag/02V4)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：局所化と空間値の全空間による余極限の候補を確認した。指定 refraction の局所化性から κ-small な QC 値輸送余錐が余極限となる型は見つからない。

:::

:::lemma_ "kerodon_7_4_6_3" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_1_5_4_13, kerodon_5_1_1_1, kerodon_5_1_2_4, kerodon_5_1_4_1, kerodon_5_6_7_6, kerodon_6_3_1_1")
Kerodon Lemma 7.4.6.3（[Tag 02V7](https://kerodon.net/tag/02V7)）。対応表の状態：なし。

全空間の前合成同値はあるが、原文は指定cocartesian辺を両側で反転した局所化の間の誘導射。局所化と指定辺の比較を引用の型に持たない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullback_snd_isPrecompositionEquivalence_of_innerAnodyne`

:::

