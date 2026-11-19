import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftAnodyneLimitRestriction
import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
import SerrePositivity.InfinityCategories.HTT.Section5_1_2.FunctorColimitConeExistence
import SerrePositivity.InfinityCategories.HTT.Section5_1_2.FunctorColimitEvaluation
import SerrePositivity.InfinityCategories.HTT.Section5_1_4.FunctorIsoExtension
import SerrePositivity.InfinityCategories.HTT.Section5_1_4.WeakContractibleOpposite
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CovariantRepresentableInfinity
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningRepresentation
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorBaseChange
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.F1CompactUniverseColimits
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.RepresentableRetractions
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.YonedaEvaluationClassification
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafDensityLeftKanCriterion
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafNativeDensityKan
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.FunctorPointwiseColimitCriterion
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCanonicalMapping
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CartesianInitialBoundary
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Colimit
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorRelativeInitial
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialOpposite
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialBoundary
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalVertices
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.PresheafDensity
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.ColimitRetractions
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Completion
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionCanonicalColimits
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionCofinal
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionExtension
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionOppositeGeneral
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionSlice
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionTerminalContraction
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SliceComplete
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.UniversalProperty
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ElementsDiagram
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafAllSmallLimits
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafPointwiseColimits
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RelativeFunctorConstFiberIso
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaInfinityFullyFaithful
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaLimits

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 5.1 ∞-Categories of Presheaves" =>
%%%
number := false
tag := "htt-5-1"
%%%

HTT 5.1 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

:::definition "htt_5_1_0_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity")
*HTT 定義 5.1.0.1*　空間値前層の準圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=333)）。対応表の状態：本体にある。

*主張*　単体的集合 $`S` 上の前層 ∞ 圏 $`\mathcal P(S)` は $`\operatorname{Fun}(S^{\mathrm{op}},\mathcal S)` である。

仮定：任意の小さい単体集合 S（HTT と一致）。結論：宇宙を合わせた Fun(Sᵒᵖ,𝒮) を前層準圏として定める（一致）。

各頂点に空間を与え、$`S` の辺を反対向きに作用させる。関手圏を取るので、その作用と同時に高次の整合性も前層のデータとなる。

:::

:::proposition "htt_5_1_0_2" (lean := "CategoryTheory.ihom")
*HTT 注意 5.1.0.2*　一般の準圏を値とする前層（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=333)）。対応表の状態：本体にある。

*主張*　任意の ∞ 圏 $`\mathcal C` に対し $`\operatorname{Fun}(S^{\mathrm{op}},\mathcal C)` を $`\mathcal C` 値前層の圏と呼べるが、値域を省いた前層はここでは空間値を指す。

仮定：任意の単体集合 S と準圏 C（Lean が弱い：内部 Hom の構成自体は準圏性を要求しない）。結論：Sᵒᵖ を始域とする内部 Hom の値が同じ Fun(Sᵒᵖ,C) を与える（一致）。

通常の集合値前層では集合の射しか記録しない。空間値を既定にすると、制限写像の間のホモトピーも前層の比較に含まれる。

:::

# 5.1.2 Colimits in ∞-Categories of Functors

%%%
number := false
tag := "htt-5-1-2"
%%%

:::lemma_ "htt_5_1_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialBoundaryLifting_of_isInitialVertex_fiber, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorRelativeInitial.initialBoundaryLifting_ihom_of_pointwise, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting.isInitialVertex_fiber") (uses := "htt_1_1_2_4, htt_2_1_3_4, htt_2_4_2_1, htt_3_3_1_5")
*HTT 補題 5.1.2.1*　点ごとの始対象を持つ切断の始対象性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=336)）。対応表の状態：一部（stronger-hyp）。

*主張*　Cartesian ファイブレーション $`Y\to S` の切断が各頂点ファイバーで始対象を選んでいれば、その切断は切断 ∞ 圏の始対象である。

KB-W2原文・型再照合：仮定：Cartesian ファイブレーションの切断が各繊維で始対象（Lean が強い：底と全空間を準圏とする）。結論：各繊維の始対象から相対始点境界充填を得て、内部 Hom の同じ境界充填を恒等底図式の繊維に制限すると、指定切断が切断準圏の始対象となる（一致する場合）。

異なる切断との比較は底と両立する必要がある。ファイバーごとの始対象性を Cartesian な移送と組み合わせて、切断全体での始対象性にする。

:::

:::proposition "htt_5_1_2_2" (lean := "SerrePositivity.InfinityCategories.HTT.Section5_1_2.exists_colimitCone_functor_of_pointwise, SerrePositivity.InfinityCategories.HTT.Section5_1_2.isColimitCone_functor_evaluation_of_pointwise_exists, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isColimitCone_of_pointwise, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeIso, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.relativeFunctorConstFiberIso") (uses := "htt_1_1_2_4, htt_1_2_13_4, htt_5_1_2_1")
*HTT 命題 5.1.2.2*　切断準圏の点ごとの余極限（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=336)）。対応表の状態：一部（special）。

*主張*　Cartesian ファイブレーションの切断 ∞ 圏の図式が各頂点ファイバーで余極限を持つなら、各点で余極限となる切断の余錐が存在し、任意の指定余錐の余極限性は各点で判定できる。

KB-W2原文・型再照合：仮定：Cartesian ファイブレーションと切断準圏の図式が各繊維で余極限を持つ（Lean が強い：一定準圏を一点から引き戻した射影の場合）。結論：この切断準圏を底上の相対関手空間の同型で関手準圏に同定し、同じ図式の点ごとの余極限余錐の存在と、任意の余錐の余極限性の点ごとの判定を得る（一致する場合。一般の Cartesian ファイブレーションは含まない）。

各点の余極限は最初には別々に与えられている。定理はそれらを底の射と整合する切断の余錐にまとめ、すでにある余錐についても点ごとの判定を与える。

:::

:::corollary "htt_5_1_2_3" (lean := "SerrePositivity.InfinityCategories.HTT.Section5_1_2.exists_colimitCone_functor_of_pointwise, SerrePositivity.InfinityCategories.HTT.Section5_1_2.isColimitCone_functor_evaluation_of_pointwise_exists, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isColimitCone_of_pointwise")
*HTT 系 5.1.2.3*　関手準圏の余極限の存在と各点での判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=337)）。対応表の状態：本体にある。

*主張*　$`\mathcal C` が $`K`-型の余極限を持てば $`\operatorname{Fun}(S,\mathcal C)` も持ち、その余錐が余極限であることは各頂点での評価で判定できる。

仮定：準圏 C に指定形状 K の全余極限が存在する（HTT と一致。Lean の存在には各評価図式の余極限だけで足りる）。結論：Fun(S,C) の指定図式の余極限が存在し、指定余錐が余極限であることはすべての評価余錐の余極限性と同値（一致）。

定値のファイバー $`\mathcal C` を持つ射影を考えると、切断が関手になる。評価した余錐をそれぞれ比較し、関手準圏における同じ余錐の普遍性を調べる。

:::

:::corollary "htt_5_1_2_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinity_hasLimit, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinity_hasColimit")
*HTT 系 5.1.2.4*　前層準圏の全小極限と全小余極限（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=337)）。対応表の状態：本体にある。

*主張*　任意の単体的集合 $`S` の空間値前層 ∞ 圏 $`\mathcal P(S)` には小さい極限と余極限がある。

仮定：任意の小さい単体集合 S と小さい図式形状（HTT と一致）。結論：同じ P(S) 上のすべての小さい図式が極限と余極限を持つ（一致）。

空間の圏がそれらを持つので、関手圏では各点の評価で計算できる。添字は $`S^{\mathrm{op}}` だが、点ごとの極限の議論では形を反転しても同じように適用できる。

:::

# 5.1.3 Yoneda’s Lemma

%%%
number := false
tag := "htt-5-1-3"
%%%

:::proposition "htt_5_1_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_isFullyFaithful")
*HTT 命題 5.1.3.1*　準圏の米田埋め込みの充満忠実性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=338)）。対応表の状態：一部（special）。

*主張*　単体的集合 $`K` の Yoneda 埋め込み $`j:K\to\mathcal P(K)` は充満忠実である。

KB-W2原文・型再照合：仮定：小さい単体集合 K（Lean が強い：K は準圏）。結論：同じ空間値前層準圏への米田写像が写像空間上で充満忠実（一致する場合）。

対象をその対象へ入る写像を集めた前層へ送る。この比較では元の対象間の写像型を、対応する表現可能前層間の自然変換の写像型として回復できる。

:::

:::proposition "htt_5_1_3_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_isLimit")
*HTT 命題 5.1.3.2*　米田埋め込みの小極限保存（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=338)）。対応表の状態：本体にある。

*主張*　小さい ∞ 圏の Yoneda 埋め込みは、元の圏に存在する小さい極限を保つ。

仮定：小さい準圏 C の指定した小極限錐（HTT と一致）。結論：同じ錐を米田埋め込みで写した全錐が前層準圏で極限となる（一致）。

各対象からの写像空間は極限の普遍性を検出する。Yoneda の像を各対象で評価すると、その同じ写像空間の比較が現れる。

:::

# 5.1.4 Idempotent Completions

%%%
number := false
tag := "htt-5-1-4"
%%%

:::definition "htt_5_1_4_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion")
*HTT 定義 5.1.4.1*　冪等完備化を与える関手の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=339)）。対応表の状態：本体にある。

*主張*　$`\mathcal C\to\mathcal D` が冪等完備化であるとは、充満忠実で、$`\mathcal D` が冪等完備であり、その全対象が $`\mathcal C` から来る対象のレトラクトであることをいう。

仮定：準圏間の関手（Lean が弱い：述語自体は任意の単体的写像を受け取る）。結論：標的の冪等完備性、充満忠実性、標的の各対象が像の対象の retract となる条件を同時に課す（一致）。

既存の対象間の写像は保持し、追加対象には既存対象からの分裂表示を要求する。この二条件と冪等完備性により、追加する対象の範囲が定まる。

:::

:::proposition "htt_5_1_4_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda_isIdempotentCompletion")
*HTT 命題 5.1.4.2*　前層準圏内の冪等完備化の存在（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=339)）。対応表の状態：本体にある。

*主張*　任意の ∞ 圏は冪等完備化を持つ。

仮定：小さい準圏 C（HTT と一致。必要なら原典と同じ宇宙拡大を行う）。結論：同じ米田埋め込みの retract 閉包への因子化が冪等完備化を与える（一致）。

前層の中で元の表現可能対象とそのレトラクトを集める方法がある。すでにある対象の写像を変えず、冪等辺の分裂に必要な対象を取り出す。

:::

:::lemma_ "htt_5_1_4_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.sliceOver_isIdempotentComplete, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.sliceUnder_isIdempotentComplete")
*HTT 補題 5.1.4.3*　冪等完備準圏のスライスとコスライス（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=340)）。対応表の状態：本体にある。

*主張*　$`\mathcal C` が冪等完備なら、任意の図式 $`p` の上の圏 $`\mathcal C_{/p}` と下の圏 $`\mathcal C_{p/}` も冪等完備である。

仮定：冪等完備準圏と任意の単体集合形状の図式（HTT と一致）。結論：同じ図式上のスライスとコスライスはともに冪等完備（一致）。

スライスに現れる冪等子は頂点の冪等子だけでなく、図式への錐または余錐との整合性を持つ。元の圏での分裂をその指定された脚と両立させる。

:::

:::lemma_ "htt_5_1_4_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.sliceOver")
*HTT 補題 5.1.4.4*　スライスへの引き戻しによる冪等完備化（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=340)）。対応表の状態：一部（stronger-hyp）。

*主張*　冪等完備化 $`\mathcal C\to\mathcal D` と $`\mathcal D` 内の図式 $`p` に対し、$`\mathcal C\times_{\mathcal D}\mathcal D_{/p}\to\mathcal D_{/p}` も冪等完備化である。

KB-W2原文・型再照合：仮定：冪等完備化を与える関手 f と標的の図式（Lean が強い：f に内ファイブレーション性を要求）。結論：同じスライス射影に沿って引き戻した関手も冪等完備化を与える（一致する場合）。

始域は $`\mathcal D` 内の錐の頂点が $`\mathcal C` から来るものを集める。図式自体が $`\mathcal C` に入ることは要求しない。

:::

:::lemma_ "htt_5_1_4_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.isWeaklyContractible_of_terminal, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.op_general, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isInitialVertex_iff_isTerminalVertex_op, SerrePositivity.InfinityCategories.HTT.Section5_1_4.isWeaklyContractible_op_iff")
*HTT 補題 5.1.4.5*　始対象を持つ冪等完備化の元の弱可縮性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=340)）。対応表の状態：本体にある。

*主張*　冪等完備化 $`\mathcal C\to\mathcal D` の終域が始対象を持てば、$`\mathcal C` は単体的集合として弱可縮である。

仮定：冪等完備化を与える関手と標的の始対象（HTT と一致）。結論：反対射も同じ冪等完備化となり、始対象を反対圏の終対象へ移した弱可縮性の判定から、元の同じ始域の弱可縮性を得る（一致）。

始対象がそのまま $`\mathcal C` に入る必要はない。$`\mathcal C` の対象のレトラクトとして与えられる情報から、$`\mathcal C` の弱ホモトピー型が点になることを得る。

:::

:::lemma_ "htt_5_1_4_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.isRightCofinal")
*HTT 補題 5.1.4.6*　冪等完備化の共終性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=341)）。対応表の状態：一部（stronger-hyp）。

*主張*　冪等完備化を与える関手は共終である。

KB-W2原文・型再照合：仮定：冪等完備化を与える関手（Lean が強い：内ファイブレーション）。結論：同じ関手は余極限を計算する向きに共終である（一致する場合）。

各終域対象について、そこから元の圏の像への射を集めるスライスを調べる。冪等完備化でのレトラクト表示が、それらのコンマ圏の弱可縮性を支える。

:::

:::lemma_ "htt_5_1_4_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.canonicalCocones_isColimit")
*HTT 補題 5.1.4.7*　冪等完備化からの全関手の左 Kan 性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=341)）。対応表の状態：本体にある。

*主張*　充満包含 $`\mathcal C_0\subseteq\mathcal C` が冪等完備化を与えるなら、任意の関手 $`F:\mathcal C\to\mathcal D` は $`F|_{\mathcal C_0}` の左 Kan 拡張である。

仮定：充満部分圏の包含が冪等完備化である準圏からの任意の関手（HTT と一致。Lean の単射・内ファイブレーションの条件は同じ全部分複体の包含で満たされる）。結論：同じ包含に沿う全標準局所余錐が余極限であり、元の関手は制限の左 Kan 拡張（一致）。

冪等完備化で追加される対象はレトラクトで、その分裂を表す射は任意の関手で保たれる。これが点ごとの左 Kan 拡張の普遍性にも使える。

:::

:::lemma_ "htt_5_1_4_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.exists_extension_to_complete_of_full_inclusion, SerrePositivity.InfinityCategories.HTT.Section5_1_4.functorIsoExtension_nonempty")
*HTT 補題 5.1.4.8*　冪等完備な標的への関手の延長（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=341)）。対応表の状態：本体にある。

*主張*　冪等完備化を与える充満包含 $`\mathcal C_0\subseteq\mathcal C` と冪等完備な $`\mathcal D` について、$`\mathcal C_0\to\mathcal D` の任意の関手は $`\mathcal C` へ延長できる。

仮定：充満部分圏の包含による冪等完備化と冪等完備な標的（HTT と一致）。結論：元の関手の制限と自然同型な延長を得て、その同型を単射上で延長し、制限が元の関手に厳密に等しい延長へ移す（一致）。

元の関手で送った冪等子を標的で分裂できるため、追加対象に値を与えられる。主張はこの操作を各対象でばらばらに行うだけでなく、全体の関手として延長できること。

:::

:::proposition "htt_5_1_4_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.pre_isQCatEquivalence")
*HTT 命題 5.1.4.9*　冪等完備化の関手準圏による普遍性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=341)）。対応表の状態：本体にある。

*主張*　冪等完備化 $`\mathcal C\to\mathcal D` と冪等完備な $`\mathcal E` に対し、前合成 $`\operatorname{Fun}(\mathcal D,\mathcal E)\to\operatorname{Fun}(\mathcal C,\mathcal E)` は ∞ 圏の同値である。

仮定：冪等完備化を与える関手と冪等完備な標的（HTT と一致）。結論：同じ関手への前合成が二つの全関手準圏の間の準圏同値となる（一致）。

元の関手を延長できるだけでなく、自然変換とその高次比較も制限で回復する。この関手圏の同値が、分裂を加える構成の普遍性になる。

:::

# 5.1.5 The Universal Property of P(S)

%%%
number := false
tag := "htt-5-1-5"
%%%

:::definition "htt_5_1_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices, SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits")
*HTT 記法 5.1.5.1*　小余極限を保つ前層関手の充満部分圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=342)）。対応表の状態：本体にある。

*主張*　$`\operatorname{Fun}^{L}(\mathcal P(S),\mathcal C)` は、小さい余極限を保つ関手を対象とする関手 ∞ 圏の充満部分圏である。

仮定：前層準圏 P(S) と準圏 C（HTT と一致）。結論：全関手準圏の頂点に同じ全小余極限保存条件を課した充満部分複体が、指定された Funᴸ(P(S),C) を構成する（一致）。

対象に余極限の保存を課し、対象間の写像空間は関手圏からそのまま取る。後の随伴関手定理により、前層圏から出る場合に左随伴を集める記法とも整合する。

:::

:::lemma_ "htt_5_1_5_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.yonedaEvaluation_classificationIso, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.yonedaInfinityMap_evaluationIso") (uses := "htt_2_0_0_3")
*HTT 補題 5.1.5.2*　前層評価の米田対象による余表現（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=342)）。対応表の状態：一部（special）。

*主張*　小さい $`S` の頂点 $`s` での前層の評価 $`F\mapsto F(s)` を分類する左ファイブレーションは、Yoneda 前層 $`j(s)` で余表現される。

KB-W2原文・型再照合：仮定：小さい単体集合 S と指定頂点（Lean が強い：S は準圏）。結論：同じ評価を分類する左ファイブレーションの全分類関手が、元の米田対象からの全共変 Hom と自然同型となる（一致する場合）。

評価結果は空間である。前層の圏で $`j(s)` から $`F` への写像空間を作ると、この同じ空間を前層 $`F` について関手的に得る。

:::

:::lemma_ "htt_5_1_5_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafNativeDensityKan.presheafIdentity_canonicalColimits, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafNativeDensityKan.presheafIdentity_isLeftKanExtension") (uses := "htt_5_1_2_2, htt_5_1_3_1, htt_5_1_5_2")
*HTT 補題 5.1.5.3*　前層準圏の恒等関手の米田左 Kan 性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=343)）。対応表の状態：一部（special）。

*主張*　小さい $`S` の Yoneda 埋め込み $`j:S\to\mathcal P(S)` に沿う $`j` 自身の左 Kan 拡張は、前層 ∞ 圏の恒等関手である。

KB-W2原文・型再照合：仮定：小さい単体集合 S（Lean が強い：S は準圏）。結論：同じ米田写像に沿う恒等関手の標準局所余錐がすべて余極限となり、同じ恒等単位付きの左 Kan 条件を満たす（一致する場合）。

前層 $`F` への表現可能前層の射を使って点ごとの添字圏を作る。主張は、その添字で表現可能前層をまとめた余極限が同じ $`F` に戻るというもの。

:::

:::lemma_ "htt_5_1_5_4" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isLimitCone_iff_restrict_of_leftAnodyne") (uses := "htt_1_1_2_4, htt_1_2_13_4, htt_3_3_3_4, htt_5_1_2_2, htt_5_1_3_2")
*HTT 補題 5.1.5.4*　共変同値の極限保存による判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=344)）。対応表の状態：一部（stronger-hyp）。

*主張*　$`S` 上の単体的写像 $`A\to B` が共変同値であることは、$`S` 上の図式の $`B` への制限の極限錐が $`A` に制限しても極限となることと同値で、その試験は空間値図式だけで足りる。

KB-W2原文・型再照合：仮定：S 上の写像 A→B が共変同値（Lean が強い：底を忘れた同じ写像が単射かつ左アノダイン）。結論：任意の準圏値図式の B 上の指定極限錐を同じ A へ制限しても極限となる（条件 (2) が一致する場合。相対共変同値での三条件の同値は含まない）。

比較するのは同じ頂点を持つ指定錐の二つの形である。空間値を試験する条件が、任意の値域の写像空間を用いる極限判定を支える。

:::

:::lemma_ "htt_5_1_5_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheaf_densityImages_canonicalColimits, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheaf_densityImages_isLeftKanExtension, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafDensityCocone_isColimit") (uses := "htt_1_1_2_4, htt_2_4_7_12, htt_4_3_2_13, htt_5_1_2_2, htt_5_1_5_2, htt_5_1_5_3, htt_5_1_5_4")
*HTT 補題 5.1.5.5*　前層上の左 Kan 関手と小余極限保存（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=344)）。対応表の状態：一部（direction）。

*主張*　小さい $`S` の前層からの関手は、表現可能前層への制限の左 Kan 拡張であるとき、かつそのときに限り小さい余極限を保ち、標的が小さい余極限を持てば任意の制限関手はそのように延長できる。

KB-W2原文・型再照合：仮定：P(S) から任意の準圏への関手が小余極限を保つ（Lean が強い：S は準圏）。結論：同じ密度余錐の像が余極限なので、元の米田制限に沿う全標準局所余錐が余極限となり、恒等単位の左 Kan 条件を満たす（(1) の保存から Kan への方向が一致。逆向きと (2) の存在は含まない）。

まず表現可能対象への値を決める。他の前層はそのような対象の余極限で組み立てるので、余極限を保つ延長の値はその組み立てに従う。

:::

:::theorem "htt_5_1_5_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheaf_densityImages_canonicalColimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonical_pinchedHomMap_equivalence") (uses := "htt_1_1_2_4, htt_4_3_2_16, htt_5_1_5_5")
*HTT 定理 5.1.5.6*　前層準圏の自由余完備化としての普遍性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=345)）。対応表の状態：一部（component）。

*主張*　小さい $`S` と小さい余極限を持つ $`\mathcal C` について、Yoneda への制限は $`\operatorname{Fun}^{L}(\mathcal P(S),\mathcal C)\simeq\operatorname{Fun}(S,\mathcal C)` を与える。

KB-W2原文・型再照合：仮定：P(S) から小余完備な準圏への小余極限保存関手二つ（Lean が強い：S は準圏）。結論：同じ米田写像への制限は、この二関手間の全写像空間で同値となり、指定 Funᴸ 上で充満忠実である（結論の一部に一致。制限の本質的全射性を含む全関手準圏の同値は含まない）。

左辺には余極限を保つ延長とその変換を集める。右辺だけ指定すればそれらを復元できるという形で、$`\mathcal P(S)` を自由な小余極限完備化とみなせる。

:::

:::definition "htt_5_1_5_7" (lean := "CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCocone_isColimit_iff")
*HTT 定義 5.1.5.7*　小余極限で閉じる充満部分圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=345)）。対応表の状態：一部（special）。

*主張*　充満部分圏が余極限で閉じるとは、そこに値を取る小図式の大きい圏での余極限も含むことをいい、対象の族が余極限で生成するとは、その族を含む余極限閉な充満部分圏が全体になることである。

KB-W2原文・型再照合：仮定：準圏の充満部分圏（Lean が強い：通常の圏の神経と通常圏の神経を形状とする図式）。結論：同じ部分圏内の図式の任意の余極限余錐の頂点が再びその部分圏に属するという閉性を定める（一致する場合。任意の単体集合形状は含まない）。

生成の判定では、族を含み余錐の頂点を落とさない部分圏を試験する。単体的集合からの写像については、その頂点の像を生成対象とみなす。

:::

:::corollary "htt_5_1_5_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafDensityPresentation, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafElementsYonedaDiagram_vertex")
*HTT 系 5.1.5.8*　米田像による前層準圏の小余極限生成（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=346)）。対応表の状態：一部（special）。

*主張*　小さい $`S` の Yoneda 像は $`\mathcal P(S)` を小さい余極限で生成する。

KB-W2原文・型再照合：仮定：小さい単体集合 S（Lean が強い：S は準圏）。結論：任意の元の前層は、頂点が元の米田像である小さい元の圏上の図式の余極限として表示される（一致する場合）。

表現可能前層から一般の前層へ向かう射を添字にして、その前層を組み立てる。したがって表現可能対象をすべて含み小余極限で閉じる部分圏に、すべての前層が入る。

:::

# 5.1.6 Complete Compactness

%%%
number := false
tag := "htt-5-1-6"
%%%

:::proposition "htt_5_1_6_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram")
*HTT 注意 5.1.6.1*　大きい準圏上の共変 Hom と宇宙拡大（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=346)）。対応表の状態：本体にある。

*主張*　大きい単体的集合でも頂点による余表現の構成を使えるが、その場合は大きい Kan 複体も含む $`\widehat{\mathcal S}` を値域とする。

仮定：任意に選んだ宇宙内の準圏とその対象（HTT と一致）。結論：その宇宙に応じた大きい空間の準圏への全共変 Hom を作り、小さい空間から一段大きい空間への指定宇宙変更を用いる（一致）。

余表現関手は頂点からの写像型を記録する。添字が大きいとその値が小さい空間とは限らないため、値域の大きさを明示する。

:::

:::definition "htt_5_1_6_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity, SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits")
*HTT 定義 5.1.6.2*　完全コンパクト対象の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=346)）。対応表の状態：本体にある。

*主張*　小さい余極限を持つ ∞ 圏の対象 $`C` は、余表現関手 $`\operatorname{Map}(C,-)` がすべての小さい余極限を保つとき完全コンパクトという。

仮定：小余極限を持つ準圏とその対象 x（HTT と一致）。結論：元の全共変 Hom(x,−) に全小余極限保存の述語を適用すると、指定余錐の同じ像を量化する完全コンパクト性の条件を得る（一致）。

filtered 余極限だけでなく、一般の小さい形での余極限を試験する。前層 ∞ 圏では、表現可能前層からの写像は評価として読めるため、この強い条件と両立する。

:::

:::lemma_ "htt_5_1_6_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isColimitCone_of_functorRetraction")
*HTT 補題 5.1.6.3*　余極限図式の retract の余極限性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=347)）。対応表の状態：本体にある。

*主張*　同じ形の余錐の圏で余極限図式のレトラクトになっている余錐は、余極限図式である。

仮定：同じ準圏を値域とする二つの全余錐と、その全関手準圏内での retract、後者の余極限性（HTT と一致）。結論：同じ元の retract 余錐も余極限である（一致）。

図式の頂点だけでなく余錐全体についてレトラクトを仮定する。普遍性を検査する写像空間の比較も同じようにレトラクトになり、同値性が伝わる。

:::

:::lemma_ "htt_5_1_6_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.covariantRepresentable_retract, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isColimitCone_of_functorRetraction")
*HTT 補題 5.1.6.4*　完全コンパクト対象の retract 閉性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=347)）。対応表の状態：本体にある。

*主張*　完全コンパクトな対象のレトラクトは完全コンパクトであり、特にこの性質は同値で不変である。

仮定：対象 x が y の retract で、Hom(y,−) が全小余極限を保つ（HTT と一致）。結論：同じ全共変 Hom(x,−) は Hom(y,−) の自然な retract となる。任意の元の余極限余錐への前合成と同じ全余錐の retract 判定により Hom(x,−) もそれを保つ（一致）。

余表現関手を取った後もレトラクト関係があり、各余極限を試験する比較が元の対象の比較のレトラクトになる。

:::

:::definition "htt_5_1_6_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram, SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits")
*HTT 定義 5.1.6.5*　完全コンパクトな左ファイブレーション（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=348)）。対応表の状態：本体にある。

*主張*　小さい余極限を持つ ∞ 圏上の左ファイブレーションが完全コンパクトであるとは、それを分類する空間値関手が小さい余極限を保つことをいう。

仮定：小余極限を持つ準圏上の左ファイブレーション（HTT と一致）。結論：同じ左ファイブレーションを分類する全空間値関手に小余極限保存の述語を適用することで、原典の完全コンパクト性の条件を定める（一致）。

保存を判定するのは全空間の射影そのものではなく、各ファイバーと共変移送を対応させる分類関手である。

:::

:::proposition "htt_5_1_6_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.yonedaInfinityMap_evaluationIso, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinity_evaluation_isColimit, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram_map_isColimit, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.covariantRepresentable_retract, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isColimitCone_of_functorRetraction") (uses := "htt_5_1_2_2, htt_5_1_5_2, htt_5_1_5_3, htt_5_1_6_4")
*HTT 命題 5.1.6.8*　前層の完全コンパクト性と米田像の retract（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=349)）。対応表の状態：一部（component）。

*主張*　小さい $`S` 上の前層が完全コンパクトであることは、ある表現可能前層 $`j(s)` のレトラクトであることと同値である。

KB-W2原文・型再照合：仮定：指定前層が元の米田像の retract（Lean が強い：S は準圏）。結論：同じ全共変 Hom は、準圏を形状とする任意の小余極限を保存する。米田評価と指定宇宙変更の同型、および retract の余極限判定で得る（(2) からの保存のうち準圏形状の部分に一致。任意の単体集合形状と (1)⇒(2) は含まない）。

表現可能前層からの写像は評価なので、余極限を点ごとに計算できる。逆向きでは、前層自身を表現可能前層の余極限として書き、その恒等射を完全コンパクト性で一つの段へ因子分解する。

:::

