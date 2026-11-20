-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.HTT.Section3_3_4.CoherentTotalCocone
import SerrePositivity.InfinityCategories.HTT.Section3_3_4.CoherentTotalObject
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.SpaceSectionsObject
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationEquivalenceLifting
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningInfinityReconstruction
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraightening
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaces
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.RightFibrationFiberCriterion
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CoherentTotalColimit
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.DiagramSectionsCone
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SpaceSmallLimits
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePullbackPathLifting

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 3.3 Applications" =>
%%%
number := false
tag := "htt-3-3"
%%%

HTT 3.3 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

*cocartesian-definition.html — 5. 何のために必要か — ∞ 圏の極限・余極限（HTT §3.3）*

- 量　／　fibration での表示
- $`\lim F`　／　cocartesian 切断の ∞ 圏
- lax 極限　／　全ての切断の ∞ 圏
- $`\operatorname{colim}F`　／　全空間 $`E` を cocartesian 辺で局所化したもの

降下（被覆に沿った極限）は $`\mathrm{Cat}_\infty` や $`\mathrm{Pr}^L` での極限なので、ここでも fibration が使われる。第 5 章の「極限 = $`\mathrm{Un}(F)` の切断の空間」はこの $`\mathcal S` 値版。

# 3.3.1 Structure Theory for Cartesian Fibrations

%%%
number := false
tag := "htt-3-3-1"
%%%

:::proposition "htt_3_3_1_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence.pullback_snd_of_relativePath")
*HTT 命題 3.3.1.3*　同値に沿うカルテシアン束の引戻し（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=223)）。対応表の状態：一部（stronger-hyp）。

*主張*　Cartesian ファイブレーション $`X\to S` を圏同値 $`T\to S` に沿って引き戻すと、射影 $`X\times_S T\to X` も圏同値になる。

KB-W2原文・型再照合：仮定：Cartesian p:X→S と同値 e:T→S に加え X,S,T が準圏、relativeEquivalencePathMapAt p 1 が trivial Kan fibration（Lean が強い）。結論：pullback.snd e p が準圏同値で、引戻しの因子の標準交換を除き原典の写像と一致。任意の単体的基底で追加の相対 path 充填仮定を外す結論はない。

主張は各ファイバーの同定だけでなく、引き戻した全空間と元の全空間を比較する。底を同値な模型に置き換えても Cartesian に組み立てた全体が同じことを示す。

:::

:::proposition "htt_3_3_1_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isQCatEquivalence_of_rightFibration_fibers") (uses := "htt_2_4_1_1, htt_2_4_2_1")
*HTT 命題 3.3.1.5*　カルテシアン束の同値の三つの判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=225)）。対応表の状態：一部（stronger-hyp）。

*主張*　同じ底上の二つの Cartesian ファイブレーションの間の Cartesian 辺を保つ射では、全空間の圏同値、各ファイバーの圏同値、標識付きの Cartesian 同値は同値である。

同じ底上のfについてp,qを右fibration、底と全空間を準圏に限定すると、isQCatEquivalence\_of\_rightFibration\_fibersは条件(2)から(1)を直接与える。全辺がCartesianなので辺保存条件も満たす。一般のCartesian束とmarked modelでの条件(3)は含まない。

持ち上げを保つ条件によって、各ファイバーで得た比較が底の射に沿った移送と整合する。これがファイバーだけの判定と全空間の判定を結ぶ。

:::

:::proposition "htt_3_3_1_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_equivalenceLifting") (uses := "htt_2_4_2_1")
*HTT 命題 3.3.1.7*　カルテシアン束の圏的持上げ性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=227)）。対応表の状態：一部（stronger-hyp）。

*主張*　単体的集合の Cartesian ファイブレーションは圏論的ファイブレーションである。

KB-W2原文・型再照合：仮定：原典の Cartesian p:X→S に加え X,S が準圏かつ p が left fibration（Lean が強い）。結論：p は単射な categorical equivalence に対する RLP を持つ F1B.EquivalenceLifting、すなわち categorical fibration（この場合の結論は一致）。一般の Cartesian p のみからの型はない。

内角の持ち上げに加え、底の同値を持ち上げる性質が必要になる。そのために底の辺に沿う Cartesian な持ち上げを用いる。

:::

# 3.3.2 Universal Fibrations

%%%
number := false
tag := "htt-3-3-2"
%%%

:::corollary "htt_3_3_2_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.nativeLeftTransportRepresentation, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.nativeLeftTransportComparison_projection, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.nativeLeftTransportComparison_isPrecompositionEquivalence, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection")
*HTT 系 3.3.2.8*　左ファイブレーションの空間値分類（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=231)）。対応表の状態：一部（stronger-hyp）。

*主張*　小さい単体的集合間の任意の左ファイブレーションは、ある写像 $`S\to\mathcal S` に沿う $`\mathcal S_{*/}\to\mathcal S` の引き戻しと左ファイブレーションとして同値である。

KB-W2原文・型再照合：仮定：小さい left fibration p:X→S に加え S が準圏（Lean が強い）。結論：nativeLeftTransportRepresentation p の図式 S→SpaceInfinity の、pointSpaceVertex からの coslice の引戻しへ、底を厳密に保つ前合成同値がある（一致）。任意の単体的 S に対して同じ比較を同値とする型はない。

$`\mathcal S` の点に、その空間からではなく点 $`*` から入る射を付け加えた普遍族を使う。底上の左ファイブレーションはこの普遍族を引き戻す写像で分類される。

:::

# 3.3.3 Limits of ∞-Categories

%%%
number := false
tag := "htt-3-3-3"
%%%

:::corollary "htt_3_3_3_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramSectionsCone_isLimit, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramSectionsCone_vertex, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentSpaceSectionsVertex_object") (uses := "htt_1_1_2_4, htt_2_0_0_3")
*HTT 系 3.3.3.4*　空間の極限を表す全切断（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=234)）。対応表の状態：一部（special）。

*主張*　空間値図式 $`p:K\to\mathcal S` を分類写像とする左ファイブレーション $`X\to K` に対し、$`p` の極限と $`X` の切断の空間は空間のホモトピー圏で自然同型である。

KB-W2原文・型再照合：仮定：任意の小さい K と p:K→SpaceInfinity に対し分類束 X を標準の smallLeftUnstraightening p に固定（Lean が強い特殊形）。結論：全切断の Kan 複体そのものを頂点とする錐が極限であり、原典のこの標準分類束の場合の式と一致。任意の分類束への全切断の輸送比較はこの型には含まない。

切断は各ファイバーから一点を選び、底のすべての単体に対してその選択を整合させる。極限を記述する右辺は、単なる各頂点の積ではなく、底上の写像空間 $`\operatorname{Map}_K(K,X)` である。

:::

# 3.3.4 Colimits of ∞-Categories

%%%
number := false
tag := "htt-3-3-4"
%%%

:::corollary "htt_3_3_4_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramTotalCocone_isColimit, SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone_vertex, SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalUnit_isWeakHomotopyEquivalence")
*HTT 系 3.3.4.6*　空間の余極限を表す分類束の全空間（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=239)）。対応表の状態：一部（special）。

*主張*　空間値図式 $`p:K\to\mathcal S` が分類する左ファイブレーションの全空間は、$`p` の余極限と空間のホモトピー圏で自然同型である。

KB-W2原文・型再照合：仮定：任意の小さい K と p:K→SpaceInfinity に対し分類束を smallLeftUnstraightening p、余極限を coherentDiagramTotalCocone p の頂点に固定（Lean が強い特殊形）。結論：元の全空間からこの余極限への標準単位が弱ホモトピー同値（一致）。任意に指定された分類束・余極限への比較はこの型には含まない。

極限が整合的な切断を集めるのに対し、余極限ではファイバーを底の図式に沿って結びつけた全体のホモトピー型が現れる。比較の対象は左ファイブレーションの底でなく全空間である。

:::

