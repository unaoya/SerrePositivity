-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncated
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import SerrePositivity.InfinityCategories.HTT.Section1_2_9.OverIso
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinQuasicategory
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoreKan
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorSpace
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FullyFaithfulConeReflection
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialOpposite
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceOverColimitCreation
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Terminal
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.LeftFiberKan
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.OuterHornDuality
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.QuasicategoryCore
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingSpace
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceLeft
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceModelEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceRightKan
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RightIntervalEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Coslice
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinLeftColimits
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinRightColimits
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalMappingSpace
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalVertices
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.KanCharacterization
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyCategoryBridge
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.OuterHornConverse

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 1.2 The Language of Higher Category Theory" =>
%%%
number := false
tag := "htt-1-2"
%%%

HTT 1.2 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 1.2.2 Mapping Spaces in Higher Category Theory

%%%
number := false
tag := "htt-1-2-2"
%%%

:::proposition "htt_1_2_2_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace")
*HTT 警告 1.2.2.2*　頂点間とスライス内の二種の Hom（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=45)）。対応表の状態：一部（component）。

*主張*　$`\operatorname{Map}_S(X,Y)` は、$`X,Y` が頂点なら写像のホモトピー型、$`S` 上の単体的集合なら構造射と両立する相対内部 Hom を表す。

原文が二つ目の用法として明記する、同じX→S,Y→Sの相対写像空間はrelativeFunctorSpaceの内部Homのfiberの定義そのもの。頂点間のH-enrichedなMapとの同定は含まない。

相対内部 Hom の単体は、パラメータをもつ写像 $`X\to Y` の全体で、$`S` への合成が指定の構造射に一致するという条件を満たす。頂点どうしの写像型を表す記法と同じなので、まず $`X,Y` の型を見る。

:::

:::proposition "htt_1_2_2_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHom_kanComplex")
*HTT 命題 1.2.2.3*　右写像空間の Kan 性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=45)）。対応表の状態：本体にある。

*主張*　∞ 圏 $`\mathcal C` の二対象 $`x,y` に対し、右写像単体集合 $`\operatorname{Hom}^R_{\mathcal C}(x,y)` は Kan 複体である。

仮定：準圏 C と頂点 x、y（HTT と一致）。結論：pinchedHom x y は最終頂点を y、それより前の面を定値 x にした右写像空間で、KanComplex を満たす（一致）。

右写像単体集合では、一つの単体の所定の面が始点の定値単体になり、残った頂点が終点になる。元の $`\mathcal C` には内角条件しか課していないが、この端点を固定した空間には全角条件が得られる。

:::

:::proposition "htt_1_2_2_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftToIntervalMappingSpace_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence")
*HTT 注意 1.2.2.5*　左右の写像空間と区間模型（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=46)）。対応表の状態：本体にある。

*主張*　左写像単体集合を反対側での右写像単体集合として定めると、∞ 圏では左・右の両模型から端点固定の柱体模型への自然な包含がホモトピー同値になる。

仮定：単体集合と二頂点、比較の同値性には準圏性（HTT と一致）。結論：反対単体集合による左模型と両端固定の区間模型があり、左右から区間模型への指定比較が同値（一致）。

柱体模型の $`n`-単体は $`\Delta^n\times\Delta^1` からの写像で、区間の両端で $`x,y` に固定する。固定した面が始点側か終点側かで左・右の単体集合は異なるが、柱体を介せば同じホモトピー型を比較できる。

:::

# 1.2.3 The Homotopy Category

%%%
number := false
tag := "htt-1-2-3"
%%%

:::proposition "htt_1_2_3_1" (lean := "CategoryTheory.nerveAdjunction")
*HTT 命題 1.2.3.1*　ホモトピー圏と通常 nerve の随伴（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=46)）。対応表の状態：Mathlib にある。

*主張*　単体的集合をその通常のホモトピー圏へ送る関手 $`h` は、通常圏の nerve に左随伴である。

仮定：単体集合の圏と通常圏の圏（HTT と一致）。結論：hoFunctor ⊣ nerveFunctor を与える（一致）。

$`S` から $`N(\mathcal D)` への写像は、$`S` を通常圏として読んだとき $`\mathcal D` への関手となる。ここでは写像の豊穣化を忘れた通常圏の随伴を考える。

:::

:::proposition "htt_1_2_3_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.kanComplex_ho_isGroupoid")
*HTT 注意 1.2.3.4*　Kan 複体の基本亜群としての h（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=47)）。対応表の状態：本体にある。

*主張*　$`hS` は頂点を対象、辺を生成射とし、二単体の三辺の合成関係と退化辺の単位関係を課した圏で、Kan 複体では基本亜群となる。

仮定：Kan 複体 S（HTT と一致）。結論：hoFunctor.obj S の全射が可逆で、辺のホモトピー類を射とする基本亜群になる（一致）。

$`S` が任意の単体的集合なら、射を記述するには辺の列を使えるようにして関係で割る。∞ 圏の場合は内角充填を用いると、辺一本のホモトピー類でも同じ情報を記述できる。

:::

:::proposition "htt_1_2_3_5" (lean := "SSet.Truncated.HomotopicL.refl, SSet.Truncated.HomotopicL.symm, SSet.Truncated.HomotopicL.trans")
*HTT 命題 1.2.3.5*　辺のホモトピーが同値関係（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=48)）。対応表の状態：Mathlib にある。

*主張*　∞ 圏では両端の等しい辺のホモトピーは同値関係をなす。

仮定：準圏の二頂点間の辺（Lean が弱い：2 切断上の Quasicategory₂ で十分）。結論：終点を退化辺に固定した二単体で定義されるホモトピーに反射律・対称律・推移律がある（一致）。

ホモトピーは二単体で表し、共通の終点における側辺を退化辺に固定する。二つのホモトピーを貼る操作が関係の推移性を与え、辺をこの関係で割る準備になる。

:::

:::proposition "htt_1_2_3_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homotopicL_edgeOp_iff, SSet.Truncated.homotopicL_iff_homotopicR")
*HTT 注意 1.2.3.6*　辺のホモトピーと反対準圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=48)）。対応表の状態：本体にある。

*主張*　∞ 圏の二辺のホモトピー関係は、反対 ∞ 圏へ移しても保たれる。

仮定：準圏 X と同じ端点を持つ二辺（HTT と一致）。結論：辺を反対へ送ると左と右のホモトピーが入れ替わり、準圏では両者が同値（一致）。

反対化によって退化辺は三角形の反対側へ動く。そこで内角を埋めた三単体の別の面を取ると、反対圏で使う向きのホモトピーが得られる。

:::

:::proposition "htt_1_2_3_7" (lean := "SSet.Truncated.Edge.CompStruct.comp_unique")
*HTT 命題 1.2.3.7*　辺のホモトピー類の合成の独立性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=49)）。対応表の状態：Mathlib にある。

*主張*　∞ 圏で二辺の合成を内角充填の第三辺のホモトピー類で定めると、充填と代表辺の選択から独立する。

仮定：準圏の二単体合成候補と、両入力辺のホモトピー（Lean が弱い：Quasicategory₂ で十分）。結論：候補の第三辺はホモトピックで、入力代表・充填の変更に依存しない（一致）。

合成を定める三角形そのものは一意でなくてよい。固定した始点・終点をもつ辺の類で比較すると、途中で選択を変えても結果は一定になる。

:::

:::proposition "htt_1_2_3_8" (lean := "SSet.Truncated.HomotopyCategory₂")
*HTT 命題 1.2.3.8*　辺のホモトピー類がなす圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=49)）。対応表の状態：Mathlib にある。

*主張*　∞ 圏 $`\mathcal C` の頂点と辺のホモトピー類は、内角充填に基づく合成と退化辺に基づく単位で通常圏 $`\pi(\mathcal C)` をなす。

仮定：準圏 C（Lean が弱い：Quasicategory₂ で十分）。結論：頂点と辺のホモトピー類を持つ型に、退化辺を恒等射、内ホーンの充填で得た類を合成とする圏構造がある（一致）。

三つの辺を合成するときは、両方の括弧づけに対応する面を三単体の中で比較する。結合律は、選んだ複合辺そのものではなくその類について要求される。

:::

:::proposition "htt_1_2_3_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge, SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory, SSet.Truncated.HomotopyCategory.functor_ext")
*HTT 命題 1.2.3.9*　二つのホモトピー圏の標準比較（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=50)）。対応表の状態：本体にある。

*主張*　∞ 圏 $`\mathcal C` について、頂点を保ち辺をその類へ送る関手 $`h\mathcal C\to\pi(\mathcal C)` は一意に定まり、圏の同型である。

仮定：準圏 C（HTT と一致）。結論：頂点と辺の類を保つ比較関手があり、逆向きの関手との合成が恒等である。頂点と辺での一致から関手の一意性が従う（一致）。

二単体の三辺の関係が $`\pi(\mathcal C)` の合成と一致するため、生成元で指定した行き先が関手になる。比較は通常圏の同型なので、二つのホモトピー圏の記述を交換してよい。

:::

# 1.2.4 Objects, Morphisms, and Equivalences

%%%
number := false
tag := "htt-1-2-4"
%%%

:::proposition "htt_1_2_4_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_iff_hasInitialHornFillers")
*HTT 命題 1.2.4.3*　可逆辺の初端外ホーン充填判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=52)）。対応表の状態：本体にある。

*主張*　∞ 圏の辺 $`e` が同値であることは、$`[0,1]` 辺が $`e` であるすべての左外角 $`\Lambda_0^n`（$`n\ge2`）が充填可能であることと同値である。

仮定：準圏 C と辺 φ（HTT と一致）。結論：辺の可逆性と、最初の辺を φ に固定したすべての Λ₀ⁿ（n≥2）の延長性の同値（一致）。

通常圏では左端の同型に沿って三角形の欠けた辺を逆射で埋める。この判定は、その操作が高次の単体を含むすべての左外角で可能になることを要求する。

:::

# 1.2.5 ∞-Groupoids and Classical Homotopy Theory

%%%
number := false
tag := "htt-1-2-5"
%%%

:::proposition "htt_1_2_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.kanComplex_iff_isGroupoid, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.kanComplex_of_leftHornFillers, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanComplex_of_rightHornFillers, SSet.KanComplex.hornFilling")
*HTT 命題 1.2.5.1*　Kan 性と片側ホーン・亜群性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=53)）。対応表の状態：本体にある。

*主張*　単体的集合について、∞ 圏でホモトピー圏が亜群であること、左端を含むすべての角が埋まること、右端を含むすべての角が埋まること、Kan 複体であることは同値である。

仮定：任意の単体集合 C（HTT と一致。亜群条件の枝では準圏を仮定し、片側ホーン条件の枝では不要）。結論：準圏で hC が亜群、左ホーン充填、右ホーン充填、Kan 性の四条件が同値（一致）。

角の添字範囲の両側にある二条件は、内角に加えて片方の外角だけを含める。どちらでもすべての辺の可逆性が分かり、残りの外角も埋められる。

:::

:::proposition "htt_1_2_5_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCore_kanComplex, SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.kanComplex_ho_isGroupoid")
*HTT 命題 1.2.5.3*　最大 Kan 部分複体の普遍性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=53)）。対応表の状態：本体にある。

*主張*　∞ 圏 $`\mathcal C` の可逆辺だけをもつ最大の単体的部分集合は Kan 複体で、任意の Kan 複体から $`\mathcal C` への写像はそこを一意に経由する。

仮定：準圏 C と試験 Kan 複体 K（HTT と一致）。結論：全辺可逆な部分複体を構成して Kan 性を示し、K からの射は可逆辺を保存するので包含の単射性により一意に持ち上がる（一致）。

対象を削るのではなく、全辺が同値である単体だけを残して最大亜群を得る。Kan 複体の辺は可逆なので、そこから入る写像の像は最初からこの部分集合に含まれる。

:::

# 1.2.7 Functors Between Higher Categories

%%%
number := false
tag := "htt-1-2-7"
%%%

:::definition "htt_1_2_7_2" (lean := "CategoryTheory.ihom")
*HTT 記法 1.2.7.2*　内部 Hom としての関手準圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=57)）。対応表の状態：Mathlib にある。

*主張*　単体的集合 $`K` と ∞ 圏 $`\mathcal C` に対し、$`\operatorname{Fun}(K,\mathcal C)` は内部 Hom で、その辺を自然変換、可逆辺を自然同値と呼ぶ。

仮定：単体集合 C、D とそのデカルト閉構造（HTT と一致）。結論：Fun(C,D) を C による内部 Hom 関手の D での値として表す（一致）。

内部 Hom の $`n`-単体は $`K\times\Delta^n\to\mathcal C` である。これにより関手・自然変換に加え、変換どうしの高次の関係も同じ対象の中に入る。

:::

:::proposition "htt_1_2_7_3" (lean := "SSet.instQuasicategoryObjIhom")
*HTT 命題 1.2.7.3*　関手準圏と両変数の同値不変性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=57)）。対応表の状態：一部（component）。

*主張*　任意の単体的集合 $`K` について $`\operatorname{Fun}(K,\mathcal C)` は $`\mathcal C` が ∞ 圏なら ∞ 圏であり、値域の ∞ 圏または添字の単体的集合の圏同値で不変である。

KB-W2原文・型再照合：仮定：任意の単体集合 K と準圏 C（HTT と一致）。結論：SSet.instQuasicategoryObjIhom により Fun(K,C) は準圏であり、(1) に一致。(2)(3) の HTT の H-enriched categorical equivalence と前合成同値述語の比較はこの検査には含まない。

値域の比較は後合成、添字の比較は前合成なので、誘導される写像の向きは異なる。添字 $`K` 自体に内角充填条件は課されない。

:::

# 1.2.8 Joins of ∞-Categories

%%%
number := false
tag := "htt-1-2-8"
%%%

:::definition "htt_1_2_8_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex")
*HTT 定義 1.2.8.1*　単体集合の順序つき結合（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=58)）。対応表の状態：本体にある。

*主張*　join $`S\star T` の単体は頂点順序を前後二つの区間に分け、前半を $`S`、後半を $`T` の単体として選ぶことで得られ、空の区間も許す。

仮定：二つの単体集合と有限全順序の次数（HTT と一致）。結論：切断点ごとの左右の積を直和に取り、空の側は一点として join を作る（一致）。

両区間のどちらかが空なら元の $`S` または $`T` の単体になる。両方が非空なら、境目の位置がどの face がどちらの因子に由来するかを決める。

:::

:::proposition "htt_1_2_8_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftUnderAdjunction, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightUnderAdjunction")
*HTT 注意 1.2.8.2*　結合の標準単体と余極限保存（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=58)）。対応表の状態：本体にある。

*主張*　片側の因子を固定した join は固定因子の下の圏への関手として余極限を保ち、通常圏の join に nerve を取ると単体的集合の join になる。

仮定：任意の単体集合を片側に固定、または両側が標準単体（HTT と一致）。結論：標準単体の join は連結順序の標準単体で、固定した側の下の圏への二つの join 関手は左随伴である（一致）。

固定した因子の包含をデータに入れているので、余極限は共有する因子の下で計算する。通常圏の場合は、連鎖が左側から右側へ移る位置で nerve の単体を分解できる。

:::

:::proposition "htt_1_2_8_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.join_quasicategory")
*HTT 命題 1.2.8.3*　準圏どうしの結合の準圏性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=59)）。対応表の状態：本体にある。

*主張*　二つの ∞ 圏の join は ∞ 圏である。

仮定：準圏 S、T（HTT と一致）。結論：Quasicategory (join S T)（一致）。

join の単体を二つの区間に分けて読むことで、角を埋める問題を元の因子の充填問題に結びつけられる。特に片側を一点に取る錐にもこの性質を使える。

:::

:::definition "htt_1_2_8_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr")
*HTT 記法 1.2.8.4*　点を結合して作る左右の錐（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=59)）。対応表の状態：本体にある。

*主張*　単体的集合 $`K` の左錐は $`\Delta^0\star K`、右錐は $`K\star\Delta^0` で、追加した点を錐点とする。

仮定：単体集合 K（HTT と一致）。結論：点との左右の join と、各点側の標準包含で指定される頂点（一致）。

左錐の点からは $`K` の頂点へ向かう辺が出て、右錐では $`K` の頂点から点へ入る。頂点の位置が、極限と余極限で使う錐の向きを決める。

:::

# 1.2.9 Overcategories and Undercategories

%%%
number := false
tag := "htt-1-2-9"
%%%

:::proposition "htt_1_2_9_1" (lean := "SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso")
*HTT 注意 1.2.9.1*　通常の対象上の圏と準圏のスライス（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=60)）。対応表の状態：一部（special）。

*主張*　位相圏の厳密可換な三角形で作る素朴なスライスは、条件によっては高次のスライスの模型になる。

KB-W2原文・型再照合：仮定：普通圏 C の nerve と c に限定（Lean が強い特殊形）。結論：nerve(Over c) と準圏 sliceOver(nervePoint c) の実際の同型を得るので、naive overcategory が正しい slice を与えるという原典の存在する場合の明示例に一致。一般の topological/enriched C の naive approximation の基準は含まない。

位相圏では三角形がホモトピーを通じて可換になることも保持したい。厳密な三角形による模型がその情報を回復できる場合を見分ける必要があり、本項は第6.1.3.13項を参照する。

:::

:::proposition "htt_1_2_9_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverEquiv")
*HTT 命題 1.2.9.2*　結合で表されるスライスの普遍性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=60)）。対応表の状態：本体にある。

*主張*　写像 $`p:K\to S` に対し、$`S_{/p}` は $`Y\star K\to S` のうち $`K` 上で $`p` に等しいものを $`Y` で表現する。

仮定：任意の単体集合 Y、K、S と p : K ⟶ S（HTT と一致）。結論：Y から sliceOver p への射と、p を右に固定した join Y K ⟶ S の全単射（一致）。

$`Y` を一点にすれば、$`p` に向かう錐を一つ選ぶことになる。$`Y` を標準単体に動かすと、その錐の間の射と高次単体までが決まる。

:::

:::proposition "htt_1_2_9_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOver_quasicategory") (uses := "htt_1_1_2_4, htt_2_1_2_2, htt_2_4_4_4, htt_2_4_4_5, htt_2_4_5_1")
*HTT 命題 1.2.9.3*　スライスの準圏性と同値不変性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=61)）。対応表の状態：一部（component）。

*主張*　∞ 圏 $`\mathcal C` の図式 $`p:K\to\mathcal C` に対する $`\mathcal C_{/p}` は ∞ 圏で、値域を圏同値で取り替えると誘導されるスライスの射も圏同値である。

KB-W2原文・型再照合：仮定：準圏 C と任意の p:K→C（HTT と一致）。結論：sliceOver p の Quasicategory を得るので最初の assertion に一致。後半の任意 categorical equivalence q に対する slice 比較は含まず、trivial Kan fibration の別の十分条件もその代用にはしない。

固定図式への錐を集めた単体集合は、それ自身が内角充填を満たす。値域の比較では図式も同じ関手で送り、両側の錐をその像どうしで比較する。

:::

:::proposition "htt_1_2_9_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverVertex")
*HTT 注意 1.2.9.4*　単体または頂点で指定したスライス（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=61)）。対応表の状態：本体にある。

*主張*　$`p` が単体 $`\sigma` を分類する場合の $`\mathcal C_{/p}` を $`\mathcal C_{/\sigma}`、頂点 $`X` の場合を $`\mathcal C_{/X}` と書く。

仮定：単体集合の標準単体からの射、特に一つの頂点（Lean が弱い：準圏性は構成に不要）。結論：図式のスライスと、頂点を零単体の射として取ったスライス（一致）。

下添字の単体は図式の形だけでなく、その $`\mathcal C` への写像も指定する。頂点の場合は対象 $`X` への射がスライスの頂点になる。

:::

:::proposition "htt_1_2_9_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderEquiv, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderVertex")
*HTT 注意 1.2.9.5*　結合を反転したコスライス（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=61)）。対応表の状態：本体にある。

*主張*　$`K\star Y\to\mathcal C` のうち $`K` 上で $`p` に等しいものを表現する単体集合を $`\mathcal C_{p/}` といい、単体や頂点の下の圏にも同じ記法を使う。

仮定：任意の単体集合の間の射 p と、特に頂点（Lean が弱い：構成に準圏性は不要）。結論：右の試験対象を付ける join でコスライスの Hom が表され、零単体の特殊化もある（一致）。

今回は固定した図式が左側なので、点に対応する頂点では図式から出る余錐を得る。上の圏を反対化して読むとこの向きになる。

:::

:::proposition "htt_1_2_9_6" (lean := "SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso")
*HTT 注意 1.2.9.6*　通常の対象上の圏の nerve 比較（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=61)）。対応表の状態：本体にある。

*主張*　通常圏 $`\mathcal C` と対象 $`X` について、$`N(\mathcal C)_{/X}` は通常のスライスの nerve $`N(\mathcal C_{/X})` と標準同型である。

仮定：通常圏 C と対象 c（HTT と一致）。結論：nerve (Over c) ≅ sliceOver (nervePoint c)（一致）。

スライスの射の列を、末尾が $`X` である一つの連鎖として読むと単体的な錐と対応する。同型はこの対応をすべての次元で行う。

:::

# 1.2.11 Subcategories of ∞-Categories

%%%
number := false
tag := "htt-1-2-11"
%%%

:::proposition "htt_1_2_11_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices")
*HTT 注意 1.2.11.1*　指定した頂点が張る充満部分圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=62)）。対応表の状態：一部（component）。

*主張*　∞ 圏の対象集合が張る充満部分圏は、頂点がその集合に属する全単体を含み、選ばれた対象間の写像型を保つ。

KB-W2原文・型再照合：仮定：準圏 C と頂点の集合（原典の full-subcategory 部分と一致）。結論：fullSubcomplexOnVertices は全頂点がその集合に属す単体を全て含む部分複体で、集合が spanned full subcategory を定める記述に一致。一般 fully faithful f の像への同値分解は含まない。

充満性は辺を一部だけ選ぶ条件ではない。頂点を選んだ後、端点間のすべての射だけでなく、それらの間の高次の関係も引き継ぐ。

:::

# 1.2.12 Initial and Final Objects

%%%
number := false
tag := "htt-1-2-12"
%%%

:::definition "htt_1_2_12_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_trivialKanFibration")
*HTT 定義 1.2.12.3*　自明ファイブレーションによる強終対象（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=63)）。対応表の状態：本体にある。

*主張*　頂点 $`Y` が強終対象であるとは $`\mathcal C_{/Y}\to\mathcal C` が自明ファイブレーションであることで、最後の頂点を $`Y` に固定した全境界の延長条件に等しい。

仮定：任意の単体集合 X の頂点（HTT と一致）。結論：IsTerminalVertex と頂点上の sliceOverProjection が自明 Kan ファイブレーションであることの同値（一致）。

スライスからの射の持ち上げは、与えられた単体へ $`Y` を最後に付ける延長として表される。この判定は対象の存在だけでなく、既指定の面と両立する延長を要求する。

:::

:::proposition "htt_1_2_12_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_pinchedHom_isContractibleKan")
*HTT 命題 1.2.12.4*　強終対象と右 Hom の可縮性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=63)）。対応表の状態：本体にある。

*主張*　∞ 圏の対象 $`Y` が強終対象であることは、すべての $`X` から $`Y` への右写像 Kan 複体が可縮であることと同値である。

仮定：準圏 C と頂点 y（HTT と一致）。結論：強終頂点条件と、各頂点 x からの右 pinched Hom が可縮 Kan 複体である条件の同値（一致）。

終対象への射の一意性は、写像空間が点と同じホモトピー型をもつ条件になる。辺の類が一つという条件に加え、射の間の高次の情報も制御する。

:::

:::proposition "htt_1_2_12_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isInitialVertex_iff_isTerminalVertex_op, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_iff_trivialKanFibration")
*HTT 注意 1.2.12.6*　反対による始対象と終対象（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=63)）。対応表の状態：本体にある。

*主張*　始対象の条件は、反対 ∞ 圏で終対象になることとして得られる。

仮定：単体集合の頂点（Lean が弱い：準圏性は不要）。結論：反対側の終頂点と始頂点が同値で、始頂点の条件はコスライス射影の自明 Kan ファイブレーション性（一致）。

終対象への写像を始対象からの写像へ反転する。端点固定条件も同時に反転するので、最初の頂点の側が対応する。

:::

:::proposition "htt_1_2_12_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveVertex_isTerminal_iff")
*HTT 例 1.2.12.7*　通常圏の終始対象と nerve（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=63)）。対応表の状態：一部（component）。

*主張*　通常圏の対象が始対象または終対象であることは、その nerve で同じ性質をもつことと同値である。

KB-W2原文・型再照合：仮定：通常圏 C と t（HTT と一致）。結論：IsTerminal t の存在 iff nerveVertex t が strong terminal vertex であるという終対象の部分を得る。始対象側と H-enriched hN(C) の terminal 定義との比較は含まない。

通常圏の二対象間の写像は集合として与えられるので、その写像型が可縮である条件は射がただ一つある条件に戻る。

:::

:::proposition "htt_1_2_12_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertices, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertices_isContractibleKan")
*HTT 命題 1.2.12.9*　終対象を張る部分複体の可縮性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=64)）。対応表の状態：本体にある。

*主張*　∞ 圏の終対象が張る充満部分圏は空であるか可縮な Kan 複体である。

仮定：終頂点の存在（HTT と一致する非空の場合。Lean が弱い：準圏性は不要）。結論：全終頂点が張る全部分複体は可縮な Kan 複体。終頂点がなければ定義から空（一致）。

終対象が一つでも存在すれば、他の終対象との比較射は同値であり、比較の高次の選択も可縮になる。対象の同型類が一つというだけでなく、その部分圏全体のホモトピー型を述べる。

:::

# 1.2.13 Limits and Colimits

%%%
number := false
tag := "htt-1-2-13"
%%%

:::definition "htt_1_2_13_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone")
*HTT 定義 1.2.13.4*　スライスによる極限と余極限（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=65)）。対応表の状態：本体にある。

*主張*　図式 $`p:K\to\mathcal C` の余極限は余錐の ∞ 圏 $`\mathcal C_{p/}` の始対象、極限は錐の ∞ 圏 $`\mathcal C_{/p}` の終対象である。

仮定：準圏 C と任意の図式 p（Lean が弱い：述語自体は準圏性なしで定義）。結論：余極限はコスライスの始頂点、極限はスライスの終頂点（一致）。

対象一点への比較だけでなく、同じ図式を延長する錐・余錐の全体の中で普遍性を課す。余錐側では普遍な余錐から各余錐へ射が向かう。

:::

:::proposition "htt_1_2_13_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitVertexIso, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitVertexIso")
*HTT 注意 1.2.13.5*　極限錐と余極限錐の頂点（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=65)）。対応表の状態：本体にある。

*主張*　余極限図式とは $`p:K\to\mathcal C` を右錐へ延長して余極限となるもので、錐点の値も余極限と呼び、極限では双対の記法を使う。

仮定：準圏の図式とその錐・余錐（HTT と一致）。結論：錐頂点を評価し、極限・余極限の頂点が選択によらず同型となる（一致）。

余極限の頂点と、そこへ向かう余錐の脚は区別される。同じ頂点に異なる余錐がある場合、余極限図式であるかは脚を含めて判定する。

:::

:::proposition "htt_1_2_13_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_of_fullyFaithful_image")
*HTT 注意 1.2.13.7*　充満部分圏に入る余極限（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=66)）。対応表の状態：一部（component）。

*主張*　充満部分圏に入る図式の余極限が大きい圏で存在し、その値も部分圏に属するなら部分圏でも同じ余極限となり、関手が余極限を保つとは像の指定余錐が余極限となることである。

KB-W2原文・型再照合：仮定：準圏間の fully faithful F と、像で余極限となる同じ余錐（原典の full inclusion の場合を含み、Lean が弱い）。結論：元の余錐は余極限なので、C 内の余極限が C′ に属せば C′ でも余極限という明記された帰結に一致。slice 全体の引戻し同一視は含まない。

充満包含では部分圏内の試験対象に向かう比較の空間が変わらない。一般の関手ではこの理由が使えないので、保存は像の余錐で別に判定する。

:::

:::proposition "htt_1_2_13_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_sliceOver_colimitCone_with_projection, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOver_isColimitCone_iff_projection") (uses := "htt_1_1_2_4")
*HTT 命題 1.2.13.8*　スライス射影による余極限の生成（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=66)）。対応表の状態：一部（special）。

*主張*　スライス $`\mathcal C_{/q}` の図式の射影が $`\mathcal C` で余極限を持てば元の図式にも余極限があり、指定余錐が余極限となることは射影した余錐で判定できる。

KB-W2原文・型再照合：仮定：準圏 C と図式 p（Lean が強い：スライスを定める q の始域 T が一点）。結論：底の余極限余錐を厳密に持ち上げ、与えた余錐が余極限かを射影で検出する（Lean が弱い：任意の T のスライスは含まない）。

スライス内では $`q` に向かう脚も指定されている。底で余極限を取ると図式のその脚が余極限対象へ延び、同じ固定図式の上で余錐として読める。

:::

# 1.2.16 The ∞-Category of Spaces

%%%
number := false
tag := "htt-1-2-16"
%%%

:::definition "htt_1_2_16_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.kanObject_simplicialCategory")
*HTT 定義 1.2.16.1*　Kan 複体の nerve による空間の圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=69)）。対応表の状態：本体にある。

*主張*　空間の ∞ 圏 $`\mathcal S` は、Kan 複体とその内部 Hom の単体的圏の整合的 nerve である。

仮定：固定した宇宙の Kan 複体（HTT と一致）。結論：KanObject に内部 Hom による単体豊穣圏構造を与え、その coherent nerve を SpaceInfinity とする（一致）。

空間の間の写像を集合にするとホモトピーが失われる。写像そのものを単体的集合にしてから nerve を取ることで、高次の写像を含む圏になる。

:::

:::proposition "htt_1_2_16_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.kanObject_sHom_kanComplex, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinity_quasicategory")
*HTT 注意 1.2.16.2*　Kan 複体間の内部 Hom の Kan 性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=69)）。対応表の状態：本体にある。

*主張*　Kan 複体 $`X,Y` の間の内部 Hom $`Y^X` は Kan 複体なので、Kan 複体の単体的圏の整合的 nerve は ∞ 圏である。

仮定：Kan 複体 X、Y（HTT と一致）。結論：内部 Hom Y\^X は Kan 複体で、その豊穣圏の nerve は準圏（一致）。

写像対象が Kan になることが、整合的 nerve に内角充填を適用するための局所条件である。この二段階により $`\mathcal S` が ∞ 圏だと分かる。

:::

:::proposition "htt_1_2_16_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity")
*HTT 注意 1.2.16.4*　小空間と大空間の宇宙の区別（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=70)）。対応表の状態：本体にある。

*主張*　小さい Kan 複体の整合的 nerve を $`\mathcal S`、より大きい範囲の Kan 複体も含めたものを $`\widehat{\mathcal S}` として使い分ける。

仮定：Kan 複体の大きさを定める宇宙 u（HTT と一致）。結論：その Kan 複体の nerve は SSet.\{u+1\} にあり、u を上げて大きい空間の準圏を区別できる（一致）。

個々の小さい空間が属する大きさと、それらすべてを集めた圏の大きさは異なる。$`\mathcal S` 自身はすでに大きいので、その中のすべての対象を使う構成では区別が必要になる。

:::

