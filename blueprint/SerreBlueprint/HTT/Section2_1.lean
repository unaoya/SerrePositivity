import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
import Mathlib.AlgebraicTopology.SimplicialSet.Op
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
import Mathlib.CategoryTheory.Grothendieck
import SerrePositivity.InfinityCategories.HTT.Section2_1_3.VertexFiberOpposite
import SerrePositivity.InfinityCategories.HTT.Section2_1_3.WeakContractibility
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationTrivialComparison
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalOppositeFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationContractible
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftAnodynePushoutProduct
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftPath
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftPrism
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceRightAnodyne
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinAnodyne
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.RelativeCoslice
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialMappingSpace
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.KanCharacterization
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.ContractibleKan
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.LeftKanFibration

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 2.1 Left Fibrations" =>
%%%
number := false
tag := "htt-2-1"
%%%

HTT 2.1 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 2.1.1 Left Fibrations in Classical Category Theory

%%%
number := false
tag := "htt-2-1-1"
%%%

:::definition "htt_2_1_1_1" (lean := "CategoryTheory.Functor.IsStronglyCocartesian")
*HTT 定義 2.1.1.1*　亜群に余ファイバー化された圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=74)）。対応表の状態：一部（component）。

*主張*　通常圏の関手が亜群による余ファイバー化であるとは、始点を指定して底の射を持ち上げられ、全空間の各射が余 Cartesian であることをいう。

KB-W2原文・型再照合：仮定：通常の F:C⥤D と射 η:C→C′（HTT の条件 (2) と一致）。結論：IsStronglyCocartesian F η の普遍性は、任意 C″ に対する指定 Hom の fiber-product comparison の全単射性を表す。全ての η に課すと (2) の成分になる。任意の底の射の持上げの存在 (1) と合わせた cofibered-in-groupoids の構造は含まない。

後者は、持ち上げた射の後に続く射を与えることと、元の始点からの射およびその底での因子分解を与えることの全単射である。底の恒等射の上でこの性質を使うと、ファイバー内の射が可逆になる。

:::

:::proposition "htt_2_1_1_2" (lean := "CategoryTheory.Grothendieck, CategoryTheory.Grothendieck.forget, CategoryTheory.Grothendieck.toTransport")
*HTT 例 2.1.1.2*　亜群値関手の Grothendieck 構成（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=74)）。対応表の状態：一部（component）。

*主張*　通常圏 $`\mathcal D` 上の亜群値関手 $`\chi` の Grothendieck 構成 $`\mathcal C_\chi\to\mathcal D` は亜群による余ファイバー化である。

KB-W2原文・型再照合：仮定：χ:D→Gpd の underlying Cat-valued functor（HTT と一致、構成は一般の Cat 値でも可能）。結論：実際の Grothendieck χ の射影と toTransport により、任意 x と底の射 f に対しその f 上の射 x→transport x f を作る。原典の cofibered-in-groupoids の条件 (1) に一致するが、全ての射の (2) の普遍性と分類同値は含まない。

射 $`d\to d'` に沿う持ち上げには $`\chi(d\to d')` で対象を送ったものを使う。ファイバー内の射は可逆なので、標準の持ち上げにファイバー内の射を合成したものも余 Cartesian になる。

:::

:::proposition "htt_2_1_1_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_reflects_invertibleEdge")
*HTT 命題 2.1.1.5*　左ファイブレーションの可逆辺反映（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=77)）。対応表の状態：本体にある。

*主張*　∞ 圏の左ファイブレーションは同値を反映する。

仮定：準圏間の左ファイブレーションと、底で可逆となる辺（HTT と一致）。結論：元の辺も可逆（一致）。

底で可逆な辺に沿う輸送はファイバーの間で可逆になる。定理はその輸送の記述だけでなく、元の全空間の指定辺そのものが同値であることを述べる。

:::

:::proposition "htt_2_1_1_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_liftInvertibleEdge_target")
*HTT 命題 2.1.1.6*　終点を指定した可逆辺の持ち上げ（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=77)）。対応表の状態：本体にある。

*主張*　∞ 圏の左ファイブレーション $`p` では、終点が $`p(Y)` である底の同値を、終点 $`Y` を指定して同値へ持ち上げられる。

仮定：底の準圏、左ファイブレーション、上の終頂点とその像を終点とする可逆辺（Lean が弱い：始域の準圏性は仮定しない）。結論：指定終点と底の辺を保つ持ち上げが存在する（一致）。

通常の左ファイブレーションの持ち上げで直接指定しやすいのは始点である。底の辺が可逆なら逆向きから持ち上げる余地ができ、全空間で得る元向きの辺も同値となる。

:::

# 2.1.2 Stability Properties of Left Fibrations

%%%
number := false
tag := "htt-2-1-2"
%%%

:::proposition "htt_2_1_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceMap_leftFibration") (uses := "htt_1_2_9_3, htt_2_0_0_3, htt_2_1_2_3")
*HTT 命題 2.1.2.1*　相対スライス制限の左ファイブレーション（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=78)）。対応表の状態：一部（component）。

*主張*　内ファイブレーション $`q:X\to S` と部分図式 $`A\subseteq B\to X` について、下の圏の相対制限写像は左ファイブレーションであり、$`q` 自身が左ファイブレーションなら上の圏の相対制限写像もそうなる。

KB-W2原文・型再照合：仮定：内ファイブレーションと図式の包含 K₀ ⊆ K（HTT と一致する第一の場合）。結論：図式の制限と底への後合成を合わせた相対コスライスの比較は左ファイブレーション（Lean が弱い：左ファイブレーションに対する slice 側の結論は含まない）。

相対制限の標的では、$`A` 上の錐と底での $`B` 上の錐が $`A` 上で一致するものを組にする。どちら向きの錐を使うかによって、元の $`q` に必要な持ち上げ条件は変わる。

:::

:::corollary "htt_2_1_2_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderProjection_leftFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnder_quasicategory")
*HTT 系 2.1.2.2*　コスライス射影の左ファイブレーション（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=79)）。対応表の状態：本体にある。

*主張*　∞ 圏 $`\mathcal C` の任意の図式 $`p:K\to\mathcal C` に対し、余錐の圏 $`\mathcal C_{p/}\to\mathcal C` の射影は左ファイブレーションで、$`\mathcal C_{p/}` も ∞ 圏になる。

仮定：準圏 C と任意の図式 p : K ⟶ C（HTT と一致）。結論：sliceUnder p の射影は左ファイブレーションで、始域は準圏（一致）。

射影は余錐をその頂点へ送る。左ファイブレーションとして見れば、頂点を底の射に沿って動かす持ち上げが、余錐を新しい終点に移す操作になる。

:::

:::lemma_ "htt_2_1_2_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_innerAnodyne_of_rightAnodyne, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_innerAnodyne_of_leftAnodyne")
*HTT 補題 2.1.2.3*　結合角の内アノダイン性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=80)）。対応表の状態：本体にある。

*主張*　二つの単体的部分集合の包含 $`A'\subseteq A`、$`B'\subseteq B` のうち、前者が右アノダインまたは後者が左アノダインなら、join の合併 $`(A'\star B)\cup(A\star B')\hookrightarrow A\star B` は内アノダインである。

仮定：両側が部分複体の包含で、左側が右アノダインまたは右側が左アノダイン（HTT と一致）。結論：二つの部分結合の和から全結合への包含は内アノダイン（一致）。

左因子・右因子で使う外角の向きが逆なのは、join が先に左の頂点を並べ、その後に右の頂点を並べるためである。合併は二つの制限データが共通部分で一致することを表す。

:::

:::proposition "htt_2_1_2_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceMap_trivialKanFibration_of_rightAnodyne") (uses := "htt_2_0_0_3, htt_2_1_2_9")
*HTT 命題 2.1.2.5*　相対コスライス比較の自明性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=80)）。対応表の状態：一部（component）。

*主張*　$`A\hookrightarrow B` が右アノダインで $`S\to T` が内ファイブレーションの場合、または前者がアノダインで後者が左ファイブレーションの場合、下の圏の対応する相対制限写像は自明 Kan ファイブレーションである。

KB-W2原文・型再照合：仮定：内ファイブレーションと右アノダイン包含（HTT と一致する第一の場合）。結論：相対コスライスの比較射は自明 Kan ファイブレーション（Lean が弱い：左ファイブレーションと全アノダイン包含の第二の場合は含まない）。

$`B` 上の余錐を延ばすとき、$`A` 上の余錐と $`T` における余錐を先に固定する。自明 Kan ファイブレーションという結論は、選んだこれらのデータを保つ延長とその高次の選択を同時に制御する。

:::

:::proposition "htt_2_1_2_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions_pushoutObjObj_point") (uses := "htt_A_1_2_2")
*HTT 命題 2.1.2.6*　左アノダイン射の三つの生成系（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=81)）。対応表の状態：一部（direction）。

*主張*　左アノダイン射は左端を許す角包含で生成でき、境界包含と $`\{0\}\hookrightarrow\Delta^1` の押し出し積、または任意の単射と同じ頂点包含の押し出し積でも同じ弱飽和類が得られる。

KB-W2原文・型再照合：仮定：任意の単射 i と始端の包含（HTT の第三生成系と一致）。結論：その pushout-product は left anodyne、したがって第三生成系の弱飽和閉包は第一の閉包に含まれるという一方向に一致。逆の包含はなく、三生成系の閉包が等しいとは判定しない。

同じ射の類を三通りに生成できるため、角の条件を使う代わりに、初端を固定した区間モデルに対する持ち上げを調べられる。

:::

:::corollary "htt_2_1_2_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions_pushoutObjObj_left")
*HTT 系 2.1.2.7*　左アノダイン射の押し出し積（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=82)）。対応表の状態：本体にある。

*主張*　左アノダイン射と単体的集合の余ファイブレーションの押し出し積は左アノダインである。

仮定：左アノダイン射 i と単射 j（HTT と一致）。結論：i と j の押し出し積は左アノダイン（一致）。

長方形の二つの部分で指定した写像が共通部分で一致しているとき、その合併から直積全体への包含が問題になる。左アノダイン性はこの余ファイブレーション方向のパラメータを加えても保たれる。

:::

:::proposition "htt_2_1_2_8"
*HTT 注意 2.1.2.8*　アノダイン射と単射の押し出し積（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=83)）。対応表の状態：Mathlib にある。

*主張*　アノダイン射と余ファイブレーションの押し出し積はアノダインであり、これは左・右アノダインの二つの結果から従う。

仮定：単射と全ホーンに関するアノダイン射（HTT と一致）。結論：左右いずれの順の押し出し積もアノダイン（一致）。

すべての角包含は片方の向きの生成元に入る。したがって両向きで得た押し出し積の性質を弱飽和閉包に広げれば、通常のアノダイン射を扱える。

宣言：`SSet.anodyneExtensions_pushoutObjObjι`、`SSet.anodyneExtensions_pushoutObjObjι'`

:::

:::corollary "htt_2_1_2_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.trivialKanFibration_relativeHom_of_leftAnodyne")
*HTT 系 2.1.2.9*　左ファイブレーションの相対内部 Hom（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=83)）。対応表の状態：本体にある。

*主張*　左ファイブレーション $`X\to S` と余ファイブレーション $`A\to B` に対し、比較 $`X^B\to X^A\times_{S^A}S^B` は左ファイブレーションで、$`A\to B` が左アノダインなら自明 Kan ファイブレーションである。

仮定：左ファイブレーション p と単射 i（HTT と一致）。結論：相対内部 Hom の比較射は左ファイブレーションで、i が左アノダインなら自明 Kan ファイブレーション（一致）。

標的は $`A` 上の持ち上げと $`S` における $`B` 上の図式を固定したもの。両者の一致の条件を引き戻しで組み立て、制限と後合成を一本の写像にする。

:::

:::corollary "htt_2_1_2_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSource_trivialKanFibration")
*HTT 系 2.1.2.10*　ホモトピー延長による左持ち上げ判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=83)）。対応表の状態：一部（direction）。

*主張*　単体的写像 $`X\to S` が左ファイブレーションであることは、区間の始点での制限比較 $`X^{\Delta^1}\to X^{\{0\}}\times_{S^{\{0\}}}S^{\Delta^1}` が自明 Kan ファイブレーションであることと同値である。

KB-W2原文・型再照合：仮定：左ファイブレーション p（元の iff の順方向の仮定と一致）。結論：指定 interval source の relativeEdgeSource p が TrivialKanFibration となるので順方向に一致。逆向きはない。

底の辺とその始点の上の点を固定したときの持ち上げを、区間の写像単体集合で表す。自明性は任意の境界をパラメータにした相対延長までを含む。

:::

# 2.1.3 A Characterization of Kan Fibrations

%%%
number := false
tag := "htt-2-1-3"
%%%

:::lemma_ "htt_2_1_3_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibration_vertex_surjective_of_essentiallySurjective, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence.isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.QCatEquivalence.isEssentiallySurjective")
*HTT 補題 2.1.3.2*　左ファイブレーションの頂点全射（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=84)）。対応表の状態：本体にある。

*主張*　Kan 複体間の左ファイブレーションがホモトピー同値なら、頂点集合上で全射である。

仮定：Kan 複体間の左ファイブレーションがホモトピー同値（HTT と一致）。結論：ホモトピー同値を準圏同値に移し、そこから得られる本質的全射性を左ファイブレーションで持ち上げて頂点の全射性を得る（一致）。

ホモトピー同値から、各底の頂点が像の頂点と同じ成分にあると分かる。そこから底の辺に沿う持ち上げを用いて、指定した頂点のちょうど上に移る。

:::

:::lemma_ "htt_2_1_3_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.leftFibration_fibration_of_kanComplex, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_innerFibration, SSet.quasicategory_of_innerFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_reflects_invertibleEdge, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective, SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.kanComplex_iff_isGroupoid")
*HTT 補題 2.1.3.3*　Kan 複体上の左ファイブレーション（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=84)）。対応表の状態：本体にある。

*主張*　底が Kan 複体である左ファイブレーションは Kan ファイブレーションである。

仮定：左ファイブレーションと底の Kan 性（HTT と一致）。結論：始域が準圏となり、底の辺はすべて可逆なので可逆性の反映と辺による表示から始域のホモトピー圏も亜群となる。始域の Kan 性が従い、全ホーンに対する右持ち上げ性を得る（一致）。

底ではすべての辺が可逆である。左側の持ち上げで得る輸送が可逆になるので、反対側の角に必要な持ち上げも制御できる。

:::

:::lemma_ "htt_2_1_3_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalLeftFibration_op_rightFibration, SerrePositivity.InfinityCategories.HTT.Section2_1_3.vertexFiberOpIso, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsContractibleKan.op, SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_iso, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_trivialKanFibration_of_contractible_fibers, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalTrivialKanFibration_op, SSet.opFunctorCompOpFunctorIso")
*HTT 補題 2.1.3.4*　可縮繊維から自明ファイブレーション（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=84)）。対応表の状態：本体にある。

*主張*　左ファイブレーションの各頂点ファイバーが可縮なら、その写像は自明 Kan ファイブレーションである。

仮定：左ファイブレーションと全頂点繊維の可縮 Kan 性（HTT と一致）。結論：反転した繊維との同型で右ファイブレーション側の可縮性を得て自明 Kan ファイブレーションとし、二重反転から元の左ファイブレーションの自明性を得る（一致）。

ファイバーが可縮なら、底の辺に沿うどの移送もホモトピー同値になる。左ファイブレーションに最初から備わる条件と合わせて、底に Kan 条件を追加せずに結論を得る。

:::

:::proposition "htt_2_1_3_5" (lean := "SerrePositivity.InfinityCategories.HTT.Section2_1_3.IsContractibleKan.isWeaklyContractible, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence.cancel_right, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence.isSimplicialHomotopyEquivalence")
*HTT 注意 2.1.3.5*　可縮繊維間の輸送の同値性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=86)）。対応表の状態：一部（component）。

*主張*　左ファイブレーションで頂点ファイバーがすべて可縮な場合も、底が Kan の場合も、ホモトピー圏を経由するファイバーの移送がすべて可逆になる。

KB-W2原文・型再照合：仮定：可縮な二つの Kan 複体と任意の射（原典の第一の明記された観察と一致）。結論：一点への二射が弱同値なので cancel\_right と Kan Whitehead により、その射は単体ホモトピー同値。一文目に一致するが、これを用いた left fibration の輸送 criterion と hT→H の関手性の議論は含まない。

前者では可縮空間の間の射であることが効き、後者では底のホモトピー圏の射がすべて同型であることが効く。異なる仮定で同じ輸送の判定を使っている。

:::

# 2.1.4 The Covariant Model Structure

%%%
number := false
tag := "htt-2-1-4"
%%%

:::proposition "htt_2_1_4_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr")
*HTT 例 2.1.4.4*　恒等写像に沿う錐の簡約（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=86)）。対応表の状態：本体にある。

*主張*　恒等図式 $`\mathrm{id}_S` への左錐と右錐の構成は、それぞれ $`S` の左錐と右錐に同定される。

仮定：単体集合 S と恒等写像（HTT と一致）。結論：一点との左右の結合を与える。恒等写像に沿う押し出しではこの錐をそのまま取れる（一致）。

恒等図式では、指定した底図式と元の図式が同じであり、追加するデータは新しい錐点だけになる。錐点を単体の先頭に置くか末尾に置くかで二つの模型を区別する。

:::

:::proposition "htt_2_1_4_10" (lean := "CategoryTheory.Over.mapPullbackAdj")
*HTT 命題 2.1.4.10*　底の変更による共変 Quillen 随伴（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=89)）。対応表の状態：一部（component）。

*主張*　底の写像 $`j:S\to S'` による後合成は引き戻し $`j^*` に左随伴で、この随伴は両スライスの共変モデル構造について Quillen 随伴になる。

KB-W2原文・型再照合：仮定：任意の j:S→S′ と SSet の実際の pullbacks（HTT と一致）。結論：Over.map j⊣pullback j は原典で明記した j! と j\* の underlying adjunction に一致。covariant model の class と左右 Quillen 性は供給していない。

$`S` 上の対象を $`S'` 上で見る向きは後合成である。逆向きは元の底へ引き戻す。随伴の主張には、スライス圏の形式的な随伴にモデル構造についての保存条件が加わる。

:::

