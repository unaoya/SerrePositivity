-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.MorphismProperty.Limits
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CosliceTriangleFiber
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationFiberReflection
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.WeakContractibleKan
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedSimplexCategory
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalAnodyneRecognition
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalCoconeRestriction
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalComposition
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalFactorizationCriterion
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalFunctorSpace
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalOpposite
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalTensor
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalWeakEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.Cofinality
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.LeftFibrationAnodynePullback
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.LeftFibrationCofinalPullback
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenA
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.RightCofinalFunctor
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.TrivialFibrationCofinality
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CosliceFiberUniversal
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceModelEquivalence

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 4.1 Cofinality" =>
%%%
number := false
tag := "htt-4-1"
%%%

HTT 4.1 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 4.1.1 Cofinal Maps

%%%
number := false
tag := "htt-4-1-1"
%%%

:::definition "htt_4_1_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal")
*HTT 定義 4.1.1.1*　右ファイブレーションで試す共終性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=241)）。対応表の状態：本体にある。

*主張*　$`S\to T` が共終であるとは、任意の右ファイブレーション $`X\to T` について、底上の切断の $`S` への制限がホモトピー同値になることをいう。

仮定：任意の単体集合の射 i : A ⟶ B（HTT と一致）。結論：B 上の任意の右ファイブレーションに対し、底上の写像空間を i で制限する射がホモトピー同値となることを共終性とする（一致）。

試験するのは任意の図式ではなく、まず右ファイブレーションの切断である。$`S` の上で得た切断が $`T` 上の切断と同じホモトピー型を持つことを求める。

:::

:::proposition "htt_4_1_1_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace_right_kanComplex")
*HTT 注意 4.1.1.2*　右ファイブレーションの相対切断空間（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=241)）。対応表の状態：本体にある。

*主張*　底上の相対写像空間 $`\operatorname{Map}_T(S,X)` は $`X^S\to T^S` の構造射 $`S\to T` 上のファイバーであり、$`X\to T` が右ファイブレーションなら Kan 複体である。

仮定：右ファイブレーションと任意の底図式（HTT と一致）。結論：相対切断空間を内部 Hom の射の指定頂点繊維として定め、その Kan 性を与える（一致）。

パラメータをつけた $`S` から $`X` への写像のうち、底への合成を定値に固定する。ファイバーを取ることで、この相対条件が全次元で保たれる。

:::

:::proposition "htt_4_1_1_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_isIso, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal.comp, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal.cancel_left, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal.isWeakHomotopyEquivalence, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_iff_rightAnodyne_of_mono")
*HTT 命題 4.1.1.3*　共終性の合成・消去と右アノダイン性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=241)）。対応表の状態：本体にある。

*主張*　単体的同型は共終で、共終射を前合成しても共終性は同じであり、共終射は弱ホモトピー同値、単射の場合は共終性と右アノダイン性が同値である。

仮定：同型、合成可能な射で前半が共終、共終な射、または単射（HTT と一致）。結論：同型の共終性、前半が共終な合成に対する後半の共終性の同値、共終射の弱ホモトピー同値性、単射における右アノダイン性との同値を得る（一致）。

共終性を切断空間の比較として読むと、合成の判定はその比較の二つずつの性質になる。単射のときは右ファイブレーションへの持ち上げで、より具体的な射のクラスとしても記述できる。

:::

:::lemma_ "htt_4_1_1_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberHomEquiv, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberRightMappingEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftRightEquivalence")
*HTT 補題 4.1.1.5*　二つの結合で定める写像空間の比較（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=242)）。対応表の状態：一部（special）。

*主張*　図式 $`p:K\to\mathcal C` と $`q:K'\to\mathcal C` に対し、片側ずつパラメータを付けた join $`(X\times K)\star K'` と $`K\star(X\times K')` 上の両端固定写像を表す二つの単体集合は Kan 複体で、自然にホモトピー同値である。

KB-W2原文・型再照合：仮定：準圏の二つの図式（Lean が強い：二図式が一点の場合）。結論：結合で表したコスライス繊維と左右の写像空間を同値で比較する（Lean が弱い：両側が任意の図式の場合の二つの Kan 複体の比較は含まない）。

どちらでも両端の図式は固定し、図式間の比較だけを動かす。パラメータを左の因子に入れるか右の因子に入れるかで模型は変わるが、比較が記録するホモトピー型は変わらない。

:::

:::proposition "htt_4_1_1_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.sliceUnderRestrict_equivalence_of_rightCofinal, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_isQCatEquivalence_iff_fibers, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection")
*HTT 命題 4.1.1.7*　共終な制限による余錐の繊維同値（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=244)）。対応表の状態：一部（special）。

*主張*　共終射 $`v:K'\to K` に沿う図式の制限は、余錐の圏の射 $`\mathcal C_{p/}\to\mathcal C_{pv/}` を底 $`\mathcal C` 上の左ファイブレーションの同値にする。

KB-W2原文・型再照合：仮定：準圏の図式を共終写像で制限する（Lean が強い：元の添字単体集合も準圏）。結論：同じ余錐制限の全空間での同値を、射影との可換性と左ファイブレーションの繊維判定に代入し、各頂点の繊維上の同値を得る（HTT の同じ繊維射。任意の添字単体集合は含まない）。

具体的には余錐の頂点を任意の $`x` に固定したとき、元の図式からの余錐と制限後の図式からの余錐の Kan 複体がホモトピー同値になる。

:::

:::proposition "htt_4_1_1_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.sliceUnderRestrict_equivalence_of_rightCofinal, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal") (uses := "htt_1_1_2_4")
*HTT 命題 4.1.1.8*　共終性の余錐圏と余極限による判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=244)）。対応表の状態：一部（direction）。

*主張*　単体的写像が共終であることは、任意の ∞ 圏値図式で余錐の圏の制限が同値になること、または任意の余極限余錐が制限後も余極限であることと同値である。

KB-W2原文・型再照合：仮定：共終な形状の射と準圏の図式（Lean が強い：元の添字が準圏で、共終性を仮定する向き）。結論：余錐圏の制限は同値となり、指定余錐の余極限性を保存・反映する（Lean が弱い：余錐圏の同値または全図式の余極限保存から共終性を検出する向きは含まない）。

普遍な余錐を制限した余錐の普遍性を比べるため、余極限の頂点に加え脚も同じ制限で運ぶ。二番目の性質は、余極限だけでなく余錐の全体を比較する。

:::

:::corollary "htt_4_1_1_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.trivialKanFibration_iff_rightFibration_and_isRightCofinal")
*HTT 系 4.1.1.11*　共終な右ファイブレーションの自明性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=245)）。対応表の状態：本体にある。

*主張*　共終な右ファイブレーションはちょうど自明ファイブレーションである。

仮定：任意の単体集合の射（HTT と一致）。結論：自明 Kan ファイブレーションであることと、共終な右ファイブレーションであることが同値（一致）。

共終性は切断空間の制限で定義されるが、射そのものに右ファイブレーション性があると、さらに全境界への持ち上げが従う。

:::

:::corollary "htt_4_1_1_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_iff_exists_anodyne_trivialKan_factorization")
*HTT 系 4.1.1.12*　共終写像の右アノダイン因子分解（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=246)）。対応表の状態：本体にある。

*主張*　単体的写像が共終であることは、右アノダイン射の後に自明ファイブレーションを続ける形へ因子分解できることと同値である。

仮定：任意の単体集合の射（HTT と一致）。結論：共終性と、右アノダイン射と自明 Kan ファイブレーションに分解できることが同値（一致）。

前半は単体的な付け足しで右ファイブレーションに対する左持ち上げ性を持つ。後半は全境界を持ち上げる射であり、共終性はその両方の合成を特徴づける。

:::

:::corollary "htt_4_1_1_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_whiskerLeft")
*HTT 系 4.1.1.13*　共終写像の任意の直積での保存（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=246)）。対応表の状態：本体にある。

*主張*　共終な単体的写像と任意の単体的集合の恒等射との積は共終である。

仮定：共終写像と任意の単体集合 K（HTT と一致）。結論：K と直積を取った誘導射は共終（一致）。

積の追加因子は切断を記述するパラメータとして読むことができる。共終性の判定がそのパラメータを入れた比較にも伝わる。

:::

# 4.1.2 Smoothness and Right Anodyne Maps

%%%
number := false
tag := "htt-4-1-2"
%%%

:::corollary "htt_4_1_2_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.rightAnodyneExtensions_iff_mono_and_isRightCofinal, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal.cancel_left")
*HTT 系 4.1.2.2*　右アノダイン射の左消去（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=247)）。対応表の状態：本体にある。

*主張*　単体的写像 $`i:A\to B`、$`j:B\to C` に対し、$`i` と $`ji` が右アノダインで $`j` が単射なら、$`j` も右アノダインである。

仮定：i と i≫j が右アノダインで j が単射（HTT の余ファイブレーションは単射）。結論：同じ二射から得た共終性を左消去に代入すると j は共終となり、j の単射性と合わせて同じ同値の逆向きにより右アノダインとなる（一致）。

まず共終性の前合成についての判定で $`j` の共終性を得る。右アノダイン性へ戻す段階で $`j` の単射性を使う。

:::

:::corollary "htt_4_1_2_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal.isWeakHomotopyEquivalence")
*HTT 系 4.1.2.6*　Kan 複体上の共終性と弱ホモトピー同値（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=248)）。対応表の状態：一部（direction）。

*主張*　底が Kan 複体である単体的写像は、共終であることと弱ホモトピー同値であることが同値である。

KB-W2原文・型再照合：仮定：Kan 複体を終域とする射（Lean が弱い：終域に Kan 性を要求しない）。結論：同じ共終射は弱ホモトピー同値となる（Lean が弱い：Kan 終域での逆向きを含まない）。

任意の底の場合、共終性は弱ホモトピー同値より強い。底が空間の模型ならその追加の向きの情報が消えるので、弱ホモトピー型の比較だけで判定できる。

:::

:::corollary "htt_4_1_2_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.rightAnodyneExtensions_iff_mono_and_isRightCofinal, CategoryTheory.MorphismProperty.of_isPushout")
*HTT 系 4.1.2.7*　押し出しによる共終性の保存（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=248)）。対応表の状態：一部（special）。

*主張*　共終な写像の押し出しは、その写像または押し出しに使う写像のどちらかが単射なら共終である。

KB-W2原文・型再照合：仮定：共終射 f の押し出しで f または相手の射が単射（Lean が強い：f 自身が単射の場合）。結論：f の右アノダイン性を同じ押し出しに移し、右アノダイン射は共終という同じ判定から押し出された f の共終性を得る（一致する場合。相手側のみが単射の場合は含まない）。

押し出しによって元の比較を新しい対象へ貼る。単射の条件は貼り合わせに対する仮定で、共終写像自体に必ず単射性を課すわけではない。

:::

:::definition "htt_4_1_2_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.leftFibration_overPullback_rightAnodyne")
*HTT 定義 4.1.2.9*　滑らかな単体集合の写像（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=250)）。対応表の状態：一部（special）。

*主張*　単体的写像が smooth であるとは、第4.1.2.8項の同値な条件、特に任意の底変換後に右アノダイン射の引き戻しが右アノダインになることを満たすことをいう。

KB-W2原文・型再照合：仮定：単体集合の射 p（Lean が強い：p が左ファイブレーション）。結論：任意の右アノダイン射を p に沿って引き戻しても右アノダインとなる（原典が定義に使う条件 (1) と一致。任意の p に対する述語はない）。

右アノダイン性を引き戻す判定を、最初に選んだ底だけでなく、先に底を替えたすべての場合に課す。ここでの smooth は単体的集合の持ち上げと共終性に関する用語である。

:::

:::proposition "htt_4_1_2_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.leftFibration_pullback_isRightCofinal")
*HTT 注意 4.1.2.10*　滑らかな写像に沿う共終性の保存（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=250)）。対応表の状態：一部（special）。

*主張*　smooth な単体的写像に沿って共終写像を引き戻すと、引き戻した写像も共終である。

KB-W2原文・型再照合：仮定：滑らかな写像 p と共終射 f（Lean が強い：p が左ファイブレーション）。結論：同じ引き戻しの射は共終（一致）。

共終射が単射でなくても主張できる。右アノダインな場合に対する定義と、共終射の因子分解の記述を組み合わせる。

:::

:::proposition "htt_4_1_2_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.leftFibration_overPullback_rightAnodyne, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_cocartesianFibration") (uses := "htt_2_4_2_1, htt_4_1_1_3")
*HTT 命題 4.1.2.15*　余デカルトファイブレーションの滑らかさ（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=252)）。対応表の状態：一部（special）。

*主張*　余 Cartesian ファイブレーションは smooth である。

KB-W2原文・型再照合：仮定：余デカルトファイブレーション p（Lean が強い：p が左ファイブレーションで、余デカルトファイブレーションの instance がある）。結論：同じ切片で右アノダイン射の引き戻しが右アノダインとなる（滑らかさの条件 (1) と一致）。

余 Cartesian な持ち上げを使えることから、底の共終比較を引き戻した結果にも同じ共終性が移る。前向きの移送が、この主張の向きを決める。

:::

# 4.1.3 Quillen’s Theorem A for ∞-Categories

%%%
number := false
tag := "htt-4-1-3"
%%%

:::theorem "htt_4_1_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_iff_weaklyContractible_coslices")
*HTT 定理 4.1.3.1*　コスライスによるクイレンの定理 A（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=254)）。対応表の状態：本体にある。

*主張*　$`\mathcal D` が ∞ 圏のとき $`f:\mathcal C\to\mathcal D` が共終であることは、各対象 $`d` について $`\mathcal C\times_{\mathcal D}\mathcal D_{d/}` が弱可縮であることと同値である。

仮定：終域が準圏である任意の単体集合の射 f（HTT と一致）。結論：f が共終であることと、各頂点のコスライスとの引き戻しが弱可縮であることが同値（一致）。

この比較の頂点は $`c` と $`d\to f(c)` の組である。単に各 $`d` がどこかの像へ射を持つだけでなく、それらの選択全体の弱ホモトピー型が点になることを要求する。

:::

:::lemma_ "htt_4_1_3_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.rightFibration_trivialKanFibration_of_weaklyContractible_fibers, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.rightFibration_cartesianFibration")
*HTT 補題 4.1.3.2*　弱可縮な繊維をもつデカルト射の共終性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=254)）。対応表の状態：一部（special）。

*主張*　頂点ファイバーがすべて弱可縮な Cartesian ファイブレーションは共終である。

KB-W2原文・型再照合：仮定：デカルトファイブレーション p の全頂点繊維が弱可縮（Lean が強い：p が右ファイブレーションで、デカルトファイブレーションの instance がある）。結論：同じ p に対する自明 Kan ファイブレーションの判定を直ちに共終性の宣言に適用すると p は共終（一致）。

各点の上を一点と同じ弱ホモトピー型とみなせる場合、底上での比較にファイバーの新しい情報が加わらない。ここでは元の写像に Cartesian の条件を置いている。

:::

:::corollary "htt_4_1_3_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.nerveMap_isRightCofinal_of_weaklyContractible_comma, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal.isWeakHomotopyEquivalence")
*HTT 系 4.1.3.3*　通常圏の神経に対するクイレンの定理 A（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=256)）。対応表の状態：本体にある。

*主張*　通常関手 $`f:\mathcal C\to\mathcal D` について、各 $`d` のコンマ圏 $`d\downarrow f` の nerve が弱可縮なら、$`N(f)` は弱ホモトピー同値である。

仮定：通常圏の関手 F と各対象のコンマ圏の神経の弱可縮性（HTT の引き戻し圏を StructuredArrow で表現）。結論：神経の射の共終性を弱ホモトピー同値の宣言へそのまま適用して同じ神経の射の弱ホモトピー同値を得る（一致）。

コンマ圏の矢印は $`d\to f(c)` の三角形が可換になるもの。これを nerve にして共終性の判定に用いると、元の二つの通常圏のホモトピー型を比較できる。

:::

