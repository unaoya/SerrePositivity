import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CosliceConverse
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.Isofibration
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationTrivialComparison
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCocartesianFibration
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinderEquivalence
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinderIntervalExtension
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.RelativeColimitTerminalIndex
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftIdentityLeg
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftUnitInvertible
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeCoconeReindexExtension
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftCanonical
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftCanonicalExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftFunctorInitial
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftRestrictionTheorem
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftUnitCanonical
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeRightOppositeCriterion
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Shapes
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LeftCanonicalRestriction
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeColimitFunctorIso
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeColimitTrivialComparison
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialBoundaryCriterion
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.RelativeCoslice
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 4.3 Kan Extensions" =>
%%%
number := false
tag := "htt-4-3"
%%%

HTT 4.3 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 4.3.1 Relative Colimits

%%%
number := false
tag := "htt-4-3-1"
%%%

:::definition "htt_4_3_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceMap, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration")
*HTT 定義 4.3.1.1*　相対余極限を定めるコスライス比較（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=279)）。対応表の状態：本体にある。

*主張*　内ファイブレーション $`f:\mathcal C\to\mathcal D` に対する相対余極限余錐は、余錐をさらに延ばす相対制限 $`\mathcal C_{\bar p/}\to\mathcal C_{p/}\times_{\mathcal D_{fp/}}\mathcal D_{f\bar p/}` が自明ファイブレーションになる余錐 $`\bar p` である。

仮定：内ファイブレーションと右結合上の余錐（Lean が弱い：比較射と自明 Kan 性の述語には内ファイブレーション性が不要）。結論：余錐の底を結合の部分複体として指定すると、制限と後合成からなる同じ引き戻し比較射の自明 Kan 性が HTT の定義になる（一致）。

試験する延長は、元図式 $`p` 上の余錐と $`\bar p` の像の上の余錐を同時に指定する。底で決めた脚を動かさずに、余錐の普遍性が成り立つことを要求する。

:::

:::proposition "htt_4_3_1_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceMap_leftFibration, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.trivialKanFibration_of_leftFibration_of_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration")
*HTT 注意 4.3.1.2*　相対余極限の圏同値による判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=279)）。対応表の状態：一部（component）。

*主張*　相対余極限の定義にある比較は、圏同値であることを調べれば自明ファイブレーションであると判定できる。

KB-W2原文・型再照合：仮定：内ファイブレーションと右結合上の余錐（Lean が強い：圏同値の判定では始域と終域が準圏）。結論：同じ相対コスライス比較の自明 Kan 性と準圏同値性が同値（Joyal 模型でのホモトピー引き戻しの同定は含まない）。

この比較は相対スライスの構成によって左ファイブレーションになる。任意の単体的写像の圏同値からは出ない境界持ち上げが、この追加の性質により従う。

:::

:::proposition "htt_4_3_1_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_isColimit_of_terminal")
*HTT 例 4.3.1.3*　一点を底とする相対余極限（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=279)）。対応表の状態：本体にある。

*主張*　一点への写像に相対的な余極限は、通常の ∞ 圏での余極限と一致する。

仮定：準圏から一点への射と指定余錐（Lean が弱い：標的を終対象として指定できる）。結論：同じ余錐の相対余極限性と絶対余極限性が同値（一致）。

底における追加の一致条件は一点上で自動的になる。残る試験は余錐圏の中の指定余錐の始対象性である。

:::

:::proposition "htt_4_3_1_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_iff_relativeCosliceMap_trivialKanFibration")
*HTT 例 4.3.1.4*　一点図式の相対余極限と余デカルト辺（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=279)）。対応表の状態：本体にある。

*主張*　一頂点の図式を延ばした辺が内ファイブレーションに相対的な余極限となることは、その辺が余 Cartesian であることと同値である。

仮定：内ファイブレーション上の辺（Lean が弱い：内ファイブレーション性を要求しない）。結論：余デカルト辺であることと、初頂点を Λ\[1,0\] で固定した同じ相対コスライス比較の自明 Kan 性が同値（一致）。

一頂点に対する余錐は辺一本になる。指定した底の辺に沿う相対的な普遍性を、この場合には余 Cartesian 辺の条件として読める。

:::

:::proposition "htt_4_3_1_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_of_functorIso") (uses := "htt_1_1_2_4, htt_2_0_0_3")
*HTT 命題 4.3.1.5*　相対余極限の合成・同型・底変換（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=279)）。対応表の状態：一部（component）。

*主張*　相対余極限は自明ファイブレーションに対して常に成り立ち、底変換と余錐の同値で保たれ、内ファイブレーションの合成では像の余錐が後半に相対的な余極限なら前半と合成に対する判定が一致する。

KB-W2原文・型再照合：仮定：内ファイブレーションと関手準圏で同値な二つの余錐（HTT の (3) と一致）。結論：二つの余錐の相対余極限性が同値（結論 (3) が一致。他の安定性はこの宣言に含まれない）。

自明ファイブレーションの場合には指定比較を全境界まで持ち上げられる。合成の比較では、まず後半の底で普遍性を使い、元の余錐の相対的な性質を前半へ戻す。

:::

:::proposition "htt_4_3_1_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_comp_iff_of_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_precomp_iff_of_trivialKanFibration")
*HTT 命題 4.3.1.6*　圏同値なファイブレーションへの移送（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=280)）。対応表の状態：一部（stronger-hyp）。

*主張*　内ファイブレーション間の可換な四角形の上下の横射が圏同値なら、指定余錐が相対余極限であることは上の同値によるその像についての相対余極限性に等しい。

KB-W2原文・型再照合：仮定：内ファイブレーションを縦射とする可換四角形で横射が圏同値（Lean が強い：横射がともに自明 Kan ファイブレーション）。結論：前合成と後合成の同値を同じ四角形に適用し、指定余錐とその像の相対余極限性が同値（一致する場合）。

上の圏だけでなく底の比較も同値であるため、相対条件を記述する引き戻しの両側を同値で比べられる。もとの余錐とその像を比較する点が重要である。

:::

:::proposition "htt_4_3_1_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.kanIsRelativeColimitCone_iff_restrict_of_rightAnodyne") (uses := "htt_1_1_2_4, htt_2_0_0_3, htt_4_1_1_1")
*HTT 命題 4.3.1.7*　共終な添字変更での相対余極限（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=281)）。対応表の状態：一部（stronger-hyp）。

*主張*　∞ 圏間の内ファイブレーションに相対的な余極限かどうかは、共終な添字の写像で指定余錐を制限しても変わらない。

KB-W2原文・型再照合：仮定：内ファイブレーション上の余錐と共終な添字変更（Lean が強い：添字変更は右アノダインな単射）。結論：同じ余錐の制限前後で相対余極限性が同値（一致）。

同じ余錐頂点と同じ底の脚を維持し、図式の添字だけを共終なものへ替える。余錐の比較を相対化しても共終性の計算が使える。

:::

:::proposition "htt_4_3_1_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeColimit_extension_over_precompositionEquivalence, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianFibration_kanEquivalenceLifting")
*HTT 命題 4.3.1.8*　共終な部分図式からの相対余極限の延長（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=281)）。対応表の状態：一部（stronger-hyp）。

*主張*　余 Cartesian ファイブレーションでは、指定した底の余錐を持ち上げる相対余極限が共終な部分図式で存在すれば、元図式にも同じ底の余錐の上に存在する。

KB-W2原文・型再照合：仮定：余デカルトファイブレーション上で底の余錐と制限の相対余極限を指定（Lean が強い：添字変更は圏同値な単射）。結論：指定した底の余錐に写る相対余極限の延長がある（Lean が強い：部分余錐も厳密に回収する）。

ここでの結論は、すでに存在する余錐の普遍性を比較するだけでなく、指定された底図式を保つ余錐を供給する。共終制限で得た持ち上げから全図式へ戻す。

:::

:::proposition "htt_4_3_1_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_of_functorIso") (uses := "htt_1_1_2_4, htt_1_2_13_4, htt_2_0_0_3")
*HTT 命題 4.3.1.9*　余デカルトな変換による相対余極限の移送（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=282)）。対応表の状態：一部（stronger-hyp）。

*主張*　二つの余錐の間の自然変換がすべての頂点で余 Cartesian で、錐点における底の辺が退化していれば、二つの相対余極限性は同値である。

KB-W2原文・型再照合：仮定：点ごとに余デカルトで頂点の底の像が退化する余錐間の変換（Lean が強い：変換が関手準圏の同型を与える場合に適用）。結論：同じ二余錐の相対余極限性が同値（一致する場合）。

余錐全体を点ごとに輸送する条件を課す。とくに錐点の像を動かさないことで、底から固定していた普遍性の比較を二つの余錐に適用できる。

:::

:::proposition "htt_4_3_1_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_iff_relativeCosliceMap_trivialKanFibration")
*HTT 命題 4.3.1.12*　弱可縮な図式の余デカルト余錐（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=285)）。対応表の状態：一部（special）。

*主張*　余 Cartesian ファイブレーションへの余錐の底図式の形 $`K` が弱可縮で、$`K` 上の全辺が余 Cartesian なら、余錐が相対余極限であることは錐を加えた全辺が余 Cartesian であることと同値である。

KB-W2原文・型再照合：仮定：弱可縮な添字の全辺を余デカルト辺に送る余錐（Lean が強い：添字が一点の場合に適用）。結論：相対余極限であることと、余錐の唯一の非退化辺が余デカルトであることが同値（一致する場合）。

図式内の輸送はすでに余 Cartesian に固定されている。残る錐点への各脚について同じ性質を検査すれば、可縮な形の相対普遍性が得られる。

:::

# 4.3.2 Kan Extensions along Inclusions

%%%
number := false
tag := "htt-4-3-2"
%%%

:::definition "htt_4_3_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape")
*HTT 記法 4.3.2.1*　部分圏に制限したスライス（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=289)）。対応表の状態：本体にある。

*主張*　充満部分圏 $`\mathcal C'\subseteq\mathcal C` に対し、$`\mathcal C'_{/p}` は $`\mathcal C_{/p}` を頂点への射影で $`\mathcal C'` に引き戻したものである。

仮定：準圏の充満部分圏と指定頂点（Lean が弱い：任意の単体集合の射と頂点）。結論：指定頂点のスライスを始点射影に沿って部分圏へ引き戻す（一致）。

固定した図式へ入る錐のうち、錐点だけを $`\mathcal C'` に制限する。図式が対象一点なら、対象への射のうち始点が部分圏に入るものを集める。

:::

:::definition "htt_4_3_2_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtendedFrom, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone")
*HTT 定義 4.3.2.2*　充満部分圏からの相対左 Kan 拡張（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=289)）。対応表の状態：本体にある。

*主張*　充満包含に沿う関手の延長が $`p`-左 Kan 拡張であるとは、各対象 $`C` で $`\mathcal C'_{/C}` 上の元関手から得る指定余錐が $`p`-相対余極限であることをいう。

仮定：充満部分圏上の制限と値域の内ファイブレーション（Lean が弱い：定義は任意の添字写像と値域写像を取る）。結論：同じスライス引き戻しから作る標準余錐に、各頂点で値域写像に関する相対余極限性を課す（一致）。

$`C` に入る部分圏の対象のすべてを添字にして、延長後の値への脚を読む。底が一点のときは各点の通常の余極限条件になる。

:::

:::proposition "htt_4_3_2_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonical_isColimit_at_image")
*HTT 注意 4.3.2.3*　部分圏の像における左 Kan 条件（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=290)）。対応表の状態：一部（special）。

*主張*　左 Kan 拡張の点ごとの条件は、充満部分圏にすでに属する対象では自動的である。

KB-W2原文・型再照合：仮定：充満部分圏の像にある頂点（Lean が強い：値域の底が一点で相対条件が絶対化する場合に適用）。結論：同じ頂点での標準左 Kan 余錐が余極限（一致する場合）。

部分圏内の対象 $`C` については、$`C` の恒等射が $`\mathcal C'_{/C}` の終対象になる。この余極限の試験は恒等射に対応する図式まで縮められる。

:::

:::lemma_ "htt_4_3_2_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeLeftKanExtendedFrom_of_functorIso")
*HTT 補題 4.3.2.6*　相対左 Kan 拡張の同型と圏同値不変性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=291)）。対応表の状態：一部（component）。

*主張*　相対左 Kan 拡張の性質は関手の同値で不変であり、充満包含・値域・底を可換に圏同値で取り替えても不変である。

KB-W2原文・型再照合：仮定：内ファイブレーションと関手準圏で同型な二関手（HTT の (1) と一致）。結論：関手同型とその逆に適用すると相対左 Kan 条件が同値（結論 (1) が一致。図式全体の圏同値での移送 (2) は含まない）。

元の部分圏の各対象からの射で作る添字圏も、対応する添字圏に移る。そこで比較した指定余錐の相対普遍性を使う。

:::

:::lemma_ "htt_4_3_2_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeInitialVertex_iff_initialBoundary")
*HTT 補題 4.3.2.10*　初頂点を固定した単体の積の境界充填（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=296)）。対応表の状態：一部（special）。

*主張*　内ファイブレーションの $`\Delta^m\times\Delta^n` 上の問題で両因子から来る全境界を固定したとき、$`(0,0)` の像が相対始対象なら延長が存在する（$`m\ge0,n\ge1`）。

KB-W2原文・型再照合：仮定：相対始対象が指定された積の境界の持ち上げ問題（Lean が強い：m=0 で始域・終域が準圏の場合）。結論：積の境界が Δⁿ の境界に一致するので、同じ四角形の持ち上げを相対始点の境界充填から得る（一致する場合）。

延長前に両方の境界面の族を与えておく。始点の条件は左下の一頂点で課し、一般にすべての頂点で相対始対象であることは求めない。

:::

:::lemma_ "htt_4_3_2_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftFunctor_relative_initialBoundary")
*HTT 補題 4.3.2.12*　相対左 Kan 関手を始点とする境界充填（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=297)）。対応表の状態：本体にある。

*主張*　圏論的ファイブレーションを値域側に持つ相対関手の充満部分圏への制限で、境界の頂点 $`0` が相対左 Kan 拡張を表すなら、その境界持ち上げ問題は解ける。

仮定：充満部分圏と圏ファイブレーション、境界の初頂点が指定の相対左 Kan 関手（HTT と一致。Lean は圏ファイブレーション性を同値な単射の持ち上げで表す）。結論：同じ関手準圏の相対制限に対して、初頂点を指定した全ての正次元境界の持ち上げがある。固定底図式の問題は底成分を定値にして適用できる（一致）。

$`n>0` の境界で部分圏への制限をすでに延ばしてある。元の圏での延長を作るには、最初の頂点において指定された点ごとの普遍性を使う。

:::

:::lemma_ "htt_4_3_2_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeLeftCanonical_strict_extension_of_local_relative_colimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtendedFrom")
*HTT 補題 4.3.2.13*　局所相対余極限からの左 Kan 拡張の存在（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=300)）。対応表の状態：本体にある。

*主張*　圏論的ファイブレーションに相対的な左 Kan 拡張が存在することは、各対象 $`C` で誘導される $`\mathcal C'_{/C}` 上の図式が指定底の余錐と両立する相対余極限を持つことと同値である。

仮定：充満部分圏の包含と圏ファイブレーション上の可換四角形（Lean では後者を同値な単射の持ち上げ性で表す）。結論：指定した底の余錐を保つ局所相対余極限から、制限と底の等式を保つ左 Kan 拡張が存在する。逆向きはその点ごとの定義（一致）。

点ごとの候補が存在するだけでは、関手としての射や高次単体の整合性はまだ指定されない。この定理が点ごとの存在を全体の関手へまとめる。

:::

:::proposition "htt_4_3_2_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction_trivialKanFibration") (uses := "htt_1_1_2_4")
*HTT 命題 4.3.2.15*　相対左 Kan 関手の制限の自明 Kan 性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=302)）。対応表の状態：一部（stronger-hyp）。

*主張*　相対左 Kan 拡張である相対関手の充満部分圏から、すべての点ごとの相対余極限を持つ制限図式の充満部分圏への制限は自明ファイブレーションである。

KB-W2原文・型再照合：仮定：充満部分圏の包含と圏ファイブレーション（Lean が強い：固定した底図式だけでなく、両立する任意の部分図式と底図式に対して局所相対余極限を要求）。結論：この仮定では標的の全関手が条件を満たす。相対左 Kan 関手の制限は自明 Kan ファイブレーションであり、固定底図式への引き戻しも自明 Kan となる（一致する場合）。

存在と同値までの一意性に加え、指定境界を含む延長ができる。二つの充満部分圏は、同じ制限を見る始域側と値域側の範囲を表している。

:::

:::corollary "htt_4_3_2_16" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section") (uses := "htt_1_1_2_1, htt_1_1_2_4, htt_4_3_2_15")
*HTT 系 4.3.2.16*　相対左 Kan 拡張を選ぶ制限射の切断（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=302)）。対応表の状態：一部（stronger-hyp）。

*主張*　部分圏上のすべての相対関手が相対左 Kan 拡張を持つなら、制限関手には切断があり、その本質像は相対左 Kan 拡張の全体で、選び方の空間は可縮である。

KB-W2原文・型再照合：仮定：部分圏上の全関手に相対左 Kan 拡張が存在（Lean が強い：固定した底図式だけでなく、両立する任意の部分図式と底図式に対する局所相対余極限を要求）。結論：同じ相対制限の自明 Kan 性から切断を得る。切断の値は相対左 Kan 関手の充満部分圏にあり、同じ制限の繊維が可縮なのでその部分圏の全関手を本質像に含む（一致する場合）。

この切断は対象ごとの独立な選択ではなく、元の関手圏全体に対する関手として与えられる。前の項の自明ファイブレーションが全単体での選択を支える。

:::

:::proposition "htt_4_3_2_18" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeRightKanExtendedFrom_iff_op_left")
*HTT 注意 4.3.2.18*　反対準圏による相対右 Kan 拡張（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=303)）。対応表の状態：本体にある。

*主張*　相対右 Kan 拡張の理論は、反対 ∞ 圏への移行により相対左 Kan 拡張から得られる。

仮定：値域の準圏間の射、部分圏への制限、指定の関手（Lean が弱い：添字の写像を任意に取れる）。結論：右相対 Kan 条件は、値域・添字・関手の全てを反転した左相対 Kan 条件と同値（一致）。

反対化すると余極限が極限へ、対象へ入るスライスが対象から出るスライスへ移り、点ごとの右 Kan 拡張の条件に変わる。

:::

# 4.3.3 Kan Extensions along General Functors

%%%
number := false
tag := "htt-4-3-3"
%%%

:::definition "htt_4_3_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge")
*HTT 定義 4.3.3.1*　一般の添字写像に沿う左延長のデータ（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=303)）。対応表の状態：本体にある。

*主張*　$`\delta:K\to K'` に沿う $`f:K\to\mathcal D` の左延長は図式 $`f':K'\to\mathcal D` と変換 $`f\to f'\delta` の組で、$`\delta` の向きを指定した写像柱体からの写像として表せる。

仮定：単体集合の写像 δ と延長先の図式、元の図式（Lean が弱い：値域の準圏性は不要）。結論：元の図式と δ への制限の間の関手準圏の辺は、両端を固定した単体ホモトピーと相互変換でき、左延長の指定自然変換を表す（一致）。

柱体 $`K\times\Delta^1` の終端を $`\delta` により $`K'` へ貼る。最初の端で $`f` を固定すると、区間に沿う写像が変換の向きを記録する。

:::

:::proposition "htt_4_3_3_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection_cocartesianFibration, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_relativeJoinCylinderComparison, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison_intervalProjection")
*HTT 注意 4.3.3.3*　相対結合の区間上の余デカルト性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=304)）。対応表の状態：一部（special）。

*主張*　一般の関手に沿う左 Kan 拡張を調べるため第4.3.3.2項で選んだ模型 $`K\to\Delta^1` は、自動的に余 Cartesian ファイブレーションである。

KB-W2原文・型再照合：仮定：写像円筒と区間上で圏同値な準圏の模型（Lean が強い：準圏間の写像に対する標準の相対結合を選ぶ）。結論：同じ区間への射影が余デカルトファイブレーション（一致する場合。任意の模型への移送は含まない）。

写像柱体を標識付きの因子分解で比較し、向きを反対化した模型の Cartesian 性を使う。この結論は指定された模型についてであり、任意の写像柱体の射影を直接扱う主張ではない。

:::

:::proposition "htt_4_3_3_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanExtension_unit_component_isIso")
*HTT 命題 4.3.3.8*　充満忠実性による左 Kan 単位の可逆性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=306)）。対応表の状態：一部（stronger-hyp）。

*主張*　左 Kan 拡張 $`f_0\to f_1\delta` の成分は、ある対象 $`C` へのすべての写像空間を $`\delta` が同値にするなら、その $`C` において同値である。

KB-W2原文・型再照合：仮定：指定対象への写像空間の比較が同値である左 Kan 拡張（Lean が強い：δ が内ファイブレーションかつ全対象で充満忠実）。結論：同じ単位の指定成分がホモトピー圏で可逆（一致）。

要求する充満忠実性は終点を $`C` に固定した部分で足りる。点ごとの余極限式では、その対象の恒等射が対応する添字圏の終対象となり、余極限がもとの値に戻る。

:::

