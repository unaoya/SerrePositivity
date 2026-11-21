-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
import Mathlib.AlgebraicTopology.SimplicialSet.Coskeletal
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.ThinNerveInnerFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.EquivalenceTerminal
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.CompositionTriangleSpace
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.ContractibleKan
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.InnerAnodyneEquivalence

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 2.3 Inner Fibrations" =>
%%%
number := false
tag := "htt-2-3"
%%%

HTT 2.3 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

:::proposition "htt_2_3_0_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.thinNerve_innerFibration")
*HTT 例 2.3.0.1*　通常圏の nerve の内ファイブレーション（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=114)）。対応表の状態：一部（special）。

*主張*　通常関手の nerve は内ファイブレーションになるが、その頂点ファイバーは底で同型な対象どうしでも異なり得る。

KB-W2原文・型再照合：仮定：通常 F:C→C′ で底 C′ が thin（Lean が強い特殊形）。結論：X=N(C) は準圏であり thinNerve\_innerFibration により N(F) は InnerFibration。最初の文のこの特殊形に一致する。底が非 thin の場合と、同型な底の二繊維が異なる実例は含まない。

内角は二射の合成を扱い、底の同型に沿う対象の移送までは要求しない。したがって内ファイブレーション一般のファイバーを関手的に比較するには別の構成が必要になる。

:::

# 2.3.1 Correspondences

%%%
number := false
tag := "htt-2-3-1"
%%%

:::proposition "htt_2_3_1_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.thinNerve_innerFibration, SSet.quasicategory_of_innerFibration")
*HTT 命題 2.3.1.5*　通常圏の nerve 上の内ファイブレーション判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=115)）。対応表の状態：一部（direction）。

*主張*　通常圏の nerve $`N(\mathcal C)` への写像 $`X\to N(\mathcal C)` が内ファイブレーションであることは、$`X` 自身が ∞ 圏であることと同値である。

KB-W2原文・型再照合：仮定：任意の通常圏 C と p:X→N(C) が inner fibration（原典の順方向と一致）。結論：N(C) の準圏性と quasicategory\_of\_innerFibration から X は準圏。逆向きは thin な C の場合のみで、一般の C に対する iff は含まない。

$`X` 内の角を先に埋めると、底への像は指定した角の充填になる。底が通常圏の nerve ならその充填は一意なので、最初に指定した底の単体に一致する。

:::

# 2.3.2 Stability Properties of Inner Fibrations

%%%
number := false
tag := "htt-2-3-2"
%%%

:::proposition "htt_2_3_2_1" (lean := "SSet.innerAnodyneExtensions_pushoutObjObjι, SSet.prodStdSimplex.innerAnodyneExtensions_unionProd_ι")
*HTT 命題 2.3.2.1*　内アノダイン射の三つの生成系（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=117)）。対応表の状態：一部（direction）。

*主張*　内アノダイン射の弱飽和類は、内角包含全部でも、$`\Lambda^2_1\hookrightarrow\Delta^2` と境界包含の押し出し積でも、同じ二次元内角と任意の単射の押し出し積でも生成される。

KB-W2原文・型再照合：仮定：boundary×inner horn、または mono×inner-anodyne の pushout-product（HTT の A2/A3 と一致）。結論：第二・第三の生成射は inner anodyne、したがってそれらの閉包⊆第一の閉包という方向に一致。逆包含と二次元ホーンから全 inner horns を生成する比較は含まない。

任意の高次内角を直接試験する条件を、二射の合成を表す二次元角と、その変形のパラメータに分けて検査できる。

:::

:::corollary "htt_2_3_2_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.trivialKanFibration_pre_of_innerAnodyne")
*HTT 系 2.3.2.2*　二次元内ホーン制限による準圏判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=118)）。対応表の状態：一部（direction）。

*主張*　単体的集合 $`\mathcal C` が ∞ 圏であることは、$`\operatorname{Fun}(\Delta^2,\mathcal C)\to\operatorname{Fun}(\Lambda_1^2,\mathcal C)` が自明ファイブレーションであることと同値である。

KB-W2原文・型再照合：仮定：C が準圏、制限射を二次元 inner horn とする（順方向の仮定と一致）。結論：trivialKanFibration\_pre\_of\_innerAnodyne によりその同じ restriction は自明 Kan fibration。逆向きはない。

制限のファイバーが記録するのは、固定された二辺を三角形へ延長する全データである。パラメータつきの境界持ち上げまで要求することで、二次元の存在条件にとどまらず全内角が扱える。

:::

:::proposition "htt_2_3_2_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleSpace_isContractibleKan")
*HTT 注意 2.3.2.3*　指定二辺の合成の選択空間（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=118)）。対応表の状態：本体にある。

*主張*　∞ 圏における接続する二辺の合成には可縮な選択空間がある。

仮定：準圏の指定された合成可能な二辺（HTT と一致）。結論：その二辺を固定したすべての合成三角形の単体集合が可縮 Kan（一致）。

選択の対象は複合辺だけではなく、それを二本の辺とつなぐ二単体である。二本の辺を固定した関手空間の制限のファイバーとしてこの空間を読む。

:::

:::corollary "htt_2_3_2_4" (lean := "SSet.innerAnodyneExtensions_pushoutObjObjι'")
*HTT 系 2.3.2.4*　内アノダイン射の押し出し積（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=118)）。対応表の状態：Mathlib にある。

*主張*　内アノダイン射と単体的集合の余ファイブレーションの押し出し積は内アノダインである。

仮定：内アノダイン射と単射の押し出し積（HTT と一致）。結論：比較射は内アノダイン（一致）。

パラメータ方向に指定しておいた境界と、内角方向に指定したデータを合わせて延長する問題である。両方向を一緒にしても、延長条件は内アノダインの範囲に収まる。

:::

:::corollary "htt_2_3_2_5" (lean := "SSet.innerFibration_pullbackObjObjπ")
*HTT 系 2.3.2.5*　内ファイブレーションの相対内部 Hom（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=119)）。対応表の状態：一部（component）。

*主張*　内ファイブレーション $`X\to S` と余ファイブレーション $`A\to B` に対し、比較 $`X^B\to X^A\times_{S^A}S^B` は内ファイブレーションで、$`A\to B` が内アノダインなら自明になる。

KB-W2原文・型再照合：仮定：任意の inner fibration p と monomorphism i（HTT と一致）。結論：innerFibration\_pullbackObjObjπ は任意の指定 pullback-Hom square の角射 q を InnerFibration とし、最初の assertion に一致。一般の底で i が inner anodyne のときの q の triviality は含まない。

$`A` における値と底での図式を同時に固定すると相対内部 Hom が出る。底を終対象へ取り、$`A` を空にすれば、任意の形 $`B` から ∞ 圏への関手圏が ∞ 圏であることも従う。

:::

# 2.3.3 Minimal Fibrations

%%%
number := false
tag := "htt-2-3-3"
%%%

:::proposition "htt_2_3_3_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.stdSimplexTarget_innerFibration, SSet.quasicategory_of_innerFibration")
*HTT 注意 2.3.3.3*　標準単体上の極小性の絶対判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=120)）。対応表の状態：一部（component）。

*主張*　$`X\to\Delta^n` が内ファイブレーションなら $`X` は ∞ 圏で、射が極小内ファイブレーションであることと $`X` が極小 ∞ 圏であることは同値である。

KB-W2原文・型再照合：仮定：p:X→Δn が inner fibration（HTT と一致）。結論：quasicategory\_of\_innerFibration と Δn の準圏性から X は準圏であり、最初の明記された assertion に一致。p の相対 minimality iff X の minimality は含まない。

底の $`\Delta^n` では同じ端点の射の自由度が無い。比較する単体間のホモトピーが底と両立する条件は自動的になるため、相対的な極小性の検査を全空間だけで行える。

:::

# 2.3.4 n-Categories

%%%
number := false
tag := "htt-2-3-4"
%%%

:::proposition "htt_2_3_4_4" (lean := "SSet.StrictSegal.isCoskeletal")
*HTT 注意 2.3.4.4*　高次境界の一意的な充填（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=125)）。対応表の状態：一部（stronger-hyp）。

*主張*　$`n`-圏 $`\mathcal C` で $`m>n+1` なら、$`m`-単体からその境界への制限は全単射である。

KB-W2原文・型再照合：仮定：n=1 とし C にさらに StrictSegal を仮定（Lean が強い）。結論：StrictSegal.isCoskeletal は IsCoskeletal C 2 を与えるので、m\>2 の boundary restriction の全単射を得る。原典の n=1 の結論は得るが、任意の 1-category の公理から StrictSegal を導く比較と一般 n は含まない。

内角から存在する充填を一つ取り、欠けていた顔を元の境界の指定と比較する。十分高い次元では内角充填の一意性が両方の顔を同じものにする。

:::

:::definition "htt_2_3_4_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan")
*HTT 定義 2.3.4.15*　Kan 複体のホモトピー群による切断（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=130)）。対応表の状態：一部（component）。

*主張*　Kan 複体が $`k`-切断（$`k\ge-1`）であるとは、すべての基点で次数 $`i>k` のホモトピー群が消えることで、$`(-2)`-切断は可縮とする。

KB-W2原文・型再照合：仮定：k=−2、対象は Kan 複体で、可縮性を全境界の RLP による native IsContractibleKan で指定（Lean の十分条件）。結論：負二次を contractible とする原典の convention の成分を表す。k≥−1 の πi の消滅の一般定義と、SpaceInfinity 上の離散同値で定義した Is0TruncatedSpace との比較は含まない。

次数ゼロは成分の条件として読む。高次だけが消える条件と、規約により指定された可縮性とは、切断度を下げたとき区別する。

:::

:::proposition "htt_2_3_4_16" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsSimplicialHomotopyEquivalence.isContractibleKan_iff")
*HTT 注意 2.3.4.16*　切断性のホモトピー同値不変性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=130)）。対応表の状態：一部（special）。

*主張*　Kan 複体の $`k`-切断性はホモトピー同値で不変であるため、空間のホモトピー圏の対象の性質として扱える。

KB-W2原文・型再照合：仮定：ホモトピー同値な二つの Kan 複体、k=−2（Lean が強い特殊形）。結論：IsSimplicialHomotopyEquivalence.isContractibleKan\_iff は可縮性を保存反映するので、原典の負二次の切断性の不変性に一致。一般の k の高次群の消滅の不変性は含まない。

比較は基点や成分の情報を保ち、対応するホモトピー群を同定する。したがって切断性を調べるために特定の Kan 模型を固定する必要はない。

:::

