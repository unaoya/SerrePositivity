import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.SimplicialNerve
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.CategoryTheory.Functor.KanExtension.Dense
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Shapes.End
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.RightFibrationFiberCriterion
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationYoneda
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CellularNaturalComparison
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FlagIso
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionMonomorphisms
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.InnerAnodyneEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationInfinity

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 2.2 Simplicial Categories and ∞-Categories" =>
%%%
number := false
tag := "htt-2-2"
%%%

HTT 2.2 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 2.2.1 The Straightening and Unstraightening Constructions (Unmarked Case)

%%%
number := false
tag := "htt-2-2-1"
%%%

原典照合の注記　原稿中の HTT Theorem 2.2.1.2 は、原典では反変モデル構造と射影モデル構造の Quillen 随伴を述べる。左ファイブレーションの共変版として読む箇所は双対との比較である。

*03-straightening.html — 3. 主定理（空間値）*

原典との違い：写像の向き

HTT は straightening $`\mathrm{St}`（左随伴）を単体的圏の側で作り、covariant モデル構造の Quillen 同値として示す（HTT §2.2.1、Thm. 2.2.1.2）。Kerodon は unstraightening を主に扱う。ここでは「fibration → 関手」の向きの写像を*直接* ∞ 圏の射として作り、それが同値であることを示している。モデル構造は使わない。逆向き（unstraightening）は、本質的全射性の証明の中で対象ごとに現れるだけである。

# 2.2.2 Straightening Over a Point

%%%
number := false
tag := "htt-2-2-2"
%%%

:::proposition "htt_2_2_2_1" (lean := "CategoryTheory.Presheaf.uliftYonedaAdjunction, CategoryTheory.Limits.coend")
*HTT 注意 2.2.2.1*　余単体的対象の実現と右随伴（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=93)）。対応表の状態：一部（component）。

*主張*　余単体的対象 $`C^\bullet` による単体的集合 $`S` の実現は余端 $`\int^{[n]}S_n\cdot C^n` であり、右随伴の $`n`-単体は $`\operatorname{Hom}(C^n,X)` である。

KB-W2原文・型再照合：仮定：余単体 C• と必要な小余極限、Yoneda に沿う colimit-preserving extension L（HTT と一致）。結論：uliftYonedaAdjunction は L⊣restrictedULiftYoneda C• で、その右随伴の n 単体は Hom(Cn,X) だから後半の adjunction と公式に一致。L と表示された coend ∫Sn×Cn の同型は含まない。

実現では $`S` の各単体の分だけ $`C^n` を取り、単体作用に沿って貼る。実現から $`X` への射は貼り合わせと両立する写像族なので、その写像族が右随伴への単体的写像になる。

:::

:::proposition "htt_2_2_2_2" (lean := "sSetTopAdj, TopCat.toSSetObjEquiv, SSet.toTopSimplex")
*HTT 例 2.2.2.2*　位相的実現と特異複体の随伴（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=93)）。対応表の状態：Mathlib にある。

*主張*　余単体的空間を位相的標準単体に取ると、対応する随伴は単体的集合の幾何学的実現と空間の特異複体である。

仮定：単体集合と位相空間（Lean が弱い：位相空間側をコンパクト生成 Hausdorff に制限しない）。結論：位相標準単体の左 Kan 拡張による実現、特異複体とその随伴を与える（一致）。

右随伴では各位相的単体から空間への連続写像を集め、面と退化を前合成で与える。左随伴の貼り合わせはその同じ位相的単体で行う。

:::

:::proposition "htt_2_2_2_3" (lean := "CategoryTheory.Functor.IsDense.leftKanExtensionIso, CategoryTheory.Presheaf.uliftYonedaAdjunction")
*HTT 例 2.2.2.3*　標準単体に沿う実現は恒等（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=93)）。対応表の状態：Mathlib にある。

*主張*　余単体的対象を単体的集合の標準単体 $`\Delta^n` とすると、実現関手と特異関手の両方が恒等関手に自然同型になる。

仮定：単体圏の Yoneda 埋め込み（Lean が弱い：一般の稠密関手を扱う）。結論：自身に沿う左 Kan 拡張は恒等と同型であり、その右随伴も随伴の一意性により恒等と同型（一致）。

右側は Yoneda によって $`n`-単体をそのまま取り出す。左側は標準単体たちを各単体に従って貼ると元の単体的集合に戻る。

:::

:::proposition "htt_2_2_2_4" (lean := "CategoryTheory.nerveAdjunction")
*HTT 例 2.2.2.4*　順序圏による実現と通常の nerve（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=93)）。対応表の状態：Mathlib にある。

*主張*　余単体的通常圏 $`[n]` を使う実現と特異関手は、単体的集合のホモトピー圏 $`hS` と通常圏の nerve を与える。

仮定：単体集合と通常圏（HTT と一致）。結論：順序圏の nerve を右随伴、ホモトピー圏 h を左随伴とする随伴を得る（一致）。

$`[n]` からの関手は対象と接続した射の列で決まるので、右側には通常の nerve が現れる。左側ではすべての二単体が合成の関係として働く。

:::

:::proposition "htt_2_2_2_5" (lean := "CategoryTheory.SimplicialNerve")
*HTT 例 2.2.2.5*　単体 nerve と豊穣圏への実現（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=93)）。対応表の状態：一部（component）。

*主張*　余単体的単体圏 $`\mathfrak C[\Delta^\bullet]` による実現は $`S\mapsto\mathfrak C[S]` であり、右随伴は整合的 nerve である。

KB-W2原文・型再照合：仮定：cosimplicial thickening を使う simplicial category（HTT と一致）。結論：SimplicialNerve は各 n に enriched functors C\[Δn\]→C を持つので、SingC•=simplicial nerve の assertion に一致。Cat∆ の全 colimits と左随伴 C\[S\] の構成は含まない。

通常の nerve の例から、各 $`[n]` を整合データを持つ豊穣圏に取り替える。右随伴の単体は、この豊穣圏からの豊穣関手で定まる。

:::

:::proposition "htt_2_2_2_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll_isPrecompositionEquivalence, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsPrecompositionEquivalence.isWeakHomotopyEquivalence")
*HTT 命題 2.2.2.7*　旗の実現から元の単体集合への弱同値（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=94)）。対応表の状態：本体にある。

*主張*　余単体的単体集合 $`Q^\bullet` の比較 $`\pi` が誘導する $`|S|_{Q^\bullet}\to S` は、任意の単体的集合 $`S` について弱ホモトピー同値である。

仮定：任意の単体集合 X（HTT と一致）。結論：旗の模型で最大元の射影の左 Kan 拡張は前合成同値であり、Kan 標的で試験する弱ホモトピー同値を従える（Lean が強い：すべての準圏を標的にできる）。

左側は一点上の straightening を記述する実現である。比較は各標準単体で定められており、その同値性を、単体を貼って一般の $`S` を得る段階へ移す。

:::

:::proposition "htt_2_2_2_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll_isPrecompositionEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_natComponent_of_stdSimplex")
*HTT 注意 2.2.2.8*　標準単体へのセル帰納による還元（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=95)）。対応表の状態：本体にある。

*主張*　第2.2.2.7項では、実現どうしの比較を標準単体の場合に確かめ、単体の貼り合わせを使って一般の単体的集合へ広げる。

仮定：始対象と標準単体上の比較、およびセル添付に必要な余極限と単射の保存（HTT と一致する還元の仮定）。結論：一般の単体集合で比較が同値となるセル帰納を、旗の射影に適用する（Lean が強い：前合成同値まで示す）。

一般の単体集合を任意の形の図式として直接比較する代わりに、骨格に沿って貼り合わせを追う。重要なのは、標準単体での比較が貼る境界との対応に自然である点である。

:::

:::proposition "htt_2_2_2_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedFlagIso")
*HTT 命題 2.2.2.13*　右写像空間の旗による自然同型（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=96)）。対応表の状態：本体にある。

*主張*　豊穣圏 $`\mathcal C` の整合的 nerve の右写像単体集合は、豊穣写像対象 $`\operatorname{Map}_{\mathcal C}(X,Y)` に $`Q^\bullet` に関する特異関手を施した単体的集合と自然同型である。

仮定：単体豊穣圏と任意の二対象（HTT と一致）。結論：nerve の右 pinched 写像空間を、豊穣 Hom に旗の右随伴を適用した単体集合と自然同型にする（一致。宇宙差は ULift で調整）。

右写像単体集合の単体には、端点側の顔が定値である条件がある。その条件を豊穣圏側で課すと、残る情報が $`Q^n` から写像対象への射になる。

:::

# 2.2.3 Straightening of Right Fibrations

%%%
number := false
tag := "htt-2-2-3"
%%%

:::definition "htt_2_2_3_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence")
*HTT 定義 2.2.3.2*　右ファイブレーションの各繊維での同値（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=98)）。対応表の状態：本体にある。

*主張*　同じ底 $`S` 上の右ファイブレーション間の射を点ごとの同値というのは、各頂点上の Kan ファイバーの誘導射がホモトピー同値である場合である。

原文が既に与える同じ右fibration p,qと底上のfについて、各vertexFiberMapがIsSimplicialHomotopyEquivalenceであるという条件はpointwise equivalenceの定義全体をそのまま表す。別の比較射・空間は用いない。

比較するのは全空間から任意に切り出した部分ではなく、各頂点 $`s` への引き戻しで得られる二つのファイバーである。底を変えず同じ頂点で比較する。

:::

:::proposition "htt_2_2_3_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isQCatEquivalence_of_rightFibration_fibers")
*HTT 注意 2.2.3.3*　右ファイブレーションの三つの同値条件（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=98)）。対応表の状態：一部（direction）。

*主張*　同じ底上の右ファイブレーション間では、点ごとの同値、反変モデル構造での同値、全空間の圏同値が一致する。

KB-W2原文・型再照合：仮定：同じ準圏 S 上の二つの右ファイブレーションと底上の f、各繊維の同値（Lean が強い：S と全空間の準圏性を指定）。結論：全空間の f は IsQCatEquivalence なので (a)⇒(c) の準圏の場合に一致。逆方向と contravariant equivalence (b) の model comparison は含まない。

反変同値は底上の射の性質、圏同値は忘れた全空間の性質である。右ファイブレーションの仮定により、いずれも頂点ファイバーの比較に還元できる。

:::

:::lemma_ "htt_2_2_3_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.relativeFunctorSpace_kanComplex_of_rightFibration")
*HTT 補題 2.2.3.4*　底の包含に沿う相対 Hom の制限（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=98)）。対応表の状態：一部（special）。

*主張*　単体的部分集合 $`S'\subseteq S` と右ファイブレーション $`Y\to S` に対して、任意の $`X\to S` からの相対写像空間の $`S'` への制限は Kan ファイブレーションになる。

KB-W2原文・型再照合：仮定：右ファイブレーション Y→S、任意の X→S、底の包含を S′=空に限定（Lean が強い特殊形）。結論：relativeFunctorSpace は Kan 複体、したがって空図式の一意な相対 Hom（終対象）への restriction は Kan fibration。この特殊形に一致し、任意 S′ の restriction criterion は含まない。

底に沿って $`X` と $`Y` の両方を引き戻してから比較する。結果は写像単体集合上で境界つきの変形を持ち上げられるという形で、写像そのものの全射性は主張しない。

:::

:::definition "htt_2_2_3_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.rightFibrationObject_category, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.rightFibrationObject_simplicialCategory")
*HTT 記法 2.2.3.8*　底上の右ファイブレーションの充満部分圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=101)）。対応表の状態：本体にある。

*主張*　$`\operatorname{RFib}(S)` は、スライス圏のうち $`S` への構造射が右ファイブレーションである対象を取った充満部分圏である。

仮定：任意の単体集合の底（HTT と一致）。結論：スライス圏の右ファイブレーションを対象とし、底上の射と相対 Hom で充満部分圏を与える（一致）。

対象には持ち上げ条件を課すが、射は元のスライスの射なので、底上の可換三角形をそのまま使える。

:::

# 2.2.5 The Joyal Model Structure

%%%
number := false
tag := "htt-2-2-5"
%%%

*coherent-nerve-diagrams.html — 1. 定義 — 基本定理と $`\mathcal S`・$`\mathrm{Cat}_\infty`*

*定理*（Cordier–Porter、HTT Prop. 1.1.5.10）：写像空間がすべて Kan 複体なら $`N^{hc}(\mathcal C)` は準圏。$`\mathfrak C\dashv N^{hc}` は Bergner と Joyal のモデル構造の Quillen 同値。

- $`\mathcal S=N^{hc}(\mathrm{Kan})`：$`\mathrm{Map}(X,Y)=\mathrm{Fun}(X,Y)`（自動的に Kan）。

:::lemma_ "htt_2_2_5_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isQCatEquivalence_of_innerAnodyne")
*HTT 補題 2.2.5.2*　内アノダイン射の圏同値性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=107)）。対応表の状態：一部（stronger-hyp）。

*主張*　内アノダイン射は圏同値である。

inner anodyne fの始域・終域がさらに準圏の場合に、isQCatEquivalence\_of\_innerAnodyneが同じfの圏同値を直接与える。任意の単体集合端点へは一般化しない。

内角の充填を付け加える生成射が、∞ 圏としての同値を変えないことを述べる。弱飽和類全体で成り立つので、複数の内角を順に付け加えた比較にも使える。

:::

