import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.Adjunction
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservingFunctorSpaces

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 6.3 The ∞-Category of ∞-Topoi" =>
%%%
number := false
tag := "htt-6-3"
%%%

HTT 6.3 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 6.3.1 Geometric Morphisms

%%%
number := false
tag := "htt-6-3-1"
%%%

:::proposition "htt_6_3_1_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.rightAdjointFunctorIso, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.leftAdjointFunctorIso")
*HTT 注意 6.3.1.2*　幾何学的射の随伴の一意性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=618)）。対応表の状態：一部（component）。

*主張*　幾何学的射の逆像 $`f^*` と順像 $`f_*` は互いに可縮な選択まで決まり、右上の星で左随伴、右下の星で右随伴を表す。

KB-W2原文・型再照合：仮定：同じ一方の関手に二つの ∞ 随伴（HTT より弱い：任意の準圏に適用でき、∞ トポス性と左完全性は不要）。結論：他方の随伴が FunctorIso で同値となる部分は一致。全随伴データの選択空間が可縮という高次の一意性まではこの二つの型には含まない。

通常はトポスの射の向きと同じ向きに順像を書く。逆像は反対の向きだが、随伴の一方を指定すれば他方も決まるので、文脈によっては逆像で幾何学的射を表す。

:::

:::proposition "htt_6_3_1_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.comp, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservesSmallLimits.comp")
*HTT 注意 6.3.1.4*　幾何学的射の合成の安定性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=619)）。対応表の状態：一部（stronger-hyp）。

*主張*　幾何学的射を二つ合成すると再び幾何学的射となり、合成の逆像は個々の逆像を逆順に合成した関手である。

KB-W2原文・型再照合：仮定：二つの幾何学的射とその左随伴（Lean が強い：左随伴が有限極限だけでなく全小極限を保存すると仮定）。結論：同じ左随伴の合成は全小極限を保存し、逆順の右随伴の合成と実際の ∞ 随伴を成すため、この場合の幾何学的射の合成は一致。

順像を合成した関手の左随伴は、もとの左随伴を反対の順に使う。有限極限を保つ二つの関手の合成も有限極限を保つので、この左随伴が幾何学的射の条件を満たす。

:::

:::definition "htt_6_3_1_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration")
*HTT 定義 6.3.1.6*　トポスファイブレーションの定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=619)）。対応表の状態：一部（component）。

*主張*　トポス・ファイブレーションは Cartesian かつ余 Cartesian なファイブレーションで、頂点上の各ファイバーは ∞ トポス、各辺に沿う共変移送は左完全である。

topos fibration の定義の条件(1)について、同じ p の CartesianFibration と CocartesianFibration の二条件を直接表す。fiberの∞-topos性と輸送の左完全性を束ねた構造は未供給。

底の辺の両方向への移送に加えて、共変側が有限極限と両立することを課す。この共変側を逆像として読むと、反変側の移送が順像になる。

:::

# 6.3.5 Étale Morphisms of ∞-Topoi

%%%
number := false
tag := "htt-6-3-5"
%%%

*classifying-shape.html — 1. $`B` とは何か — $`B` は torsor を分類する*

$$`\mathrm{Map}(X,BG)\ \simeq\ \{X\text{ 上の }G\text{ torsor の }\infty\text{ 亜群}\}.`

$`B\mathbb Z` への写像は被覆空間、$`BU(1)` への写像は複素直線束、$`B^2A` への写像は $`BA` torsor すなわち $`A` gerbe を分類する。

*classifying-shape.html — 1. $`B` とは何か — 層（∞ トポス）の場合*

群の層 $`\mathcal G` の $`B\mathcal G` は、前層 $`U\mapsto B(\mathcal G(U))` を*層化*したもの（∞ トポスの中では $`\Omega` の逆として特徴づけられる、HTT Lemma 7.2.2.11）。層化が本質的で、
$$`\Gamma(B\mathcal G)\ =\ \{\text{底の上の }\mathcal G\text{ torsor}\}\ \neq\ B(\Gamma\mathcal G),`
差が非自明な torsor（$`H^1` にあたるもの）。

- 記号　／　群　／　何を分類するか／何であるか
- $`BG`（$`\mathrm{Fun}(BG,D(k))`）　／　群 $`G`　／　$`BG` からの関手 = $`G` がホモトピー整合的に作用する対象
- $`B\hat{\mathbb Z}`　／　$`\mathrm{Gal}(\overline{\mathbb F}_q/\mathbb F_q)`　／　$`\mathrm{Spec}\,\mathbb F_q` のエタールホモトピー型（副有限な円周）
- $`B\mathbb Z`（層）　／　定数層 $`\mathbb Z`　／　$`\mathbb Z` torsor
- $`B\mathbf{Pic}`（層）　／　$`\mathbf{Pic}=\mathrm{Aut}(\mathrm{Mod})`　／　$`\mathrm{Mod}` の捻れた形（Brauer 類）
- $`B^2\mathbb G_m`（層）　／　$`\mathbb G_m`　／　$`\mathbb G_m` gerbe

*一般原理*：対象 $`X` の捻れた形（局所的に $`X` と同値なもの）は $`B\mathrm{Aut}(X)` の大域切断で分類される（局所的に $`X` と同値なものは、$`X` との同値のなす $`\mathrm{Aut}(X)` torsor と同じ）。$`\mathbf{Br}=\Gamma(B\mathbf{Pic})` はその例で、Postnikov 分解 $`B^2\mathbb G_m\to B\mathbf{Pic}\to B\mathbb Z` は $`\mathbf{Pic}\simeq\mathbb Z\times B\mathbb G_m` に $`B` を当てはめたもの。「$`B^2\mathbb G_m` は 1-連結」は「$`B` を二回取ったので $`\pi_0` と $`\pi_1` が消えている」という意味。

