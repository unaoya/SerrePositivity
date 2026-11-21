-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.Sieves.Basic
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.WellPowered
import SerrePositivity.InfinityCategories.Sheaves.CoverageStableDescent
import SerrePositivity.InfinityCategories.Sheaves.DiscretePresheaf
import SerrePositivity.InfinityCategories.Sheaves.DiscreteSheafificationUnitInverted
import SerrePositivity.InfinityCategories.Sheaves.SheafCondition
import SerrePositivity.InfinityCategories.Sheaves.SheafGlobalSectionsFamily
import SerrePositivity.InfinityCategories.Sheaves.Sheafification

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 6.2 Constructions of ∞-Topoi" =>
%%%
number := false
tag := "htt-6-2"
%%%

HTT 6.2 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 6.2.1 Left Exact Localizations

%%%
number := false
tag := "htt-6-2-1"
%%%

:::proposition "htt_6_2_1_3" (lean := "CategoryTheory.Subobject, CategoryTheory.small_subobject, CategoryTheory.wellPowered_of_smallCategory")
*HTT 命題 6.2.1.3*　対象の部分対象が小さい半順序となること（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=594)）。対応表の状態：一部（special）。

*主張*　可提示な ∞ 圏 $`\mathcal X` の対象 $`X` に対し、単射 $`U\to X` の同値類を因子分解で順序づけた $`\operatorname{Sub}(X)` は小さい半順序集合である。

KB-W2原文・型再照合：仮定：X を小さい通常圏の nerve に特殊化（Lean が強い。presentability はこの結論に不要）。結論：MonoOver の thin skeleton として部分対象が半順序を成し、WellPowered の実在する small-category instance から小ささが得られ一致。一般の大きい presentable 準圏の小ささは含まない。

スライス $`\mathcal X_{/X}` の全対象を数えているのではなく、$`(-1)`-切断な対象だけを取り出す。この半順序の各元は、小さい生成族のうちその元以下にあるものの上限として決まる。これが存在する部分対象の大きさを制御する。

:::

# 6.2.2 Grothendieck Topologies and Sheaves in Higher Category Theory

%%%
number := false
tag := "htt-6-2-2"
%%%

:::definition "htt_6_2_2_1" (lean := "CategoryTheory.Sieve, CategoryTheory.Sieve.pullback, CategoryTheory.GrothendieckTopology")
*HTT 定義 6.2.2.1*　篩と高次圏上の Grothendieck 位相（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=595)）。対応表の状態：一部（special）。

*主張*　篩は射の終点を含めば始点も含む充満部分圏で、対象 $`C` 上の篩はスライス $`\mathcal C_{/C}` の篩である。Grothendieck 位相は最大篩を被覆とし、引き戻しで被覆を保ち、ある被覆篩の各射に沿って被覆となる篩を被覆に含める。

KB-W2原文・型再照合：仮定：∞ 圏 C（Lean が強い：通常圏の神経の場合に限定）。結論：対象への射の前合成で閉じる篩、その引き戻し、最大篩・基底変換・局所性という三公理の位相を定義する（この場合に一致）。通常圏の C/c の全部分圏はその射を対象とし、前合成閉性が同じ下方閉性になる。一般の準圏の slice とその篩の比較は含まない。

対象上の篩の元は $`C` に入る射であり、前合成をしても篩に残る。第三条件により、目的の篩を直接調べる代わりに、すでに被覆と分かっている篩の各脚上で調べてよい。

:::

:::proposition "htt_6_2_2_2" (lean := "CategoryTheory.GrothendieckTopology.trivial, CategoryTheory.GrothendieckTopology.trivial_covering")
*HTT 例 6.2.2.2*　自明な Grothendieck 位相（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=596)）。対応表の状態：一部（special）。

*主張*　任意の ∞ 圏には、各対象上の最大篩だけを被覆とする自明な Grothendieck 位相がある。

KB-W2原文・型再照合：仮定：C は通常圏の nerve（Lean が強い）。結論：最大篩だけが被覆する自明位相を構成し、被覆の iff も一致。任意の準圏での篩全体の定義は含まない。

$`C` 上の最大篩には恒等射がある。推移性を確認する際も、恒等射に沿う引き戻しを調べれば元の篩が最大であることが分かる。

:::

:::proposition "htt_6_2_2_3" (lean := "CategoryTheory.GrothendieckTopology, CategoryTheory.Sieve")
*HTT 注意 6.2.2.3*　ホモトピー圏と Grothendieck 位相（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=596)）。対応表の状態：一部（component）。

*主張*　∞ 圏上の Grothendieck 位相はホモトピー圏上の Grothendieck 位相と同じデータであり、通常圏の nerve の場合は通常の位相の定義に戻る。

KB-W2原文・型再照合：仮定：C が通常圏の nerve の場合に限定（Lean が強い）。結論：最初の「この場合は通常の Grothendieck 位相に還元する」という定義の部分は一致。一般 C の h(C/c)→(hC)/c による篩の全単射と hC への位相の降下は含まない。

スライスのホモトピー圏とホモトピー圏のスライスとの比較関手は、通常は圏同値にならない。ただし両側で篩を指定するのに必要な情報は、どの射がどの射を経由するかである。射のホモトピー類へ移すときも、この閉性を用いる。

:::

:::definition "htt_6_2_2_6" (lean := "SerrePositivity.InfinityCategories.Sheaves.IsSheaf, SerrePositivity.InfinityCategories.Sheaves.SheafCat, SerrePositivity.InfinityCategories.Sheaves.isSheaf_toGrothendieck_iff_of_stable, SerrePositivity.InfinityCategories.Sheaves.isSheaf_pretopology_iff")
*HTT 定義 6.2.2.6*　被覆篩に局所な空間値層の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=597)）。対応表の状態：一部（special）。

*主張*　小さい ∞ site $`\mathcal C` の層とは、被覆篩に対応する単射 $`U\hookrightarrow y(C)` ごとに $`\operatorname{Map}(y(C),F)\to\operatorname{Map}(U,F)` が同値となる空間値前層 $`F` であり、これらが $`\operatorname{Shv}(\mathcal C)` という充満部分圏をなす。

小さい通常の site の nerve に特殊化。空間値では被覆篩の制限錐の極限性として同じ層条件を表し、その頂点が張る充満部分準圏を取る。引き戻しで生成篩が安定な coverage と、引き戻しを持つ前位相では生成被覆だけで判定できる。底が任意の ∞ 圏の場合は含まない。

左辺は Yoneda により $`F(C)`。右辺は被覆篩の各脚への制限を、脚どうしの射も含めて整合させた切断の空間である。したがって、層条件は「被覆上の整合的な切断」の空間が $`F(C)` から復元できることを表す。

\#\#\# 小さい通常の site での層条件

被覆篩 $`S` の各脚を $`\mathcal C` へ忘却し、反対化した図式で $`F` を評価する。$`F(C)` はこの図式への標準錐の頂点であり、各脚は前層の制限写像になる。

生成篩の引き戻しが再び基本被覆の生成篩になる coverage では、基本被覆の生成篩での極限性から、任意の脚に沿う引き戻しの極限性も従う。ここから生成された Grothendieck 位相での層条件を得る。引き戻しのある通常圏上の前位相では、基本族を引き戻してこの仮定を満たす。弱い coverage について、引き戻しが基本被覆で細分されるという条件だけから、この判定を使うことはできない。

:::

:::proposition "htt_6_2_2_7" (lean := "SerrePositivity.InfinityCategories.Sheaves.sheafification_exists, SerrePositivity.InfinityCategories.Sheaves.sheafification_exists_spaces, SerrePositivity.InfinityCategories.Sheaves.discreteSheafificationUnitHom_post_isIso")
*HTT 命題 6.2.2.7*　空間値層化の位相的局所化と高次トポス性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=597)）。対応表の状態：一部（special）。

*主張*　小さい ∞ site $`\mathcal C` について、$`\operatorname{Shv}(\mathcal C)` は前層 ∞ 圏 $`\mathcal P(\mathcal C)` の位相的局所化であり、したがって ∞ トポスである。

小さい通常の site 上で、被覆篩の生成辺族の局所対象と層の一致から、空間値を含む可提示係数の層への反射を得る。離散係数では指定層化単位をこの反射が逆にすることも示す。元の結論のうち反射を供給し、左完全性・位相的局所化・∞ トポス性は結論に含まない。

層化は被覆篩の包含を逆にする局所化であり、層の包含に左随伴を与える。位相的局所化であるという結論には、反射の存在に加えて、有限極限の保存と、単射である生成射によって局所化が定まることが含まれる。

\#\#\# 通常の site 上の可提示係数

係数の検出族を選び、被覆篩の包含と検出対象を組み合わせて前層準圏の小さい辺族を作る。この辺族への局所性を制限錐の極限性と比較し、層の充満部分準圏への反射を Bousfield 局所化から得る。空間値はこの結果の適用例である。

離散係数については、通常の集合値層化の指定単位から作る写像が空間値層化の後で可逆になる。一般の係数忘却が層化単位を局所同値へ送るところまでをこの比較に含めない。

:::

:::definition "htt_6_2_2_8" (lean := "CategoryTheory.GrothendieckTopology.Cover")
*HTT 記法 6.2.2.8*　被覆篩を動かす圏の構成（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=597)）。対応表の状態：一部（component）。

*主張*　$`\operatorname{Cov}(\mathcal C)` は対象とその被覆篩の組を集め、通常圏では篩の各脚を先の篩に送る射をとり、∞ 圏では $`\mathcal C\times_{N(h\mathcal C)}N(\operatorname{Cov}(h\mathcal C))` で定義される。

KB-W2原文・型再照合：仮定：C は通常圏の nerve（Lean が強い）。結論：固定 c 上の fiber に当たる被覆篩の半順序 J.Cover c は一致。全基底上の Cov(C) とその Cartesian fibration の構成・一般 hC による引き戻しは含まない。

射の向きは、始域側の被覆の脚を対象間の射と合成し、終域側の篩に入る向きである。同じ対象上で恒等射にかかる場合、この条件は篩の包含になる。

:::

