-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Basic
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.EffectiveEpi.Basic
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Limits.VanKampen
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Subobject.Classifier.Defs
import Mathlib.CategoryTheory.Types.Basic
import SerrePositivity.InfinityCategories.HTT.Section6_1_2.OppositeIso
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.FunctorCategory

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 6.1 ∞-Topoi: Definitions and Characterizations" =>
%%%
number := false
tag := "htt-6-1"
%%%

HTT 6.1 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

:::proposition "htt_6_1_0_1" (lean := "CategoryTheory.plusPlusAdjunction, CategoryTheory.preservesFiniteLimits_presheafToSheaf, CategoryTheory.sheafification_reflective")
*HTT 命題 6.1.0.1*　通常トポスのギロー公理（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=546)）。対応表の状態：一部（component）。

*主張*　通常圏が Grothendieck トポスであることは、集合値前層圏の左完全局所化であること、または可提示性・余極限の普遍性・余積の非交和性・同値関係の有効性を満たすことと同値である。

KB-W2原文・型再照合：仮定：通常の小さいサイト上の集合値層圏（HTT の (A) をその標準表示に特殊化、Type の層化 instance は LeftExact.lean に実在）。結論：層化の反射随伴と有限極限保存から (A)⇒(B) の標準表示の場合は直接得られる（一部一致）。任意の圏への同値による輸送、(B)⇒(C)、(C)⇒(A) は含まない。

サイト上の層として与える形と、圏の内部だけで調べる形をつなぐ定理である。例えば余極限の普遍性は、スライスを替える引き戻しが余極限と可換することを要求する。

:::

# 6.1.1 Giraud’s Axioms in the ∞-Categorical Setting

%%%
number := false
tag := "htt-6-1-1"
%%%

:::definition "htt_6_1_1_2" (lean := "CategoryTheory.IsUniversalColimit")
*HTT 定義 6.1.1.2*　余極限が普遍的であるという定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=550)）。対応表の状態：一部（special）。

*主張*　可提示 ∞ 圏の余極限が普遍的であるとは、各射 $`T\to S` に沿う引き戻し $`\mathcal C_{/S}\to\mathcal C_{/T}` が小さい余極限を保つことをいう。

KB-W2原文・型再照合：仮定：X と添字を通常圏の nerve に特殊化（Lean が強い）。結論：全 pullback した cocone が余極限という通常圏での普遍性の定義は一致。任意の単体集合添字の native 反変引き戻し関手全体を定義するものではない。

余極限を取る操作と底を替える操作の順序を交換できる条件である。随伴関手定理を使う場合は、引き戻し関手に右随伴が存在するかで検査できる。

:::

:::proposition "htt_6_1_1_5" (lean := "CategoryTheory.EffectiveEpi, CategoryTheory.EffectiveEpiStruct, CategoryTheory.isColimitCoforkOfEffectiveEpi, CategoryTheory.effectiveEpi_of_kernelPair")
*HTT 注意 6.1.1.5*　通常圏の有効全射の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=552)）。対応表の状態：Mathlib にある。

*主張*　有効全射 $`X\to Y` に沿って引き戻した $`Y` からの射は、$`X\times_Y X` の二つの射影の後で一致する $`X` からの射として特徴づけられる。

仮定：通常圏の射と存在する kernel pair（HTT と一致）。結論：全ての同値対を等しくする射の一意な因子化と kernel pair の coequalizer による有効全射の定義が一致。EffectiveEpiStruct が因子化、両補題が coequalizer との相互変換を与える。

全射性の圏論的な判定は、$`Y` からの射を $`X` 上で区別できるという条件である。有効性はその像も記述し、二つの引き戻しの一致が降下の必要十分条件になる。

:::

:::proposition "htt_6_1_1_6" (lean := "CategoryTheory.epi_iff_surjective, CategoryTheory.isSplitEpi_iff_surjective, CategoryTheory.IsSplitEpi.EffectiveEpi, CategoryTheory.epi_of_effectiveEpi")
*HTT 事実 6.1.1.6*　集合における同値関係と有効全射（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=553)）。対応表の状態：一部（component）。

*主張*　集合圏では同値関係はすべて有効で、有効全射は集合としての全射に一致する。

KB-W2原文・型再照合：仮定：集合の圏（HTT と一致、Classical.choice を使用）。結論：有効全射と全射の同値の部分は一致。全ての集合の同値関係が有効であるという前半の一般の内部関係の結論はこの宣言群には含まない。

集合の同値関係から商集合を作ると、同じ商の元へ移る二点の組がちょうどもとの同値関係になる。全射はこの操作で得られる商写像として表せる。

:::

# 6.1.2 Groupoid Objects

%%%
number := false
tag := "htt-6-1-2"
%%%

:::definition "htt_6_1_2_2" (lean := "CategoryTheory.SimplicialObject, CategoryTheory.SimplicialObject.Augmented, AugmentedSimplexCategory.equivAugmentedSimplicialObject, SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso, SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveOppositeIso")
*HTT 定義 6.1.2.2*　単体対象と増大単体対象の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=554)）。対応表の状態：一部（special）。

*主張*　∞ 圏 $`\mathcal C` の単体的対象は $`N(\Delta)^{\mathrm{op}}\to\mathcal C`、増大単体的対象は空順序集合を加えた $`N(\Delta_+)^{\mathrm{op}}\to\mathcal C` で、それぞれの関手 ∞ 圏を $`\mathcal C_\Delta,\mathcal C_{\Delta_+}` と記す。

KB-W2原文・型再照合：仮定：C を通常圏 D の nerve に特殊化（Lean が強い）。結論：Δop→D と Δ+op→D としての単体対象・増大単体対象の定義は一致。増大対象の Mathlib 表示との同値、反対圏と関手圏の nerve の同型もある。任意の準圏 C 全体の定義ではない。

増大対象では $`[-1]=\varnothing` での値も指定する。$`[-1]` は $`\Delta_+` で始対象なので、反対化した添字では正次数から増大項への写像が現れる。

:::

:::proposition "htt_6_1_2_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso, SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveOppositeIso")
*HTT 注意 6.1.2.3*　通常圏の単体対象と nerve の比較（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=555)）。対応表の状態：本体にある。

*主張*　通常圏 $`\mathcal D` の nerve を値域とすると、単体的対象の ∞ 圏は $`\mathcal D` の通常の単体的対象の圏の nerve と自然同型である。

仮定：通常圏 C と Δ（HTT と一致、同一宇宙に配置）。結論：nerve の関手圏同型と反対圏同型を合成して Fun(N(Δ)op,N(C))≅N(Δop⥤C) が得られ、一致。

$`\Delta^{\mathrm{op}}` も通常圏であるため、その nerve から $`N(\mathcal D)` への写像は普通の関手として読める。この同定は関手を対象にしたところで終わらず、自然変換を含む全次元に及ぶ。

:::

:::definition "htt_6_1_2_5" (lean := "CategoryTheory.Functor.Elements, CategoryTheory.Functor.Elements.π, CategoryTheory.Functor.Elements.costructuredArrowYonedaEquivalence")
*HTT 記法 6.1.2.5*　単体の圏と増大図式の記法（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=556)）。対応表の状態：一部（component）。

*主張*　$`\Delta/K` は $`K` の単体とその間の単体写像の可換三角形からなる圏で、$`U[K]` は単体的対象 $`U` をこの添字圏の反対圏の nerve へ制限した図式である。

KB-W2原文・型再照合：仮定：単体集合 K を Δop 上の集合値前層として扱う（HTT と一致）。結論：Δ/K に当たる K.Elements の反対圏、その射影と representable→K による表示は一致。これを任意の増大準圏図式 U に合成する U\[K\] の記法全体は含まない。

元の $`U` は単体の次元と単調写像に応じて値を与える。$`\Delta/K` を添字にすれば、同じ次元でも $`K` 内の異なる単体を区別し、その間の面・退化の写像を追える。

:::

# 6.1.3 ∞-Topoi and Descent

%%%
number := false
tag := "htt-6-1-3"
%%%

*fibered-descent.html — 5. ∞ への接続*

*三角圏では貼り合わせができない*：$`X=U\cup V` で、$`U`・$`V` 上の複体と重なりでの擬同型を与えても、錐が関手的でないので貼り合わせが一意に決まらず、三重の重なりでのコサイクルをホモトピーで満たすための高次データも要る。

*∞ 圏では降下が成り立つ*：
$$`D(X)\ \xrightarrow{\ \sim\ }\ \lim_{[n]\in\Delta}D(U_n)\qquad\bigl(\text{Zariski なら } D(X)\simeq D(U)\times_{D(U\cap V)}D(V)\bigr)`
（たとえば $`D_{\mathrm{qc}}` の fpqc 降下）。§4.3 の表の最後の行で、SGA1 のコサイクル条件が補章 3 の立方体の整合性の無限の列に置き換わったもの。

- SGA1　／　∞ 版
- ファイバー圏　／　cartesian fibration（$`\mathrm{Sch}^{\mathrm{op}}\to\mathrm{Cat}_\infty` の unstraightening）
- 2-米田 $`\mathcal F_X\simeq\mathrm{Hom}_{\mathrm{Cart}}(\mathcal C/X,\mathcal F)`　／　fibration 版の米田
- 降下データ = 篩からの cartesian 関手　／　cartesian 切断の ∞ 圏 = $`\mathrm{Cat}_\infty` での極限（HTT §3.3）
- Bénabou–Roubaud + Beck　／　Barr–Beck–Lurie（HA §4.7）+ Beck–Chevalley
- コサイクル条件（$`U_2` まで）　／　Čech 脈体全体の totalization

∞ では、Čech 脈体だけでなく任意の超被覆に対して降下を要求するか（hypercompleteness）という新しい区別が生じる。1 圏では切り詰めのおかげで両者が一致していた。

:::definition "htt_6_1_3_1" (lean := "CategoryTheory.NatTrans.Equifibered")
*HTT 定義 6.1.3.1*　カルテジアン自然変換の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=562)）。対応表の状態：一部（special）。

*主張*　二つの $`K`-図式の間の自然変換が Cartesian であるとは、$`K` の各辺に沿う自然性の正方形が引き戻しであることをいう。

KB-W2原文・型再照合：仮定：準圏 X と添字 K を通常圏の nerve に特殊化（Lean が強い）。結論：各辺の自然性四角が pullback となるというカルテジアン自然変換の通常圏での定義は一致。任意の単体集合 K についての native 述語ではない。

自然変換の縦の成分を一つずつ見るだけでは足りない。各辺で、始点の成分が終点での成分を引き戻したものとして図式的に決まることを見る。

:::

:::definition "htt_6_1_3_4" (lean := "CategoryTheory.MorphismProperty.IsStableUnderBaseChange")
*HTT 記法 6.1.3.4*　引き戻し安定な射の族の記法（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=564)）。対応表の状態：一部（component）。

*主張*　引き戻しを持つ ∞ 圏の射の族が引き戻しに安定なら、その射が張る矢印 ∞ 圏から終点への写像は Cartesian ファイブレーションであり、Cartesian 辺だけに制限すると右ファイブレーションを得る。

KB-W2原文・型再照合：仮定：X を通常圏の nerve に特殊化（Lean が強い）。結論：射の性質が任意の pullback で保存されるという S の条件は一致。OSX と pullback 四角だけの OX(S)、その Cartesian/right fibration の結論はこの型に含まない。

終点を沿わせて矢印を持ち上げる操作は矢印の引き戻しである。射の族を選んでもこの操作が可能なためには、引き戻して得られる矢印も同じ族に属する必要がある。

:::

:::lemma_ "htt_6_1_3_15" (lean := "CategoryTheory.IsUniversalColimit.map_reflective")
*HTT 補題 6.1.3.15*　左完全反射による普遍性の保存（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=569)）。対応表の状態：一部（special）。

*主張*　可提示 ∞ 圏の余極限が普遍的なら、その可到達な左完全局所化でも余極限は普遍的である。

KB-W2原文・型再照合：仮定：通常圏 C,D の反射随伴で、必要な pullback が存在し左随伴が保存（HTT を通常圏に特殊化。全有限極限保存はこれを満たす）。結論：C の普遍的 cocone を反射すると D の普遍的 cocone となり一致。全 native 準圏での左完全局所化の主張ではない。

局所化の前に引き戻しと余極限を比較し、その比較を局所化後へ移す。左完全性によって、比較内の引き戻しは同じ局所化を施しても保持される。

:::

# 6.1.6 ∞-Topoi and Classifying Objects

%%%
number := false
tag := "htt-6-1-6"
%%%

:::definition "htt_6_1_6_1" (lean := "CategoryTheory.Subobject.Classifier")
*HTT 定義 6.1.6.1*　射の族と部分対象の分類対象（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=584)）。対応表の状態：一部（component）。

*主張*　引き戻しに安定な射の族を分類する射とは、その族の射を対象、引き戻し正方形を射とする ∞ 圏の終対象であり、すべての単射を分類する終点が部分対象分類子である。

KB-W2原文・型再照合：仮定：通常圏の nerve に特殊化し S を全ての mono に限定（Lean が強い）。結論：任意の mono が一意な pullback として得られるという部分対象分類子の部分は一致。一般の射族 S の右 fibration の終対象としての定義は含まない。

ある射が分類射の引き戻しになる図式をとることが、分類射への矢印になる。終対象性は、引き戻しによる表示を得られることに加えて、選択の空間が可縮であることを表す。

:::

