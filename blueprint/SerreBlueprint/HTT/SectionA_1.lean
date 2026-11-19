import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.LiftingProperties.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Mathlib.CategoryTheory.Monoidal.Opposite
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.MorphismProperty.Retract
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered
import Mathlib.CategoryTheory.Presentable.LocallyPresentable
import Mathlib.CategoryTheory.SmallObject.Basic
import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleSmallObject
import SerrePositivity.HomotopicalAlgebra.Smith.ClosedGeneratedClass
import SerrePositivity.HomotopicalAlgebra.Smith.CoproductClosure
import SerrePositivity.HomotopicalAlgebra.Smith.Smallness

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT A.1 Category Theory" =>
%%%
number := false
tag := "htt-A-1"
%%%

HTT A.1 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# A.1.1 Compactness and Presentability

%%%
number := false
tag := "htt-A-1-1"
%%%

:::definition "htt_A_1_1_1" (lean := "CategoryTheory.isCardinalFiltered_preorder, CategoryTheory.IsCardinalFiltered.exists_max")
*HTT 定義 A.1.1.1*　κ filtered 半順序と compact 対象（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=806)）。対応表の状態：一部（component）。

*主張*　通常圏の対象が $`\kappa`-コンパクトであるとは、その対象からの Hom が $`\kappa`-濾過半順序で添字付けられた余極限を保つことである。

KB-W2原文・型再照合：仮定：半順序 I と正則 κ（HTT の最初の定義と一致）。結論：κ-small family が上界を持つ条件から IsCardinalFiltered I κ、逆に exists\_max から各 κ-small subset に上界を得て、最初の定義は一致。本文後半の poset-indexed Hom colimit による κ-compact/small の定義と、Mathlib の全 κ-filtered category を使う IsCardinalPresentable の比較はこの型に含まない。

半順序が $`\kappa`-濾過であるとは濃度 $`<\kappa` の部分集合に上界があることをいう。ある小さい正則基数でコンパクトとなる対象を小さいと呼び、以後それ以上の正則基数でもコンパクトとなる。

:::

:::definition "htt_A_1_1_2" (lean := "CategoryTheory.IsLocallyPresentable, CategoryTheory.IsCardinalLocallyPresentable")
*HTT 定義 A.1.1.2*　通常圏の局所可呈示性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=806)）。対応表の状態：一部（direction）。

*主張*　通常圏が可提示であるとは、局所小で小余極限を持ち、小さい集合の対象で余極限生成され、各対象がある小さい正則基数でコンパクトであることである。

KB-W2原文・型再照合：仮定：通常圏 C に Mathlib IsLocallyPresentable を仮定（Lean が強い：一つの正則 κ と κ-presentable な filtered generating family を選ぶ）。結論：小さい余極限と小さい生成族があり、各対象の presentability・局所小性の既存 instance により原典の四条件を満たす方向は一致。HTT の colimit generating set と各対象の small だけから一様な κ-filtered generator を抽出する逆方向の比較は含まない。

コンパクト性は生成集合に属する対象について調べれば足りる。この場合は任意の対象を生成集合の小図式の余極限として表し、図式も扱える大きい基数を取る。

:::

# A.1.2 Lifting Problems and the Small Object Argument

%%%
number := false
tag := "htt-A-1-2"
%%%

:::proposition "htt_A_1_2_1" (lean := "CategoryTheory.HasLiftingProperty, CategoryTheory.MorphismProperty.rlp, CategoryTheory.MorphismProperty.llp, CategoryTheory.MorphismProperty.le_llp_rlp")
*HTT 注意 A.1.2.1*　終対象に対する拡張性の記法（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=807)）。対応表の状態：Mathlib にある。

*主張*　射 $`A\to B` に関して対象 $`X` が延長性を持つとは、任意の $`A\to X` が $`B\to X` に延びることである。

仮定：p:A→B と X→1、1 が終対象（HTT と一致）。結論：HasLiftingProperty p (X→1) は任意の CommSq に lift を要求し、下辺と可換性は終対象性で一意なので、A→X が B→X に延長するという原典の extension property に一致。 さらに S.rlp、S.llp が二つの直交類の記法に対応し、le\_llp\_rlp は S⊆S.rlp.llp を直接与える。

右の射を $`X\to 1` とした持ち上げ条件である。集合 $`S` の各射に対する右持ち上げ類を作り、その類に対する左持ち上げ類を作ると、元の $`S` がその中に含まれる。

:::

:::definition "htt_A_1_2_2" (lean := "CategoryTheory.MorphismProperty.IsStableUnderCobaseChange, CategoryTheory.MorphismProperty.IsStableUnderTransfiniteComposition, CategoryTheory.MorphismProperty.IsStableUnderRetracts")
*HTT 定義 A.1.2.2*　弱飽和な射の類の三つの閉性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=807)）。対応表の状態：Mathlib にある。

*主張*　小余極限を持つ通常圏の弱飽和な射の類は、押し出し・超限合成・矢印圏でのレトラクトで閉じている。

仮定：小余極限を持つ通常圏と射の類 S（HTT と一致）。結論：pushout・任意の小さい well-ordered continuous composition・arrow retract に関する三つの class が、原典の weak saturation の各条件に一致。別の全射条件を加える強飽和とは区別する。

超限合成では、各段のそれ以前の余極限からその段への射を検査する。すべてのその射が類に入ると、始域から超限列全体の余極限への射も入る。

:::

:::proposition "htt_A_1_2_3" (lean := "CategoryTheory.MorphismProperty.IsStableUnderTransfiniteComposition, CategoryTheory.MorphismProperty.isomorphisms_le_of_containsIdentities, CategoryTheory.MorphismProperty.comp_mem")
*HTT 命題 A.1.2.3*　弱飽和な類の同型と合成による閉性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=808)）。対応表の状態：Mathlib にある。

*主張*　小余極限を持つ通常圏の弱飽和類は全同型を含み、二つの射の合成に関して閉じている。

仮定：S が原典の三閉性を持つ（HTT と一致）。結論：transfinite-composition closure から Mathlib の既存 instance が IsMultiplicative を与えて恒等・合成で閉じ、retract/pushout の iso 安定性と isomorphisms\_le\_of\_containsIdentities から全同型を含む（一致）。

零段の超限合成から恒等射が入り、押し出しで同型も入る。長さ二の列に超限合成の条件を適用すると通常の合成が得られる。

:::

:::proposition "htt_A_1_2_5" (lean := "SerrePositivity.Smith.hasSmallObjectArgument, SerrePositivity.Smith.AccessibleSmallObject.exists_factorization_at, SerrePositivity.Smith.generatedLeft_le_of_closed, SerrePositivity.MorphismClosure.stableUnderCoproducts")
*HTT 命題 A.1.2.5*　関手的で可到達な小対象分解（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=808)）。対応表の状態：一部（stronger-hyp）。

*主張*　可提示な通常圏で、小さい射の族に対し、左の射がその弱飽和閉包に属し、右の射が元の族に対する右持ち上げ性を持つ関手的因子分解がある。

KB-W2原文・型再照合：仮定：原典の C に加え Mathlib IsLocallyPresentable C、局所小性と一つの colimit universe を明示し、生成射の類は小さい（Lean の形式的仮定が強い）。結論：I.rlp.llp と I.rlp の同じ functorial factorization があり、生成射の両端が κ-presentable なら指定分解の全 arrow factors が κ-filtered colimits を保つ。generatedLeft\_le\_of\_closed と coproduct closure により左類は最小の弱飽和類に入り、原典の二結論に一致。この Mathlib presentability と原典の poset 型定義の完全な比較は含まない。

生成射の両端が共通の正則基数 $`\kappa` でコンパクトなら、この因子分解関手は $`\kappa`-濾過余極限を保つ。因子分解の出力は、二つの射とその合成を含む図式である。

:::

:::corollary "htt_A_1_2_7" (lean := "SerrePositivity.Smith.hasSmallObjectArgument, SerrePositivity.Smith.generatedLeft_le_of_closed, SerrePositivity.MorphismClosure.stableUnderCoproducts, CategoryTheory.MorphismProperty.le_llp_rlp, CategoryTheory.MorphismProperty.llp_rlp_of_hasSmallObjectArgument")
*HTT 系 A.1.2.7*　生成された左持上げ類の最小性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=809)）。対応表の状態：一部（stronger-hyp）。

*主張*　可提示な通常圏で、小さい射の集合が生成する弱飽和類は、その集合に対する右持ち上げ類に対して左持ち上げ性を持つ射の類である。

KB-W2原文・型再照合：仮定：小さい生成射の類 I、C は Mathlib IsLocallyPresentable（Lean の形式的仮定が強い）。結論：I⊆I.rlp.llp、任意の weakly saturated P⊇I に I.rlp.llp⊆P となり、原典の最小性に一致。I.rlp.llp の三閉性は ordinary lifting-class の既存 instances で与えられる。HTT の presentable の四条件からの比較は別途必要。

小対象論法で該当する射を因子分解すると、左持ち上げ性を使ってその射を左因子のレトラクトにできる。これにより弱飽和類への包含が従う。

:::

# A.1.3 Monoidal Categories

%%%
number := false
tag := "htt-A-1-3"
%%%

:::proposition "htt_A_1_3_1" (lean := "CategoryTheory.CartesianMonoidalCategory.ofHasFiniteProducts, CategoryTheory.CartesianMonoidalCategory.ofChosenFiniteProducts")
*HTT 例 A.1.3.1*　有限積によるデカルトモノイダル構造（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=811)）。対応表の状態：Mathlib にある。

*主張*　有限積を持つ通常圏には、テンソルを直積、単位を終対象とするデカルト・モノイダル構造が入る。

仮定：通常圏 C が有限積を持つ（HTT と一致）。結論：選んだ終対象と二項積から CartesianMonoidalCategory C を構成し、tensor はその選んだ積、unit は終対象。積の普遍性による associator/unitor の構成なので原典に一致。

結合子と単位子は積の普遍性から誘導する。積や終対象の選択を変えても、得られるモノイダル圏は標準的に同値である。

:::

:::proposition "htt_A_1_3_2" (lean := "CategoryTheory.MonoidalCategory")
*HTT 注意 A.1.3.2*　モノイダル構造の略記の慣習（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=812)）。対応表の状態：Mathlib にある。

*主張*　モノイダル圏を $`C` や $`(C,\otimes)` と略記するときも、単位・結合子・単位子を構造の一部として含める。

仮定：通常圏 C（HTT と一致）。結論：MonoidalCategory C は tensor と unit と associator/unitor 及び pentagon/triangle の証明を一つの構造に束ね、C の monoidal structure と呼ぶ略記の内容に一致。

テンソルの記号だけで構造を表すのは表記上の省略である。自然同型と整合条件を備えたデータが前提となる。

:::

:::proposition "htt_A_1_3_3" (lean := "CategoryTheory.MonoidalOpposite, CategoryTheory.MonoidalOpposite.tensorLeftIso")
*HTT 注意 A.1.3.3*　テンソルの順序を反転した構造（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=812)）。対応表の状態：Mathlib にある。

*主張*　モノイダル構造の反対は、同じ圏で $`A\otimes^{\mathrm{op}}B=B\otimes A` とする積の順序の反転である。

仮定：モノイダル圏 C（HTT と一致）。結論：Cᴹᵒᵖ は underlying arrows を反転せず tensor の引数を反転した圏で、元の右 tensor と反対側の左 tensor が同型。原典の ⊗op と一致し、Cᵒᵖ と混同しない。

結合子と単位子も因子の順序の反転に合わせて移す。対象と射を持つ基礎圏は同じである。

:::

:::definition "htt_A_1_3_4" (lean := "CategoryTheory.Closed, CategoryTheory.MonoidalClosed, CategoryTheory.MonoidalOpposite.tensorLeftIso")
*HTT 定義 A.1.3.4*　左右の閉モノイダル構造（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=812)）。対応表の状態：Mathlib にある。

*主張*　左閉性は各 $`A\otimes-` が右随伴を持つこと、右閉性は各 $`-\otimes A` が右随伴を持つことで、閉性はその両方を指す。

仮定：モノイダル C（HTT と一致）。結論：Mathlib Closed A は tensorLeft A の右随伴を選び、MonoidalClosed C は全 A で要求するので HTT の left-closed に一致。right-closed は Cᴹᵒᵖ の同じ構造により表せ、両方を要求すれば原典の closed。Mathlib の docstring の right-closed という名称だけで左右を判断しない。

テンソルが対称でないときは二種類の内部 Hom を区別する。右閉性はテンソル順序を反転した構造の左閉性に当たる。

:::

:::definition "htt_A_1_3_5" (lean := "CategoryTheory.Functor.LaxMonoidal, CategoryTheory.Functor.OplaxMonoidal, CategoryTheory.Functor.Monoidal, CategoryTheory.NatTrans.IsMonoidal")
*HTT 定義 A.1.3.5*　lax と oplax モノイダル関手（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=812)）。対応表の状態：Mathlib にある。

*主張*　右 lax モノイダル関手は $`G(A)\otimes G(B)\to G(A\otimes B)` と $`1_D\to G(1_C)` を備え、結合と単位の整合条件を満たす。

仮定：モノイダル圏 C,D と関手 F（HTT と一致）。結論：LaxMonoidal は 1D→F1C と FX⊗FY→F(X⊗Y)、OplaxMonoidal は逆向き、Monoidal は互いに逆な両構造、IsMonoidal は単位と tensor map に可換な変換であり、原典の right-lax/left-lax/monoidal の定義に一致。

左 lax の構造射はどちらも逆向きになる。モノイダル自然変換はこれらの構造射と可換である。構造射が同型なら逆射で他方の lax 構造を定められ、この場合をモノイダル関手と呼ぶ。

:::

:::proposition "htt_A_1_3_6" (lean := "CategoryTheory.Adjunction.laxMonoidalEquivOplaxMonoidal")
*HTT 注意 A.1.3.6*　随伴に沿う lax 構造の移送（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=813)）。対応表の状態：Mathlib にある。

*主張*　モノイダル圏の間の随伴 $`F\dashv G` では、$`G` の右 lax モノイダル構造と $`F` の左 lax モノイダル構造が対応する。

仮定：モノイダル圏の通常の随伴 F⊣G（HTT と一致）。結論：G.LaxMonoidal≃F.OplaxMonoidal が両構造の相互逆の対応で、原典の右随伴の right-lax と左随伴の left-lax の対応に一致。

テンソルと単位の構造射を随伴で移すと向きの異なる構造射になる。結合と単位の整合条件も対応する。

:::

:::proposition "htt_A_1_3_7" (lean := "CategoryTheory.Functor.OplaxMonoidal.ofChosenFiniteProducts")
*HTT 例 A.1.3.7*　有限積保存とモノイダル関手（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=813)）。対応表の状態：Mathlib にある。

*主張*　デカルト・モノイダル構造を持つ圏の間の任意の関手は標準的な左 lax 構造を持ち、それがモノイダル関手となることは有限積保存と同値である。

仮定：CartesianMonoidalCategory C,D と任意の F:C⥤D（HTT と一致）。結論：F の canonical oplax structure は積の比較写像であり、その構造について Monoidal の存在 iff PreservesFiniteProducts F（一致）。

二項積の比較射を積の射影の像から作り、単位の比較射を終対象への一意な射として作る。この両方が同型なら、空積を含む有限積を保存する。

:::

# A.1.4 Enriched Category Theory

%%%
number := false
tag := "htt-A-1-4"
%%%

:::proposition "htt_A_1_4_1" (lean := "CategoryTheory.MonoidalClosed.enrichedCategorySelf, CategoryTheory.MonoidalClosed.enrichedCategorySelf_hom, CategoryTheory.MonoidalOpposite.tensorLeftIso")
*HTT 例 A.1.4.1*　閉モノイダル圏の自己豊穣（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=814)）。対応表の状態：Mathlib にある。

*主張*　右閉モノイダル圏は、内部 Hom $`Y^X` を写像対象として自分自身で豊穣化できる。

仮定：HTT の right-closed な C、すなわち tensorRight X に右随伴を持つ（Mathlib では Cᴹᵒᵖ の MonoidalClosed と一致）。結論：自己豊穣の Hom は指定した internal Hom で、合成と単位もそれから作る（一致）。Mathlib の enriched composition は Hom(X,Y)⊗Hom(Y,Z) の順であり、monoidal opposite を通じた規約の反転を明記して用いる。

$`-\otimes X` と $`(-)^X` の随伴に付随する評価射を使う。二つの評価を順に行う射の随伴によって、内部 Hom の合成を作る。

:::

:::proposition "htt_A_1_4_2" (lean := "CategoryTheory.ForgetEnrichment, CategoryTheory.EnrichedCategory")
*HTT 例 A.1.4.2*　集合で豊穣化された圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=815)）。対応表の状態：Mathlib にある。

*主張*　集合のデカルト・モノイダル圏で豊穣化した圏は、通常の圏である。

仮定：Cartesian monoidal な Type に豊穣された対象の型 D（HTT と一致）。結論：Hom-object は集合、unit は各恒等、composition は集合の二項写像であり、ForgetEnrichment の Hom(1,Hom(X,Y)) は単位型からの写像すなわち Hom(X,Y) の元で、通常圏の定義と一致。

写像対象は集合、豊穣合成は Hom 集合の直積から別の Hom 集合への写像である。単位射は一点集合からの写像として恒等射を指定する。

:::

:::proposition "htt_A_1_4_3" (lean := "CategoryTheory.TransportEnrichment, CategoryTheory.ForgetEnrichment, CategoryTheory.EnrichedCategory")
*HTT 注意 A.1.4.3*　lax 関手による豊穣の基底変換（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=815)）。対応表の状態：Mathlib にある。

*主張*　右 lax モノイダル関手 $`G:C\to C'` は、写像対象に $`G` を適用して $`C`-豊穣圏を $`C'`-豊穣圏に移す。

仮定：lax monoidal F:V→W と V-enriched D（HTT と一致、合成の tensor 順序は一貫して monoidal opposite の規約へ反転）。結論：同じ対象で Hom=F(HomD)、unit=ε≫F(id)、composition=μ≫F(comp) という transport があり、ForgetEnrichment は Hom(1,HomD) を射とする通常圏（一致）。

合成は $`G` のテンソル比較を通して元の合成の像へ進み、単位は単位比較を通して元の単位の像へ進む。$`G=\operatorname{Hom}_C(1,-)` は、豊穣圏の基礎にある通常圏を取り出す例である。

:::

:::proposition "htt_A_1_4_4" (lean := "CategoryTheory.EnrichedFunctor, CategoryTheory.EnrichedNatTrans")
*HTT 注意 A.1.4.4*　豊穣関手と豊穣自然変換（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=815)）。対応表の状態：一部（component）。

*主張*　豊穣関手は対象と写像対象の写像からなり、豊穣単位と合成を保つ。豊穣自然変換は成分の射が写像対象上の自然性を満たす。

KB-W2原文・型再照合：仮定：同じ V に豊穣された D,D′（HTT と一致、tensor 順序は反転規約）。結論：対象写像・Hom-object 上の写像と unit/comp 公理、各対象の unit-shaped morphism と enriched naturality による functor/natural transformation の定義は一致。本文後半の任意の豊穣圏の tensor/cotensor の表現可能性とその存在は含まない。

自然性は各対象対について、成分を始域側で合成する写像と終域側で合成する写像が、豊穣関手の構造を通じて一致することをいう。写像対象の中で可換性を要求する点が通常の対象ごとの記述を強めている。

:::

:::proposition "htt_A_1_4_5" (lean := "CategoryTheory.MonoidalClosed.enrichedCategorySelf, CategoryTheory.MonoidalClosed.enrichedCategorySelf_hom")
*HTT 例 A.1.4.5*　自己豊穣のテンソルと余テンソル（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=817)）。対応表の状態：一部（component）。

*主張*　右閉モノイダル圏を自身の上で豊穣化すると、自身によるテンソルを持つ。余テンソルも持つことは左閉性と同値である。

KB-W2原文・型再照合：仮定：right-closed C を規約反転して MonoidalClosed とする（HTT の自己豊穣部分と一致）。結論：internal Hom による自己豊穣は一致。enriched tensor を corepresentable functor として定めた構造と、左閉性 iff 全 cotensor の存在の比較宣言はないため、その部分は数えない。

右閉性から得られる内部 Hom とテンソルの随伴を使ってテンソルの普遍性を得る。余テンソルに必要な随伴は反対側の因子を固定したときのものである。

:::

