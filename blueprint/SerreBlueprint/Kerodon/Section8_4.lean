-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Functor.KanExtension.Dense
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndLeftKanPreservation
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndLeftKanUnitRecovery
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndRestrictionEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafNativeDensityKan
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaRestrictionEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.EquivalenceSmallLimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.ComparisonCartesian
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Definition
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftCanonical
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Shapes
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LeftAdjointAllColimitPreservation
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.LocallySmall
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.DenseCanonicalColimits
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.PresheafDensity
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.PresheafYonedaLeftKan
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.SigmaLeftKanAllColimitPreservation
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Completion
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafPointwiseColimits
import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.LeftPointwise

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "8.4 Cocompletion" =>
%%%
number := false
tag := "kerodon-8-4"
%%%

Kerodon の 8.4 節（[Tag 03V7](https://kerodon.net/tag/03V7)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::definition "kerodon_8_4_0_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheaf_exists_yonedaLeftKan, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinity_hasColimit")
Kerodon Definition 8.4.0.1（[Tag 04B8](https://kerodon.net/tag/04B8)）。対応表の状態：一部。

*主張*　無限圏の関手 $`h:C\to\widehat C` が余完備化を与えるとは、$`\widehat C` が余完備で、任意の余完備無限圏 $`D` に対し、小さい余極限を保つ $`\widehat C\to D` の圏から $`\operatorname{Fun}(C,D)` への前合成が同値になることである。

hを小準圏の標準Yoneda、ĈをPresheafInfinityに指定するとpresheafInfinity\_hasColimitは原文の条件(1)の小余完備性を直接与える。任意のh,Ĉの定義全体、全保存関手の制限同値(2)は含まない。

:::

:::theorem "kerodon_8_4_0_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinity_hasColimit, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheaf_exists_yonedaLeftKan, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafYonedaLeftKan_canonicalColimits")
Kerodon Theorem 8.4.0.3（[Tag 03W9](https://kerodon.net/tag/03W9)）。対応表の状態：一部。

*主張*　本質的に小さい無限圏 $`C` の共変 Yoneda 埋め込みは、空間値前層の無限圏 $`\operatorname{Fun}(C^{\mathrm{op}},S)` を $`C` の余完備化として示す。

小さいCの標準Yonedaに限るとpresheafInfinity\_hasColimitはcocompletionの小余完備性という同じ結論成分を直接返す。presheaf\_exists\_yonedaLeftKanは延長を構成するが、その小余極限保存と全準圏の制限同値まではこの引用から数えない。

:::

# 8.4.1 Dense Functors

%%%
number := false
tag := "kerodon-8-4-1"
%%%

Kerodon [Tag 03V8](https://kerodon.net/tag/03V8)

:::definition "kerodon_8_4_1_1" (lean := "CategoryTheory.Functor.IsDense, CategoryTheory.Functor.isDense_iff_fullyFaithful_restrictedULiftYoneda")
Kerodon Definition 8.4.1.1（[Tag 03V9](https://kerodon.net/tag/03V9)）。対応表の状態：Mathlib にある。

*主張*　局所小さい通常の圏 $`D` の充満部分圏 $`C` は、$`y` を $`\operatorname{Hom}_D(-,y)|_C` に送る $`D\to\operatorname{Fun}(C^{\mathrm{op}},\operatorname{Set})` が充満忠実なとき稠密である。

仮定：通常圏 C,D と充満な F : C⥤D。原文の充満部分圏の包含を含む（Lean が弱い）。結論：isDense\_iff\_fullyFaithful\_restrictedULiftYoneda は稠密性と Hom\_D(F−,−) の充満忠実性の iff（原文の定義と一致）。

:::

:::definition "kerodon_8_4_1_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.canonicalColimits_of_identityRestriction_bijective, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone") (uses := "kerodon_1_4_0_1")
Kerodon Definition 8.4.1.5（[Tag 03VD](https://kerodon.net/tag/03VD)）。対応表の状態：本体にある。

*主張*　無限圏 $`D` の充満部分圏 $`C` は、全対象 $`x` について、$`C\times_D D_{/x}` からの標準右錐が $`D` で余極限図式になるとき稠密である。

leftKanCanonicalCocone i (𝟙 D) Xに全XでIsColimitConeを課すことが、原文の指定したC×\_D D\_/Xからの標準余錐によるdenseの定義そのもの。標準余錐の構成を追記し、専用のDense名の有無でpartialにしない。

:::

:::proposition "kerodon_8_4_1_8"
Kerodon Proposition 8.4.1.8（[Tag 03VG](https://kerodon.net/tag/03VG)）。対応表の状態：なし。

通常圏の制限Yonedaの充満忠実性は原文のSpace値の制限Yonedaへの比較を持たない。通常の密度のiffだけを直接の特殊形としない。

宣言：`CategoryTheory.Functor.isDense_iff_fullyFaithful_restrictedULiftYoneda`、`CategoryTheory.Functor.IsDense.of_fullyFaithful_restrictedULiftYoneda`

:::

:::corollary "kerodon_8_4_1_9" (lean := "CategoryTheory.Functor.isDense_iff_fullyFaithful_restrictedULiftYoneda, CategoryTheory.Functor.isDense_iff_nonempty_isPointwiseLeftKanExtension, SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerve_isLeftKanExtensionHom_iff_pointwise, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeLeftKanExtendedFrom_iff_refl_extension, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.isLeftKanExtension_iff_forall_transport")
Kerodon Corollary 8.4.1.9（[Tag 03VH](https://kerodon.net/tag/03VH)）。対応表の状態：一部。

*主張*　局所小さい通常の圏の充満部分圏が稠密であることは、その神経が無限圏として稠密な部分圏であることと同値である。

C,Dを同じ宇宙の小さい通常圏に限ると、isDense\_iff\_nonempty\_isPointwiseLeftKanExtension、nerve\_isLeftKanExtensionHom\_iff\_pointwise、恒等変換の標準Kan余錐の判定を合わせ、同じ包含と恒等単位の密度のiffを直接得る。任意の局所小で大きい圏は含まない。

:::

:::definition "kerodon_8_4_1_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.canonicalColimits_of_identityRestriction_bijective, CategoryTheory.Functor.IsDense, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension, SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_3_1_5")
Kerodon Definition 8.4.1.15（[Tag 03VP](https://kerodon.net/tag/03VP)）。対応表の状態：本体にある。

*主張*　無限圏 $`D` への単体集合の写像 $`F:C\to D` は、$`F` の恒等変換が $`\mathrm{id}_D` を $`F` の $`F` に沿う左 Kan 拡張として示すとき稠密である。

IsLeftKanExtension F F (𝟙 D) (functorHomotopyRefl F)を課すことが原文の同じFのdenseの定義そのもの。一般の指定変換の型と恒等変換を追記し、専用のDense名の欠如は不足にしない。

:::

:::proposition "kerodon_8_4_1_22" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_4_4_4, kerodon_7_3_6_1, kerodon_7_4_4_14, kerodon_7_6_6_19, kerodon_8_3_1_3, kerodon_8_3_3_9, kerodon_8_3_3_13")
Kerodon Proposition 8.4.1.22（[Tag 03VX](https://kerodon.net/tag/03VX)）。対応表の状態：なし。

通常圏のrestrictedULiftYonedaの充満忠実性は、原文の指定λのSpace値Yonedaと任意単体図式Fへの比較を含まない。

宣言：`CategoryTheory.Functor.isDense_iff_fullyFaithful_restrictedULiftYoneda`、`CategoryTheory.Functor.IsDense.of_fullyFaithful_restrictedULiftYoneda`

:::

:::proposition "kerodon_8_4_1_23"
Kerodon Proposition 8.4.1.23（[Tag 03VZ](https://kerodon.net/tag/03VZ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の充満関手では密性を制限 Yoneda の充満忠実性で判定できる。任意の単体写像の密性から像を含む充満∞部分圏の密性へ移す型は見つからない。

:::

# 8.4.2 Density of Yoneda Embeddings

%%%
number := false
tag := "kerodon-8-4-2"
%%%

Kerodon [Tag 03W1](https://kerodon.net/tag/03W1)

:::theorem "kerodon_8_4_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafDensityCocone_isColimit, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafDensityPresentation, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafNativeDensityKan.presheafIdentity_isLeftKanExtension, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafNativeDensityKan.presheafIdentity_canonicalColimits") (uses := "kerodon_1_4_0_1, kerodon_8_3_3_9")
Kerodon Theorem 8.4.2.1（[Tag 03W2](https://kerodon.net/tag/03W2)）。対応表の状態：一部。

*主張*　局所小さい無限圏の共変 Yoneda 埋め込みは稠密である。

Cを小準圏、hを標準Yonedaに限ると現本体presheafIdentity\_isLeftKanExtensionは同じhに沿う恒等関手の恒等単位の左Kan性、すなわち原文のdensityそのものを直接返す。elements図式の類似の密度だけでなく標準Kan余錐の型を追記した。

:::

:::corollary "kerodon_8_4_2_2" (uses := "kerodon_1_4_0_1, kerodon_8_3_3_13, kerodon_8_4_2_1")
Kerodon Corollary 8.4.2.2（[Tag 03W3](https://kerodon.net/tag/03W3)）。対応表の状態：なし。

elements-Yoneda図式の余極限性は、全表現可能前層の充満部分圏の包含に沿う全標準Kan余錐の余極限性ではない。その形状変更の比較を引用に持たない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafDensityCocone_isColimit`

:::

:::definition "kerodon_8_4_2_4" (uses := "kerodon_1_4_0_1, kerodon_8_4_1_22, kerodon_8_4_2_5")
Kerodon Variant 8.4.2.4（[Tag 03W5](https://kerodon.net/tag/03W5)）。対応表の状態：なし。

固定宇宙の標準densityは、原文の指定κで切った前層圏における同じYonedaの密度への大きさの比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafDensityCocone_isColimit`

:::

:::proposition "kerodon_8_4_2_5" (uses := "kerodon_1_4_0_1, kerodon_8_1_1_11, kerodon_8_3_1_3, kerodon_8_3_4_15, kerodon_8_3_4_16, kerodon_8_3_5_1")
Kerodon Proposition 8.4.2.5（[Tag 03W6](https://kerodon.net/tag/03W6)）。対応表の状態：なし。

各F,yでのYoneda評価の同値は、原文の指定κ値のevという全二変数profunctorのcorepresentationを与える自然同型との比較を持たない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaPresheafEvaluation_isQCatEquivalence`

:::

:::corollary "kerodon_8_4_2_7" (uses := "kerodon_1_4_0_1, kerodon_5_6_0_6, kerodon_5_6_6_21, kerodon_8_4_2_5")
Kerodon Corollary 8.4.2.7（[Tag 04BB](https://kerodon.net/tag/04BB)）。対応表の状態：なし。

標準elementsとYoneda sliceの比較は原文の任意の指定right fibration Uに対する表現Fの条件とのiffではない。底上で同じUと同一視する比較が必要。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafElementsYonedaSliceComparison_isQCatEquivalence`

:::

:::corollary "kerodon_8_4_2_8" (uses := "kerodon_1_4_0_1, kerodon_8_4_2_7")
Kerodon Corollary 8.4.2.8（[Tag 05WB](https://kerodon.net/tag/05WB)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：元の図式が C で極限を持つ場合にその表現可能前層の極限を扱う。一般の f の前層極限が反対スライスの輸送を表すという同定は、ecf(κ) の形状制限を含めて見つからない。

:::

# 8.4.3 Cocompletion via the Yoneda Embedding

%%%
number := false
tag := "kerodon-8-4-3"
%%%

Kerodon [Tag 03W8](https://kerodon.net/tag/03W8)

*presentable-route.html — 4. $`\mathcal P(A)` の普遍性*

*定理*（1 圏：古典、∞ 圏：HTT Thm 5.1.5.6）．$`A` を小さい（∞）圏、$`\mathcal E` を小さい余極限をすべて持つ（∞）圏とする。制限
$$`y^*\colon\ \mathrm{Fun}^L(\mathcal P(A),\mathcal E)\ \longrightarrow\ \mathrm{Fun}(A,\mathcal E)`
は（∞）圏の同値である。ここで $`\mathrm{Fun}^L` は小さい余極限を保つ関手の充満部分圏。逆は $`y` に沿った左 Kan 拡張で、
$$`(\mathrm{Lan}_y f)(F)=\operatorname*{colim}_{(a,x)\in\mathrm{el}(F)}f(a)\quad\text{（1 圏）},\qquad (\mathrm{Lan}_y f)(F)=\operatorname*{colim}\bigl(\mathrm{Un}(F)\to A\xrightarrow{f}\mathcal E\bigr)\quad\text{（}\infty\text{ 圏）}.`

$`A` と $`\mathcal E` の役割

- \*\*$`A`\*\*：任意の小さい（∞）圏。小ささは、$`\mathcal P(A)` の Hom（写像空間）が小さくなること、および公式の余極限の添字 $`\mathrm{el}(F)`・$`\mathrm{Un}(F)` が小さくなることのために要る。

- \*\*$`\mathcal E`\*\*：小さい余極限をすべて持つ任意の（∞）圏。大きくてよい（$`\mathrm{Set}`、$`\mathcal S`、$`\mathrm{sSet}`、$`D(R)`、$`\mathrm{Cat}_\infty` など）。

- 定理は、そのような組 $`(A,\mathcal E)` ごとに成り立つ。「$`\mathcal P(A)` は、余極限を持つどんな $`\mathcal E` に対しても、$`A` からの関手を余極限を保つ関手に一意に延長できる」という意味で $`A` の自由余完備化である。

- 表現可能性定理（§5）では、$`A` を $`\mathcal C` の $`\kappa`-コンパクト対象のなす小さい部分圏に取り、$`\mathcal E=\mathcal S^{\mathrm{op}}`（1 圏なら $`\mathrm{Set}^{\mathrm{op}}`）に取る。「$`H\colon\mathcal P(A)^{\mathrm{op}}\to\mathcal S` が余極限を極限に送る」は「$`H^{\mathrm{op}}\colon\mathcal P(A)\to\mathcal S^{\mathrm{op}}` が余極限を保つ」と同じで、$`\mathcal S` が小さい極限を持つので $`\mathcal S^{\mathrm{op}}` は小さい余極限を持つ。

*presentable-route.html — 4. $`\mathcal P(A)` の普遍性 — 証明の流れ*

- ステップ　／　1 圏　／　∞ 圏
- ① 米田　／　自然変換の定義から直接　／　関手版の米田。Hom 関手の構成に straightening
- ② co-Yoneda　／　$`F\cong\operatorname{colim}_{\mathrm{el}(F)}y(a)`　／　$`F\simeq\operatorname{colim}(\mathrm{Un}(F)\to A\xrightarrow{y}\mathcal P(A))`（HTT Lemma 5.1.5.3）
- ③ 一意性　／　余極限を保つ関手は②で $`A` での値で決まる。自然変換も同様　／　余極限を保つ関手は制限の左 Kan 拡張。Kan 拡張の空間が可縮（HTT Prop. 4.3.2.15）
- ④ 存在　／　公式で $`\mathrm{Lan}_y f` を定義し、右随伴 $`R(e)=\mathrm{Hom}(f(-),e)` を作る　／　同じ方針。右随伴の関手性に $`\mathcal E` の Hom 関手が要る

*② の計算*．1 圏では
$$`\mathrm{Hom}\Bigl(\operatorname*{colim}_{\mathrm{el}(F)}y(a),G\Bigr)\cong\lim_{(a,x)\in\mathrm{el}(F)}G(a)\cong\mathrm{Nat}(F,G),`
二つ目は自然変換の定義そのもの。∞ 圏では
$$`\mathrm{Map}\Bigl(\operatorname*{colim}_{\mathrm{Un}(F)}y\circ p,G\Bigr)\simeq\lim_{\mathrm{Un}(F)}G\circ p\simeq\mathrm{Fun}_{/A}\bigl(\mathrm{Un}(F),\mathrm{Un}(G)\bigr)\simeq\mathrm{Map}_{\mathcal P(A)}(F,G),`
二つ目は「$`\mathcal S` 値図式の極限は unstraightening の切断の空間」（第 5 章 §3）、三つ目は unstraightening の写像空間の比較（補章 §5）。1 圏で定義だったところが定理に置き換わる。

*④ の右随伴*．$`\mathrm{Hom}_{\mathcal E}(\Phi F,e)\cong\lim_{\mathrm{el}(F)}\mathrm{Hom}(f(a),e)\cong\mathrm{Nat}(F,R(e))` で $`\Phi\dashv R`。これは realization ⊣ nerve の形で、$`A=\Delta`、$`f=|\Delta^\bullet|` なら幾何学的実現と特異単体集合、$`f=\mathfrak C[\Delta^\bullet]` なら $`\mathfrak C\dashv N^{hc}`（補章 3）。

:::definition "kerodon_8_4_3_1"
Kerodon Definition 8.4.3.1（[Tag 04BD](https://kerodon.net/tag/04BD)）。対応表の状態：なし。

固定宇宙のYoneda左Kan延長は、原文の任意のhと正則κについてのκ余完備性・κ保存関手の全準圏の制限同値の定義に一致しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheaf_exists_yonedaLeftKan`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafYonedaLeftKan_canonicalColimits`

:::

:::theorem "kerodon_8_4_3_2" (uses := "kerodon_1_4_0_1, kerodon_7_3_5_8, kerodon_7_3_6_15, kerodon_8_3_3_13, kerodon_8_4_3_4, kerodon_8_4_3_5")
Kerodon Theorem 8.4.3.2（[Tag 04BE](https://kerodon.net/tag/04BE)）。対応表の状態：なし。

全小余完備な標的への左Kan延長存在だけでは、原文のS\_\<κ値の前層圏がκ-cocompletionであるという同じ結論の条件を直接返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheaf_exists_yonedaLeftKan`

:::

:::lemma_ "kerodon_8_4_3_4" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_5_6_7_7, kerodon_8_3_1_3, kerodon_8_3_3_13")
Kerodon Lemma 8.4.3.4（[Tag 03WG](https://kerodon.net/tag/03WG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：小さい標準 right unstraightening から表現可能前層への図式がある。表現可能前層の充満部分圏と F 上のスライスの引き戻し自体の本質的 κ-small 性を示す型は見つからない。

:::

:::theorem "kerodon_8_4_3_5" (uses := "kerodon_1_4_0_1, kerodon_7_3_6_13, kerodon_7_4_1_15, kerodon_7_4_1_22, kerodon_8_3_3_13, kerodon_8_4_2_2, kerodon_8_4_2_5, kerodon_8_4_3_4")
Kerodon Theorem 8.4.3.5（[Tag 03WH](https://kerodon.net/tag/03WH)）。対応表の状態：なし。

presheafYonedaLeftKan\_canonicalColimitsは既に左Kan拡張を仮定する。原文のκ余極限保存との逆向きは型になく、P\_Σの保存判定も全前層圏とは異なる対象。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafYonedaLeftKan_canonicalColimits`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.sigmaLeftKanExtension_preservesSmallColimits_iff`

:::

:::corollary "kerodon_8_4_3_8"
Kerodon Corollary 8.4.3.8（[Tag 03WL](https://kerodon.net/tag/03WL)）。対応表の状態：なし。

小さいelements図式の密度表示はあるが、原文の指定κで切った値圏とκ-smallなKを同時に満たす型への大きさの比較がない。宇宙で小さいというだけを数値κの特殊形にしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafDensityCocone_isColimit`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityCocone_vertex`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafElementsYonedaDiagram`

:::

:::corollary "kerodon_8_4_3_9"
Kerodon Corollary 8.4.3.9（[Tag 05JC](https://kerodon.net/tag/05JC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：前層の表現可能生成と、通常圏で極限が誘導する表現可能データはある。T の制限の κ-small 性・極限保存から T をその制限前層で表現する iff は見つからない。

:::

# 8.4.4 Example: The Universal Property of S

%%%
number := false
tag := "kerodon-8-4-4"
%%%

Kerodon [Tag 06YD](https://kerodon.net/tag/06YD)

:::theorem "kerodon_8_4_4_1"
Kerodon Theorem 8.4.4.1（[Tag 06YE](https://kerodon.net/tag/06YE)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一般の小さい準圏の前層圏からの左 Kan 延長と、空間圏の小余極限存在を確認した。S\_\{\<κ\} を一点の自由 κ-余完備化として、任意の可縮な X での評価が κ-余連続関手の圏との同値になる型は見つからない。

:::

:::corollary "kerodon_8_4_4_3"
Kerodon Corollary 8.4.4.3（[Tag 06YG](https://kerodon.net/tag/06YG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：0-truncated 空間の述語と空間圏の小余極限はある。任意の n の κ-small 切断空間上での評価の充満忠実性と、像を n-cotruncated 対象とする条件は見つからない。

:::

:::corollary "kerodon_8_4_4_5"
Kerodon Corollary 8.4.4.5（[Tag 06YJ](https://kerodon.net/tag/06YJ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：0-truncated 空間の述語と、切断制限のない前層上の Yoneda 左 Kan 延長はある。任意の整数 n に対する S\^\{≤n\} からの余連続関手を n-cotruncated 対象と対応させる評価の型は見つからない。

:::

# 8.4.5 Cocontinuous Extensions

%%%
number := false
tag := "kerodon-8-4-5"
%%%

Kerodon [Tag 03WM](https://kerodon.net/tag/03WM)

:::proposition "kerodon_8_4_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheaf_exists_yonedaLeftKan, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafYonedaLeftKan_unit_isIso")
Kerodon Proposition 8.4.5.1（[Tag 03WN](https://kerodon.net/tag/03WN)）。対応表の状態：一部。

*主張*　本質的に小さい無限圏 $`C` から、余完備で局所的に小さい無限圏 $`D` への $`f:C\to D` を取る。$`D` の共変 Yoneda 埋め込みと $`f^{\mathrm{op}}` に沿う制限の合成は左随伴 $`F:\operatorname{Fun}(C^{\mathrm{op}},S)\to D` を持ち、$`F` と $`C` の Yoneda 埋め込みの合成は $`f` と自然同型である。

Cを小準圏、標準Yonedaに限ればpresheaf\_exists\_yonedaLeftKanとunit\_isIsoは同じfについてFとF∘h≅fという原文の延長・回収の結論成分を直接作る。そのFが指定Gの左随伴という条件は含まない。

:::

:::corollary "kerodon_8_4_5_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.sigmaLeftKanExtension_preservesSmallColimits_iff, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.adjunction_preservesSmallColimits")
Kerodon Corollary 8.4.5.2（[Tag 04BF](https://kerodon.net/tag/04BF)）。対応表の状態：一部。

*主張*　$`C` が本質的に小さく、$`D` が余完備で局所小さい無限圏とする。関手 $`\operatorname{Fun}(C^{\mathrm{op}},S)\to D` が小さい余極限を保つことは、それが右随伴を持つことと同値である。

原文(2)の同じFに右随伴があるとき、小形状の余極限を左随伴が保存する本体の定理を適用すれば(1)を直接得る。P\_Σの別の保存判定は根拠とせず、(1)⇒(2)は含まない。

:::

:::corollary "kerodon_8_4_5_3" (lean := "CategoryTheory.Adjunction.rightAdjoint_preservesLimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.adjunction_preservesSmallLimits")
Kerodon Corollary 8.4.5.3（[Tag 04BG](https://kerodon.net/tag/04BG)）。対応表の状態：一部。

*主張*　本質的に小さい無限圏 $`C` に対し、$`\operatorname{Fun}(C,S)^{\mathrm{op}}\to S` が左随伴を持つこと、$`\operatorname{Fun}(C,S)` の対象に表現されること、小さい極限を保つことは同値である。

本体のQCatAdjunctionの右随伴による極限保存は、原文の同じFについて(1)⇒(3)を直接与える。Mathlibの通常圏の保存だけを根拠とはしない。表現可能性(2)と逆向きは含まない。

:::

:::definition "kerodon_8_4_5_4"
Kerodon Variant 8.4.5.4（[Tag 03WP](https://kerodon.net/tag/03WP)）。対応表の状態：なし。

固定宇宙の前層上のYoneda左Kan延長は、原文のS\_\<κ値の同じ指定Gの左随伴への比較を持たない。unitの可逆性だけはその随伴と同じ結論ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheaf_exists_yonedaLeftKan`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafYonedaLeftKan_unit_isIso`

:::

:::proposition "kerodon_8_4_5_6"
Kerodon Proposition 8.4.5.6（[Tag 04KT](https://kerodon.net/tag/04KT)）。対応表の状態：なし。

reflectionMappingEquivalenceは同じ単位の前合成による写像空間同値で、原文のF自身による後合成θとは異なる射。isLocalForHomの表現可能反転も、そのθと同定する型がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.reflectionMappingEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_iff_representableInverts`

:::

# 8.4.6 Adjoining Colimits to ∞-Categories

%%%
number := false
tag := "kerodon-8-4-6"
%%%

Kerodon [Tag 04BH](https://kerodon.net/tag/04BH)

:::definition "kerodon_8_4_6_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestrictionEquivalence, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaSiftedContinuousRestriction_isQCatEquivalence")
Kerodon Definition 8.4.6.1（[Tag 04BJ](https://kerodon.net/tag/04BJ)）。対応表の状態：一部。

*主張*　無限圏の関手 $`h:C\to\widehat C` が単体集合の族 $`\mathbb K` に関する余完備化を与えるとは、$`\widehat C` が $`\mathbb K`-余完備で、各 $`\mathbb K`-余完備な $`D` への $`\mathbb K`-余連続関手を $`h` に沿って制限すると $`\operatorname{Fun}(C,D)` との同値になることである。

𝕂を小κ-filtered形状、hを小準圏CのindYonedaに指定すると、Indのκ-filtered余完備性とindKappaContinuousRestrictionEquivalenceが同じ二条件を直接与える。任意𝕂と任意hを判定する定義全体は含まない。

:::

:::proposition "kerodon_8_4_6_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestrictionEquivalence, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaSiftedContinuousRestriction_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda_isIdempotentCompletion") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Proposition 8.4.6.3（[Tag 04BL](https://kerodon.net/tag/04BL)）。対応表の状態：一部。

*主張*　任意の無限圏 $`C` と単体集合の族 $`\mathbb K` に対し、$`C` の $`\mathbb K`-余完備化が存在する。構造関手は稠密かつ充満忠実で、$`C` に存在するすべての極限を保つ。

𝕂を小κ-filtered形状、Cを小準圏に限ると、Indの余完備性・制限同値とindYoneda\_isFullyFaithfulは同じK-cocompletionの存在と充満忠実性を直接返す。任意𝕂、densityと全既存極限保存の成分は含まない。

:::

:::definition "kerodon_8_4_6_6" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_8_3_3_13, kerodon_8_3_3_14, kerodon_8_4_2_4")
Kerodon Construction 8.4.6.6（[Tag 04BN](https://kerodon.net/tag/04BN)）。対応表の状態：なし。

Indの最小κ-filtered閉包は固定宇宙の前層圏内の構成。原文の指定したS\_\<κ内での任意の形状族の最小閉包との型の比較がなく、単なる最小性の類似だけは数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isIndVertex_kappaColimitClosed`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isIndVertex_minimal`

:::

:::proposition "kerodon_8_4_6_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestriction_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaSiftedContinuousRestriction_isQCatEquivalence") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_8_4_1, kerodon_7_3_6_15, kerodon_8_3_3_13, kerodon_8_4_6_6, kerodon_8_4_6_9, kerodon_8_4_6_10")
Kerodon Proposition 8.4.6.8（[Tag 04BQ](https://kerodon.net/tag/04BQ)）。対応表の状態：一部。

*主張*　任意の無限圏 $`C` と単体集合の族 $`\mathbb K` に対し、8.4.6.6 で作る $`\widehat C` への共変 Yoneda 埋め込みは $`\mathbb K`-余完備化を与える。

𝕂を小κ-filtered形状とし、閉包を標準Indで表示する場合、Indのκ-filtered余完備性とindKappaContinuousRestriction\_isQCatEquivalenceは同じYoneda制限の普遍性を直接返す。指定濃度で切った別の閉包模型への比較と任意𝕂は含まない。

:::

:::lemma_ "kerodon_8_4_6_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_exists_leftKanExtension_with_recovery, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indLeftKanExtension_preservesSmallKappaFilteredColimits") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_8_3_3_17, kerodon_8_4_3_2, kerodon_8_4_3_5, kerodon_8_4_6_6")
Kerodon Lemma 8.4.6.9（[Tag 04BR](https://kerodon.net/tag/04BR)）。対応表の状態：一部。

*主張*　無限圏 $`C` の 8.4.6.6 の $`\mathbb K`-余完備化と $`\mathbb K`-余完備な無限圏 $`D` に対し、任意の $`f:C\to D` は $`C` 上で自然同型を伴う延長 $`F:\widehat C\to D` を持つ。この $`F` は Yoneda の本質像から左 Kan 拡張され、$`\mathbb K`-余連続である。

𝕂を小κ-filtered形状、閉包を標準Indに限ると、ind\_exists\_leftKanExtension\_with\_recoveryとindLeftKanExtension\_preservesSmallKappaFilteredColimitsは同じfの拡張と回収同型およびκ-filtered保存を直接返す。任意𝕂の閉包は含まない。

:::

:::lemma_ "kerodon_8_4_6_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indLeftKanExtension_preservesSmallKappaFilteredColimits, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestrictionEquivalence") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_3_6_9, kerodon_8_4_6_6, kerodon_8_4_6_9")
Kerodon Lemma 8.4.6.10（[Tag 04BS](https://kerodon.net/tag/04BS)）。対応表の状態：一部。

*主張*　無限圏 $`C` の 8.4.6.6 の $`\mathbb K`-余完備化から $`\mathbb K`-余完備な $`D` への関手は、Yoneda の本質像から左 Kan 拡張されているとき、かつそのときに限り $`\mathbb K`-余連続である。

𝕂を小κ-filtered形状、閉包を標準Indに限ると、indLeftKanExtension\_preservesSmallKappaFilteredColimitsは同じ指定Fについて左Kan拡張⇒κ-cocontinuousの向きを直接返す。任意𝕂と逆向きは含まない。

:::

:::corollary "kerodon_8_4_6_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indLeftKanExtension_unit_isIso, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indLeftKanExtension_preservesSmallKappaFilteredColimits") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_8_4_6_6, kerodon_8_4_6_8, kerodon_8_4_6_10")
Kerodon Corollary 8.4.6.11（[Tag 05ZZ](https://kerodon.net/tag/05ZZ)）。対応表の状態：一部。

*主張*　無限圏の $`\mathbb K`-余完備化 $`h:C\to\widehat C`、$`\mathbb K`-余完備な $`D`、$`f:C\to D,F:\widehat C\to D` と変換 $`\alpha:f\to Fh` を取る。$`\alpha` が左 Kan 拡張を示すことは、$`F` が $`\mathbb K`-余連続で $`\alpha` が自然同型であることと同値である。

hをindYoneda、𝕂を小κ-filtered形状に限ると、指定αの左Kan性からunit\_isIsoとpreservesSmallKappaFilteredColimitsが同じαの(2)⇒(1)を直接与える。任意のcocompletionと逆向きは含まない。

:::

:::corollary "kerodon_8_4_6_12"
Kerodon Corollary 8.4.6.12（[Tag 05JD](https://kerodon.net/tag/05JD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左ファイブレーションの分類の基底変更と左余終性の slice 判定はある。K-余完備化への制限ファイバー積の射影の左余終性を輸送表現の K-余連続性で判定する型は見つからない。

:::

:::proposition "kerodon_8_4_6_13"
Kerodon Proposition 8.4.6.13（[Tag 0600](https://kerodon.net/tag/0600)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Ind-Yoneda 上の恒等関手の延長に使える型と、前層圏から Ind 部分圏への反射随伴はある。任意の K-余完備化 h の左随伴存在を C の K-余完備性と比較し、恒等関手の延長だとする型は見つからない。

:::

# 8.4.7 Functoriality of Cocompletion

%%%
number := false
tag := "kerodon-8-4-7"
%%%

Kerodon [Tag 060N](https://kerodon.net/tag/060N)

:::definition "kerodon_8_4_7_1"
Kerodon Definition 8.4.7.1（[Tag 060P](https://kerodon.net/tag/060P)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：各 C での Ind-Yoneda と関手の制限同値はある。QC の自己関手 T の単位の全頂点が K-余完備化であり、T の全辺が K-余連続となる定義は見つからない。

:::

:::proposition "kerodon_8_4_7_2"
Kerodon Proposition 8.4.7.2（[Tag 060Q](https://kerodon.net/tag/060Q)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：κ-filtered と sifted の場合に、個々の始域に対する制限同値を構成する。任意の小さい形状族に対して QC 全体の自己関手を作り、その同型を除いた一意性を示す型は見つからない。

:::

:::definition "kerodon_8_4_7_3"
Kerodon Definition 8.4.7.3（[Tag 060R](https://kerodon.net/tag/060R)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：個別の Ind に対する制限同値と presentable 圏上の余連続射の準圏模型はある。λ-small 準圏全体の自己関手と単位に K-余完備化および K-余連続性を課す述語は見つからない。

:::

:::proposition "kerodon_8_4_7_5"
Kerodon Proposition 8.4.7.5（[Tag 060T](https://kerodon.net/tag/060T)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：濃度変更の条件と一つの κ の Ind に対する普遍性はある。指数余終性で任意の形状族の余完備化が λ-small に収まり、QC\_\{\<λ\} の自己関手として同型を除き一意となる型は見つからない。

:::

:::lemma_ "kerodon_8_4_7_7"
Kerodon Lemma 8.4.7.7（[Tag 060W](https://kerodon.net/tag/060W)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：特定の Ind の制限同値と、左 Kan 延長を h Fun の Hom 集合で比較する型はある。任意の K と λ で余完備化、λ-small 標的の関手圏、core、h QC の四判定を往復する型は見つからない。

:::

:::proposition "kerodon_8_4_7_8"
Kerodon Proposition 8.4.7.8（[Tag 060X](https://kerodon.net/tag/060X)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定 C の前層圏から Ind または Σ 部分圏への反射随伴はある。QC\_\{\<λ\} の K-余完備部分の包含への左随伴と、任意の η をその単位とする判定は見つからない。

:::

:::corollary "kerodon_8_4_7_9"
Kerodon Corollary 8.4.7.9（[Tag 060Y](https://kerodon.net/tag/060Y)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定 C の Ind の普遍性と、別の前層包含に対する随伴はある。全 λ-small C での存在から一つの自己関手 T を作り、その K-余完備部分圏への因数分解で特徴づける型は見つからない。

:::

:::proposition "kerodon_8_4_7_10"
Kerodon Proposition 8.4.7.10（[Tag 060Z](https://kerodon.net/tag/060Z)）。対応表の状態：なし。

indInfinity\_isLocallySmallは固定宇宙の局所小性。原文の特定λでの局所λ-small性とecf(λ)-小形状の閉包への大きさ比較がなく、同じ結論とはしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.indInfinity_isLocallySmall`

:::

:::corollary "kerodon_8_4_7_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.indInfinity_isLocallySmall")
Kerodon Corollary 8.4.7.12（[Tag 0611](https://kerodon.net/tag/0611)）。対応表の状態：一部。

*主張*　局所小さい無限圏の、小さい単体集合の族 $`\mathbb K` に関する余完備化は局所小さい。

Cを小準圏、𝕂を小κ-filtered形状、cocompletionを標準Indに限るとindInfinity\_isLocallySmallは原文の同じ余完備化の局所小性を直接返す。任意𝕂と任意の局所小Cは含まない。

:::

:::proposition "kerodon_8_4_7_14"
Kerodon Proposition 8.4.7.14（[Tag 0613](https://kerodon.net/tag/0613)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Ind の局所小ささは写像空間についての型で、濃度変更の条件も定義される。κ-small 形状族の自由閉包全体が本質的 λ-small になるという対象も含む濃度評価は見つからない。

:::

# 8.4.8 Recognition of Cocompletions

%%%
number := false
tag := "kerodon-8-4-8"
%%%

Kerodon [Tag 03WR](https://kerodon.net/tag/03WR)

:::definition "kerodon_8_4_8_1"
Kerodon Definition 8.4.8.1（[Tag 03WS](https://kerodon.net/tag/03WS)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：全小余極限保存の述語と、前層評価が κ-filtered 余極限を保つ型はある。局所小かつ余完備な任意の D の対象に対し、全 Hom 関手の全小余極限保存を要求する atomic 述語は見つからない。

:::

:::definition "kerodon_8_4_8_3"
Kerodon Definition 8.4.8.3（[Tag 03WU](https://kerodon.net/tag/03WU)）。対応表の状態：なし。

IsDetectingは通常圏のHom集合の全単射で可逆性を判定する。原文の同じ準圏のKan写像空間の同値による検出条件との比較がない。

宣言：`CategoryTheory.ObjectProperty.IsDetecting`

:::

:::proposition "kerodon_8_4_8_6"
Kerodon Proposition 8.4.8.6（[Tag 03WX](https://kerodon.net/tag/03WX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：標準 Yoneda の充満忠実性と各前層の正準余錐の余極限性はある。任意の f で像の atomic 性と弱密度から余完備化を復元する判定は見つからない。

:::

:::corollary "kerodon_8_4_8_7"
Kerodon Corollary 8.4.8.7（[Tag 03WY](https://kerodon.net/tag/03WY)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：個別の Ind の局所小ささと、前層圏で表現可能対象からの生成はある。局所小余完備な任意の D が小さい atomic 弱密族を持つことと自由余完備化の存在を結ぶ iff は見つからない。

:::

:::lemma_ "kerodon_8_4_8_8"
Kerodon Lemma 8.4.8.8（[Tag 03X1](https://kerodon.net/tag/03X1)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：充満忠実性の後合成への移送と Ind の Yoneda 自体の充満忠実性はある。f=F∘h とその像の Hom の K-余連続性だけから拡張 F が充満忠実となる型は見つからない。

:::

:::definition "kerodon_8_4_8_9"
Kerodon Variant 8.4.8.9（[Tag 03WZ](https://kerodon.net/tag/03WZ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Ind の特定の制限同値と κ-filtered 余極限での閉性はある。任意の形状族について、K-余完備性・充満忠実性・像の Hom 保存・生成という四条件で f を判定する型は見つからない。

:::

:::corollary "kerodon_8_4_8_10"
Kerodon Corollary 8.4.8.10（[Tag 05JE](https://kerodon.net/tag/05JE)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Ind の閉性と、通常圏で生成対象の包含を形状族の閉包へ移す単調性はある。元の K-余完備化 f を全部分圏へ制限し、生成部分への新たな余完備化とする型は見つからない。

:::

# 8.4.9 Cocompletion and Right Fibrations

%%%
number := false
tag := "kerodon-8-4-9"
%%%

Kerodon [Tag 04BU](https://kerodon.net/tag/04BU)

:::theorem "kerodon_8_4_9_1"
Kerodon Theorem 8.4.9.1（[Tag 06MN](https://kerodon.net/tag/06MN)）。対応表の状態：なし。

elementsとYoneda sliceの同値は特定の底上の比較。原文のĈ,Êの余完備化の条件(b)(c)を同時に満たす図式ではなく、pullbackだけの別図式は直接の成分としない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafElementsYonedaSliceComparison_isQCatEquivalence`

:::

:::corollary "kerodon_8_4_9_6"
Kerodon Corollary 8.4.9.6（[Tag 04BW](https://kerodon.net/tag/04BW)）。対応表の状態：なし。

元のelements準圏とYoneda commaの比較は、原文の全前層圏P(E)とP(C)\_/Fの間の同じTの圏同値ではない。対象と射影の比較が不足。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafElementsYonedaSliceComparison_isQCatEquivalence`

:::

:::lemma_ "kerodon_8_4_9_7"
Kerodon Lemma 8.4.9.7（[Tag 06MT](https://kerodon.net/tag/06MT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：右ファイブレーションと表現可能 Hom の比較、および厳密 filtered 図式のファイバー余極限はある。K-余連続な右ファイブレーションで h\^\{U(X)\} の K-余連続性から h\^X の保存性を導く型は見つからない。

:::

