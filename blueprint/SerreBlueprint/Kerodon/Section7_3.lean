import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantRightKanReduction
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Transport
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.CanonicalMappingTrivial
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.ComparisonCartesian
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.ComparisonCocartesian
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Definition
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.GlobalIsofibrationDiagram
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Hom
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.InitialBoundaryCoconeRestriction
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCanonicalMapping
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaCoconeColimit
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaHomUniversal
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftHomUniversal
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftHomotopyInvariant
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftIdentityLeg
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanColimitExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftStrictExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftTerminalRestrictionExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftUnitCanonical
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftUnitInvertible
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.PosetNestedCanonicalRestriction
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeColimitConstantFamily
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeCosliceEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinCartesianRestriction
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinFamilyAssembly
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinRelativeUniversalExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftCanonical
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftCanonicalExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftConstantFamily
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftExtension
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftRestrictionTheorem
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftStrictExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftUnitInvertible
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeMappingPullback
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeRightRestrictionTheorem
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightHomotopyInvariant
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Shapes
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LeftCanonicalRestriction
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeColimit
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeColimitFunctorIso
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeColimitPointwise
import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.ClassicalHomUniversal

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "7.3 Kan Extensions" =>
%%%
number := false
tag := "kerodon-7-3"
%%%

Kerodon の 7.3 節（[Tag 02Y1](https://kerodon.net/tag/02Y1)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

*04-yoneda-adjunction-kan.html — 6. Kan 拡張 — 主な結果*

- 内容　／　Lean　／　場所
- 存在 ⇔ 各点の局所図式が余極限を持つ　／　\`exists\_kanLeftExtension\_iff\_local\_colimits\`　／　F1B/KanLeftCommaCoconeColimit
- 一意性：二つの左 Kan 拡張は $`\beta` と両立する \`FunctorIso\` で結ばれる　／　\`kanLeftKanExtensionIso\`　／　F1B/KanLeftHomUniversal
- 充満忠実な $`\delta` に沿う場合、単位は可逆（拡張は本当に「拡張」）　／　\`kanLeftKanExtension\_unit\_isIso\`　／　F1B/KanLeftUnitInvertible
- 各点の条件 ⇔ Hom の普遍性（$`\mathrm{Fun}(C,D)` での左随伴的な性質）　／　\`exists\_kanLeftExtension\_with\_homUniversal\_of\_local\_colimits\` など　／　F1B/KanLeftHomUniversal
- nerve の場合：通常の pointwise 左 Kan 拡張と一致　／　\`kanNerve\_isLeftKanExtensionHom\_iff\_pointwise\`　／　F1B/KanNerveLeftPointwise

右 Kan 拡張も双対的に揃っている（局所図式は $`K\times_C C_{c/}`、条件は極限）。

*04-yoneda-adjunction-kan.html — 6. Kan 拡張 — 証明の方針（存在）*

各点で余極限を選ぶだけでは、それらを一つの関手 $`F` に束ねられない。そこで「相対 join」による表示を使う。拡張の問題を $`C` の単体に沿った相対的な延長の問題に書き直し（\`LeftKanRelativeJoinRealization\`）、各単体で局所余極限の普遍性から延長を作る。そのうえで厳密化（\`Strictification\`）して、元の $`\beta` を保ったまま関手に組み立てる（F1B/KanGlobal\*、KanRelative\*）。第 2 章の「関手 ∞ 圏の極限の各点計算」と同じ型の議論で、各点の選択を骨格に沿って自然な族へ延ばしていく。

*04-yoneda-adjunction-kan.html — 7. 通常の圏論との整合（B5）*

F1B では、∞ 圏の概念を通常の圏の nerve に制限すると Mathlib の概念に一致することを確かめている（F1B/KanNerve\*、71 ファイル）。

- 随伴：\`kanNonempty\_adjunction\_iff\_nerveAdjunction\`

- 左右の Kan 拡張（pointwise）：\`kanNerve\_isLeftKanExtensionHom\_iff\_pointwise\`、\`kanNerve\_isRightKanExtensionHom\_iff\_pointwise\`

- 局所的な Kan 錐の双方向の移送：\`kanNerveLeftCoconeTransport\_cocone\`、\`kanNerveRightConeTransport\_cone\`

定義が意図どおりであることを確かめる検算の役目を果たしている。第 2 章で見たとおり、一般の極限についての同種の比較は、Core にはまだ小さな例しかない。

*f-b-literature-yoneda.html — 4. Kan 拡張の位置づけ — 4.1 二つの役割*

- *極限の一般化*：各点の右 Kan 拡張は $`\mathrm{Ran}_fF(d)=\lim(d\downarrow f\to C\to\mathcal E)`、$`d\downarrow f=C\times_D D_{d/}`。Kerodon が 7.1 → 7.2 → 7.3 と並べるのはこのため。

- *整合的な関手を作る手段*：$`C_0\subseteq C` 上の関手を左 Kan 拡張した関手の全体は $`\mathrm{Fun}(C_0,\mathcal D)` に trivial fibration で写る（Kerodon 7.3.6）。小さな部分で値を決めれば、全体への延長が可縮な選択の空間から一意に得られる。極限を関手にする構成（trivial fibration の切断）の一般化。

*f-b-literature-yoneda.html — 4. Kan 拡張の位置づけ — 4.2 この先の定義で使う場面*

- 場面　／　Kan 拡張としての捉え方
- 前層の普遍性　／　余極限を保つ $`\mathcal P(A)\to\mathcal D` は Yoneda に沿った $`\mathrm{Lan}_yF`
- $`\mathrm{Ind}` の普遍性　／　filtered 余極限を保つ延長も同じ型
- $`F_!`　／　$`\mathcal P(C)\to\mathcal P(D)` は左 Kan 拡張
- realization ⊣ nerve　／　presentable の特徴づけ（Lurie–Simpson）の核心
- 六関手形式の構成　／　$`D(X)=\lim_{\mathrm{Spec}A\to X}D(A)` のようにアフィンから右 Kan 拡張で延ばす。Liu–Zheng・Mann の延長定理も同じ型

関手を作る手段として、第 6 章 §8 の (a) 厳密な単体的関手、(b) straightening に加え、(c) 小さい部分で決めて Kan 拡張で延ばす、がある。六関手形式に向けては (c) が主役になる場面が多い。

*f-b-literature-yoneda.html — 4. Kan 拡張の位置づけ — 4.3 「すべては Kan 拡張」*

- 1 圏での主張　／　∞ 版
- 極限は一点への Kan 拡張　／　成り立つ（§4.4）
- $`G` が左随伴を持つ ⇔ $`\mathrm{Lan}_G\mathrm{id}` が存在して $`G` で保たれる（絶対 Kan 拡張）　／　成り立つ。∞-cosmos では随伴を absolute lifting として扱う
- 密度 $`\mathrm{id}=\mathrm{Lan}_yy`　／　成り立つ（presheafElementsColimitCocone\_isColimit、F2）
- codensity モナド $`\mathrm{Ran}_GG`　／　成り立つが ∞ 版のモナド論（HA 第 4 章）の上に立つ
- end・coend　／　twisted arrow 上の極限・余極限

∞ では各点の Kan 拡張を定義に採るのが普通（Kerodon 7.3.1）。それが存在するとき制限の随伴になることは定理（7.3.6）。Riehl–Verity でも各点の Kan 拡張は comma で定義される。

*f-b-literature-yoneda.html — 4. Kan 拡張の位置づけ — 4.4 一点への Kan 拡張*

大域的には、$`\mathrm{Ran}_f` は制限 $`f^*\colon\mathrm{Fun}(D,\mathcal E)\to\mathrm{Fun}(C,\mathcal E)` の右随伴。$`D=\ast` なら $`\mathrm{Fun}(\ast,\mathcal E)=\mathcal E`、$`f^*` は対角 $`\delta` なので $`\mathrm{Ran}_{C\to\ast}=\lim`。各点の形でも $`d\downarrow f=C` なので値は $`\lim_CF`。Kerodon・HTT は Kan 拡張を各点の形（極限を使う形）で定義するので、極限が先で Kan 拡張が後。1 圏論の流儀で Kan 拡張を先に定義すれば、極限はその特別な場合として定義できる。

:::definition "kerodon_7_3_0_1" (lean := "CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension")
Kerodon Definition 7.3.0.1（[Tag 02Y2](https://kerodon.net/tag/02Y2)）。対応表の状態：Mathlib にある。

*主張*　通常の圏の関手 $`F:C\to D` が充満部分圏 $`C^0` から左 Kan 拡張されているとは、任意の対象 $`c` で、$`C^0` の対象から $`c` への射で添字付けた $`F` の値の図式の余極限を、標準の余錐が $`F(c)` として与えることをいう。

仮定：通常圏の関手に沿う指定の LeftExtension。包含に限定しない（Lean が弱い）。結論：IsPointwiseLeftKanExtension は各対象で StructuredArrow による余錐の IsColimit。全部分圏の包含と制限からの標準変換を取ると原文の余錐（原文と一致）。

:::

# 7.3.1 Kan Extensions along General Functors

%%%
number := false
tag := "kerodon-7-3-1"
%%%

Kerodon [Tag 02Y7](https://kerodon.net/tag/02Y7)

:::definition "kerodon_7_3_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape") (uses := "kerodon_1_4_0_1, kerodon_4_6_4_15")
Kerodon Notation 7.3.1.1（[Tag 02Y8](https://kerodon.net/tag/02Y8)）。対応表の状態：一部。

*主張*　無限圏の図式 $`\delta:K\to C` と対象 $`c` に対し、$`K_{/c}=K\times_C C_{/c}`、$`K_{c/}=C_{c/}\times_C K` と置く。スライス・余スライスの対角射は、それぞれ $`\delta|_{K_{/c}}\to\underline c` と $`\underline c\to\delta|_{K_{c/}}` を与える。

leftKanShapeとrightKanShapeは原文のK\_/CとK\_C/という二つの指定pullbackを直接構成する。γ,γ′の自然変換までは引用に含まない。

:::

:::definition "kerodon_7_3_1_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanConeTransport, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram")
Kerodon Definition 7.3.1.2（[Tag 02Y9](https://kerodon.net/tag/02Y9)）。対応表の状態：本体にある。

*主張*　無限圏の関手 $`F:C\to D` と単体図式 $`\delta:K\to C,F_0:K\to D` に対し、$`\alpha:F\delta\to F_0` が右 Kan 拡張を与えるとは、任意の $`c` で誘導される錐 $`\underline{F(c)}\to F_0|_{K_{c/}}` が極限を与えることである。

仮定：単体写像 δ、F₀、F と SSet.Homotopy (δ≫F) F₀。定義自体は C,D の Quasicategory を要求しない（Lean が弱い）。結論：各 c で輸送した右 Kan 錐が IsLimitCone となる条件（原文の右 Kan 拡張と一致）。

:::

:::proposition "kerodon_7_3_1_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport.isColimitCone_iff, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanConeTransport.isLimitCone_iff")
Kerodon Warning 7.3.1.4（[Tag 02YB](https://kerodon.net/tag/02YB)）。対応表の状態：本体にある。

*主張*　Kan 拡張を点ごとに判定するとき、評価した自然変換の合成はホモトピーまでで定まり、それが普遍錐となるかはそのホモトピー類で決まる。

仮定：Quasicategory D、固定 δ,F₀,F と固定 α または β、同じ c における二つの輸送（Kerodon の合成の選択に一致）。結論：二つの輸送錐の極限性と輸送余錐の余極限性の二つの iff（合成の選択によらない点で一致）。

:::

:::definition "kerodon_7_3_1_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram")
Kerodon Variant 7.3.1.5（[Tag 02YC](https://kerodon.net/tag/02YC)）。対応表の状態：本体にある。

*主張*　無限圏の関手 $`F:C\to D` と単体図式 $`\delta:K\to C,F_0:K\to D` に対し、$`\beta:F_0\to F\delta` が左 Kan 拡張を与えるとは、任意の $`c` で誘導される余錐 $`F_0|_{K_{/c}}\to\underline{F(c)}` が余極限を与えることである。

仮定：単体写像 δ、F₀、F と SSet.Homotopy F₀ (δ≫F)。定義自体は C,D の Quasicategory を要求しない（Lean が弱い）。結論：各 c における輸送済み左 Kan 余錐の IsColimitCone（原文と一致）。

*04-yoneda-adjunction-kan.html — 6. Kan 拡張 — 定義：各点の条件*

$`\delta\colon K\to C`、$`F_0\colon K\to D` と、$`F\colon C\to D` および変換 $`\beta\colon F_0\Rightarrow F\delta` について、$`F` が左 Kan 拡張であるとは、各 $`c\in C` で、局所図式

$$`K\times_C C_{/c}\longrightarrow K\xrightarrow{F_0}D`

の上の誘導された余錐（頂点 $`F(c)`）が余極限であることをいう（Kerodon Variant 7.3.1.5）。

\`\`\`text
def IsLeftKanExtension \{K C D : SSet.\{u\}\} (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D)
    (β : SSet.Homotopy F₀ (δ ≫ F)) : Prop :=
  ∀ c : C \_⦋0⦌, ∃ t : LeftKanCoconeTransport δ F₀ F β c, IsColimitCone t.cocone
\`\`\`

変換 $`\beta` は単体的ホモトピー（$`K\times\Delta^1\to D`）として厳密に持つ。$`h\,\mathrm{Fun}` の射として持つ版が \`IsLeftKanExtensionHom\` である（F1B/KanExtensionHom）。

:::

:::proposition "kerodon_7_3_1_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.isLeftKanExtension_iff_of_homMk_eq, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.isRightKanExtension_iff_of_homMk_eq, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtensionHom")
Kerodon Remark 7.3.1.10（[Tag 02YG](https://kerodon.net/tag/02YG)）。対応表の状態：本体にある。

*主張*　無限圏の図式の間の自然変換 $`F\delta\to F_0` が右 Kan 拡張を与えるかどうかも、自然変換 $`F_0\to F\delta` が左 Kan 拡張を与えるかどうかも、関手圏でのその変換のホモトピー類によって決まる。

仮定：Quasicategory D、同じ端点の二変換と内部 Hom のホモトピー圏で同じ射を表す等式（Kerodon と一致）。結論：両変換の IsLeftKanExtension の iff、および右側の iff（原文と一致）。

:::

:::proposition "kerodon_7_3_1_14" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_3_6_1, kerodon_5_6_7_6, kerodon_7_2_1_13, kerodon_7_2_2_3, kerodon_7_3_1_2")
Kerodon Proposition 7.3.1.14（[Tag 02YL](https://kerodon.net/tag/02YL)）。対応表の状態：なし。

引用は通常圏のKan拡張の指定自然変換の判定。原文の∞圏での自然変換・任意の単体図式とのnerve比較がなく、相対余極限の添字変更もそのまま同じKan拡張ではない。

宣言：`CategoryTheory.Functor.isRightKanExtension_iff_precomp`、`CategoryTheory.Functor.isLeftKanExtension_iff_precomp`

:::

:::corollary "kerodon_7_3_1_15"
Kerodon Corollary 7.3.1.15（[Tag 06ME](https://kerodon.net/tag/06ME)）。対応表の状態：なし。

通常圏のRightExtensionの圏同値と存在のiffは、原文の∞圏の指定βとGα≫βの右Kan性を同じ変換として比較する型ではない。

宣言：`CategoryTheory.Functor.rightExtensionEquivalenceOfIso₁`、`CategoryTheory.Functor.hasRightExtension_iff_of_iso₁`

:::

:::proposition "kerodon_7_3_1_16"
Kerodon Proposition 7.3.1.16（[Tag 02YM](https://kerodon.net/tag/02YM)）。対応表の状態：なし。

Mathlibの通常圏の前合成によるKan拡張のiffは、原文の∞圏の指定変換と右Kan性への比較を欠く。通常圏の類似の(2)だけを直接の特殊形としない。

宣言：`CategoryTheory.Functor.isRightKanExtension_iff_precomp_equivalence`、`CategoryTheory.Functor.isLeftKanExtension_iff_precomp_equivalence`

:::

:::corollary "kerodon_7_3_1_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanExtension_unit_isIso, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanExtension_unit_isIso")
Kerodon Corollary 7.3.1.17（[Tag 02YN](https://kerodon.net/tag/02YN)）。対応表の状態：一部。

*主張*　無限圏の充満忠実関手 $`G:C^0\to C` に沿う右 Kan 拡張 $`F` の比較 $`\alpha:FG\to F_0` は自然同型である。左 Kan 拡張の比較 $`F_0\to FG` も自然同型である。

δをinner fibrationにも限るとkanLeftKanExtension\_unit\_isIsoは、充満忠実な同じδに沿う左Kan拡張の指定単位βが可逆と直接返す。右Kan拡張の余単位の節は含まない。

:::

:::proposition "kerodon_7_3_1_18" (lean := "SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRightKanExtension_refl_of_frameCofinality")
Kerodon Proposition 7.3.1.18（[Tag 039N](https://kerodon.net/tag/039N)）。対応表の状態：一部。

*主張*　$`\delta:K\to C` がある辺の族に関する局所化を与え、$`\alpha:F\delta\to F_0` が関手圏の同型なら、$`\alpha` は $`F` を $`F_0` の $`\delta` に沿う右 Kan 拡張として示す。

δをモデル圏のbifibrant部分のhammockLocalizationNerveMap、F₀=δ≫G、αを恒等変換に制限すると、移動後のmodelBifibrantSourceRightKanExtension\_refl\_of\_frameCofinalityは同じαの右Kan性を返す。ModelCategory C・指定resolution・frame余終性を明示入力とするschema（一般の具体的instanceなし）で、任意の局所化ではない。

:::

# 7.3.2 Kan Extensions along Inclusions

%%%
number := false
tag := "kerodon-7-3-2"
%%%

Kerodon [Tag 02YP](https://kerodon.net/tag/02YP)

:::definition "kerodon_7_3_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtendedFrom") (uses := "kerodon_1_4_0_1, kerodon_4_3_5_12, kerodon_7_3_1_1")
Kerodon Definition 7.3.2.1（[Tag 02YQ](https://kerodon.net/tag/02YQ)）。対応表の状態：一部。

*主張*　無限圏の関手 $`F:C\to D` が充満部分圏 $`C^0` から $`c` で左 Kan 拡張されているとは、$`C^0\times_C C_{/c}` の右錐をスライス縮約射と $`F` で送った図式が余極限図式であることをいう。右 Kan 拡張では $`C^0\times_C C_{c/}` の左錐と余スライス縮約射で極限図式を要求する。全ての $`c` で成り立つとき $`C^0` から左または右 Kan 拡張されているという。

leftKanCanonicalCocone δ F cは原文のC⁰\_/cに沿う同じ標準余錐で、そのIsColimitConeという型が左Kan extended at cの定義を直接与える。右側の定義はこの引用に含まない。

:::

:::proposition "kerodon_7_3_2_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeLeftKanExtendedFrom_iff_refl_extension, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_isColimit_of_terminal") (uses := "kerodon_1_4_0_1, kerodon_7_3_1_2, kerodon_7_3_1_5, kerodon_7_3_2_1")
Kerodon Proposition 7.3.2.6（[Tag 02YU](https://kerodon.net/tag/02YU)）。対応表の状態：一部。

*主張*　無限圏の充満部分圏 $`i:C^0\to C` に対し、$`F:C\to D` が $`C^0` から左 Kan 拡張されていることは、制限 $`F_0` の恒等変換 $`F_0\to Fi` が左 Kan 拡張を与えることと同値である。逆向きの恒等変換と右 Kan 拡張についても同様である。

Uを終対象への射として相対余極限と絶対余極限のiffを各輸送余錐に適用すると、kanIsRelativeLeftKanExtendedFrom\_iff\_refl\_extensionは原文の左側の恒等変換のKan性とのiffを直接与える。右側のiffは含まない。

:::

:::corollary "kerodon_7_3_2_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanExtension_unit_isIso, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanExtension_canonicalColimits_of_unit_isIso")
Kerodon Corollary 7.3.2.7（[Tag 02YV](https://kerodon.net/tag/02YV)）。対応表の状態：一部。

*主張*　無限圏の充満部分圏 $`C^0\subseteq C` と自然変換 $`\beta:F_0\to F|_{C^0}` に対し、$`\beta` が包含に沿う左 Kan 拡張を与えることは、$`F` が $`C^0` から左 Kan 拡張されていて $`\beta` が自然同型であることと同値である。

全部分圏の包含δについて、kanLeftKanExtension\_unit\_isIsoとcanonicalColimits\_of\_unit\_isIsoを順に用いると、左Kan拡張⇒単位β可逆かつFが左Kan extendedという同じβについての向きを直接得る。逆向きは引用に含まない。

:::

:::corollary "kerodon_7_3_2_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftExtension_iff_local_colimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftCanonical_strict_extension_of_local_colimits")
Kerodon Corollary 7.3.2.8（[Tag 02YW](https://kerodon.net/tag/02YW)）。対応表の状態：本体にある。

*主張*　無限圏の充満部分圏 $`C^0\subseteq C` 上の関手 $`F_0` が自然変換による左 Kan 拡張を持つことは、$`C^0` で厳密に $`F_0` に一致し、$`C^0` から左 Kan 拡張されている関手 $`F:C\to D` が存在することと同値である。

仮定：C⁰↪C は充満忠実な mono で inner fibration、各圏は quasicategory（原文の全部分圏の包含と一致）。結論：変換つき左 Kan 拡張の存在と各局所余極限を比較し、局所余極限から制限が F₀ に厳密に等しい標準左 Kan 拡張を構成する（原文の二つの存在に一致）。

:::

:::definition "kerodon_7_3_2_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftCanonical_strict_extension_of_local_colimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone")
Kerodon Definition 7.3.2.9（[Tag 02YX](https://kerodon.net/tag/02YX)）。対応表の状態：一部。

*主張*　無限圏の充満部分圏 $`C^0\subseteq C` の関手 $`F_0` の左 Kan 拡張とは、$`C^0` から左 Kan 拡張されており、制限が $`F_0` に等しい関手である。右 Kan 拡張も対応する右の条件で定める。

δ≫F=F₀という厳密延長に対し、leftKanCanonicalCocone δ F cの全cでの余極限性が原文の左Kan延長の定義部分を直接与える。右Kan延長の定義は含まない。別のGの存在だけを定義の証拠とはしない。

:::

:::proposition "kerodon_7_3_2_11" (uses := "kerodon_1_4_0_1, kerodon_7_3_1_5, kerodon_7_3_2_1")
Kerodon Proposition 7.3.2.11（[Tag 02YZ](https://kerodon.net/tag/02YZ)）。対応表の状態：なし。

relativeJoin上の局所余錐と指定βの左Kan性のiffはあるが、原文のF自身が全頂点でKから左Kan extendedであることと、この局所余錐条件を同定する型が引用にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeLeftKanExtension_relativeJoin_iff_local_relativeColimits`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanRelativeJoinRealization.Strictification.isLeftKanExtension_iff_local_colimits`

:::

:::corollary "kerodon_7_3_2_13"
Kerodon Corollary 7.3.2.13（[Tag 02Z1](https://kerodon.net/tag/02Z1)）。対応表の状態：なし。

exists\_relativeJoin\_local\_colimitsは端点と変換の類を保つ相対join表示を返すが、返す条件は局所余錐の余極限性。原文(1)の同じ全関手のleftKanExtendedFromという条件との比較を欠く。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension.exists_relativeJoin_local_colimits`

:::

:::corollary "kerodon_7_3_2_14"
Kerodon Corollary 7.3.2.14（[Tag 03U3](https://kerodon.net/tag/03U3)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：prism の持ち上げは cocartesian な輸送を作り、相対 Kan 判定は comma 形状の各局所余極限を調べる。Δ¹ の二ファイバー間で F(β) を与えた二つの左 Kan 条件の比較は見つからない。

:::

# 7.3.3 Relative Kan Extensions

%%%
number := false
tag := "kerodon-7-3-3"
%%%

Kerodon [Tag 02Z2](https://kerodon.net/tag/02Z2)

:::definition "kerodon_7_3_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtendedFrom, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtension")
Kerodon Definition 7.3.3.1（[Tag 02Z3](https://kerodon.net/tag/02Z3)）。対応表の状態：一部。

*主張*　無限圏の関手 $`F:C\to D`、$`U:D\to E` と充満部分圏 $`C^0\subseteq C` を取る。$`c` における $`U`-左 Kan 拡張性は $`C^0\times_C C_{/c}` の標準右錐の像が $`U`-余極限図式であることであり、$`U`-右 Kan 拡張性は $`C^0\times_C C_{c/}` の標準左錐の像が $`U`-極限図式であることである。全対象で成り立てば $`C^0` からの相対 Kan 拡張となる。

IsRelativeLeftKanExtendedFromの定義は全cについて同じleftKanCanonicalCoconeのIsRelativeColimitConeを要求し、原文のU-left Kan条件を直接表す。右Kan側の定義は含まない。

:::

:::proposition "kerodon_7_3_3_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonical_isColimit_at_image, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftTransport_image_isColimit_at_image, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_isColimit_of_terminal") (uses := "kerodon_1_4_0_1, kerodon_4_7_3_20, kerodon_7_2_3_6")
Kerodon Proposition 7.3.3.7（[Tag 02Z8](https://kerodon.net/tag/02Z8)）。対応表の状態：一部。

*主張*　無限圏の関手 $`F:C\to D` は、充満部分圏 $`C^0\subseteq C` の対象に同型な点では、任意の関手 $`U:D\to E` に関して $`C^0` から $`U`-左および $`U`-右 Kan 拡張されている。

Uを終対象への射、cを包含δの実際の像δkに限ると、kanLeftCanonical\_isColimit\_at\_imageと終対象上の相対余極限のiffは同じ標準余錐のU余極限性を直接与える。δはinnerかつ充満忠実。任意Uや像と同型な全cは含まない。

:::

:::proposition "kerodon_7_3_3_11" (uses := "kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_2_4, kerodon_6_2_2_6, kerodon_6_2_2_23, kerodon_6_2_2_24")
Kerodon Proposition 7.3.3.11（[Tag 039R](https://kerodon.net/tag/039R)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左 Kan 性の型は各 comma ファイバーの相対余極限との iff。充満余反射部分圏を仮定して右随伴が反転する辺、または余反射を表す辺の像の U-cocartesian 性と比較する型は見つからない。

:::

:::corollary "kerodon_7_3_3_12"
Kerodon Corollary 7.3.3.12（[Tag 039S](https://kerodon.net/tag/039S)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左 Kan の単位の可逆性を扱う。余反射の余単位や右随伴で同型となる辺を F が反転する条件との iff は見つからない。

:::

:::corollary "kerodon_7_3_3_13" (uses := "kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_7_3_3_11")
Kerodon Corollary 7.3.3.13（[Tag 043G](https://kerodon.net/tag/043G)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：値域の底 E が終対象となる制限の自明 Kan ファイブレーションの型を確認した。原文の始対象全体が張る始域側部分圏からの相対左 Kan 性と全辺の U-cocartesian 性との iff は見つからない。

:::

:::corollary "kerodon_7_3_3_14"
Kerodon Corollary 7.3.3.14（[Tag 05E0](https://kerodon.net/tag/05E0)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の始対象の点包含は左余終になる。任意の∞圏の始対象全体からの左 Kan 性、全辺の可逆性、定値図式との同型を比較する型は見つからない。

:::

:::proposition "kerodon_7_3_3_18"
Kerodon Proposition 7.3.3.18（[Tag 03U5](https://kerodon.net/tag/03U5)）。対応表の状態：なし。

引用は一つの相対余極限余錐の添字変更。原文は全cのcomma図式と二つの全部分圏の指定Kan条件のiffであり、そのcomma図式の同定は引用の型にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeColimitCone_iff_restrict_of_precompositionEquivalence`

:::

:::proposition "kerodon_7_3_3_21"
Kerodon Proposition 7.3.3.21（[Tag 02ZG](https://kerodon.net/tag/02ZG)）。対応表の状態：なし。

相対始頂点のpullback保存とそのHom比較は部品。原文のcubeのcosliceと全ての指定標準Kan余錐を比較する型がなく、同じFの結論は直接得られない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.KanRelativeInitialVertex.pullback_snd`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInitial_pinchedHom_pullback_trivialKanFibration`

:::

:::corollary "kerodon_7_3_3_22"
Kerodon Corollary 7.3.3.22（[Tag 02ZJ](https://kerodon.net/tag/02ZJ)）。対応表の状態：なし。

相対始頂点のpullback保存だけでは、原文のU-leftKan条件をV-leftKan条件へ移すための各comma余錐の比較がない。別のpullbackの普遍性は数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.KanRelativeInitialVertex.pullback_snd`

:::

:::corollary "kerodon_7_3_3_23"
Kerodon Corollary 7.3.3.23（[Tag 02ZK](https://kerodon.net/tag/02ZK)）。対応表の状態：なし。

相対始頂点のpullback補題は、原文のfiber中の同じFの標準Kan余錐と全空間の標準余錐との同定、およびcartesian性による逆向きを結論しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.KanRelativeInitialVertex.pullback_snd`

:::

# 7.3.4 Kan Extensions along Fibrations

%%%
number := false
tag := "kerodon-7-3-4"
%%%

Kerodon [Tag 02ZL](https://kerodon.net/tag/02ZL)

:::proposition "kerodon_7_3_4_1" (uses := "kerodon_1_4_0_1, kerodon_4_7_3_20, kerodon_4_7_3_22, kerodon_5_1_4_1, kerodon_7_2_2_7, kerodon_7_2_3_10")
Kerodon Proposition 7.3.4.1（[Tag 02ZM](https://kerodon.net/tag/02ZM)）。対応表の状態：なし。

fiberwiseHomの相対始境界とfiber余錐を比較する補題はあるが、原文の任意の指定βの左Kan性とそのfiberwise境界条件を同定する型が引用にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFiberCocone_isColimit_of_initialBoundary`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinColimitProjection_trivialKanFibration`

:::

:::corollary "kerodon_7_3_4_2"
Kerodon Corollary 7.3.4.2（[Tag 02ZN](https://kerodon.net/tag/02ZN)）。対応表の状態：なし。

全fiber余錐の余極限性から関手制限のInitialBoundaryLiftingは得られるが、原文のFがKからleftKanExtendedFromであるという点ごとの定義への比較は引用にない。境界充填という証明部品だけでは数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFiberCocone_isColimit_of_initialBoundary`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFunctor_initialBoundary_of_colimit_fibers`

:::

:::proposition "kerodon_7_3_4_3" (uses := "kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_7_2_2_3, kerodon_7_3_3_7, kerodon_7_3_4_1")
Kerodon Proposition 7.3.4.3（[Tag 02ZP](https://kerodon.net/tag/02ZP)）。対応表の状態：なし。

相対fiber余錐と相対始境界の両方向の部品は、原文の全FのU-leftKanExtendedFromという条件との比較を含まない。二つの異なる条件の補題があるだけではiffの一部としない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFiberCocone_relative_of_initialBoundary`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRelative_initialBoundary_of_relativeColimit`

:::

:::proposition "kerodon_7_3_4_4"
Kerodon Proposition 7.3.4.4（[Tag 02ZQ](https://kerodon.net/tag/02ZQ)）。対応表の状態：なし。

exists\_kanRelativeJoin\_diagram\_of\_pointwise\_colimitsは相対join上の図式と境界充填を返す。原文のδに沿う指定自然変換の左Kan拡張へ戻す比較がこの引用の型にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeJoin_diagram_of_colimits`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeJoin_diagram_of_pointwise_colimits`

:::

:::lemma_ "kerodon_7_3_4_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRestriction_preservesCartesianEdges, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeJoin_family_extension_of_colimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_isColimit_of_terminal")
Kerodon Lemma 7.3.4.5（[Tag 02ZR](https://kerodon.net/tag/02ZR)）。対応表の状態：一部。

*主張*　単体集合の余デカルトファイブレーション $`K\to C`、全頂点を含む $`C_0\subseteq C` とその引き戻し $`K_0`、無限圏の同型ファイブレーション $`U:D\to E` を取る。$`K\coprod_{K_0}(K_0\star_{C_0}C_0)` 上の $`E` に対する持ち上げが、$`C_0` にない各単体の始頂点 $`c` で $`K_c^{\triangleright}` 上の $`U`-余極限図式を与えるなら、$`K\star_C C` 上の指定の底写像に沿って延長できる。

C,Dを準圏、Uを終対象への射に限ると、fiberwiseHomの随伴で同じ押し出しからの指定F₀を族へ移し、exists\_kanRelativeJoin\_family\_extension\_of\_colimitsは元と同じF₀を保つ解を直接返す。相対余極限は終対象上では絶対余極限と同値。一般Uは含まない。

:::

:::lemma_ "kerodon_7_3_4_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeJoin_family_extension_of_colimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRelativeColimitRestriction_trivialKanFibration")
Kerodon Lemma 7.3.4.6（[Tag 02ZU](https://kerodon.net/tag/02ZU)）。対応表の状態：一部。

*主張*　単体集合の余デカルトファイブレーション $`K\to C` と無限圏の同型ファイブレーション $`U:D\to E` を取る。相対結合 $`K\star_C C\to E` の $`K` 上の持ち上げと、すべての頂点 $`c` でそれを延長する $`K_c^{\triangleright}` 上の $`U`-余極限図式が指定されれば、すべての指定を保つ全体の持ち上げが存在する。

Cを準圏に限り、全ての同じ型の持ち上げ問題について局所余錐があると強めると、relativeColimitRestrictionの頂点全射性は同じF₀,Gを保つ大域解の存在を返す。指定された各F\_Cとの厳密一致の結論は含まない。

:::

:::proposition "kerodon_7_3_4_7"
Kerodon Proposition 7.3.4.7（[Tag 02ZW](https://kerodon.net/tag/02ZW)）。対応表の状態：なし。

制限の頂点全射性は全fiber余錐が相対余極限な解を返すが、原文(1)のU-leftKanExtendedFromへの比較を引用に含まない。全局所解の存在という強化だけではその不足は埋まらない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRelativeColimitRestriction_trivialKanFibration`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRelativeColimitRestriction_surjective`

:::

:::corollary "kerodon_7_3_4_8"
Kerodon Corollary 7.3.4.8（[Tag 02ZY](https://kerodon.net/tag/02ZY)）。対応表の状態：なし。

返される図式の条件は関手制限の相対始境界充填であり、原文(1)のKからleftKanExtendedFromという指定条件ではない。その比較なしに存在の片方向とは数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeJoin_diagram_of_pointwise_colimits`

:::

# 7.3.5 Existence of Kan Extensions

%%%
number := false
tag := "kerodon-7-3-5"
%%%

Kerodon [Tag 02ZZ](https://kerodon.net/tag/02ZZ)

:::proposition "kerodon_7_3_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftExtension_iff_local_colimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRightExtension_iff_local_limits") (uses := "kerodon_1_4_0_1, kerodon_4_1_3_1, kerodon_4_1_3_3, kerodon_5_6_7_6, kerodon_7_2_1_13, kerodon_7_2_2_9, kerodon_7_3_1_14, kerodon_7_3_2_11, kerodon_7_3_5_8")
Kerodon Proposition 7.3.5.1（[Tag 0300](https://kerodon.net/tag/0300)）。対応表の状態：一部。

*主張*　無限圏 $`C,D` と図式 $`\delta:K\to C,F_0:K\to D` に対し、$`F_0` が $`\delta` に沿う左 Kan 拡張を持つことは、各 $`c` で $`K_{/c}` に制限した図式が余極限を持つことと同値である。右 Kan 拡張の存在は、全ての $`K_{c/}` 上の制限に極限があることと同値である。

Kも準圏に強めれば左右それぞれのexists\_kanLeft/RightExtension\_iff\_local\_colimits/limitsは同じδ,F₀について原文の二つのiffを直接返す。任意の単体集合Kは含まない。

:::

:::corollary "kerodon_7_3_5_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftExtension_of_local_colimits")
Kerodon Corollary 7.3.5.2（[Tag 0301](https://kerodon.net/tag/0301)）。対応表の状態：一部。

*主張*　無限圏 $`C,D` と図式 $`\delta:K\to C` に対し、各 $`c` で $`D` が $`K\times_C C_{/c}` 添字の余極限を持つなら、任意の $`K\to D` は $`\delta` に沿う左 Kan 拡張を持つ。

Kを準圏に強めると、全ての形状の余極限存在を各leftKanDiagramに適用しexists\_kanLeftExtension\_of\_local\_colimitsから同じF₀の拡張を直接得る。

:::

:::corollary "kerodon_7_3_5_3"
Kerodon Corollary 7.3.5.3（[Tag 039T](https://kerodon.net/tag/039T)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：任意の δ に対する相対 Kan 性は comma の各ファイバーの相対余極限と比較できる。原文の G(C) とその lax holim 射影のファイバーを結び、左 Kan 拡張の存在と各 G(C) 上の余極限を比較する型は見つからない。

:::

:::proposition "kerodon_7_3_5_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeLeftCanonical_strict_extension_of_local_relative_colimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanGlobalRelative_diagram_with_relative_colimits_of_isofibration")
Kerodon Proposition 7.3.5.5（[Tag 0302](https://kerodon.net/tag/0302)）。対応表の状態：本体にある。

*主張*　無限圏の充満部分圏 $`C^0\subseteq C`、同型ファイブレーション $`U:D\to E`、$`G:C\to E` と $`G|_{C^0}` の持ち上げ $`F_0` を取る。$`C^0` から $`U`-左 Kan 拡張された全体の持ち上げが存在することは、各 $`c` の $`(C^0\times_C C_{/c})^{\triangleright}` 上で誘導される持ち上げ問題が $`U`-余極限図式を解に持つことと同値である。

仮定：全部分圏の包含、U の EquivalenceLifting、可換四角形。局所標準余錐の相対余極限による持ち上げを各頂点で仮定する（Kerodon と一致）。結論：両側の等式を保つ厳密な延長 G が存在し、U-relative left Kan extended from となる（原文と一致）。

:::

:::corollary "kerodon_7_3_5_7" (uses := "kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_7_1_5_21, kerodon_7_1_8_10")
Kerodon Corollary 7.3.5.7（[Tag 043J](https://kerodon.net/tag/043J)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：各頂点での相対始性を関手空間の境界充填につなぐ補題はある。cartesian fibration の全ファイバーの始対象から切断を構成し、その始性との iff を得る型は見つからない。

:::

:::corollary "kerodon_7_3_5_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftCanonical_strict_extension_of_local_colimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftExtension_iff_local_colimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRightExtension_iff_local_limits") (uses := "kerodon_1_4_0_1, kerodon_7_3_5_5")
Kerodon Corollary 7.3.5.8（[Tag 0307](https://kerodon.net/tag/0307)）。対応表の状態：本体にある。

*主張*　無限圏の充満部分圏 $`C^0\subseteq C` の関手 $`F_0:C^0\to D` が左 Kan 拡張を持つことは、各 $`c\in C` で $`C^0\times_C C_{/c}` による $`F_0` の図式に余極限があることと同値である。右 Kan 拡張は $`C^0\times_C C_{c/}` による図式に極限があることと同値である。

全部分圏の始域は準圏なので、左右のexists\_kanExtension\_iff\_local\_colimits/limitsを同じ包含δ,F₀へ適用すると原文の二つのiffを直接得る。右側の既存定理を追記し、専用の一宣言の不足はpartial理由にしない。

:::

:::corollary "kerodon_7_3_5_9" (uses := "kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_7_2_2_14, kerodon_7_3_5_5")
Kerodon Corollary 7.3.5.9（[Tag 047U](https://kerodon.net/tag/047U)）。対応表の状態：なし。

comma全局所相対余錐の存在から延長を作る型はあるが、原文(2)は余反射の各辺のcocartesian liftだけの条件。その条件を全局所余錐へ変換する型が引用にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeLeftCanonical_strict_extension_of_comma_colimits`

:::

:::corollary "kerodon_7_3_5_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeLeftCanonical_strict_extension_of_comma_colimits") (uses := "kerodon_1_4_0_1, kerodon_5_1_4_1")
Kerodon Corollary 7.3.5.10（[Tag 039V](https://kerodon.net/tag/039V)）。対応表の状態：一部。

*主張*　無限圏の余反射的充満部分圏 $`C^0\subseteq C` と余デカルトファイブレーション $`U:D\to E` に対し、$`C\to E` の $`C^0` 上の任意の持ち上げは、$`C^0` から $`U`-左 Kan 拡張された関手に延長できる。

同じF₀,Gの全comma余錐に指定された相対余極限が存在することも加えると、exists\_kanRelativeLeftCanonical\_strict\_extension\_of\_comma\_colimitsは同じ持ち上げ問題のU-leftKan解を直接返す。始域の余反射性や始対象だけからその入力を得たとはしない。

:::

:::corollary "kerodon_7_3_5_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeLeftCanonical_strict_extension_of_comma_colimits") (uses := "kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_7_3_5_10")
Kerodon Corollary 7.3.5.11（[Tag 043K](https://kerodon.net/tag/043K)）。対応表の状態：一部。

*主張*　始対象を持つ無限圏 $`C` と余デカルトファイブレーション $`U:D\to E` に対し、$`C\to E` の始対象の充満部分圏上の持ち上げは、その部分圏から $`U`-左 Kan 拡張された全体の持ち上げに延長できる。

同じF₀,Gの全comma余錐に指定された相対余極限が存在することも加えると、exists\_kanRelativeLeftCanonical\_strict\_extension\_of\_comma\_colimitsは同じ持ち上げ問題のU-leftKan解を直接返す。始域の余反射性や始対象だけからその入力を得たとはしない。

:::

# 7.3.6 The Universal Property of Kan Extensions

%%%
number := false
tag := "kerodon-7-3-6"
%%%

Kerodon [Tag 0308](https://kerodon.net/tag/0308)

:::proposition "kerodon_7_3_6_1" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_1_5_6_7, kerodon_1_5_7_6, kerodon_4_1_3_3, kerodon_4_6_8_1, kerodon_5_2_3_15, kerodon_6_2_5_1, kerodon_7_3_2_11, kerodon_7_3_3_7, kerodon_7_3_6_9")
Kerodon Proposition 7.3.6.1（[Tag 0309](https://kerodon.net/tag/0309)）。対応表の状態：なし。

LeftKanHomUniversalはh FunのHom集合の全単射。原文の同じ合成写像のKan複体としてのホモトピー同値までは型にない。π₀の結果は写像空間の同値という結論の成分と数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanExtension_homUniversal`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanHomUniversal`

:::

:::corollary "kerodon_7_3_6_3" (uses := "kerodon_1_4_0_1, kerodon_6_2_6_1, kerodon_7_3_6_1")
Kerodon Corollary 7.3.6.3（[Tag 030B](https://kerodon.net/tag/030B)）。対応表の状態：なし。

MathlibのlanAdjunctionは通常の関手圏の随伴。原文のFun準圏間の指定制限関手の随伴へのnerve比較が引用にない。

宣言：`CategoryTheory.Functor.lanAdjunction`、`CategoryTheory.Functor.lanUnit`

:::

:::corollary "kerodon_7_3_6_4" (lean := "CategoryTheory.Functor.lanAdjunction, CategoryTheory.Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftExtension_with_homUniversal_of_local_colimits")
Kerodon Corollary 7.3.6.4（[Tag 030C](https://kerodon.net/tag/030C)）。対応表の状態：一部。

*主張*　無限圏 $`C,D` と単体図式 $`\delta:K\to C` に対し、$`D` が全ての $`c\in C` について $`K\times_C C_{/c}` 添字の余極限を持つとする。制限 $`\operatorname{Fun}(C,D)\to\operatorname{Fun}(K,D)` は左随伴を持ち、それは図式を $`\delta` に沿う左 Kan 拡張に送る。

Kを準圏に強めればexists\_kanLeftExtension\_with\_homUniversal\_of\_local\_colimitsは全F₀について同じδに沿う左Kan拡張の存在を直接返す。原文の左随伴の構成およびその単位との同定は含まない。

:::

:::corollary "kerodon_7_3_6_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanExtensionHom_homUniversal, SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.kanClassical_isLeftKanExtension_iff_bijective") (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_7_3_6_1")
Kerodon Corollary 7.3.6.5（[Tag 030D](https://kerodon.net/tag/030D)）。対応表の状態：一部。

*主張*　$`F_0:K\to D` が $`\delta:K\to C` に沿う左 Kan 拡張を持つと仮定する。自然変換 $`\beta:F_0\to F\delta` が $`F` を左 Kan 拡張として示すことは、任意の $`G:C\to D` に対し、制限と $`\beta` との合成で得る $`\operatorname{Hom}(F,G)\to\operatorname{Hom}(F_0,G\delta)` がホモトピー同値となることと同値である。ホモトピー圏の Hom 集合で全単射となることとも同値である。

Kを準圏に強めるとkanLeftKanExtensionHom\_homUniversalは同じβについて原文(1)⇒(3)のh Fun上のHom全単射を直接返す。写像空間同値(2)や逆向きは含まない。

:::

:::proposition "kerodon_7_3_6_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftMappingPullbackComparison_equivalence, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeRightMappingPullbackComparison_equivalence")
Kerodon Proposition 7.3.6.7（[Tag 030F](https://kerodon.net/tag/030F)）。対応表の状態：本体にある。

*主張*　無限圏の関手 $`U:D\to E` と $`F,G:C\to D`、充満部分圏 $`C^0\subseteq C` を取る。$`F` が $`U`-左 Kan 拡張されているか $`G` が $`U`-右 Kan 拡張されていれば、射空間 $`\operatorname{Hom}(F,G)` と $`\operatorname{Hom}(UF,UG)` をそれぞれ $`C^0` に制限する正方形はホモトピー引き戻しである。

仮定：quasicategory の全部分圏の包含を mono・inner fibration・充満忠実として取る。F の相対左 Kan 性または G の相対右 Kan 性（Kerodon と一致）。結論：指定された写像空間の引き戻しへの比較が IsSimplicialHomotopyEquivalence（原文と一致）。

:::

:::corollary "kerodon_7_3_6_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonical_pinchedHomMap_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCanonical_pinchedHomMap_trivialKanFibration")
Kerodon Corollary 7.3.6.9（[Tag 030M](https://kerodon.net/tag/030M)）。対応表の状態：本体にある。

*主張*　無限圏の関手 $`F,G:C\to D` の少なくとも一方について、$`F` が充満部分圏 $`C^0` から左 Kan 拡張されているか $`G` が右 Kan 拡張されているなら、射空間 $`\operatorname{Hom}(F,G)` の $`C^0` への制限は自明な Kan ファイブレーションである。

仮定：quasicategory の全部分圏の包含を mono とし、F の各左標準余錐が余極限、または G の各右標準錐が極限（Kerodon と一致）。結論：前合成 δ が誘導する指定 pinched Hom 間の写像が TrivialKanFibration（使用する Hom の模型で一致）。

:::

:::corollary "kerodon_7_3_6_10" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_7_3_14, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_7_3_3_13, kerodon_7_3_6_7")
Kerodon Corollary 7.3.6.10（[Tag 043M](https://kerodon.net/tag/043M)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対左 Kan 性を入力にした写像空間の比較はある。始対象への評価で、F が全辺を cocartesian に送ることから直接 Hom の同値を得る型は見つからない。

:::

:::corollary "kerodon_7_3_6_11" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_7_3_3_13, kerodon_7_3_5_11, kerodon_7_3_6_10")
Kerodon Corollary 7.3.6.11（[Tag 043N](https://kerodon.net/tag/043N)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対写像空間の比較と cocartesian な prism の構成はある。始点のファイバーの始対象を使って切断の始対象を構成し、F の全辺と始点像の条件で始性を特徴付ける型は見つからない。

:::

:::corollary "kerodon_7_3_6_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftMappingPullbackComparison_equivalence") (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_7_1_5_12, kerodon_7_3_6_7")
Kerodon Corollary 7.3.6.12（[Tag 030N](https://kerodon.net/tag/030N)）。対応表の状態：一部。

*主張*　充満部分圏 $`C^0\subseteq C` 上で指定された持ち上げに延長 $`F:C\to D` を求める無限圏の持ち上げ問題で、$`U:D\to E` に関する左 Kan 拡張を与える解が一つ存在するとする。任意の解 $`F` がそのような拡張であることは、任意の $`G:C\to D` に対し $`\operatorname{Hom}(F,G)` と $`\operatorname{Hom}(UF,UG)` を $`C^0` に制限する正方形がホモトピー引き戻しであることと同値である。

全部分圏の包含に対しkanRelativeLeftMappingPullbackComparison\_equivalenceは、同じU,F,Gと制限について(1)からホモトピー引き戻しへの比較同値(2)を直接返す。逆向きは含まない。

:::

:::corollary "kerodon_7_3_6_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonical_pinchedHomMap_trivialKanFibration") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_3_7_6, kerodon_4_1_4_2, kerodon_4_6_1_22, kerodon_7_3_6_12")
Kerodon Corollary 7.3.6.13（[Tag 030Q](https://kerodon.net/tag/030Q)）。対応表の状態：一部。

*主張*　無限圏の関手 $`F:C\to D` の充満部分圏 $`C^0` への制限が左 Kan 拡張を持つとする。$`F` 自身が $`C^0` から左 Kan 拡張されていることは、全ての $`G:C\to D` に対する射空間 $`\operatorname{Hom}(F,G)` の制限がホモトピー同値であること、または自明な Kan ファイブレーションであることと同値である。

kanLeftCanonical\_pinchedHomMap\_trivialKanFibrationは原文(1)⇒(3)を同じF,Gの制限のpinched Homモデルで直接返す。(1)⇒(2)も自然なpinched/interval比較で得るが、その比較だけで別モデルの厳密Kanファイブレーション性を主張しない。全逆向きは含まない。

:::

:::theorem "kerodon_7_3_6_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction_isFullyFaithful, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeRightKanRestriction_trivialKanFibration") (uses := "kerodon_1_4_0_1, kerodon_4_4_5_1, kerodon_7_1_5_18, kerodon_7_3_5_5, kerodon_7_3_6_7")
Kerodon Theorem 7.3.6.14（[Tag 030R](https://kerodon.net/tag/030R)）。対応表の状態：一部。

*主張*　無限圏の同型ファイブレーション $`U:D\to E` と充満部分圏 $`C^0\subseteq C` を取る。$`C^0` から $`U`-左 Kan 拡張された関手の充満部分圏から、各 $`c` の $`(C^0\times_C C_{/c})^{\triangleright}` 上で $`U`-余極限の持ち上げがあるデータの充満部分圏への相対制限は、自明な Kan ファイブレーションである。

全てのF₀,H₀の局所相対余錐があると強めれば、Bは全pullbackとなりkanRelativeLeftKanRestriction\_trivialKanFibrationが同じ制限Vを返す。任意の真の充満部分圏Bの場合は含まない。

:::

:::corollary "kerodon_7_3_6_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction_terminal_trivialKanFibration") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_3_6_14")
Kerodon Corollary 7.3.6.15（[Tag 030S](https://kerodon.net/tag/030S)）。対応表の状態：一部。

*主張*　無限圏の充満部分圏 $`C^0\subseteq C` から左 Kan 拡張される関手の充満部分圏を $`C^0` に制限する。任意の $`c` について $`C^0\times_C C_{/c}` 上に余極限を持つ関手の充満部分圏への、この制限は自明な Kan ファイブレーションである。

全F₀,cで局所余極限があると強めればFun′(C⁰,D)は全関手圏となり、terminal版の制限のtrivialKanFibrationは同じ左Kan関手の制限の結論を直接与える。任意の真の部分圏への制限は含まない。

:::

# 7.3.7 Kan Extensions in Functor ∞-Categories

%%%
number := false
tag := "kerodon-7-3-7"
%%%

Kerodon [Tag 047V](https://kerodon.net/tag/047V)

:::theorem "kerodon_7_3_7_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeLeftKanExtendedFrom_constantFamily") (uses := "kerodon_1_4_0_1, kerodon_7_3_7_13")
Kerodon Theorem 7.3.7.1（[Tag 047W](https://kerodon.net/tag/047W)）。対応表の状態：一部。

*主張*　無限圏の指数化可能な内部ファイブレーション $`C\to B` と関手 $`V:D\to E` を取る。$`f:A\to\operatorname{Fun}(C/B,D)` に対応する $`F:A\times_B C\to D` が $`A^0\times_B C` から $`V`-左 Kan 拡張されていれば、$`f` は $`A^0` から $`V` の後合成に関して左 Kan 拡張されている。

Bを一点、FをC因子に依らない定値族に限りVをinner fibrationに強めると、kanIsRelativeLeftKanExtendedFrom\_constantFamilyは同じ転置fのV′-leftKan条件を直接返す。一般の相対関手圏は含まない。

:::

:::corollary "kerodon_7_3_7_3"
Kerodon Corollary 7.3.7.3（[Tag 047Y](https://kerodon.net/tag/047Y)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：relativeFunctorSpace は底上の固定図式の空間。相対左 Kan 性と comma ファイバーの相対余極限の比較もある。可変ファイバーを持つ Fun(C/B,D) の射影について、引き戻し上の非相対左 Kan 性を移す型は見つからない。

:::

:::corollary "kerodon_7_3_7_4"
Kerodon Corollary 7.3.7.4（[Tag 047Z](https://kerodon.net/tag/047Z)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対左 Kan 図式から関手圏内の定値パラメータ族を作って相対左 Kan 性を保つ。A×C 上の任意の図式の左 Kan 性を仮定し curry に渡す型は見つからない。

:::

:::corollary "kerodon_7_3_7_5"
Kerodon Corollary 7.3.7.5（[Tag 0480](https://kerodon.net/tag/0480)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：内部 Hom への定値族は扱う。一般の F:A×C→D を A⁰×C から左 Kan 拡張する条件で、その curry が A⁰ から左 Kan 拡張となる型は見つからない。

:::

:::corollary "kerodon_7_3_7_6" (uses := "kerodon_1_4_0_1, kerodon_4_5_8_18, kerodon_7_3_7_1")
Kerodon Corollary 7.3.7.6（[Tag 0481](https://kerodon.net/tag/0481)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対 join に含めた特定の底辺の cocartesian 性はある。Δ¹×\_B C 上の V-左 Kan 性から関手圏の後合成 V′ に関する辺の cocartesian 性を得る型は見つからない。

:::

:::corollary "kerodon_7_3_7_9" (uses := "kerodon_1_4_0_1, kerodon_7_3_7_6")
Kerodon Corollary 7.3.7.9（[Tag 0484](https://kerodon.net/tag/0484)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対 join の底射影に関する cocartesian fibration はある。Fun(C/B,D)→B の指定辺を、左端ファイバーからの左 Kan 性で判定する型は見つからない。

:::

:::lemma_ "kerodon_7_3_7_10" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_5_1, kerodon_4_5_3_34, kerodon_4_5_6_20, kerodon_7_1_7_1")
Kerodon Lemma 7.3.7.10（[Tag 0485](https://kerodon.net/tag/0485)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：全余錐族の相対始性と指定余錐の相対余極限性の iff を確認した。全 A と底への拡張を量化した join 制限の同値性から、指定充満部分圏の全対象を判定する型は見つからない。

:::

:::proposition "kerodon_7_3_7_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_functor_of_pointwise, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeColimitCone_constantFamily") (uses := "kerodon_1_4_0_1, kerodon_4_5_8_18, kerodon_7_3_5_5, kerodon_7_3_6_14, kerodon_7_3_7_10")
Kerodon Proposition 7.3.7.13（[Tag 0488](https://kerodon.net/tag/0488)）。対応表の状態：一部。

*主張*　無限圏の指数化可能な内部ファイブレーション $`C\to B`、関手 $`V:D\to E`、無限圏 $`K` を取る。$`f:K^{\triangleright}\to\operatorname{Fun}(C/B,D)` に対応する $`K^{\triangleright}\times_B C\to D` が $`K\times_B C` から $`V`-左 Kan 拡張されているなら、$`f` は $`V` による後合成に関して余極限図式である。

Bを一点、Vをinner fibrationとし、仮定を各aの指定余錐がV余極限であることにも強めると、kanIsRelativeColimitCone\_functor\_of\_pointwiseは同じ転置fのV′余極限性を直接返す。元のleftKan仮定だけから点ごとの条件を得たとはしない。

:::

# 7.3.8 Transitivity of Kan Extensions

%%%
number := false
tag := "kerodon-7-3-8"
%%%

Kerodon [Tag 030U](https://kerodon.net/tag/030U)

:::proposition "kerodon_7_3_8_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.isColimitCone_iff_restrict_of_poset_nested_canonical, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonical_pre_initialBoundary, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.isColimitCone_iff_restrict_of_initialBoundary, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.hasColimit_iff_leftKanExtension, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_isColimit_of_terminal") (uses := "kerodon_1_4_0_1, kerodon_3_4_1_11, kerodon_3_4_1_13, kerodon_7_1_6_19, kerodon_7_3_6_7, kerodon_7_3_6_9")
Kerodon Proposition 7.3.8.1（[Tag 030V](https://kerodon.net/tag/030V)）。対応表の状態：一部。

*主張*　無限圏の右錐 $`\bar F:C^{\triangleright}\to D` の $`C` への制限が充満部分圏 $`C^0` から $`U:D\to E` に関して左 Kan 拡張されているとする。$`\bar F` が $`U`-余極限図式であることは、$`(C^0)^{\triangleright}` への制限がそうであることと同値である。

Uを終対象への射に限れば相対余極限は絶対余極限。同じFの標準左Kan余錐からkanLeftCanonical\_pre\_initialBoundaryを得てisColimitCone\_iff\_restrict\_of\_initialBoundaryへ渡すと、原文の指定余錐の制限とのiffを直接得る。U=idはこの特殊化ではない。

:::

:::corollary "kerodon_7_3_8_2"
Kerodon Corollary 7.3.8.2（[Tag 06AX](https://kerodon.net/tag/06AX)）。対応表の状態：なし。

colimitConstInitialは通常圏で一つの選択済み定値図式の余極限対象の同型。原文の指定された任意の余錐についての相対余極限性のiffと比較する型がない。

宣言：`CategoryTheory.Limits.colimitConstInitial`

:::

:::corollary "kerodon_7_3_8_3" (lean := "CategoryTheory.Functor.isColimitCoconeOfIsLeftKanExtension, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonical_pre_initialBoundary, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.isColimitCone_iff_restrict_of_initialBoundary") (uses := "kerodon_1_4_0_1, kerodon_7_3_8_1")
Kerodon Corollary 7.3.8.3（[Tag 030Y](https://kerodon.net/tag/030Y)）。対応表の状態：本体にある。

*主張*　無限圏の図式 $`F:C\to D` が充満部分圏 $`C^0` から左 Kan 拡張されているなら、$`F` の右錐が余極限図式であることは、その $`(C^0)^{\triangleright}` への制限が余極限図式であることと同値である。

全部分圏の包含と同じFにkanLeftCanonical\_pre\_initialBoundaryを適用し、isColimitCone\_iff\_restrict\_of\_initialBoundaryへ渡せば、原文の指定余錐とその制限の余極限性のiffを直接得る。通常圏の類似だけでなく同じ∞圏の二宣言を追記した。

:::

:::corollary "kerodon_7_3_8_4" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_1_5_6_7, kerodon_1_5_7_5, kerodon_4_1_3_3, kerodon_7_2_1_19, kerodon_7_2_2_2, kerodon_7_3_4_3, kerodon_7_3_8_1")
Kerodon Corollary 7.3.8.4（[Tag 06AY](https://kerodon.net/tag/06AY)）。対応表の状態：なし。

MathlibのFubiniは通常圏の構成済み積余錐。原文の指定二重joinの同じFおよびU相対余極限性との比較がない。

宣言：`CategoryTheory.Limits.isColimitCoconeOfHasColimitCurryCompColim`

:::

:::definition "kerodon_7_3_8_5" (uses := "kerodon_7_3_8_4")
Kerodon Variant 7.3.8.5（[Tag 06AZ](https://kerodon.net/tag/06AZ)）。対応表の状態：なし。

通常圏の反復余極限の構成は、原文の指定Fにおける三つのjoin余錐の相対余極限性のiffを結論しない。

宣言：`CategoryTheory.Limits.isColimitCoconeOfHasColimitCurryCompColim`

:::

:::corollary "kerodon_7_3_8_6" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_1_8_13, kerodon_7_3_8_5")
Kerodon Corollary 7.3.8.6（[Tag 06B0](https://kerodon.net/tag/06B0)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対余極限余錐を定値パラメータ族に写す型はある。相対余極限図式を頂点に持つ任意の族の levelwise U-余極限での閉性は見つからない。

:::

:::corollary "kerodon_7_3_8_7"
Kerodon Corollary 7.3.8.7（[Tag 06TJ](https://kerodon.net/tag/06TJ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：準圏の一般の極限性と n-truncation 関連の用語を別々に検索した。全写像空間の n-truncation で定義した対象のクラスが任意の極限に閉じる型は見つからない。

:::

:::corollary "kerodon_7_3_8_8" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_3_8_6")
Kerodon Corollary 7.3.8.8（[Tag 06B1](https://kerodon.net/tag/06B1)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：関手圏の点ごとの余極限判定と通常圏の積図式の余極限構成はある。各項目が余極限図式である族の、点ごとの余極限も余極限図式となる型は見つからない。

:::

:::proposition "kerodon_7_3_8_9"
Kerodon Proposition 7.3.8.9（[Tag 030Z](https://kerodon.net/tag/030Z)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：点ごとの comma 余錐に相対余極限性を課す形はある。右ファイブレーションで引き戻した部分圏に対し b と V(b) の条件を比較する型は見つからない。

:::

:::corollary "kerodon_7_3_8_10" (uses := "kerodon_1_4_0_1")
Kerodon Corollary 7.3.8.10（[Tag 0310](https://kerodon.net/tag/0310)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：全点での条件は comma ファイバーの相対余極限性で特徴付ける。右ファイブレーションに沿う保存と、各ファイバー非空による反映は見つからない。

:::

:::corollary "kerodon_7_3_8_11"
Kerodon Corollary 7.3.8.11（[Tag 0311](https://kerodon.net/tag/0311)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左 Kan 拡張の述語と通常圏の同値による添字変更はある。右ファイブレーションに沿う絶対左 Kan 性の保存と非空ファイバーによる反映は見つからない。

:::

:::proposition "kerodon_7_3_8_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.posetSubtype_canonicalColimit_nested") (uses := "kerodon_1_4_0_1, kerodon_7_3_8_1, kerodon_7_3_8_10")
Kerodon Proposition 7.3.8.12（[Tag 0312](https://kerodon.net/tag/0312)）。対応表の状態：一部。

*主張*　無限圏の充満部分圏の列 $`C^0\subseteq C\subseteq\bar C` について、$`\bar F:\bar C\to D` が $`U:D\to E` に関して $`C^0` から左 Kan 拡張されていることは、$`\bar F` が $`C` から、$`\bar F|_C` が $`C^0` から、それぞれ $`U`-左 Kan 拡張されていることと同値である。

Uを終対象への射、Cの塔を半順序集合の充満部分nerveに限ると、posetSubtype\_canonicalColimit\_nestedは原文の左辺⇒(2)を同じ制限関手について直接返す。(1)および逆向きは含まない。

:::

:::corollary "kerodon_7_3_8_14" (lean := "CategoryTheory.Functor.isLeftKanExtension_iff_postcompose, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.posetSubtype_canonicalColimit_nested") (uses := "kerodon_1_4_0_1, kerodon_7_3_8_12")
Kerodon Corollary 7.3.8.14（[Tag 0314](https://kerodon.net/tag/0314)）。対応表の状態：一部。

*主張*　無限圏の充満部分圏の列 $`C^0\subseteq C\subseteq\bar C` に対して、$`\bar F:\bar C\to D` が $`C^0` から左 Kan 拡張されていることは、$`\bar F` が $`C` から、$`\bar F|_C` が $`C^0` から左 Kan 拡張されていることと同値である。

半順序集合のnerveとその充満部分圏の塔に限ればposetSubtype\_canonicalColimit\_nestedは同じFの左辺⇒(2)を直接返す。通常圏のisLeftKanExtension\_iff\_postcomposeだけは根拠としない。

:::

:::corollary "kerodon_7_3_8_15"
Kerodon Corollary 7.3.8.15（[Tag 0315](https://kerodon.net/tag/0315)）。対応表の状態：なし。

isPointwiseLeftKanExtensionAtOfIso′は通常圏の点ごとのKan条件の輸送。原文の∞圏の同じ標準相対余錐への比較がなく、類似の輸送だけでは数えない。

宣言：`CategoryTheory.Functor.LeftExtension.isPointwiseLeftKanExtensionAtOfIso'`

:::

:::proposition "kerodon_7_3_8_16" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.sliceUnderRestrict_isQCatEquivalence_of_initialBoundary, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonical_pre_initialBoundary, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_isColimit_of_terminal, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.isColimitCone_iff_restrict_of_initialBoundary")
Kerodon Proposition 7.3.8.16（[Tag 0316](https://kerodon.net/tag/0316)）。対応表の状態：一部。

*主張*　無限圏の関手 $`F:C\to D` が充満部分圏 $`C^0` から $`U:D\to E` に関して左 Kan 拡張され、$`F_0=F|_{C^0}` とする。このとき余スライスの相対制限 $`D_{F/}\to D_{F_0/}\times_{E_{UF_0/}}E_{UF/}` は同値である。

Uを終対象への射に限れば、同じFのkanLeftCanonical\_pre\_initialBoundaryとsliceUnderRestrict\_isQCatEquivalence\_of\_initialBoundaryは原文のθの絶対coslice制限の同値を直接返す。一般Uの相対pullbackは含まない。U=idとはしない。

:::

:::corollary "kerodon_7_3_8_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeCosliceMap_trivialKanFibration_of_precompositionEquivalence")
Kerodon Corollary 7.3.8.17（[Tag 0319](https://kerodon.net/tag/0319)）。対応表の状態：一部。

*主張*　無限圏の内部ファイブレーション $`U:D\to E` に関して $`F:C\to D` が充満部分圏 $`C^0` から左 Kan 拡張され、$`F_0=F|_{C^0}` とする。余スライスの相対制限 $`D_{F/}\to D_{F_0/}\times_{E_{UF_0/}}E_{UF/}` は自明な Kan ファイブレーションである。

UをEquivalenceLifting、包含C⁰→CをIsPrecompositionEquivalenceにも強めれば、kanRelativeCosliceMap\_trivialKanFibration\_of\_precompositionEquivalenceは原文と同じ相対coslice制限θのtrivialKanFibrationを直接返す。Fの相対Kan性だけの場合は含まない。

:::

:::corollary "kerodon_7_3_8_18" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeCosliceMap_trivialKanFibration_of_precompositionEquivalence, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonical_pinchedHomMap_trivialKanFibration")
Kerodon Corollary 7.3.8.18（[Tag 031A](https://kerodon.net/tag/031A)）。対応表の状態：一部。

*主張*　無限圏の関手 $`F:C\to D` が充満部分圏 $`C^0` から左 Kan 拡張されているなら、$`F_0=F|_{C^0}` とおくと余スライスの制限 $`D_{F/}\to D_{F_0/}` は自明な Kan ファイブレーションである。

包含C⁰→CをIsPrecompositionEquivalenceにも強め、Uを終対象への射として相対coslice補題を用いれば、同じ絶対coslice制限θのtrivialKanFibrationを直接得る。個別のpinchedHomMapの結果だけは全cosliceの代用にしない。

:::

:::corollary "kerodon_7_3_8_19"
Kerodon Corollary 7.3.8.19（[Tag 031B](https://kerodon.net/tag/031B)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：既存 U-余極限余錐の充填性と、各 comma 余錐からの厳密相対左 Kan 拡張の存在はある。相対左 Kan 性を持つ F の指定底余錐を持ち上げる存在を部分圏で判定する iff は見つからない。

:::

:::corollary "kerodon_7_3_8_20" (lean := "CategoryTheory.Functor.isColimitCoconeOfIsLeftKanExtension, CategoryTheory.Functor.colimitIsoOfIsLeftKanExtension, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.hasColimit_iff_leftKanExtension, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeLeftKanExtendedFrom_iff_refl_extension, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_isColimit_of_terminal")
Kerodon Corollary 7.3.8.20（[Tag 031E](https://kerodon.net/tag/031E)）。対応表の状態：本体にある。

*主張*　無限圏の関手 $`F:C\to D` が充満部分圏 $`C^0` から左 Kan 拡張されているなら、$`F` に $`D` で余極限があることと、$`F|_{C^0}` に $`D` で余極限があることは同値である。

恒等変換のleftKan性は標準余錐の定値輸送で得られるので、hasColimit\_iff\_leftKanExtensionを同じ包含とFに適用すれば原文の存在のiffを直接得る。通常圏の類似に加えてこの準圏の根拠を追記した。

:::

:::proposition "kerodon_7_3_8_22"
Kerodon Proposition 7.3.8.22（[Tag 031F](https://kerodon.net/tag/031F)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：各局所相対余極限からの一段の厳密延長と、通常圏の指定単位に沿う左 Kan 性の推移性はある。既存の F を与えた isofibration の二つの持ち上げ問題の解の存在を比較する型は見つからない。

:::

:::corollary "kerodon_7_3_8_23"
Kerodon Corollary 7.3.8.23（[Tag 031L](https://kerodon.net/tag/031L)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏で二段の指定済み変換の左 Kan 性を比較する。∞圏の F と制限からの拡張の存在の iff としての推移性は見つからない。

:::

:::proposition "kerodon_7_3_8_24" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.isColimitCone_iff_restrict_of_initialBoundary, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonical_pre_initialBoundary") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_6_2, kerodon_5_1_4_1, kerodon_5_1_4_20, kerodon_5_2_3_17, kerodon_5_3_6_1, kerodon_7_2_2_3, kerodon_7_2_3_10, kerodon_7_3_1_10, kerodon_7_3_2_11, kerodon_7_3_8_14")
Kerodon Proposition 7.3.8.24（[Tag 031M](https://kerodon.net/tag/031M)）。対応表の状態：一部。

*主張*　無限圏の関手 $`G:C_0\to C_1`、$`H:C_1\to C_2` と $`F_i:C_i\to D` の間の変換 $`\alpha:F_0\to F_1G,\beta:F_1\to F_2H` を取る。$`\alpha` が左 Kan 拡張を与えるなら、$`\beta` が $`H` に沿う左 Kan 拡張を与えることは、$`\alpha` と $`\beta G` の合成が $`HG` に沿う左 Kan 拡張を与えることと同値である。

C₂を一点、Gを全部分圏の包含、αを厳密制限の恒等変換に限る。すると同じβのKan性はその頂点への余錐の余極限性で、kanLeftCanonical\_pre\_initialBoundaryとisColimitCone\_iff\_restrict\_of\_initialBoundaryは原文の(1)⇔(2)を直接返す。一般Hや一般αは含まない。

:::

:::proposition "kerodon_7_3_8_25" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.hasColimit_iff_leftKanExtension") (uses := "kerodon_1_4_0_1, kerodon_7_2_2_3, kerodon_7_3_2_11, kerodon_7_3_5_8, kerodon_7_3_8_12, kerodon_7_3_8_24")
Kerodon Proposition 7.3.8.25（[Tag 031N](https://kerodon.net/tag/031N)）。対応表の状態：一部。

*主張*　無限圏の $`G:C_0\to C_1,H:C_1\to C_2` に対し、$`F_1` が $`F_0` の $`G` に沿う左 Kan 拡張なら、$`F_1` の $`H` に沿う左 Kan 拡張の存在は、$`F_0` の $`HG` に沿う左 Kan 拡張の存在と同値である。

C₂を一点に限れば左Kan拡張の存在は同じF₁,F₀の余極限の存在。hasColimit\_iff\_leftKanExtensionはこの場合の(1)⇔(2)を直接返す。一般のHは含まない。

:::

:::corollary "kerodon_7_3_8_26" (lean := "CategoryTheory.Functor.isColimitCoconeOfIsLeftKanExtension, CategoryTheory.Functor.colimitIsoOfIsLeftKanExtension, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.hasColimit_iff_leftKanExtension, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeLeftKanExtendedFrom_iff_refl_extension, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_isColimit_of_terminal") (uses := "kerodon_1_4_0_1, kerodon_4_1_3_3, kerodon_7_3_1_5, kerodon_7_3_1_14, kerodon_7_3_8_24, kerodon_7_3_8_25")
Kerodon Corollary 7.3.8.26（[Tag 039X](https://kerodon.net/tag/039X)）。対応表の状態：一部。

*主張*　$`\alpha:F_0\to F\delta` が $`\delta:K\to C` に沿う無限圏 $`D` での左 Kan 拡張を示すなら、$`F` に余極限があることと $`F_0` に余極限があることは同値である。$`F\to\underline x` が余極限を与えることは、$`\alpha` と制限を合成した $`F_0\to\underline x|_K` が余極限を与えることと同値である。

Kを準圏に強めるとhasColimit\_iff\_leftKanExtensionは原文(1)の同じF,F₀の余極限存在のiffを直接返す。指定βについての余極限性を比較する(2)は含まない。

:::

# 7.3.9 Relative Colimits for Cocartesian Fibrations

%%%
number := false
tag := "kerodon-7-3-9"
%%%

Kerodon [Tag 031Q](https://kerodon.net/tag/031Q)

:::proposition "kerodon_7_3_9_1"
Kerodon Proposition 7.3.9.1（[Tag 06B2](https://kerodon.net/tag/06B2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対余極限の定義と、既存の相対余極限余錐の像に同型な指定底余錐へ移す構成がある。各ファイバーの K-余完備性と全輸送による保存が任意の指定底余錐の持ち上げと同値となる型は見つからない。

:::

:::corollary "kerodon_7_3_9_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeLeftCanonical_strict_extension_of_comma_colimits")
Kerodon Corollary 7.3.9.2（[Tag 0320](https://kerodon.net/tag/0320)）。対応表の状態：一部。

*主張*　無限圏の余デカルトファイブレーション $`U:D\to E` と充満部分圏 $`C^0\subseteq C` を取る。各ファイバーに全ての $`c\in C` について $`C^0\times_C C_{/c}` 添字の余極限があり、各共変移送がそれを保つなら、$`C^0` 上の持ち上げは $`U`-左 Kan 拡張として $`C` 上に延長できる。

仮定を、同じFと底図式の全comma余錐上に指定された相対余極限が存在することにも強めれば、exists\_kanRelativeLeftCanonical\_strict\_extension\_of\_comma\_colimitsは同じ持ち上げ問題のU-leftKan解を直接返す。fiber余完備性と輸送保存だけからその入力を得たとはしない。

:::

:::proposition "kerodon_7_3_9_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_of_functorIso")
Kerodon Proposition 7.3.9.3（[Tag 031R](https://kerodon.net/tag/031R)）。対応表の状態：一部。

*主張*　無限圏の内部ファイブレーション $`U:D\to E` と、右錐 $`F_0,F_1` の間の各成分が $`U`-余デカルトな変換を取る。$`F_0` が $`U`-余極限図式なら $`F_1` もそうであり、錐頂点で変換が同型なら逆も成り立つ。

指定αが全余錐のFunctorIsoも与えると強めればkanIsRelativeColimitCone\_iff\_of\_functorIsoは同じ二余錐の相対余極限性を両方向に直接移す。全成分cocartesianという元の仮定だけは含まない。

:::

:::corollary "kerodon_7_3_9_4"
Kerodon Corollary 7.3.9.4（[Tag 031V](https://kerodon.net/tag/031V)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対余極限性を全余錐族の相対始性と比較する型はある。弱可縮な K 上の全辺の U-cocartesian 性と、底の各辺と余錐の相対余極限性との iff は見つからない。

:::

:::proposition "kerodon_7_3_9_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianFibration_lift_prism")
Kerodon Proposition 7.3.9.5（[Tag 031W](https://kerodon.net/tag/031W)）。対応表の状態：一部。

*主張*　無限圏の余デカルトファイブレーション $`U:D\to E` と右錐 $`g:K^{\triangleright}\to E`、その $`K` 上の持ち上げ $`f_0` を取る。$`g` の縦辺に沿う共変移送により $`f_0` から錐頂点の像 $`e` 上の図式 $`f_1` への成分ごとに余デカルトな変換を取れる。$`f_0` が $`g` 上で $`U`-余極限図式へ延長できることは、$`f_1` にファイバーの余極限があり、$`e` から出る底の全ての射の共変移送がそれを保つことと同値である。

cocartesianFibration\_lift\_prismを原文のc≫gへ適用すれば、同じf₀から指定された底の変換上の成分ごとcocartesianなαを直接構成する。終点が定値Eなのでf₁は同じ終点fiberを通る。後半の余極限存在と輸送保存のiffは含まない。

:::

