import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.CanonicalMappingTrivial
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.ComparisonCartesian
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.ComparisonCocartesian
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Definition
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.GlobalIsofibrationDiagram
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Hom
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.InitialBoundaryCoconeRestriction
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCanonicalMapping
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaCoconeColimit
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftHomotopyInvariant
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanColimitExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftStrictExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftCanonical
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftCanonicalExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeMappingPullback
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightHomotopyInvariant
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Shapes
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LeftCanonicalRestriction

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "7.3 Kan Extensions" =>
%%%
number := false
tag := "kerodon-7-3"
%%%

Kerodon の 7.3 節（[Tag 02Y1](https://kerodon.net/tag/02Y1)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::definition "kerodon_7_3_0_1" (lean := "CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension")
Kerodon Definition 7.3.0.1（[Tag 02Y2](https://kerodon.net/tag/02Y2)）。対応表の状態：Mathlib にある。

仮定：通常圏の関手に沿う指定の LeftExtension。包含に限定しない（Lean が弱い）。結論：IsPointwiseLeftKanExtension は各対象で StructuredArrow による余錐の IsColimit。全部分圏の包含と制限からの標準変換を取ると原文の余錐（原文と一致）。

:::

# 7.3.1 Kan Extensions along General Functors

%%%
number := false
tag := "kerodon-7-3-1"
%%%

Kerodon [Tag 02Y7](https://kerodon.net/tag/02Y7)

:::definition "kerodon_7_3_1_1" (uses := "kerodon_1_4_0_1, kerodon_4_6_4_15")
Kerodon Notation 7.3.1.1（[Tag 02Y8](https://kerodon.net/tag/02Y8)）。対応表の状態：一部。

leftKanShapeとrightKanShapeは原文のK\_/CとK\_C/という二つの指定pullbackを直接構成する。γ,γ′の自然変換までは引用に含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape`

:::

:::definition "kerodon_7_3_1_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanConeTransport, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram")
Kerodon Definition 7.3.1.2（[Tag 02Y9](https://kerodon.net/tag/02Y9)）。対応表の状態：本体にある。

仮定：単体写像 δ、F₀、F と SSet.Homotopy (δ≫F) F₀。定義自体は C,D の Quasicategory を要求しない（Lean が弱い）。結論：各 c で輸送した右 Kan 錐が IsLimitCone となる条件（原文の右 Kan 拡張と一致）。

:::

:::proposition "kerodon_7_3_1_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport.isColimitCone_iff, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanConeTransport.isLimitCone_iff")
Kerodon Warning 7.3.1.4（[Tag 02YB](https://kerodon.net/tag/02YB)）。対応表の状態：本体にある。

仮定：Quasicategory D、固定 δ,F₀,F と固定 α または β、同じ c における二つの輸送（Kerodon の合成の選択に一致）。結論：二つの輸送錐の極限性と輸送余錐の余極限性の二つの iff（合成の選択によらない点で一致）。

:::

:::definition "kerodon_7_3_1_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram")
Kerodon Variant 7.3.1.5（[Tag 02YC](https://kerodon.net/tag/02YC)）。対応表の状態：本体にある。

仮定：単体写像 δ、F₀、F と SSet.Homotopy F₀ (δ≫F)。定義自体は C,D の Quasicategory を要求しない（Lean が弱い）。結論：各 c における輸送済み左 Kan 余錐の IsColimitCone（原文と一致）。

:::

:::proposition "kerodon_7_3_1_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.isLeftKanExtension_iff_of_homMk_eq, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.isRightKanExtension_iff_of_homMk_eq, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtensionHom")
Kerodon Remark 7.3.1.10（[Tag 02YG](https://kerodon.net/tag/02YG)）。対応表の状態：本体にある。

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

:::corollary "kerodon_7_3_1_17"
Kerodon Corollary 7.3.1.17（[Tag 02YN](https://kerodon.net/tag/02YN)）。対応表の状態：一部。

δをinner fibrationにも限るとkanLeftKanExtension\_unit\_isIsoは、充満忠実な同じδに沿う左Kan拡張の指定単位βが可逆と直接返す。右Kan拡張の余単位の節は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanExtension_unit_isIso`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanExtension_unit_isIso`

:::

:::proposition "kerodon_7_3_1_18"
Kerodon Proposition 7.3.1.18（[Tag 039N](https://kerodon.net/tag/039N)）。対応表の状態：一部。

δをモデル圏のbifibrant部分のhammockLocalizationNerveMap、F₀=δ≫G、αを恒等変換に制限すると、移動後のmodelBifibrantSourceRightKanExtension\_refl\_of\_frameCofinalityは同じαの右Kan性を返す。ModelCategory C・指定resolution・frame余終性を明示入力とするschema（一般の具体的instanceなし）で、任意の局所化ではない。

宣言：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRightKanExtension_refl_of_frameCofinality`

:::

# 7.3.2 Kan Extensions along Inclusions

%%%
number := false
tag := "kerodon-7-3-2"
%%%

Kerodon [Tag 02YP](https://kerodon.net/tag/02YP)

:::definition "kerodon_7_3_2_1" (uses := "kerodon_1_4_0_1, kerodon_4_3_5_12, kerodon_7_3_1_1")
Kerodon Definition 7.3.2.1（[Tag 02YQ](https://kerodon.net/tag/02YQ)）。対応表の状態：一部。

leftKanCanonicalCocone δ F cは原文のC⁰\_/cに沿う同じ標準余錐で、そのIsColimitConeという型が左Kan extended at cの定義を直接与える。右側の定義はこの引用に含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtendedFrom`

:::

:::proposition "kerodon_7_3_2_6" (uses := "kerodon_1_4_0_1, kerodon_7_3_1_2, kerodon_7_3_1_5, kerodon_7_3_2_1")
Kerodon Proposition 7.3.2.6（[Tag 02YU](https://kerodon.net/tag/02YU)）。対応表の状態：一部。

Uを終対象への射として相対余極限と絶対余極限のiffを各輸送余錐に適用すると、kanIsRelativeLeftKanExtendedFrom\_iff\_refl\_extensionは原文の左側の恒等変換のKan性とのiffを直接与える。右側のiffは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeLeftKanExtendedFrom_iff_refl_extension`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_isColimit_of_terminal`

:::

:::corollary "kerodon_7_3_2_7"
Kerodon Corollary 7.3.2.7（[Tag 02YV](https://kerodon.net/tag/02YV)）。対応表の状態：一部。

全部分圏の包含δについて、kanLeftKanExtension\_unit\_isIsoとcanonicalColimits\_of\_unit\_isIsoを順に用いると、左Kan拡張⇒単位β可逆かつFが左Kan extendedという同じβについての向きを直接得る。逆向きは引用に含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanExtension_unit_isIso`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanExtension_canonicalColimits_of_unit_isIso`

:::

:::corollary "kerodon_7_3_2_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftExtension_iff_local_colimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftCanonical_strict_extension_of_local_colimits")
Kerodon Corollary 7.3.2.8（[Tag 02YW](https://kerodon.net/tag/02YW)）。対応表の状態：本体にある。

仮定：C⁰↪C は充満忠実な mono で inner fibration、各圏は quasicategory（原文の全部分圏の包含と一致）。結論：変換つき左 Kan 拡張の存在と各局所余極限を比較し、局所余極限から制限が F₀ に厳密に等しい標準左 Kan 拡張を構成する（原文の二つの存在に一致）。

:::

:::definition "kerodon_7_3_2_9"
Kerodon Definition 7.3.2.9（[Tag 02YX](https://kerodon.net/tag/02YX)）。対応表の状態：一部。

δ≫F=F₀という厳密延長に対し、leftKanCanonicalCocone δ F cの全cでの余極限性が原文の左Kan延長の定義部分を直接与える。右Kan延長の定義は含まない。別のGの存在だけを定義の証拠とはしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftCanonical_strict_extension_of_local_colimits`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone`

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

:::definition "kerodon_7_3_3_1"
Kerodon Definition 7.3.3.1（[Tag 02Z3](https://kerodon.net/tag/02Z3)）。対応表の状態：一部。

IsRelativeLeftKanExtendedFromの定義は全cについて同じleftKanCanonicalCoconeのIsRelativeColimitConeを要求し、原文のU-left Kan条件を直接表す。右Kan側の定義は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtendedFrom`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtension`

:::

:::proposition "kerodon_7_3_3_7" (uses := "kerodon_1_4_0_1, kerodon_4_7_3_20, kerodon_7_2_3_6")
Kerodon Proposition 7.3.3.7（[Tag 02Z8](https://kerodon.net/tag/02Z8)）。対応表の状態：一部。

Uを終対象への射、cを包含δの実際の像δkに限ると、kanLeftCanonical\_isColimit\_at\_imageと終対象上の相対余極限のiffは同じ標準余錐のU余極限性を直接与える。δはinnerかつ充満忠実。任意Uや像と同型な全cは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonical_isColimit_at_image`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftTransport_image_isColimit_at_image`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_isColimit_of_terminal`

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

:::lemma_ "kerodon_7_3_4_5"
Kerodon Lemma 7.3.4.5（[Tag 02ZR](https://kerodon.net/tag/02ZR)）。対応表の状態：一部。

C,Dを準圏、Uを終対象への射に限ると、fiberwiseHomの随伴で同じ押し出しからの指定F₀を族へ移し、exists\_kanRelativeJoin\_family\_extension\_of\_colimitsは元と同じF₀を保つ解を直接返す。相対余極限は終対象上では絶対余極限と同値。一般Uは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRestriction_preservesCartesianEdges`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeJoin_family_extension_of_colimits`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_isColimit_of_terminal`

:::

:::lemma_ "kerodon_7_3_4_6"
Kerodon Lemma 7.3.4.6（[Tag 02ZU](https://kerodon.net/tag/02ZU)）。対応表の状態：一部。

Cを準圏に限り、全ての同じ型の持ち上げ問題について局所余錐があると強めると、relativeColimitRestrictionの頂点全射性は同じF₀,Gを保つ大域解の存在を返す。指定された各F\_Cとの厳密一致の結論は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeJoin_family_extension_of_colimits`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRelativeColimitRestriction_trivialKanFibration`

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

:::proposition "kerodon_7_3_5_1" (uses := "kerodon_1_4_0_1, kerodon_4_1_3_1, kerodon_4_1_3_3, kerodon_5_6_7_6, kerodon_7_2_1_13, kerodon_7_2_2_9, kerodon_7_3_1_14, kerodon_7_3_2_11, kerodon_7_3_5_8")
Kerodon Proposition 7.3.5.1（[Tag 0300](https://kerodon.net/tag/0300)）。対応表の状態：一部。

Kも準圏に強めれば左右それぞれのexists\_kanLeft/RightExtension\_iff\_local\_colimits/limitsは同じδ,F₀について原文の二つのiffを直接返す。任意の単体集合Kは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftExtension_iff_local_colimits`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRightExtension_iff_local_limits`

:::

:::corollary "kerodon_7_3_5_2"
Kerodon Corollary 7.3.5.2（[Tag 0301](https://kerodon.net/tag/0301)）。対応表の状態：一部。

Kを準圏に強めると、全ての形状の余極限存在を各leftKanDiagramに適用しexists\_kanLeftExtension\_of\_local\_colimitsから同じF₀の拡張を直接得る。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftExtension_of_local_colimits`

:::

:::corollary "kerodon_7_3_5_3"
Kerodon Corollary 7.3.5.3（[Tag 039T](https://kerodon.net/tag/039T)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：任意の δ に対する相対 Kan 性は comma の各ファイバーの相対余極限と比較できる。原文の G(C) とその lax holim 射影のファイバーを結び、左 Kan 拡張の存在と各 G(C) 上の余極限を比較する型は見つからない。

:::

:::proposition "kerodon_7_3_5_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeLeftCanonical_strict_extension_of_local_relative_colimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanGlobalRelative_diagram_with_relative_colimits_of_isofibration")
Kerodon Proposition 7.3.5.5（[Tag 0302](https://kerodon.net/tag/0302)）。対応表の状態：本体にある。

仮定：全部分圏の包含、U の EquivalenceLifting、可換四角形。局所標準余錐の相対余極限による持ち上げを各頂点で仮定する（Kerodon と一致）。結論：両側の等式を保つ厳密な延長 G が存在し、U-relative left Kan extended from となる（原文と一致）。

:::

:::corollary "kerodon_7_3_5_7" (uses := "kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_7_1_5_21, kerodon_7_1_8_10")
Kerodon Corollary 7.3.5.7（[Tag 043J](https://kerodon.net/tag/043J)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：各頂点での相対始性を関手空間の境界充填につなぐ補題はある。cartesian fibration の全ファイバーの始対象から切断を構成し、その始性との iff を得る型は見つからない。

:::

:::corollary "kerodon_7_3_5_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftCanonical_strict_extension_of_local_colimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftExtension_iff_local_colimits, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRightExtension_iff_local_limits") (uses := "kerodon_1_4_0_1, kerodon_7_3_5_5")
Kerodon Corollary 7.3.5.8（[Tag 0307](https://kerodon.net/tag/0307)）。対応表の状態：本体にある。

全部分圏の始域は準圏なので、左右のexists\_kanExtension\_iff\_local\_colimits/limitsを同じ包含δ,F₀へ適用すると原文の二つのiffを直接得る。右側の既存定理を追記し、専用の一宣言の不足はpartial理由にしない。

:::

:::corollary "kerodon_7_3_5_9" (uses := "kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_7_2_2_14, kerodon_7_3_5_5")
Kerodon Corollary 7.3.5.9（[Tag 047U](https://kerodon.net/tag/047U)）。対応表の状態：なし。

comma全局所相対余錐の存在から延長を作る型はあるが、原文(2)は余反射の各辺のcocartesian liftだけの条件。その条件を全局所余錐へ変換する型が引用にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeLeftCanonical_strict_extension_of_comma_colimits`

:::

:::corollary "kerodon_7_3_5_10" (uses := "kerodon_1_4_0_1, kerodon_5_1_4_1")
Kerodon Corollary 7.3.5.10（[Tag 039V](https://kerodon.net/tag/039V)）。対応表の状態：一部。

同じF₀,Gの全comma余錐に指定された相対余極限が存在することも加えると、exists\_kanRelativeLeftCanonical\_strict\_extension\_of\_comma\_colimitsは同じ持ち上げ問題のU-leftKan解を直接返す。始域の余反射性や始対象だけからその入力を得たとはしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeLeftCanonical_strict_extension_of_comma_colimits`

:::

:::corollary "kerodon_7_3_5_11" (uses := "kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_7_3_5_10")
Kerodon Corollary 7.3.5.11（[Tag 043K](https://kerodon.net/tag/043K)）。対応表の状態：一部。

同じF₀,Gの全comma余錐に指定された相対余極限が存在することも加えると、exists\_kanRelativeLeftCanonical\_strict\_extension\_of\_comma\_colimitsは同じ持ち上げ問題のU-leftKan解を直接返す。始域の余反射性や始対象だけからその入力を得たとはしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeLeftCanonical_strict_extension_of_comma_colimits`

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

:::corollary "kerodon_7_3_6_4"
Kerodon Corollary 7.3.6.4（[Tag 030C](https://kerodon.net/tag/030C)）。対応表の状態：一部。

Kを準圏に強めればexists\_kanLeftExtension\_with\_homUniversal\_of\_local\_colimitsは全F₀について同じδに沿う左Kan拡張の存在を直接返す。原文の左随伴の構成およびその単位との同定は含まない。

宣言：`CategoryTheory.Functor.lanAdjunction`、`CategoryTheory.Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftExtension_with_homUniversal_of_local_colimits`

:::

:::corollary "kerodon_7_3_6_5" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_7_3_6_1")
Kerodon Corollary 7.3.6.5（[Tag 030D](https://kerodon.net/tag/030D)）。対応表の状態：一部。

Kを準圏に強めるとkanLeftKanExtensionHom\_homUniversalは同じβについて原文(1)⇒(3)のh Fun上のHom全単射を直接返す。写像空間同値(2)や逆向きは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanExtensionHom_homUniversal`、`SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.kanClassical_isLeftKanExtension_iff_bijective`

:::

:::proposition "kerodon_7_3_6_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftMappingPullbackComparison_equivalence, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeRightMappingPullbackComparison_equivalence")
Kerodon Proposition 7.3.6.7（[Tag 030F](https://kerodon.net/tag/030F)）。対応表の状態：本体にある。

仮定：quasicategory の全部分圏の包含を mono・inner fibration・充満忠実として取る。F の相対左 Kan 性または G の相対右 Kan 性（Kerodon と一致）。結論：指定された写像空間の引き戻しへの比較が IsSimplicialHomotopyEquivalence（原文と一致）。

:::

:::corollary "kerodon_7_3_6_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonical_pinchedHomMap_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCanonical_pinchedHomMap_trivialKanFibration")
Kerodon Corollary 7.3.6.9（[Tag 030M](https://kerodon.net/tag/030M)）。対応表の状態：本体にある。

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

:::corollary "kerodon_7_3_6_12" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_7_1_5_12, kerodon_7_3_6_7")
Kerodon Corollary 7.3.6.12（[Tag 030N](https://kerodon.net/tag/030N)）。対応表の状態：一部。

全部分圏の包含に対しkanRelativeLeftMappingPullbackComparison\_equivalenceは、同じU,F,Gと制限について(1)からホモトピー引き戻しへの比較同値(2)を直接返す。逆向きは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftMappingPullbackComparison_equivalence`

:::

:::corollary "kerodon_7_3_6_13" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_3_7_6, kerodon_4_1_4_2, kerodon_4_6_1_22, kerodon_7_3_6_12")
Kerodon Corollary 7.3.6.13（[Tag 030Q](https://kerodon.net/tag/030Q)）。対応表の状態：一部。

kanLeftCanonical\_pinchedHomMap\_trivialKanFibrationは原文(1)⇒(3)を同じF,Gの制限のpinched Homモデルで直接返す。(1)⇒(2)も自然なpinched/interval比較で得るが、その比較だけで別モデルの厳密Kanファイブレーション性を主張しない。全逆向きは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonical_pinchedHomMap_trivialKanFibration`

:::

:::theorem "kerodon_7_3_6_14" (uses := "kerodon_1_4_0_1, kerodon_4_4_5_1, kerodon_7_1_5_18, kerodon_7_3_5_5, kerodon_7_3_6_7")
Kerodon Theorem 7.3.6.14（[Tag 030R](https://kerodon.net/tag/030R)）。対応表の状態：一部。

全てのF₀,H₀の局所相対余錐があると強めれば、Bは全pullbackとなりkanRelativeLeftKanRestriction\_trivialKanFibrationが同じ制限Vを返す。任意の真の充満部分圏Bの場合は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction_trivialKanFibration`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction_isFullyFaithful`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeRightKanRestriction_trivialKanFibration`

:::

:::corollary "kerodon_7_3_6_15" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_3_6_14")
Kerodon Corollary 7.3.6.15（[Tag 030S](https://kerodon.net/tag/030S)）。対応表の状態：一部。

全F₀,cで局所余極限があると強めればFun′(C⁰,D)は全関手圏となり、terminal版の制限のtrivialKanFibrationは同じ左Kan関手の制限の結論を直接与える。任意の真の部分圏への制限は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction_terminal_trivialKanFibration`

:::

# 7.3.7 Kan Extensions in Functor ∞-Categories

%%%
number := false
tag := "kerodon-7-3-7"
%%%

Kerodon [Tag 047V](https://kerodon.net/tag/047V)

:::theorem "kerodon_7_3_7_1" (uses := "kerodon_1_4_0_1, kerodon_7_3_7_13")
Kerodon Theorem 7.3.7.1（[Tag 047W](https://kerodon.net/tag/047W)）。対応表の状態：一部。

Bを一点、FをC因子に依らない定値族に限りVをinner fibrationに強めると、kanIsRelativeLeftKanExtendedFrom\_constantFamilyは同じ転置fのV′-leftKan条件を直接返す。一般の相対関手圏は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeLeftKanExtendedFrom_constantFamily`

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

:::proposition "kerodon_7_3_7_13" (uses := "kerodon_1_4_0_1, kerodon_4_5_8_18, kerodon_7_3_5_5, kerodon_7_3_6_14, kerodon_7_3_7_10")
Kerodon Proposition 7.3.7.13（[Tag 0488](https://kerodon.net/tag/0488)）。対応表の状態：一部。

Bを一点、Vをinner fibrationとし、仮定を各aの指定余錐がV余極限であることにも強めると、kanIsRelativeColimitCone\_functor\_of\_pointwiseは同じ転置fのV′余極限性を直接返す。元のleftKan仮定だけから点ごとの条件を得たとはしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_functor_of_pointwise`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeColimitCone_constantFamily`

:::

# 7.3.8 Transitivity of Kan Extensions

%%%
number := false
tag := "kerodon-7-3-8"
%%%

Kerodon [Tag 030U](https://kerodon.net/tag/030U)

:::proposition "kerodon_7_3_8_1" (uses := "kerodon_1_4_0_1, kerodon_3_4_1_11, kerodon_3_4_1_13, kerodon_7_1_6_19, kerodon_7_3_6_7, kerodon_7_3_6_9")
Kerodon Proposition 7.3.8.1（[Tag 030V](https://kerodon.net/tag/030V)）。対応表の状態：一部。

Uを終対象への射に限れば相対余極限は絶対余極限。同じFの標準左Kan余錐からkanLeftCanonical\_pre\_initialBoundaryを得てisColimitCone\_iff\_restrict\_of\_initialBoundaryへ渡すと、原文の指定余錐の制限とのiffを直接得る。U=idはこの特殊化ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.isColimitCone_iff_restrict_of_poset_nested_canonical`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonical_pre_initialBoundary`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.isColimitCone_iff_restrict_of_initialBoundary`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.hasColimit_iff_leftKanExtension`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_isColimit_of_terminal`

:::

:::corollary "kerodon_7_3_8_2"
Kerodon Corollary 7.3.8.2（[Tag 06AX](https://kerodon.net/tag/06AX)）。対応表の状態：なし。

colimitConstInitialは通常圏で一つの選択済み定値図式の余極限対象の同型。原文の指定された任意の余錐についての相対余極限性のiffと比較する型がない。

宣言：`CategoryTheory.Limits.colimitConstInitial`

:::

:::corollary "kerodon_7_3_8_3" (lean := "CategoryTheory.Functor.isColimitCoconeOfIsLeftKanExtension, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonical_pre_initialBoundary, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.isColimitCone_iff_restrict_of_initialBoundary") (uses := "kerodon_1_4_0_1, kerodon_7_3_8_1")
Kerodon Corollary 7.3.8.3（[Tag 030Y](https://kerodon.net/tag/030Y)）。対応表の状態：本体にある。

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

:::proposition "kerodon_7_3_8_12" (uses := "kerodon_1_4_0_1, kerodon_7_3_8_1, kerodon_7_3_8_10")
Kerodon Proposition 7.3.8.12（[Tag 0312](https://kerodon.net/tag/0312)）。対応表の状態：一部。

Uを終対象への射、Cの塔を半順序集合の充満部分nerveに限ると、posetSubtype\_canonicalColimit\_nestedは原文の左辺⇒(2)を同じ制限関手について直接返す。(1)および逆向きは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.posetSubtype_canonicalColimit_nested`

:::

:::corollary "kerodon_7_3_8_14" (uses := "kerodon_1_4_0_1, kerodon_7_3_8_12")
Kerodon Corollary 7.3.8.14（[Tag 0314](https://kerodon.net/tag/0314)）。対応表の状態：一部。

半順序集合のnerveとその充満部分圏の塔に限ればposetSubtype\_canonicalColimit\_nestedは同じFの左辺⇒(2)を直接返す。通常圏のisLeftKanExtension\_iff\_postcomposeだけは根拠としない。

宣言：`CategoryTheory.Functor.isLeftKanExtension_iff_postcompose`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.posetSubtype_canonicalColimit_nested`

:::

:::corollary "kerodon_7_3_8_15"
Kerodon Corollary 7.3.8.15（[Tag 0315](https://kerodon.net/tag/0315)）。対応表の状態：なし。

isPointwiseLeftKanExtensionAtOfIso′は通常圏の点ごとのKan条件の輸送。原文の∞圏の同じ標準相対余錐への比較がなく、類似の輸送だけでは数えない。

宣言：`CategoryTheory.Functor.LeftExtension.isPointwiseLeftKanExtensionAtOfIso'`

:::

:::proposition "kerodon_7_3_8_16"
Kerodon Proposition 7.3.8.16（[Tag 0316](https://kerodon.net/tag/0316)）。対応表の状態：一部。

Uを終対象への射に限れば、同じFのkanLeftCanonical\_pre\_initialBoundaryとsliceUnderRestrict\_isQCatEquivalence\_of\_initialBoundaryは原文のθの絶対coslice制限の同値を直接返す。一般Uの相対pullbackは含まない。U=idとはしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.sliceUnderRestrict_isQCatEquivalence_of_initialBoundary`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonical_pre_initialBoundary`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_isColimit_of_terminal`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.isColimitCone_iff_restrict_of_initialBoundary`

:::

:::corollary "kerodon_7_3_8_17"
Kerodon Corollary 7.3.8.17（[Tag 0319](https://kerodon.net/tag/0319)）。対応表の状態：一部。

UをEquivalenceLifting、包含C⁰→CをIsPrecompositionEquivalenceにも強めれば、kanRelativeCosliceMap\_trivialKanFibration\_of\_precompositionEquivalenceは原文と同じ相対coslice制限θのtrivialKanFibrationを直接返す。Fの相対Kan性だけの場合は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeCosliceMap_trivialKanFibration_of_precompositionEquivalence`

:::

:::corollary "kerodon_7_3_8_18"
Kerodon Corollary 7.3.8.18（[Tag 031A](https://kerodon.net/tag/031A)）。対応表の状態：一部。

包含C⁰→CをIsPrecompositionEquivalenceにも強め、Uを終対象への射として相対coslice補題を用いれば、同じ絶対coslice制限θのtrivialKanFibrationを直接得る。個別のpinchedHomMapの結果だけは全cosliceの代用にしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeCosliceMap_trivialKanFibration_of_precompositionEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonical_pinchedHomMap_trivialKanFibration`

:::

:::corollary "kerodon_7_3_8_19"
Kerodon Corollary 7.3.8.19（[Tag 031B](https://kerodon.net/tag/031B)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：既存 U-余極限余錐の充填性と、各 comma 余錐からの厳密相対左 Kan 拡張の存在はある。相対左 Kan 性を持つ F の指定底余錐を持ち上げる存在を部分圏で判定する iff は見つからない。

:::

:::corollary "kerodon_7_3_8_20" (lean := "CategoryTheory.Functor.isColimitCoconeOfIsLeftKanExtension, CategoryTheory.Functor.colimitIsoOfIsLeftKanExtension, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.hasColimit_iff_leftKanExtension, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeLeftKanExtendedFrom_iff_refl_extension, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_isColimit_of_terminal")
Kerodon Corollary 7.3.8.20（[Tag 031E](https://kerodon.net/tag/031E)）。対応表の状態：本体にある。

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

:::proposition "kerodon_7_3_8_24" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_6_2, kerodon_5_1_4_1, kerodon_5_1_4_20, kerodon_5_2_3_17, kerodon_5_3_6_1, kerodon_7_2_2_3, kerodon_7_2_3_10, kerodon_7_3_1_10, kerodon_7_3_2_11, kerodon_7_3_8_14")
Kerodon Proposition 7.3.8.24（[Tag 031M](https://kerodon.net/tag/031M)）。対応表の状態：一部。

C₂を一点、Gを全部分圏の包含、αを厳密制限の恒等変換に限る。すると同じβのKan性はその頂点への余錐の余極限性で、kanLeftCanonical\_pre\_initialBoundaryとisColimitCone\_iff\_restrict\_of\_initialBoundaryは原文の(1)⇔(2)を直接返す。一般Hや一般αは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.isColimitCone_iff_restrict_of_initialBoundary`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonical_pre_initialBoundary`

:::

:::proposition "kerodon_7_3_8_25" (uses := "kerodon_1_4_0_1, kerodon_7_2_2_3, kerodon_7_3_2_11, kerodon_7_3_5_8, kerodon_7_3_8_12, kerodon_7_3_8_24")
Kerodon Proposition 7.3.8.25（[Tag 031N](https://kerodon.net/tag/031N)）。対応表の状態：一部。

C₂を一点に限れば左Kan拡張の存在は同じF₁,F₀の余極限の存在。hasColimit\_iff\_leftKanExtensionはこの場合の(1)⇔(2)を直接返す。一般のHは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.hasColimit_iff_leftKanExtension`

:::

:::corollary "kerodon_7_3_8_26" (uses := "kerodon_1_4_0_1, kerodon_4_1_3_3, kerodon_7_3_1_5, kerodon_7_3_1_14, kerodon_7_3_8_24, kerodon_7_3_8_25")
Kerodon Corollary 7.3.8.26（[Tag 039X](https://kerodon.net/tag/039X)）。対応表の状態：一部。

Kを準圏に強めるとhasColimit\_iff\_leftKanExtensionは原文(1)の同じF,F₀の余極限存在のiffを直接返す。指定βについての余極限性を比較する(2)は含まない。

宣言：`CategoryTheory.Functor.isColimitCoconeOfIsLeftKanExtension`、`CategoryTheory.Functor.colimitIsoOfIsLeftKanExtension`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.hasColimit_iff_leftKanExtension`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeLeftKanExtendedFrom_iff_refl_extension`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_isColimit_of_terminal`

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

:::corollary "kerodon_7_3_9_2"
Kerodon Corollary 7.3.9.2（[Tag 0320](https://kerodon.net/tag/0320)）。対応表の状態：一部。

仮定を、同じFと底図式の全comma余錐上に指定された相対余極限が存在することにも強めれば、exists\_kanRelativeLeftCanonical\_strict\_extension\_of\_comma\_colimitsは同じ持ち上げ問題のU-leftKan解を直接返す。fiber余完備性と輸送保存だけからその入力を得たとはしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeLeftCanonical_strict_extension_of_comma_colimits`

:::

:::proposition "kerodon_7_3_9_3"
Kerodon Proposition 7.3.9.3（[Tag 031R](https://kerodon.net/tag/031R)）。対応表の状態：一部。

指定αが全余錐のFunctorIsoも与えると強めればkanIsRelativeColimitCone\_iff\_of\_functorIsoは同じ二余錐の相対余極限性を両方向に直接移す。全成分cocartesianという元の仮定だけは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_of_functorIso`

:::

:::corollary "kerodon_7_3_9_4"
Kerodon Corollary 7.3.9.4（[Tag 031V](https://kerodon.net/tag/031V)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対余極限性を全余錐族の相対始性と比較する型はある。弱可縮な K 上の全辺の U-cocartesian 性と、底の各辺と余錐の相対余極限性との iff は見つからない。

:::

:::proposition "kerodon_7_3_9_5"
Kerodon Proposition 7.3.9.5（[Tag 031W](https://kerodon.net/tag/031W)）。対応表の状態：一部。

cocartesianFibration\_lift\_prismを原文のc≫gへ適用すれば、同じf₀から指定された底の変換上の成分ごとcocartesianなαを直接構成する。終点が定値Eなのでf₁は同じ終点fiberを通る。後半の余極限存在と輸送保存のiffは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianFibration_lift_prism`

:::

