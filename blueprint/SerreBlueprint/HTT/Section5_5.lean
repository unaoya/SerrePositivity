-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Presentable.LocallyPresentable
import Mathlib.Order.CompleteLattice.Defs
import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.AdjointRepresentability
import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
import SerrePositivity.InfinityCategories.HTT.Section5_5_4.StronglySaturatedHom
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.AdjunctionPinchedSpaces
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.LocalEquivalences
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveInvertedHom
import SerrePositivity.InfinityCategories.Kerodon.ExactnessAndAnimation.SimplicialObjectsOfInfinityCategories.SigmaFilteredGeometricDetection
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CovariantRepresentableInfinity
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.InitialSectionLifting
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.Accessibility
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.Accessible
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleFunctor
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleReflectiveImage
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.LocalStrongSaturation
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.StronglySaturatedClosure
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.Definition
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.SpacePresentable
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AccessibleCorepresentability
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AccessibleFunctorEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AdjointFunctorTheorem
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.BousfieldReflection
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.BousfieldSaturation
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorPresentable
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratedArrowsPresentable
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratedSourcePresentable
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratedSourceSmallColimits
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalObjects
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalSaturatedClosure
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NativeAdjointFunctorCriterion
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NativeContravariantHomContinuity
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NativeSmallHomContinuity
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PiPresentable
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrInfinity
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentablePresheafReflection
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentablePullback
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableSmallLimits
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservingFunctorSpaces
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafBarDegreeComparison
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafBarRealization
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafPresentable
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaFilteredGeometricPreservation
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaFilteredGeometricUniversality
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaSimplicialIndDiagram
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaYonedaFiniteCoproducts
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaYonedaInfinity
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedCoherentEmptyProductNative
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedCoherentProductComparison
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedCoherentProductNativeCone
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedContractibility
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedInfinity
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedSimplexCategory
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaReflectorAdjunction
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaYonedaColimitPreservationCriterion
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.SiftedColimitPreservation
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LeftAdjointAllColimitPreservation
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.PullbackSmallColimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ReflectionSmallColimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Space
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibrationTerminalLift
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 5.5 Presentable ∞-Categories" =>
%%%
number := false
tag := "htt-5-5"
%%%

HTT 5.5 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

*presentable-route.html — 6. Gabriel–Ulmer と Lurie–Simpson — ∞ 圏で何が変わるか*

- ステップ　／　1 圏　／　∞ 圏
- nerve $`N` の構成　／　書くだけ　／　$`\mathcal C` の Hom 関手（米田）が要る
- filtered の定義　／　$`\kappa`-小さい図式に余錐がある　／　全ての $`\kappa`-小さい単体的集合 $`K` について $`K\to\mathcal F` が $`K^{\triangleright}` に延びる（HTT §5.3.1）
- $`A_{/c}` が filtered　／　余極限が余錐　／　slice と join の扱いが要る
- 余単位が同値　／　元で全射・単射　／　写像空間の同値。filtered ∞ 圏の弱可縮性（HTT Lemma 5.3.1.18）と cofinality
- 像の特定　／　$`\mathrm{Set}` で filtered 余極限と有限極限が可換　／　$`\mathcal S` で $`\kappa`-filtered 余極限と $`\kappa`-小さい極限が可換（HTT Prop. 5.3.3.3）
- 主張 4　／　直交部分圏定理（Freyd–Kelly）　／　小対象論法による局所化の存在（HTT Prop. 5.5.4.15）

1 圏で「元を数えて全射・単射」だった部分が、∞ 圏では「ファイバーが可縮」になり、filtered ∞ 圏の弱可縮性と cofinality（Quillen の定理 A の ∞ 版）が効く。

:::definition "htt_5_5_0_1" (lean := "SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable")
*HTT 定義 5.5.0.1*　表示可能準圏の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=474)）。対応表の状態：本体にある。

*主張*　可提示 ∞ 圏とは、可到達で、すべての小余極限を持つ ∞ 圏である。

仮定：準圏 C（HTT と一致）。結論：accessible で全小余極限を持つという二条件による presentability の定義（一致）。小ささの宇宙は accessibility と余極限で揃える。

可到達性で小さい生成データを確保し、その上で余極限には濾過性を課さず存在を要求する。

:::

:::proposition "htt_5_5_0_2" (lean := "CategoryTheory.IsLocallyPresentable")
*HTT 注意 5.5.0.2*　通常の圏の局所表示可能性という用語（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=475)）。対応表の状態：Mathlib にある。

*主張*　通常の圏の文献でいう「局所可提示」は、この節の「可提示」に当たる。

仮定：通常の圏 C（HTT の用語の注意と一致）。結論：ある正則濃度の compact 生成性と全小余極限による locally presentable という通常圏の用語を与える（一致）。この注意だけで通常の圏の神経と native IsPresentable の比較を主張しない。

通常圏の結果を参照するときは、用語の「局所」の有無に注意すれば同じ性質を追える。

:::

# 5.5.1 Presentability

%%%
number := false
tag := "htt-5-5-1"
%%%

:::theorem "htt_5_5_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsPresentable.exists_presheafReflection, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjoint_isAccessible") (uses := "htt_1_1_2_4, htt_4_2_3_11, htt_5_1_3_1, htt_5_2_7_5, htt_5_3_4_5, htt_5_3_4_15, htt_5_3_5_11, htt_5_3_5_12, htt_5_4_2_2, htt_5_5_1_4")
*HTT 定理 5.5.1.1*　表示可能性の六つの同値な特徴づけ（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=475)）。対応表の状態：一部（direction）。

*主張*　可提示性には、可到達性と小さい余極限の存在、小さい余極限を持つコンパクト生成圏の Ind 表示、前層圏の可到達局所化などによる同値な特徴付けがある。

KB-W2原文・型再照合：仮定：presentable な準圏 C（HTT と一致）。結論：小準圏 A の前層圏からの反映表示 L⊣R と R の充満忠実性、L の全小余極限保存を構成し、R も accessible（(1)⇒(5) に一致）。(2)(3) の全 κ-small compact 余極限や (4)(6) との全ての同値はこの宣言群にない。

ある正則基数で可到達かつ同じ基数のコンパクト対象に同基数未満の余極限があれば十分である。可提示なら、任意の正則基数でコンパクト対象が対応する小余極限を持つ。全体が局所小で小余極限を持ち、共通の基数でコンパクトな小さい対象族が小余極限で全体を生成する、とも言い換えられる。

:::

:::proposition "htt_5_5_1_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjoint_isAccessible, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.mapJoinCocone_isColimit_of_adjunction, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor.comp, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsAccessibleFunctor.of_functorIso")
*HTT 命題 5.5.1.2*　局所化像の到達可能性と局所化関手の到達可能性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=476)）。対応表の状態：一部（direction）。

*主張*　可到達 ∞ 圏の反射的局所化では、局所対象の圏が可到達であることと、局所化の自己関手が可到達であることは同値である。

KB-W2原文・型再照合：仮定：accessible C と accessible D への反映 f⊣g、および元の L≃g∘f（HTT の (2) と一致）。結論：f は余極限を保存する左随伴として、g は右随伴として accessible で、その同じ合成 L も accessible（(2)⇒(3) に一致）。L の accessibility だけから像の accessibility を得る逆方向は含まない。

反射への射とその充満忠実な右随伴を合成すると自己関手になる。自己関手に関する判定と、可到達な圏への局所化を選んでその合成で表す判定は一致する。

:::

:::lemma_ "htt_5_5_1_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.adjunction_isKappaCompact_image")
*HTT 補題 5.5.1.4*　右随伴の連続性による左随伴のコンパクト保存（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=477)）。対応表の状態：本体にある。

*主張*　小さい $`\kappa`-濾過余極限を持つ圏の間の随伴 $`F\dashv G` で、$`G` がその余極限を保つなら $`F` は $`\kappa`-コンパクト対象を保つ。

仮定：小 κ-filtered 余極限を持つ二準圏の元の随伴 L⊣R と R の κ-連続性（HTT と一致。Lean は全余極限存在を不要とする）。結論：L は同じ κ の compact 対象を compact 対象へ送る（一致）。全共変 Hom の随伴同型で証明されている。

$`F(c)` から濾過余極限への写像空間を、随伴で $`c` から $`G` を適用した対象への写像空間に移す。$`G` の保存性と $`c` のコンパクト性を順に使う。

:::

:::proposition "htt_5_5_1_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.reflectiveSubcategory_hasSmallColimits, SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable")
*HTT 注意 5.5.1.6*　到達可能な局所化の表示可能性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=478)）。対応表の状態：本体にある。

*主張*　可提示 ∞ 圏の可到達局所化は可提示である。

仮定：presentable C とその accessible な反映像 D（HTT と一致）。結論：元の C の全小余極限を同じ reflector で写して D の全小余極限を得るので、D は accessible と合わせて presentable（一致）。局所化の存在を別途仮定する原典と揃える。

もとの圏を小さい圏上の前層圏の可到達局所化として表示し、局所化を合成することで新しい圏の前層表示を得る。

:::

:::proposition "htt_5_5_1_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SpaceTensorData, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.spaceTensorData, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tensorSpaceFunctor, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.pinchedHomEquivalence")
*HTT 注意 5.5.1.7*　表示可能準圏の空間によるテンソル（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=478)）。対応表の状態：本体にある。

*主張*　可提示 ∞ 圏 $`C` は空間によるテンソルを持ち、$`\operatorname{Map}_C(c\otimes S,d)\simeq \operatorname{Map}(S,\operatorname{Map}_C(c,d))` が成り立つ。

仮定：presentable な E と元の対象 M、小空間 S（HTT と一致）。結論：S↦S⊗M の全単体の関手と、Map(M,−) の同じ小空間模型に対する ∞ 随伴を構成する（一致）。SpaceTensorData.represents が元の全共変 Hom との比較を明示し、別の形式的 Hom で代用しない。原典のホモトピー圏の Map 表示はこの全随伴の成分である。

$`c\otimes S` は $`S` で添字付けた定値図式の余極限である。ここで述べる写像空間の式は空間のホモトピー圏での同型を与え、操作は $`C` のホモトピー圏にも降りる。

:::

:::proposition "htt_5_5_1_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.space_isPresentable")
*HTT 例 5.5.1.8*　空間準圏の表示可能性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=479)）。対応表の状態：本体にある。

*主張*　空間の ∞ 圏 $`\mathcal S` は可提示である。

仮定：固定した小さい宇宙の空間準圏（HTT と一致）。結論：元の空間準圏は compact 生成性と全小余極限から presentable（一致）。

空間の可到達性と小余極限の存在を組み合わせ、可提示性の定義を満たすことが分かる。

:::

:::proposition "htt_5_5_1_9" (lean := "SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits.isKappaAccessibleFunctor") (uses := "htt_1_1_2_4, htt_5_1_5_6, htt_5_3_4_17, htt_5_3_5_10, htt_5_5_1_1")
*HTT 命題 5.5.1.9*　余極限保存のコンパクト部分での判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=479)）。対応表の状態：一部（component）。

*主張*　$`C` が $`\kappa`-可到達であるとき、可提示 ∞ 圏の間の関手 $`F:C\to D` が小余極限を保つことは、$`\kappa`-濾過余極限と $`C^\kappa` の $`\kappa`-小余極限を保つことで判定できる。

KB-W2原文・型再照合：仮定：presentable な二準圏、κ-accessible な始域、全小余極限保存関手 f（HTT の (1) と一致）。結論：(2) の一つの要件である同じ κ の連続性（一致）。κ-compact 部分上の κ-small 余極限保存との組合せから全余極限保存を復元する逆方向はなく、両条件の iff と数えない。

小余極限を一度にすべて検査する代わりに、コンパクトな部分の小さい図式と、それをつなぐ濾過図式を検査する。制限の終域には $`D` 全体を使う。

:::

# 5.5.2 Representable Functors and the Adjoint Functor Theorem

%%%
number := false
tag := "htt-5-5-2"
%%%

:::proposition "htt_5_5_2_2" (lean := "SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.presentableContinuous_isRepresentable, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallContravariantHom_sendsSmallColimitsToLimits_native")
*HTT 命題 5.5.2.2*　表示可能準圏上の連続前層の表現可能性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=481)）。対応表の状態：本体にある。

*主張*　可提示 ∞ 圏 $`C` 上の反変空間値関手 $`C^{\mathrm{op}}\to\mathcal S` は、小極限を保つとき、かつそのときに限り、$`C` の対象で表現される。

仮定：presentable C と元の小空間値前層 F:Cᵒᵖ→Space（HTT と一致）。結論：F が表現可能であることと、C の全小余極限を Space の極限へ送ることの両方向（一致）。原典の Cᵒᵖ の小極限保存と同じ条件であり、全関手の自然同型で表現する。

保存条件は、$`C` の小余極限を空間の極限に移すことを意味する。表現対象 $`c` があれば関手の値は $`\operatorname{Map}_C(-,c)` で与えられる。

:::

:::corollary "htt_5_5_2_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsPresentable.hasSmallLimits")
*HTT 系 5.5.2.4*　表示可能準圏の小完備性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=482)）。対応表の状態：本体にある。

*主張*　可提示 ∞ 圏では任意の小極限が存在する。

仮定：presentable な準圏 C（HTT と一致）。結論：全小単体集合形状の全指定図式が小極限を持つ（一致）。準圏形状に限定せず全小形状を量化する。

錐の写像空間を表す関手を点ごとの極限で作ると、各表現可能関手の極限保存性が受け継がれる。表現可能性の判定で、この関手の表現対象として極限を得る。

:::

:::proposition "htt_5_5_2_5" (lean := "completeLatticeOfSup")
*HTT 注意 5.5.2.5*　小半順序の上限と下限の存在（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=482)）。対応表の状態：一部（component）。

*主張*　小さい半順序集合 $`A` の nerve が可提示であることは、$`A` の任意の部分集合が最小上界を持つことと同値である。

KB-W2原文・型再照合：仮定：半順序で各部分集合の指定上限が最小上界を満たす（HTT の末尾の古典的観察と一致）。結論：同じ順序に全ての下限も持つ完備束構造を構成する（一致する成分）。N(A) の native presentability との iff は構成していないので、その最初の結論までの一致とはしない。

薄い圏では余極限が最小上界になる。空集合の上界の条件には最小元の存在も含まれる。小さい半順序圏では冪等射の分裂が自動的なので可到達性も得られる。

:::

:::proposition "htt_5_5_2_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.accessible_preservesLimits_isCorepresentable, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsPresentable.hasSmallLimits, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallHomComposite_isAccessible_native, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallHomComposite_preservesSmallLimits_native")
*HTT 命題 5.5.2.7*　到達可能な極限保存関手の余表現可能性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=483)）。対応表の状態：本体にある。

*主張*　可提示 ∞ 圏 $`C` から空間への共変関手 $`F` は、可到達かつ小極限を保つとき、かつそのときに限り、$`\operatorname{Map}_C(c,-)` の形で表される。

仮定：presentable C と元の小空間値 F:C→Space（HTT と一致）。結論：accessible かつ全小極限保存なら元の対象で余表現可能、その逆も全 Hom の小模型への二つの保存定理を恒等関手に適用して得る（一致）。余表現対象の compact 濃度を指定入力にしない。

小極限の保存は共表現可能関手の普遍性に対応する。可到達性は、共表現対象を見つけるために必要な小さい生成部分を選ぶ際に使う。

:::

:::proposition "htt_5_5_2_8" (lean := "SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.presentableContinuous_isRepresentable")
*HTT 注意 5.5.2.8*　表現可能性の別証明への注意（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=483)）。対応表の状態：本体にある。

*主張*　共変関手の共表現可能性を示す証明を反変の場合に合わせて調整すると、反変の表現可能性定理の別証明が得られる。

仮定：presentable C の小空間値前層が全小余極限を小極限へ送る（参照先 5.5.2.2 と一致）。結論：同じ元の前層が表現可能（一致）。原典は前項の手法による別証明が可能と述べる注意であり、その証明手法自体を別の形式的な主張に追加していない。

参照しているのは 5.5.2.7 の証明と 5.5.2.2 の結論である。共変側には可到達性の条件が明示され、反変側には小極限の保存を課す。

:::

:::corollary "htt_5_5_2_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_rightAdjoint_iff_preservesSmallColimits, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_leftAdjoint_iff_accessible_preservesLimits")
*HTT 系 5.5.2.9*　表示可能準圏の随伴関手定理（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=484)）。対応表の状態：本体にある。

*主張*　可提示 ∞ 圏の間の関手が右随伴を持つことは小余極限の保存と同値であり、左随伴を持つことは可到達性と小極限の保存と同値である。

仮定：presentable な二準圏と元の関手 F（HTT と一致）。結論：(1) 右随伴存在と全小余極限保存、(2) 左随伴存在と accessibility および全小極限保存の二つの同値（一致）。いずれも元の F の全 ∞ 随伴を構成し、未供給の宇宙比較や具体モデル圏 instance を入力に残さない。

右随伴の値は反変関手 $`c\mapsto\operatorname{Map}_D(F(c),d)` を表現する対象から得る。左随伴の値は共変関手 $`c\mapsto\operatorname{Map}_D(d,F(c))` を共表現する対象から得る。

:::

:::proposition "htt_5_5_2_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_rightAdjoint_iff_preservesSmallColimits_of_representability_native, SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.presentableContinuous_isRepresentable")
*HTT 注意 5.5.2.10*　標的の局所小性に弱めた右随伴定理（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=484)）。対応表の状態：一部（stronger-hyp）。

*主張*　右随伴の存在を小余極限の保存から導く際、可提示な始域に対し、終域には本質的な局所小性で足りる。

KB-W2原文・型再照合：仮定：presentable な始域と accessible な標的 D（Lean が強い：原典の局所小性だけより強いが、D の presentability は不要）。結論：元の F が右随伴を持つことと全小余極限保存の iff（この場合に一致）。必要な始域上の全連続前層の表現定理は presentableContinuous\_isRepresentable で供給でき、未証明の比較仮定ではない。

終域の写像空間を使って始域上に空間値関手を作り、始域で表現可能性を適用する。終域の生成性はこの手順に現れない。

:::

# 5.5.3 Limits and Colimits of Presentable ∞-Categories

%%%
number := false
tag := "htt-5-5-3"
%%%

:::definition "htt_5_5_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrL, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrR, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace")
*HTT 定義 5.5.3.1*　表示可能準圏の高次圏 PrL と PrR（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=484)）。対応表の状態：本体にある。

*主張*　$`\operatorname{Pr}^L` と $`\operatorname{Pr}^R` の対象は可提示 ∞ 圏で、射にはそれぞれ小余極限保存関手と、可到達な小極限保存関手を取る。

仮定：固定宇宙の presentable な準圏（HTT と一致）。結論：全小余極限保存関手を射とする PrL と、accessible で全小極限保存な関手を射とする PrR を、それらの全関手同値の Kan core を豊穣 Hom とする coherent nerve で構成する（一致）。関手の同型類の集合だけへ商を取らない。

随伴関手定理によって、前者の射は左随伴、後者の射は右随伴である。随伴を取り替える操作は射の向きを逆にする。

:::

:::definition "htt_5_5_3_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration, SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable")
*HTT 定義 5.5.3.2*　表示可能ファイブレーションの定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=485)）。対応表の状態：本体にある。

*主張*　単体集合の射が可提示ファイブレーションであるとは、デカルトかつ余デカルトであり、各頂点上のファイバーが可提示であることである。

仮定：単体集合の射 p:X→S と各頂点ファイバー（HTT と一致）。結論：Cartesian と cocartesian の両ホーン持ち上げ条件、および各実ファイバーの presentability の三条件をそのまま組み合わせて定義できる（一致）。単に分類関手の各値だけを条件に置き換えていない。

底の辺に沿って二方向の移送を取ると、ファイバー間の随伴が得られる。定義では各ファイバーに可提示性を課す。

:::

:::proposition "htt_5_5_3_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet_isPresentable")
*HTT 命題 5.5.3.5*　表示可能準圏の小積（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=485)）。対応表の状態：本体にある。

*主張*　小さい集合で添字付けられた可提示 ∞ 圏の積は可提示である。

仮定：小族の各準圏が presentable（HTT と一致）。結論：同じ全単体を成分ごとに取った積準圏が presentable（一致）。空族も含む。

可到達性は小さい積に関する閉性から従い、小余極限は各座標で計算する。

:::

:::proposition "htt_5_5_3_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functor_isPresentable") (uses := "htt_1_1_2_4, htt_5_1_2_2, htt_5_4_4_3, htt_5_5_0_1")
*HTT 命題 5.5.3.6*　表示可能な値を持つ関手準圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=485)）。対応表の状態：一部（special）。

*主張*　可提示 ∞ 圏 $`C` と小さい単体集合 $`K` に対して、関手圏 $`\operatorname{Fun}(K,C)` は可提示である。

KB-W2原文・型再照合：仮定：presentable C と小準圏 K（Lean が強い：任意の小単体集合でなく準圏形状）。結論：元の Fun(K,C) が presentable（この形状の場合に一致）。非準圏形状の fibrant 模型との比較を仮定して一般化しない。

可到達性は小さい図式圏の定理から、小余極限は各点での余極限の計算から得られる。

:::

:::proposition "htt_5_5_3_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheaf_isPresentable")
*HTT 注意 5.5.3.7*　前層準圏の表示可能性と自由性への解釈（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=486)）。対応表の状態：一部（component）。

*主張*　小さい単体集合 $`S` の空間値前層圏 $`\mathcal P(S)` は可提示であり、米田写像は可提示圏への関手に対する自由な余極限完備化を与える。

KB-W2原文・型再照合：仮定：小準圏 S（Lean が強い：任意の小単体集合でなく準圏）。結論：P(S) が presentable（第一の結論に一致）。S↦P(S) を全 Cat∞ から PrL への左随伴として構成する全高次の自然性までは含まない。

$`\mathcal P(S)` から可提示圏 $`D` への小余極限保存関手を米田写像で制限すると、$`S` から $`D` への関手が得られる。普遍性はその制限が関手圏の同値となる形で表される。

:::

:::proposition "htt_5_5_3_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isPresentable_iff_equivalence")
*HTT 命題 5.5.3.10*　表示可能準圏の上圏の表示可能性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=487)）。対応表の状態：一部（special）。

*主張*　可提示 ∞ 圏 $`C` の小さい図式 $`p` に対し、上の圏 $`C_{/p}` は可提示である。

KB-W2原文・型再照合：仮定：presentable C と終対象 x の一点図式（Lean が強い：一般の小図式 p を終対象の一点に限定）。結論：同じ C/x の元の射影が全準圏同値であるため C/x は presentable（この場合に一致）。元の射影の同値は終対象の境界条件から構成でき、別の圏との未供給比較ではない。

上の圏の可到達性に加え、指定された図式への錐を小余極限でまとめられることを使う。錐の頂点から出る矢印は余極限の普遍性で誘導される。

:::

:::proposition "htt_5_5_3_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_iff_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isPresentable_iff_equivalence") (uses := "htt_1_1_2_4, htt_5_4_5_16")
*HTT 命題 5.5.3.11*　表示可能準圏の下圏の表示可能性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=487)）。対応表の状態：一部（special）。

*主張*　可提示 ∞ 圏 $`C` の小さい図式 $`p` に対し、下の圏 $`C_{p/}` は可提示である。

KB-W2原文・型再照合：仮定：presentable C と始対象 x の一点図式（Lean が強い：p を始対象の一点に限定）。結論：同じ Cx/ の元の射影が全準圏同値なので Cx/ は presentable（この場合に一致）。一般の小図式の下圏の compact 生成性は結論しない。

下の圏は可到達である。余錐をまとめるときは固定した始域からの射も保存する必要があり、頂点の余極限を取るだけでは処理できない図式もある。例えば空図式の余極限は $`p` の余極限余錐である。

:::

:::proposition "htt_5_5_3_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullback_isPresentable_of_accessiblePullback, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.pullback_isAccessible, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pullback_preservesSmallColimits_iff_components") (uses := "htt_1_1_2_4, htt_5_5_0_1, kerodon_7_1_9_8, kerodon_9_5_4_6")
*HTT 命題 5.5.3.12*　表示可能な余極限保存関手の引き戻し（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=487)）。対応表の状態：一部（special）。

*主張*　可提示 ∞ 圏と小余極限保存関手のホモトピー引き戻しは可提示であり、そこへの関手の小余極限保存性は引き戻しの両射影で判定できる。

KB-W2原文・型再照合：仮定：presentable な三準圏と全小余極限保存な両脚（Lean が強い：元の平方は一方が categorical lifting を持つ strict pullback）。結論：同じ引き戻しが presentable、元の引き戻しへの関手の全小余極限保存の成分判定（この模型で一致）。汎用 accessibility 命題の入力は実証済みの AccessiblePullback.pullback\_isAccessible で供給できる。

可到達性と成分ごとの余極限の定理を合わせる。原典の合成が定義されるよう、$`f` の終域は引き戻しの頂点 $`X'` と読む。恒等関手を取ると両射影も小余極限を保つ。

:::

:::corollary "htt_5_5_3_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.InitialSectionLifting.cocartesianSectionsEvaluate_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isPresentable_iff_equivalence")
*HTT 系 5.5.3.14*　表示可能族の余カルテジアン切断の表示可能性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=488)）。対応表の状態：一部（special）。

*主張*　小さい底上の可提示ファイブレーションの余デカルト切断の ∞ 圏は可提示である。

KB-W2原文・型再照合：仮定：presentable fibration p:X→S（Lean が強い：小基底 S は始対象 s を持つ準圏）。結論：同じ全 coCartesian 切断準圏の s での評価が実ファイバー Xs との全準圏同値であるため、同じ切断準圏が presentable（この場合に一致）。一般の小 S の極限や、coCartesian 条件を課さない全切断へは拡張しない。

底の各点への評価を通じて余デカルト切断を整合条件つきの族として扱う。各ファイバーの可提示性と、余デカルト移送が左随伴として小余極限を保つことが使われる。

:::

# 5.5.4 Local Objects

%%%
number := false
tag := "htt-5-5-4"
%%%

:::definition "htt_5_5_4_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalForHom")
*HTT 定義 5.5.4.1*　辺族に対する局所対象と局所同値（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=491)）。対応表の状態：本体にある。

*主張*　射の族 $`S` に対し、$`S`-局所対象は $`S` の各射を写像空間への前合成で同値に移す対象であり、$`S`-同値は全局所対象への写像空間で同値を誘導する射である。

仮定：準圏 C と元の一次単体の集合 S（HTT と一致）。結論：S の各辺による Map(Y,Z)→Map(X,Z) が空間同値となる対象、および全局所対象が検出する同値としての S-equivalence を定義する（一致）。

$`s:x\to y` に対して検査する向きは $`\operatorname{Map}(y,z)\to\operatorname{Map}(x,z)` である。同じ形の検査を使い、先に対象を定めてから射の類を定める。

:::

:::proposition "htt_5_5_4_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.reflective_isLocal_iff_invertedEdges, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.reflective_localEquivalences_eq")
*HTT 命題 5.5.4.2*　反射の局所対象と反転辺による判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=491)）。対応表の状態：一部（component）。

*主張*　局所化 $`L` が同値に移す射を $`S` とすると、局所対象は $`L` の本質像、$`S`-同値は $`S` に一致する。可到達な始域では、局所化の可到達性は小さい部分族で局所対象を検査できることと同値である。

KB-W2原文・型再照合：仮定：任意の準圏の指定反射 r（HTT と一致）。結論：反射の像とその反転辺に局所な対象の一致、および S-equivalence がちょうど反転辺である (1)(2)（一致）。(3) の一般の accessible C における三条件同値は含まない。

局所化の単位を使うと、$`S`-局所な対象が局所化済みであることが分かる。可到達性の判定は、$`L` 自身にも局所対象の圏にも適用できる。

:::

:::definition "htt_5_5_4_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.IsStronglySaturatedEdgeSetOfShapes")
*HTT 定義 5.5.4.5*　余極限に関する辺集合の強飽和性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=494)）。対応表の状態：本体にある。

*主張*　強飽和な射の類は、押し出し、矢印圏での小余極限、および 2 単体の三辺に対する二つから三つの規則で閉じている。

仮定：全小余極限を持つ準圏と辺集合（HTT と一致）。結論：押し出し・射準圏内の全小余極限・二対三則で強飽和性を定義する（一致）。Lean は同値を含むことも明記するが、全余極限と押し出しから HTT 5.5.4.6 により従う同じ条件である。

余極限の操作では射の始域と終域の両方を動かせる。二つから三つの規則には、合成に加えて合成から一つの因子を取り出す判定も含まれる。

:::

:::proposition "htt_5_5_4_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.IsStronglySaturatedEdgeSetOfShapes, SerrePositivity.InfinityCategories.HTT.Section5_5_4.stronglySaturated_mem_iff_of_homMk_eq")
*HTT 注意 5.5.4.6*　強飽和類の同値包含と辺の代表変更（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=495)）。対応表の状態：一部（component）。

*主張*　強飽和類は全同値を含み、ホモトピーとレトラクトで閉じている。

KB-W2原文・型再照合：仮定：全小余極限を持つ準圏と強飽和辺集合（HTT と一致）。結論：全可逆辺の包含と、同じホモトピー圏の射を表す同端点の辺の所属不変性（明示された二つの結論に一致）。一般の retract に対する閉性はこの宣言には含まない。

空の余極限で始対象の恒等射が入るため、その押し出しとして同値が入る。同一の始域・終域を持つホモトピックな射の比較も押し出しで得られ、レトラクトは矢印圏での余極限を使って扱える。

:::

:::proposition "htt_5_5_4_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.stronglySaturatedClosure, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.subset_stronglySaturatedClosure, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.stronglySaturatedClosure_minimal, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.stronglySaturatedClosure_stronglySaturated, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.IsOfSmallStrongGeneration")
*HTT 注意 5.5.4.7*　強飽和生成閉包と小生成性の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=495)）。対応表の状態：本体にある。

*主張*　強飽和類の交叉は強飽和なので、任意の射の族は最小の強飽和類を生成する。小さい族で生成できるとき小生成と呼ぶ。

仮定：準圏 C と小余極限の宇宙および辺集合（HTT と一致）。結論：全強飽和上集合の共通部分、最小性、強飽和性、および小族で生成される条件を定義し証明する（一致）。共通部分の各閉性条件は同じ全称条件のままである。

生成とは、押し出し・小余極限・二つから三つの規則を課した上で、指定の射を含む最小の類を取ることである。

:::

:::lemma_ "htt_5_5_4_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.localEquivalences_stronglySaturated")
*HTT 補題 5.5.4.11*　局所同値の辺集合の強飽和性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=496)）。対応表の状態：本体にある。

*主張*　小余極限を持つ ∞ 圏で、任意の射の族 $`S_0` に対する $`S_0`-同値の全体は強飽和である。

仮定：全小余極限を持つ準圏 C と任意の辺集合 S0（HTT と一致）。結論：全 S0-local 対象により検出される元の辺集合が、小形状の押し出し・射余極限・二対三則で強飽和（一致）。反射の存在は入力でない。

任意の局所対象への写像空間は余極限を極限に移す。押し出しと矢印圏の余極限で同値の判定が保たれ、合成に対して二つから三つの規則が成り立つ。

:::

:::lemma_ "htt_5_5_4_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSource_small_colimit_mem")
*HTT 補題 5.5.4.12*　強飽和類の固定始域射圏の余極限閉性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=496)）。対応表の状態：一部（stronger-hyp）。

*主張*　小余極限を持つ ∞ 圏で、強飽和類に属する固定始域 $`c` からの射の充満部分圏は、下の圏 $`C_{c/}` の小余極限で閉じている。

Cをpresentable、Sを小さい辺族の強飽和生成閉包に限定すると、generatedSource\_small\_colimit\_memは同じCx/のS辺の余錐が再びSに属すると直接示す。一般の強飽和Sと単に小余完備なCへの拡張は含まない。

下の圏では始域を固定した余極限を取る。矢印圏で始域も一緒に余極限にした後、始域を戻す押し出しを使うことで強飽和性を適用できる。

:::

:::lemma_ "htt_5_5_4_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory_isPresentable")
*HTT 補題 5.5.4.14*　強飽和射圏の表示可能性と小生成性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=498)）。対応表の状態：一部（direction）。

*主張*　可提示 ∞ 圏の強飽和類が小生成であることと、その射の矢印圏内の充満部分圏が可到達であること、可提示であることは同値である。

KB-W2原文・型再照合：仮定：presentable C と小生成な強飽和 S（HTT と一致、小生成性の定義の辺族を用いる）。結論：同じ S の全射準圏が presentable、従って accessible という (3)⇒(2)⇒(1)（一致）。accessible な任意の強飽和射圏から小生成族を回収する逆向きは結論しない。

強飽和性はすでに矢印圏内の小余極限に関する閉性を含む。可到達なら、小さいコンパクト生成系から強飽和類の生成元を得られる。

:::

:::proposition "htt_5_5_4_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_bousfieldLocalReplacement, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalObjects_isPresentable, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldReflection, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfield_generatedEdges_eq_localEquivalences, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfield_generatedEdges_eq_invertedEdges")
*HTT 命題 5.5.4.15*　小辺族による Bousfield 局所化の存在（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=500)）。対応表の状態：本体にある。

*主張*　可提示 ∞ 圏の小さい射の族 $`S` に対し、局所対象は可提示な反射部分圏をなし、反射が同値にする射は $`S`-同値、すなわち $`S` の強飽和閉包に一致する。

仮定：presentable C と小さい元の辺族（HTT と一致）。結論：強飽和生成閉包内の辺による全対象の局所置換、元の局所対象全部分圏の presentability・反射、および局所同値＝強飽和生成閉包＝同じ反射の反転辺という (1)–(4)（一致）。局所置換や反射の存在を追加で仮定しない。

任意の対象から局所対象への射を強飽和閉包の中で選べる。局所対象への写像空間でその射が同値を誘導するため、この選択は反射の単位となる。

:::

# 5.5.5 Factorization Systems on Presentable ∞-Categories

%%%
number := false
tag := "htt-5-5-5"
%%%

:::definition "htt_5_5_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.IsStronglySaturatedEdgeSetOfShapes")
*HTT 定義 5.5.5.1*　表示可能圏の飽和射類の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=503)）。対応表の状態：一部（stronger-hyp）。

*主張*　可提示 ∞ 圏の射の類が飽和であるとは、同値を含み、合成・押し出し・矢印圏の小余極限で閉じていることである。

同じ辺集合SにIsStronglySaturatedEdgeSetOfShapesを課すと、定義の最初の四成分が可逆辺の包含、pushout閉性、小余極限閉性、合成閉性を直接与え、原文のsaturated条件を満たす。余分なtwo-out-of-three条件を外した一般の述語は供給しない。

強飽和性で使う二つから三つの規則のうち、この定義で要求するのは合成に関する閉性である。

:::

:::proposition "htt_5_5_5_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.IsStronglySaturatedEdgeSetOfShapes")
*HTT 例 5.5.5.5*　強飽和類は飽和類でもある（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=504)）。対応表の状態：本体にある。

*主張*　可提示 ∞ 圏の強飽和な射の類は飽和である。

仮定：presentable C の強飽和な元の辺集合 S（HTT と一致）。結論：同じ S の全射余極限・同値包含と合成・押し出しという飽和性の三条件（一致）。定義の各成分をそのまま取り出せるので、別の生成閉包への同定は不要。

強飽和類には同値が入り、三辺の規則から合成で閉じる。押し出しと矢印圏の小余極限については、両方の定義で同じ条件を用いる。

:::

:::lemma_ "htt_5_5_5_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory_isPresentable")
*HTT 補題 5.5.5.9*　飽和射圏の表示可能性と小生成性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=505)）。対応表の状態：一部（stronger-hyp）。

*主張*　可提示 ∞ 圏の飽和類が小生成であることは、その射を対象とする矢印圏の充満部分圏が可提示であることと同値である。

KB-W2原文・型再照合：仮定：presentable C と小生成飽和 S（Lean が強い：S は小さい辺族の強飽和生成閉包）。結論：同じ S の全射準圏の presentability（この場合の小生成性から表示可能性に一致）。任意の飽和生成閉包や逆向きの生成族回収は結論しない。

ここでの生成は飽和閉包、つまり同値・合成・押し出し・小余極限を課した閉包を指す。

:::

:::lemma_ "htt_5_5_5_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSource_small_colimit_mem")
*HTT 補題 5.5.5.11*　飽和類の固定始域射圏の余極限閉性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=507)）。対応表の状態：一部（stronger-hyp）。

*主張*　可提示 ∞ 圏の飽和類に属する $`x` からの射は、下の圏 $`C_{x/}` の小余極限で閉じている。

KB-W2原文・型再照合：仮定：presentable C と飽和 S および X（Lean が強い：S は小さい辺族の強飽和生成閉包）。結論：同じ Cx/ 内の S の全部分圏の任意の指定小余極限が再び S に属する（この場合に一致）。単なる抽象的な余極限の存在だけでなく、元の包含先での余錐を扱う。

固定した始域からの射をまとめるには、矢印圏の余極限の後に始域を調整する。飽和性の押し出しに関する条件がここで使える。

:::

:::lemma_ "htt_5_5_5_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_bousfieldLocalReplacement, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalObject_stronglySaturatedClosure_iff")
*HTT 補題 5.5.5.14*　小生成飽和類の局所対象への置換（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=509)）。対応表の状態：一部（stronger-hyp）。

*主張*　可提示 ∞ 圏の小生成な飽和類 $`S` に対し、各対象 $`x` から $`S`-局所対象 $`y` への射を $`S` の中で選べる。

KB-W2原文・型再照合：仮定：presentable C と小生成飽和 S（Lean が強い：S は小さい辺族の強飽和生成閉包）。結論：各 X から同じ S 内の辺で S-local Y に写す置換（この場合に一致）。局所対象は元の族と強飽和閉包で同じであり、小族への局所性だけを未比較のまま渡さない。

小さい生成族を使って持ち上げに必要な射を順に加える。結論は最終的な射が元の飽和類に属するところまで含む。

:::

# 5.5.6 Truncated Objects

%%%
number := false
tag := "htt-5-5-6"
%%%

:::definition "htt_5_5_6_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex")
*HTT 定義 5.5.6.1*　写像空間による切断対象の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=511)）。対応表の状態：一部（special）。

*主張*　対象 $`c` が $`k`-切断されているとは全ての $`\operatorname{Map}(d,c)` が $`k`-切断空間であることで、$`k=-2` は終対象、$`k=0` は離散対象を指す。

KB-W2原文・型再照合：仮定：準圏 C と整数 k≥−2（Lean が強い：k=−2 に限定）。結論：−2 切断対象を終対象とする明示された規約を、元の終対象述語で表す（この部分に一致）。全 k の写像空間のホモトピー群による切断性や全部分圏の族は定義していない。

$`k\ge -1` の写像空間による定義と終対象の規約を合わせ、$`\tau_{\le k}C` はこの条件を満たす対象の充満部分圏とする。

:::

:::lemma_ "htt_5_5_6_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex")
*HTT 補題 5.5.6.3*　切断対象の高次境界充填による判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=511)）。対応表の状態：一部（special）。

*主張*　$`k\ge-2` に対し、対象 $`c` が $`k`-切断されていることは、最終頂点を $`c` に送る $`\partial\Delta^n` の図式が全ての $`n\ge k+3` で $`\Delta^n` に延びることで判定できる。

KB-W2原文・型再照合：仮定：準圏 C の対象と k≥−2（Lean が強い：k=−2 に限定）。結論：終対象 iff 最後の頂点を固定した全正次元境界の充填、という本文の n≥k+3 の条件そのもの（この場合に一致）。IsTerminalVertex の定義を展開すると両条件は同一で、一般の切断性は仮定しない。

最後の頂点を固定することで、対象 $`c` に入る写像空間の高次の球面の充填を単体集合の条件で表す。

:::

:::proposition "htt_5_5_6_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_isTerminalVertex_of_contractibleFiber")
*HTT 注意 5.5.6.6*　余カルテジアン族のファイバーと全空間の切断性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=512)）。対応表の状態：一部（special）。

*主張*　余デカルト・ファイブレーション $`p:C\to D` で、対象 $`c` がそのファイバーで $`k`-切断され、$`p(c)` が底で $`k`-切断されていれば、$`c` は全体でも $`k`-切断されている。

KB-W2原文・型再照合：仮定：coCartesian p:E→B とファイバー・基底で k 切断な点（Lean が強い：k=−2、p は left fibration、指定ファイバーは可縮 Kan）。結論：同じファイバーの指定点は元の全空間 E の終対象、従って −2 切断（この場合に一致）。元の点を保持し、全空間の弱可縮性だけで代用しない。

$`d\to c` の写像空間を底の写像空間に写す。指定された底の辺上のホモトピーファイバーは、$`d` を余デカルト移送した後のファイバー内の写像空間である。底と各ファイバーの切断性から全体の切断性を得る。

:::

# 5.5.7 Compactly Generated ∞-Categories

%%%
number := false
tag := "htt-5-5-7"
%%%

:::definition "htt_5_5_7_1" (lean := "SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible")
*HTT 定義 5.5.7.1*　κ コンパクト生成準圏の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=519)）。対応表の状態：本体にある。

*主張*　$`\kappa`-コンパクト生成 ∞ 圏とは、可提示かつ $`\kappa`-可到達な ∞ 圏である。単にコンパクト生成という場合は $`\kappa=\omega` を指す。

仮定：正則 κ と準圏 C（HTT と一致）。結論：κ-compactly generated を presentable かつ κ-accessible とする条件と κ=ℵ0 の規約を、元の二述語の連言で表せる（一致）。定義後の全高次圏の同値はこの定義の行に含めない。

小さい $`\kappa`-コンパクト対象の圏を選べば、その $`\operatorname{Ind}_\kappa` 完備化で全体を表せる。この小さい圏は $`\kappa`-小余極限を持つ。

:::

:::proposition "htt_5_5_7_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.adjunction_isKappaCompact_image") (uses := "htt_5_1_2_2, htt_5_3_1_7, htt_5_3_4_5")
*HTT 命題 5.5.7.2*　随伴の連続性とコンパクト対象の保存（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=519)）。対応表の状態：一部（direction）。

*主張*　小さい $`\kappa`-濾過余極限を持つ圏の間の随伴では、右随伴のその余極限の保存から左随伴の $`\kappa`-コンパクト性の保存が従い、左側の圏が $`\kappa`-可到達なら逆も成り立つ。

KB-W2原文・型再照合：仮定：κ-filtered 余極限を持つ準圏の指定随伴 L⊣R と κ-continuous な R（HTT と一致）。結論：L が同じ κ-compact 対象を κ-compact に送る (1)（一致）。C が κ-accessible のときの逆方向 (2) は、この全般性の公開型には含まない。

逆向きには、右随伴の余極限比較射を始域の $`\kappa`-コンパクト生成対象からの写像空間で検査する。随伴で移した生成対象もコンパクトなので比較が同値になる。

:::

:::corollary "htt_5_5_7_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.reflectiveImage_isKappaAccessible") (uses := "htt_1_1_2_4, htt_5_3_1_7, htt_5_3_4_5, htt_5_5_7_2")
*HTT 系 5.5.7.3*　κ 連続な局所化のコンパクト生成性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=519)）。対応表の状態：一部（stronger-hyp）。

*主張*　$`\kappa`-コンパクト生成圏の局所化が $`\kappa`-濾過余極限を保つことは局所対象のその余極限での閉性と同値であり、このとき局所化先も $`\kappa`-コンパクト生成である。

KB-W2原文・型再照合：仮定：κ-compactly generated C の指定反射 L⊣R（Lean が強い：包含 R の κ-continuity、反射像の全小余極限と固定頂点写像の小ささを明示）。結論：同じ反射像の κ-accessibility、仮定した余完備性と合わせ κ-compact generation という (4)（一致）。L 自身の κ-continuity との iff や retract の特徴づけは結論しない。

局所化は $`\kappa`-コンパクト対象を局所化先のコンパクト対象に移す。局所化先の $`\kappa`-コンパクト対象はちょうどそのような像のレトラクトである。原典の (5) の compact は (3) と証明で使う $`\kappa`-compact として読む。

:::

# 5.5.8 Nonabelian Derived Categories

%%%
number := false
tag := "htt-5-5-8"
%%%

:::definition "htt_5_5_8_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity")
*HTT 定義 5.5.8.1*　sifted 単体集合の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=524)）。対応表の状態：本体にある。

*主張*　単体集合 $`K` が篩状であるとは、空でなく、対角写像 $`K\to K\times K` が共終であることである。

仮定：任意の小単体集合 K（HTT と一致、準圏性を要求しない）。結論：非空性と二項対角の right cofinality という二条件で sifted 性を定義する（一致）。

対角の共終性によって、二変数を別々に動かす余極限と、一つの添字を両変数に入れる余極限を比較できる。

:::

:::proposition "htt_5_5_8_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.isSiftedInfinity_of_filtered")
*HTT 例 5.5.8.3*　フィルター準圏の sifted 性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=524)）。対応表の状態：本体にある。

*主張*　濾過 ∞ 圏は篩状である。

仮定：任意の filtered 準圏 K（HTT と一致）。結論：同じ K が非空で二項対角 right cofinal、従って sifted（一致）。

濾過性は空でないことを含み、二つの対象や有限の整合性のデータを同じ段階で受け止められるので、対角の共終性が得られる。

:::

:::lemma_ "htt_5_5_8_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.smallSimplexOpposite_isSiftedInfinity")
*HTT 補題 5.5.8.4*　単体添字の反対圏の sifted 性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=524)）。対応表の状態：本体にある。

*主張*　単体圏 $`\Delta` の反対圏の nerve は篩状である。

仮定：小宇宙の単体圏の反対の神経（HTT と一致、SmallSimplexOpposite は同じ添字の宇宙持ち上げ）。結論：元の N(Δop) が sifted（一致）。

したがって単体的対象の幾何学的実現は篩状余極限の例になる。ここで検査する対角は $`N(\Delta)^{\mathrm{op}}` の対角である。

:::

:::proposition "htt_5_5_8_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.coherentProductTotalKanComparison_homotopyEquivalence")
*HTT 命題 5.5.8.6*　各変数の sifted 保存から同時保存へ（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=525)）。対応表の状態：一部（special）。

*主張*　篩状な $`K` に対し、$`K`-型余極限を別々の変数で保つ二変数関手は、一緒に動かした $`K`-型余極限も保つ。

KB-W2原文・型再照合：仮定：sifted K と各変数で K 余極限を保つ二変数関手（Lean が強い：C=D=E=Space、二変数関手は積）。結論：元の二つの coherent 空間図式の点ごとの積の余極限と両余極限の積を比較する同じ射が単体的ホモトピー同値（この積の場合に一致）。単位と元の二射影の比較を伴う。

二つの余極限を順に取り、$`K\times K` 上の余極限として扱う。対角の共終性によってもとの $`K` に戻せる。

:::

:::proposition "htt_5_5_8_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.isWeaklyContractible_of_sifted")
*HTT 命題 5.5.8.7*　sifted 単体集合の弱可縮性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=525)）。対応表の状態：本体にある。

*主張*　篩状な単体集合は弱可縮である。

仮定：任意の sifted 単体集合 K（HTT と一致）。結論：同じ K が弱可縮（一致）。準圏性や特定の Kan 置換の選択を追加入力にしない。

対角の共終性は実現された空間とその二乗の比較に現れる。空でないので成分が一つに絞られ、高次のホモトピー群でも対角が同型になるため非自明な元が残らない。

:::

:::definition "htt_5_5_8_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSigmaPresheaf, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity")
*HTT 定義 5.5.8.8*　有限積保存前層の準圏 PΣ の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=525)）。対応表の状態：本体にある。

*主張*　有限余積を持つ小さい ∞ 圏 $`C` に対し、$`\mathcal P_\Sigma(C)` は有限積を保存する空間値前層の充満部分圏である。

仮定：有限余積を持つ小準圏 C（HTT と一致、Lean の定義自体は存在しない有限積の条件を課さず使える）。結論：Cop→Space の有限積を保つ前層の全高次単体を保持した全部分準圏 PΣ(C)（一致）。

$`C` の有限余積が反対圏では積になる。空の余積も条件に入るため、始対象での前層の値は可縮である。

:::

:::proposition "htt_5_5_8_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigma_exists_reflector, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap_inclusion, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYoneda_finiteCoproduct_isColimit, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.sigmaInclusion_preservesSmallSiftedColimits")
*HTT 命題 5.5.8.10*　有限積保存前層の反射と閉性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=525)）。対応表の状態：一部（component）。

*主張*　$`\mathcal P_\Sigma(C)` は前層圏の可到達局所化で、篩状余極限で閉じ、コンパクト生成される。米田埋め込みはこの圏で有限余積を保つ。

KB-W2原文・型再照合：仮定：有限余積を持つ小準圏 C（HTT と一致）。結論：元の包含の左随伴の存在、Yoneda の同じ因子化と有限余積保存、および PΣ の sifted 余極限閉性という (1) の反射部分・(2)・(4)（一致）。反射の accessibility、任意の随伴との (3) の iff、(6) の compact generation はこの組には含まない。

前層圏から可提示圏への左随伴の米田制限が有限余積を保つことと、その右随伴が $`\mathcal P_\Sigma(C)` を経由することは同値である。反射を前層圏の自己関手として見ても篩状余極限を保つ。

:::

:::lemma_ "htt_5_5_8_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedCoherentProductNativeCone_isLimit, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedCoherentEmptyProductNativeCone_isLimit")
*HTT 補題 5.5.8.11*　sifted 余極限関手の有限積保存（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=526)）。対応表の状態：一部（special）。

*主張*　篩状な $`K` に対し、有限積と $`K`-型余極限を持つ圏で積が各変数ごとにその余極限を保てば、$`K`-型余極限関手は有限積を保つ。

KB-W2原文・型再照合：仮定：有限積と K 余極限を持ち積が各変数でそれを保つ準圏（Lean が強い：Space の場合）。結論：coherent 空間図式の元の余極限と二項積・空積の比較が実際の極限錐となる（この場合に有限積保存と一致）。任意 X の積保存を仮定して同じ比較を一般化したとはしない。

二項積は二変数の判定で扱える。空の積については $`K` の弱可縮性が使われ、終対象の定値図式の余極限は終対象となる。

:::

:::proposition "htt_5_5_8_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedCoherentProductNativeCone_isLimit, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedCoherentEmptyProductNativeCone_isLimit")
*HTT 注意 5.5.8.12*　空間と高次トポスでの積と sifted 余極限（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=526)）。対応表の状態：一部（component）。

*主張*　空間の ∞ 圏と、さらに一般に任意の ∞ トポスで、篩状余極限は有限積と交換する。

KB-W2原文・型再照合：仮定：小 sifted K（HTT と一致）。結論：Space の元の coherent K 余極限の積・空積との交換（本文の空間の場合に一致）。任意の ∞-topos で各変数の積が余極限を保存するという後半の拡張は含まない。

前項の仮定にある積の余極限保存性を、空間や ∞ トポスで適用できる。積と余極限の交換を示す際には、対象の並びを同じ添字で動かしてよい。

:::

:::lemma_ "htt_5_5_8_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarObject_realization, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarObject_degree_coproduct, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarDegreeDiagram_representable")
*HTT 補題 5.5.8.13*　前層の表現可能余積による単体的表示（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=527)）。対応表の状態：本体にある。

*主張*　小さい ∞ 圏上の任意の空間値前層は、各次数が表現可能前層の小余積となる単体的前層の幾何学的実現で得られる。

仮定：任意の小準圏 C と前層 X（HTT と一致、有限余積の仮定も不要）。結論：同じ前層値の全単体的 bar 図式が X を実現し、各次数は元の表現可能前層の小さい離散余極限であるという (1)(2)（一致）。PresheafBarRealization の全前層版は、PΣ の Ind 値表示に制限されない。

各段には表現可能前層からなる表示を使い、面・退化写像がそれらを一つの前層へ組み立てる。各段が単独で表現可能となる必要はない。

:::

:::lemma_ "htt_5_5_8_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheaf_simplicialIndDiagram, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.sigmaInclusion_preservesSmallSiftedColimits")
*HTT 補題 5.5.8.14*　PΣ 対象の Ind 値単体的表示（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=527)）。対応表の状態：一部（direction）。

*主張*　有限余積を持つ小さい $`C` に対し、前層が $`\mathcal P_\Sigma(C)` に入ることは、$`\operatorname{Ind}(C)` 値の単体的対象の前層圏での実現として書けることと同値である。

KB-W2原文・型再照合：仮定：有限余積を持つ小 C と PΣ(C) の対象 X（HTT と一致）。結論：実際の Ind(C) 値の全単体的図式と PΣ 内の実現 X が存在し、包含は実現を保つので元の P(C) 内でも同じ表示となる (1)⇒(2)（一致）。任意の P(C) 内の Ind 値表示から X の有限積保存を回収する逆向きはこの型の結論に含まない。

有限余積を扱えるため、前層の表示に使う小余積は有限部分から濾過余極限で組み立てられる。逆向きでは、米田像からの濾過余極限と実現が有限積保存性を保つ。

:::

:::proposition "htt_5_5_8_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaFilteredGeometricRestriction_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigma_preservesSmallSiftedColimits_iff_filtered_geometric, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigma_preservesSmallColimits_iff_yoneda_finiteCoproducts_of_filtered_geometric")
*HTT 命題 5.5.8.15*　PΣ の生成操作と関手の普遍性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=528)）。対応表の状態：本体にある。

*主張*　濾過余極限と幾何学的実現を持つ $`D` に対し、これらを保つ $`\mathcal P_\Sigma(C)\to D` の圏は、米田制限で $`\operatorname{Fun}(C,D)` と同値である。

仮定：有限余積を持つ小 C、filtered 余極限と幾何学的実現を持つ D（HTT と一致、(3) には有限余積存在）。結論：元の Yoneda 制限による全関手準圏の同値、生成操作保存から sifted 保存、全小余極限保存 iff 元の C 上で有限余積保存という (1)–(3)（一致）。元の全自然変換と高次単体を保持する。

このように延長した関手は篩状余極限を保つ。さらに $`D` に有限余積がある場合、全小余極限の保存は、制限した関手の有限余積保存で判定できる。

:::

:::corollary "htt_5_5_8_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExactnessAndAnimation.SimplicialObjectsOfInfinityCategories.preservesSmallFiltered_of_sifted, SerrePositivity.InfinityCategories.Kerodon.ExactnessAndAnimation.SimplicialObjectsOfInfinityCategories.preservesSmallGeometric_of_sifted")
*HTT 系 5.5.8.17*　sifted 保存とフィルター・実現保存の判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=529)）。対応表の状態：一部（direction）。

*主張*　小余極限を持つ ∞ 圏を始域とする関手は、濾過余極限と幾何学的実現を保つとき、かつそのときに限り、篩状余極限を保つ。

KB-W2原文・型再照合：仮定：全小余極限を持つ C から任意 D への sifted 余極限保存関手（HTT と一致）。結論：同じ関手は filtered 余極限と幾何学的実現を保つという必要方向（一致）。逆方向の既存の型は始域 PΣ の場合だけで、任意 C への主張を追加議論なしには結論しない。

濾過図式と単体的図式はいずれも篩状である。逆向きには、この二種類で篩状余極限の保存を検査できるという前項の普遍性を使う。

:::

:::definition "htt_5_5_8_18" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExactnessAndAnimation.SimplicialObjectsOfInfinityCategories.PreservesSmallGeometricRealizations, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity")
*HTT 定義 5.5.8.18*　幾何学的実現による射影対象の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=530)）。対応表の状態：本体にある。

*主張*　幾何学的実現を持つ ∞ 圏で、対象 $`p` が射影的であるとは $`\operatorname{Map}(p,-)` が幾何学的実現を保つことである。

仮定：幾何学的実現を持つ準圏 C と対象 P（HTT と一致）。結論：P の全共変表現可能関手が指定した全単体的余極限を保つという projective の定義を、元の Hom 関手と保存述語でそのまま表せる（一致）。通常圏の射に対する持ち上げ性と置き換えない。

ここでの射影性は空間値の共表現関手で測る。実現前の各次数での写像空間をまとめたものが、実現に向かう写像空間と一致することを要求する。

:::

:::proposition "htt_5_5_8_20" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExactnessAndAnimation.SimplicialObjectsOfInfinityCategories.preservesSmallFiltered_of_sifted, SerrePositivity.InfinityCategories.Kerodon.ExactnessAndAnimation.SimplicialObjectsOfInfinityCategories.preservesSmallGeometric_of_sifted, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact")
*HTT 注意 5.5.8.20*　コンパクト射影対象と sifted Hom 保存（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=530)）。対応表の状態：一部（direction）。

*主張*　小余極限を持つ ∞ 圏で、対象がコンパクトかつ射影的であることは、その対象からの写像空間関手が篩状余極限を保つことと同値である。

KB-W2原文・型再照合：仮定：全小余極限を持つ C と対象 X の全 Hom が sifted 余極限を保つ（HTT と一致）。結論：同じ Hom の filtered 余極限・幾何学的実現保存、従って X は compact かつ projective という必要方向（一致）。任意 C の Hom に対する逆方向を始域 PΣ の特別な判定から補わない。

コンパクト性が濾過余極限を、射影性が幾何学的実現を担う。篩状余極限の保存は、その二種類を一つの条件にまとめる。

:::

