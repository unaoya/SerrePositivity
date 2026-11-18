import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Limits.Sifted
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndLeftKanPreservation
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndLeftKanUnitRecovery
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndRestrictionEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PresheafSubcategory
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafNativeDensityKan
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.F2PresentableSiftedFiniteDiagonal
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedContractibility
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedInfinity
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedProductComparison
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedSimplexCategory
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedTerminalComparison
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaReflectorAdjunction
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaRestrictionEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalOpposite
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CoherentTotalColimit

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "9.7 Tensor Products of ∞-Categories" =>
%%%
number := false
tag := "kerodon-9-7"
%%%

Kerodon の 9.7 節（[Tag 06ZD](https://kerodon.net/tag/06ZD)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 9.7.1 Relative Cocompletion

%%%
number := false
tag := "kerodon-9-7-1"
%%%

Kerodon [Tag 06ZF](https://kerodon.net/tag/06ZF)

:::definition "kerodon_9_7_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestriction_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaSiftedContinuousRestriction_isQCatEquivalence")
Kerodon Definition 9.7.1.1（[Tag 06ZG](https://kerodon.net/tag/06ZG)）。対応表の状態：一部。

Qを空、Kを全小κ-filtered形状、Hを小準圏Cの標準indYonedaに限ると、Indのκ-filtered余完備性とindKappaContinuousRestriction\_isQCatEquivalenceは同じHの余完備化条件を直接満たす。任意の関係Qは含まない。

:::

:::theorem "kerodon_9_7_1_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestriction_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaSiftedContinuousRestriction_isQCatEquivalence")
Kerodon Theorem 9.7.1.4（[Tag 06ZK](https://kerodon.net/tag/06ZK)）。対応表の状態：一部。

Qを空、Kを全小κ-filtered形状、Hを小準圏Cの標準indYonedaに限ると、Indのκ-filtered余完備性とindKappaContinuousRestriction\_isQCatEquivalenceは同じHの余完備化条件を直接満たす。任意の関係Qは含まない。

:::

:::proposition "kerodon_9_7_1_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigma_exists_reflector, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity")
Kerodon Proposition 9.7.1.6（[Tag 06ZM](https://kerodon.net/tag/06ZM)）。対応表の状態：一部。

Cが有限余積を持ちQをその余積図式とする標準Σ前層の場合、sigma\_exists\_reflectorは同じ有限余積を積へ送る前層部分の反射随伴という(1)の成分を直接返す。任意Qと数値λでの(2)は含まない。

:::

:::definition "kerodon_9_7_1_10"
Kerodon Construction 9.7.1.10（[Tag 06ZR](https://kerodon.net/tag/06ZR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：小 κ-filtered 余極限で閉じた Ind の頂点と、別途指定した辺族での Bousfield 局所化はある。指定した余錐を余極限にする相対前層模型で、任意の K に関する最小閉部分圏を取る原文の H は未確認。

:::

:::lemma_ "kerodon_9_7_1_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_exists_leftKanExtension_with_recovery, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indLeftKanExtension_preservesSmallKappaFilteredColimits")
Kerodon Lemma 9.7.1.11（[Tag 06ZS](https://kerodon.net/tag/06ZS)）。対応表の状態：一部。

Qを空、Hを標準indYoneda、Kを全小κ-filtered形状に限ると、ind\_exists\_leftKanExtension\_with\_recoveryとindLeftKanExtension\_preservesSmallKappaFilteredColimitsは原文の同じfの左Kan延長F、その回収同型、FのK-余連続性という存在の結論を直接与える。任意Qと指定変換αの全iffは含まない。

:::

:::corollary "kerodon_9_7_1_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indLeftKanExtension_preservesSmallKappaFilteredColimits")
Kerodon Corollary 9.7.1.12（[Tag 06ZT](https://kerodon.net/tag/06ZT)）。対応表の状態：一部。

Qを空、Hを標準indYoneda、Kを全小κ-filtered形状に限ると、indLeftKanExtension\_preservesSmallKappaFilteredColimitsは同じFと恒等単位の左Kan性からFのκ-filtered余極限保存を直接返す。(1)⇒(2)のこの場合で、任意Qと逆向きは含まない。

:::

:::corollary "kerodon_9_7_1_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafNativeDensityKan.presheafIdentity_isLeftKanExtension")
Kerodon Corollary 9.7.1.13（[Tag 06ZU](https://kerodon.net/tag/06ZU)）。対応表の状態：一部。

Qを空、Kを全小形状、Hを標準Yonedaに限るとpresheafIdentity\_isLeftKanExtensionは同じ恒等関手の恒等単位の左Kan性、すなわち原文のdenseを直接返す。

:::

:::corollary "kerodon_9_7_1_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isFullyFaithful")
Kerodon Corollary 9.7.1.14（[Tag 06ZV](https://kerodon.net/tag/06ZV)）。対応表の状態：一部。

Qを空、Hを小準圏Cの標準indYonedaに限るとindYoneda\_isFullyFaithfulは原文の同じHの充満忠実性を直接返す。この場合右辺の関係条件は空であり、任意Qのiffは含まない。

:::

:::corollary "kerodon_9_7_1_15"
Kerodon Corollary 9.7.1.15（[Tag 06ZW](https://kerodon.net/tag/06ZW)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単体集合の濃度制限と、コンパクト生成モデルの濃度変更はある。指定余錐を持つ相対 K-余完備化の本質的 λ-小ささを、λ の指数共終性から導く型は未確認。

:::

:::definition "kerodon_9_7_1_16"
Kerodon Definition 9.7.1.16（[Tag 06ZX](https://kerodon.net/tag/06ZX)）。対応表の状態：なし。

Σ前層上の保存性のiffは原文のK0⊂Kによる指定制限関手の全準圏同値を返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigma_preservesSmallColimits_iff_yoneda_of_cocomplete`

:::

:::proposition "kerodon_9_7_1_20"
Kerodon Proposition 9.7.1.20（[Tag 0701](https://kerodon.net/tag/0701)）。対応表の状態：なし。

Σ前層上の保存性判定とsifted関手の制限同値は、原文の全K-余連続関手とK0-余連続関手の同じ制限を比較していない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigma_preservesSmallColimits_iff_yoneda_of_cocomplete`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaSiftedContinuousRestriction_isQCatEquivalence`

:::

:::corollary "kerodon_9_7_1_22"
Kerodon Corollary 9.7.1.22（[Tag 0703](https://kerodon.net/tag/0703)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定された圏からの Ind の制限同値と小余極限を保つ関手の PrL の構成はある。二つの形状族の準圏の圏の包含に対し、相対余完備化を左随伴にする結果は未確認。

:::

# 9.7.2 Digression: Sifted ∞-Categories

%%%
number := false
tag := "kerodon-9-7-2"
%%%

Kerodon [Tag 02QD](https://kerodon.net/tag/02QD)

:::definition "kerodon_9_7_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity, CategoryTheory.IsSifted, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.nonemptyFiniteDiagonal_isRightCofinal")
Kerodon Definition 9.7.2.1（[Tag 02QE](https://kerodon.net/tag/02QE)）。対応表の状態：一部。

IsSiftedInfinityのfield diagonal\_rightCofinalは原文の有限集合Iが二点の場合の同じ対角のright cofinal性を直接与える。nonemptyFiniteDiagonal\_isRightCofinalは非空有限反復積へ拡張するが、任意有限集合と空添字を含む定義全体の比較は含まない。

:::

:::definition "kerodon_9_7_2_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.nonemptyFiniteDiagonal_isRightCofinal, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_iff_isRightCofinal_op")
Kerodon Variant 9.7.2.3（[Tag 02QG](https://kerodon.net/tag/02QG)）。対応表の状態：一部。

反対のIsSiftedInfinityとisLeftCofinal\_iff\_isRightCofinal\_opにより同じ有限対角の左余終性の条件を与える。空集合の場合と積・opの全比較はこの引用だけに含まない。

:::

:::proposition "kerodon_9_7_2_5"
Kerodon Proposition 9.7.2.5（[Tag 02QJ](https://kerodon.net/tag/02QJ)）。対応表の状態：なし。

通常圏のsifted性のFinal/同値不変性は、原文の単体集合のright cofinal性・categorical equivalenceへの比較を含まない。

宣言：`CategoryTheory.IsSifted.of_final_functor_from_sifted`

:::

:::proposition "kerodon_9_7_2_6"
Kerodon Proposition 9.7.2.6（[Tag 02QK](https://kerodon.net/tag/02QK)）。対応表の状態：なし。

通常圏のsifted性のFinal/同値不変性は、原文の単体集合のright cofinal性・categorical equivalenceへの比較を含まない。

宣言：`CategoryTheory.IsSifted.isSifted_of_equiv`

:::

:::proposition "kerodon_9_7_2_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.isWeaklyContractible_of_sifted")
Kerodon Proposition 9.7.2.7（[Tag 02QL](https://kerodon.net/tag/02QL)）。対応表の状態：本体にある。

仮定：任意の K : SSet と IsSiftedInfinity K。原文の全有限対角の条件から使うのは空と二項の場合（Lean が弱い）。結論：IsWeaklyContractible K（原文と一致）。

:::

:::proposition "kerodon_9_7_2_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.nonemptyFiniteDiagonal_isRightCofinal, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.isWeaklyContractible_of_sifted, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity")
Kerodon Proposition 9.7.2.8（[Tag 02QM](https://kerodon.net/tag/02QM)）。対応表の状態：一部。

IsSiftedInfinityの二つのfields nonempty\_verticesとdiagonal\_rightCofinalは同じKの非空性と同じ二項対角のright cofinal性を直接返す。任意有限集合による原文の定義との比較を含む逆向きはこの引用だけで主張しない。

:::

:::corollary "kerodon_9_7_2_9"
Kerodon Corollary 9.7.2.9（[Tag 02QN](https://kerodon.net/tag/02QN)）。対応表の状態：なし。

二項余積からsifted性を得る型は、原文の二つのcosliceのfiber productの弱可縮性を同じ条件と判定する型ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.isSiftedInfinity_of_hasBinaryCoproducts`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.isSiftedInfinity_op_of_hasFiniteProducts`、`CategoryTheory.IsSifted.isSifted_of_hasBinaryCoproducts_and_nonempty`

:::

:::proposition "kerodon_9_7_2_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.smallSimplexOpposite_isSiftedInfinity, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.simplexDegreeDiagonal_nerve_isRightCofinal")
Kerodon Proposition 9.7.2.10（[Tag 02QP](https://kerodon.net/tag/02QP)）。対応表の状態：本体にある。

仮定：外部の圏の仮定なし（Kerodon と一致）。結論：小宇宙へ移した Δᵒᵖ の nerve に IsSiftedInfinity。反対圏での sifted 性として nerve Δ の cosifted 性を得る（原文と一致）。

:::

:::proposition "kerodon_9_7_2_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.totalKanProductComparison_isWeakHomotopyEquivalence_of_sifted, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.continuousKanTerminalComparison_isWeakHomotopyEquivalence_of_sifted, CategoryTheory.IsSifted.colim_preservesFiniteProducts_of_isSifted, CategoryTheory.IsSifted.of_colim_preservesFiniteProducts, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramTotalCocone_isColimit")
Kerodon Proposition 9.7.2.12（[Tag 0704](https://kerodon.net/tag/0704)）。対応表の状態：一部。

同じ二つの空間値図式のunstraighteningにtotalKanProductComparisonを適用すると、siftedなKの余極限と二項積の比較が弱同値となる向きを直接得る。分類と全体余極限の同じ比較も併用し、逆向きは含まない。

:::

:::definition "kerodon_9_7_2_13"
Kerodon Variant 9.7.2.13（[Tag 0705](https://kerodon.net/tag/0705)）。対応表の状態：なし。

全空間値のproduct比較は原文の数値κで切ったS\_\<κにおける同じ余極限比較への大きさの比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.totalKanProductComparison_isWeakHomotopyEquivalence_of_sifted`

:::

# 9.7.3 Tensor Products of ∞-Categories

%%%
number := false
tag := "kerodon-9-7-3"
%%%

Kerodon [Tag 0707](https://kerodon.net/tag/0707)

:::definition "kerodon_9_7_3_1"
Kerodon Definition 9.7.3.1（[Tag 0708](https://kerodon.net/tag/0708)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：二つの固定圏の余連続関手の全部分圏と、固定対象を空間でテンソルする一変数関手はある。任意の T:C×D→E が各変数で K-余連続という述語とその全部分圏は未確認。

:::

:::proposition "kerodon_9_7_3_5"
Kerodon Proposition 9.7.3.5（[Tag 070C](https://kerodon.net/tag/070C)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：定数関手の sifted 余極限保存と対角の右共終性はある。積を余域に持つ関手の成分ごとの保存の定理は、積を始域に持つ T の別々の変数の保存と全体の保存を比較する原文とは向きが異なる。

:::

:::corollary "kerodon_9_7_3_6"
Kerodon Corollary 9.7.3.6（[Tag 070D](https://kerodon.net/tag/070D)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：有限余積と sifted 余極限による一変数の保存判定はある。二変数での有限余極限保存と、積からの関手の κ-小 filtered 余極限保存を組み合わせる iff は未確認。

:::

:::definition "kerodon_9_7_3_7"
Kerodon Definition 9.7.3.7（[Tag 070E](https://kerodon.net/tag/070E)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単体集合の直積の余完備性と随伴の直積はある。原文は各変数で余連続な関手を表現する別のテンソルであり、その制限同値を含む定義は未確認。

:::

:::proposition "kerodon_9_7_3_9"
Kerodon Proposition 9.7.3.9（[Tag 070G](https://kerodon.net/tag/070G)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：直積の presentability と、固定圏の前層への左 Kan 延長はある。別々に K-余連続な関手を表現する圏を任意の K について構成する存在は未確認。

:::

:::definition "kerodon_9_7_3_10"
Kerodon Notation 9.7.3.10（[Tag 070H](https://kerodon.net/tag/070H)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：直積に沿う同値・随伴と、絶対 Ind の制限同値を確認した。K-双線形関手を表すテンソル圏と指定の二変数関手を同値まで一意に選ぶ型は未確認。

:::

:::definition "kerodon_9_7_3_14"
Kerodon Variant 9.7.3.14（[Tag 070M](https://kerodon.net/tag/070M)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単体集合の直積の小ささとその準圏の小余極限はある。κ-小形状の余極限を各変数で保つ関手を表現する κ-余完備テンソルの定義は未確認。

:::

:::definition "kerodon_9_7_3_15"
Kerodon Variant 9.7.3.15（[Tag 070N](https://kerodon.net/tag/070N)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単体集合の直積とその随伴はある。全小余極限について双線形な関手を表現する余完備テンソルの定義は未確認。

:::

# 9.7.4 Unitality

%%%
number := false
tag := "kerodon-9-7-4"
%%%

Kerodon [Tag 070Q](https://kerodon.net/tag/070Q)

:::proposition "kerodon_9_7_4_1"
Kerodon Proposition 9.7.4.1（[Tag 070R](https://kerodon.net/tag/070R)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定対象を空間でテンソルする関手はある。原文の空間の圏を単位とする余完備テンソルへの X↦Δ⁰⊗X が圏同値になる型は未確認。

:::

:::definition "kerodon_9_7_4_2"
Kerodon Notation 9.7.4.2（[Tag 070S](https://kerodon.net/tag/070S)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：有限単体模型による全空間の compact 生成と、別の前層の Ind 閉性はある。Δ⁰ 一点を含む任意 K の最小余極限閉部分圏を S\_\{\<κ\} に構成する定義は未確認。

:::

:::proposition "kerodon_9_7_4_8"
Kerodon Proposition 9.7.4.8（[Tag 070Y](https://kerodon.net/tag/070Y)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定対象に空間をテンソルする随伴と、二空間の直積はある。任意 K の S\_\{\<K\}×C で双線形である全関手、単位での同型、さらに余完備テンソルを表す性質を一緒に得る型は未確認。

:::

:::corollary "kerodon_9_7_4_12"
Kerodon Corollary 9.7.4.12（[Tag 0712](https://kerodon.net/tag/0712)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：空間を固定対象に作用させる随伴と全空間の生成はある。S\_\{\<K\} を使う K-余完備テンソルへの点による挿入が同値となる結果は未確認。

:::

# 9.7.5 Tensor Products of Presentable ∞-Categories

%%%
number := false
tag := "kerodon-9-7-5"
%%%

Kerodon [Tag 0713](https://kerodon.net/tag/0713)

:::proposition "kerodon_9_7_5_1"
Kerodon Proposition 9.7.5.1（[Tag 0714](https://kerodon.net/tag/0714)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：既存の tensor\_isPresentable は SSet のカルテシアンな積 C×D の presentability を示す。原文の双線形関手を表現する余完備テンソルの presentability は未確認。

:::

:::definition "kerodon_9_7_5_2"
Kerodon Construction 9.7.5.2（[Tag 0715](https://kerodon.net/tag/0715)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単体集合の積では成分射の積を作り、その余極限保存や同型を比較できる。異なる形状族の余完備テンソル間の F⊗G と指定の可換同型正方形は未確認。

:::

:::proposition "kerodon_9_7_5_3"
Kerodon Proposition 9.7.5.3（[Tag 0716](https://kerodon.net/tag/0716)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：絶対 Ind の制限同値と直積上の随伴はある。相対完備化する二つの関手の余完備テンソルが、K から K̂ への相対余完備化となる比較は未確認。

:::

:::corollary "kerodon_9_7_5_5"
Kerodon Corollary 9.7.5.5（[Tag 0718](https://kerodon.net/tag/0718)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：二つの Ind の直積には presentability を得る型がある。λ-余完備テンソルを同じ κ,λ で compact 生成する結論は未確認。

:::

:::corollary "kerodon_9_7_5_6"
Kerodon Corollary 9.7.5.6（[Tag 0719](https://kerodon.net/tag/0719)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：直積の presentability はあるが、同じ κ における二圏の生成を余完備テンソルへ移す型は未確認。

:::

:::corollary "kerodon_9_7_5_7"
Kerodon Corollary 9.7.5.7（[Tag 071A](https://kerodon.net/tag/071A)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：直積の Ind 模型と、空間が ℵ₀-accessible である結果はある。ℵ₀-compact 生成が双線形関手を表現するテンソルで保存される型は未確認。

:::

:::proposition "kerodon_9_7_5_8"
Kerodon Proposition 9.7.5.8（[Tag 071B](https://kerodon.net/tag/071B)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：既存の定理は直積がある濃度で presentable になる結果と、成分射の積が指定濃度で accessible になる結果。原文の余完備テンソルが同じ κ で presentable になる型は未確認。

:::

:::proposition "kerodon_9_7_5_9"
Kerodon Proposition 9.7.5.9（[Tag 071C](https://kerodon.net/tag/071C)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：右随伴側の関手空間と直積の presentability はある。原文の Dᵒᵖ から C への小極限保存関手の全部分圏と余完備テンソルの標準同値は未確認。

:::

:::proposition "kerodon_9_7_5_13"
Kerodon Proposition 9.7.5.13（[Tag 071G](https://kerodon.net/tag/071G)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：反射の随伴と余単位を単体集合の直積で合成する型はある。双線形の余完備テンソルで二つの局所化をテンソルし、Bousfield 局所化になる結果は未確認。

:::

# 9.7.6 Locally Truncated ∞-Categories

%%%
number := false
tag := "kerodon-9-7-6"
%%%

Kerodon [Tag 071H](https://kerodon.net/tag/071H)

:::proposition "kerodon_9_7_6_1"
Kerodon Proposition 9.7.6.1（[Tag 071J](https://kerodon.net/tag/071J)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：離散空間と同値である述語および直積の定理を確認した。任意の n で一方の局所切断性が余完備テンソルへ移る型は未確認。

:::

:::proposition "kerodon_9_7_6_2"
Kerodon Proposition 9.7.6.2（[Tag 071K](https://kerodon.net/tag/071K)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：空間の 0 切断と固定対象への空間作用、余連続関手圏はある。S\^\{≤n\}\_\{\<κ\} によるテンソルが局所 n 切断され、点による制限で指定の圏同値を与える結論は未確認。

:::

:::corollary "kerodon_9_7_6_3"
Kerodon Corollary 9.7.6.3（[Tag 071L](https://kerodon.net/tag/071L)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：離散空間の表示と固定対象を空間でテンソルする関手はある。局所 n 切断性を切断空間による余完備テンソルへの点の射が同値かどうかで判定する iff は未確認。

:::

:::proposition "kerodon_9_7_6_5"
Kerodon Proposition 9.7.6.5（[Tag 071N](https://kerodon.net/tag/071N)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：小辺族に対する一般の反射局所化と離散空間の充満忠実な埋め込みを確認した。任意の presentable C の n 切断対象を指定テンソルの充満忠実右随伴の本質像とする型は未確認。

:::

:::definition "kerodon_9_7_6_10"
Kerodon Variant 9.7.6.10（[Tag 071T](https://kerodon.net/tag/071T)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：有限単体集合の Kan 置換のコンパクト性と、κ-コンパクト対象の有限余極限閉性はある。有限切断空間との余完備テンソル、有限余極限保存関手の制限同値および局所 n 切断性の判定は未確認。

:::

# 9.7.7 Associativity

%%%
number := false
tag := "kerodon-9-7-7"
%%%

Kerodon [Tag 071U](https://kerodon.net/tag/071U)

:::proposition "kerodon_9_7_7_1"
Kerodon Proposition 9.7.7.1（[Tag 071V](https://kerodon.net/tag/071V)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単体集合の直積による関手圏の比較や随伴はある。三圏からの双線形・多重線形関手を表現する二つの括りの間に、指定正方形を持つ結合の同値は未確認。

:::

:::definition "kerodon_9_7_7_2"
Kerodon Definition 9.7.7.2（[Tag 071W](https://kerodon.net/tag/071W)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定二圏の余連続関手圏と、余域が積の場合の成分判定はある。始域の有限個の変数を一つずつ固定し K-余連続性を課す全部分圏は未確認。

:::

:::definition "kerodon_9_7_7_6"
Kerodon Definition 9.7.7.6（[Tag 0720](https://kerodon.net/tag/0720)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：有限個の積の presentability や、一つの Ind の制限同値はある。有限族からの各変数で余連続な関手を表す圏を定義する三条件は未確認。

:::

:::proposition "kerodon_9_7_7_9"
Kerodon Proposition 9.7.7.9（[Tag 0723](https://kerodon.net/tag/0723)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：直積の presentability と固定圏への米田の左 Kan 延長はある。任意の有限族の K-多重線形関手を表現するテンソル圏の存在は未確認。

:::

:::proposition "kerodon_9_7_7_10"
Kerodon Proposition 9.7.7.10（[Tag 0724](https://kerodon.net/tag/0724)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：直積を余域とする関手圏の同型と、一つの Ind の制限同値はある。有限集合間の写像に沿う各テンソルで前合成して、多重線形関手圏の同値を得る主張は未確認。

:::

:::corollary "kerodon_9_7_7_11"
Kerodon Corollary 9.7.7.11（[Tag 0725](https://kerodon.net/tag/0725)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：余連続関手の合成と、絶対的な Ind の制限同値はある。有限族をまとめるテンソル射と、まとめた族をテンソルする射の合成が元の族の普遍性を満たす型は未確認。

:::

:::proposition "kerodon_9_7_7_14"
Kerodon Proposition 9.7.7.14（[Tag 0728](https://kerodon.net/tag/0728)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：PrL と準圏のホモトピー圏を扱う構成、および直積の同値はある。κ-小形状族で制限した QC のホモトピー圏に、余完備テンソルと S\_\{\<K\} を単位とするモノイド構造は未確認。

:::

# 9.7.8 Idempotent ∞-Categories

%%%
number := false
tag := "kerodon-9-7-8"
%%%

Kerodon [Tag 072B](https://kerodon.net/tag/072B)

:::definition "kerodon_9_7_8_1"
Kerodon Definition 9.7.8.1（[Tag 072C](https://kerodon.net/tag/072C)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：準圏内の冪等射の分裂と直積の presentability はある。原文は圏自体の余完備テンソルの冪等性であり、指定対象でのテンソル挿入が圏同値となる述語は未確認。

:::

:::definition "kerodon_9_7_8_5"
Kerodon Definition 9.7.8.5（[Tag 072G](https://kerodon.net/tag/072G)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：PrL と余連続関手空間および固定対象への空間作用はある。圏 E による余完備テンソルが恒等と同値である presentable 圏の全部分圏は未確認。

:::

:::proposition "kerodon_9_7_8_10"
Kerodon Proposition 9.7.8.10（[Tag 072M](https://kerodon.net/tag/072M)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単独の準圏内の反射、余連続関手圏、直積の随伴を確認した。PrL における E 加群の包含が両随伴を持ち、指定の余完備テンソル・関手圏で表す型は未確認。

:::

:::definition "kerodon_9_7_8_12"
Kerodon Definition 9.7.8.12（[Tag 072P](https://kerodon.net/tag/072P)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定対象での空間テンソルの写像空間随伴と、別の冪等完備性はある。E×E の K-双線形関手の評価が余連続関手圏への同値になるという圏 E の述語は未確認。

:::

:::proposition "kerodon_9_7_8_16"
Kerodon Proposition 9.7.8.16（[Tag 072T](https://kerodon.net/tag/072T)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：固定対象への空間作用と余連続関手空間はある。原文の圏 E の加群性について、テンソル模型・関手圏模型・評価のホモトピー逆・双線形作用を結ぶ同値は未確認。

:::

:::definition "kerodon_9_7_8_17"
Kerodon Definition 9.7.8.17（[Tag 072U](https://kerodon.net/tag/072U)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：余完備な準圏と余連続関手の模型はある。K-余完備な C が圏 E の加群であることを、指定の余完備テンソルによる条件で定義する型は未確認。

:::

:::proposition "kerodon_9_7_8_20"
Kerodon Proposition 9.7.8.20（[Tag 072X](https://kerodon.net/tag/072X)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：絶対的な Ind の制限と単独の反射はある。E によるテンソル挿入との前合成と、E の関手圏からの評価との後合成が、任意の E 加群に対し同値となる二結果は未確認。

:::

:::proposition "kerodon_9_7_8_27"
Kerodon Proposition 9.7.8.27（[Tag 0734](https://kerodon.net/tag/0734)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Ind 内の compact 部分の冪等完備化と絶対的な制限同値はある。原文の「圏を余完備テンソルすると冪等」の性質を相対 Ind で移し、冪等完備性のもとで反映する型は未確認。

:::

:::proposition "kerodon_9_7_8_29"
Kerodon Proposition 9.7.8.29（[Tag 0736](https://kerodon.net/tag/0736)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：特定形状の絶対的な余完備化の制限同値はある。二つの形状族の間で余完備冪等圏を相対完備化したとき、同じ C の E と E₀ に対する加群性が同値になる型は未確認。

:::

