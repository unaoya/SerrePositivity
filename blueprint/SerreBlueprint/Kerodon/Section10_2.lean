import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Shapes
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "10.2 Regular ∞-Categories" =>
%%%
number := false
tag := "kerodon-10-2"
%%%

Kerodon の 10.2 節（[Tag 04TM](https://kerodon.net/tag/04TM)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::definition "kerodon_10_2_0_2" (lean := "CategoryTheory.RegularEpi, CategoryTheory.regularEpiOfKernelPair, CategoryTheory.regularEpiOfEffectiveEpi, CategoryTheory.isRegularEpi_iff_effectiveEpi, CategoryTheory.isColimitCoforkOfEffectiveEpi")
Kerodon Definition 10.2.0.2（[Tag 04TP](https://kerodon.net/tag/04TP)）。対応表の状態：Mathlib にある。

仮定：通常圏の射 f と f 自身の引き戻し。原文は圏全体に引き戻しを要求し、Lean は対象の核対だけを要求する（Lean が弱い）。結論：regularEpiOfKernelPair は核対の射影の余等化子から RegularEpi を構成する。逆は EffectiveEpi を介して isColimitCoforkOfEffectiveEpi が同じ核対の Cofork.ofπ f の IsColimit を与える（原文の定義と一致）。

:::

:::definition "kerodon_10_2_0_6"
Kerodon Definition 10.2.0.6（[Tag 04TT](https://kerodon.net/tag/04TT)）。対応表の状態：一部。

通常圏のRegularのfieldsとstrongEpiMonoFactorisation、そのeのIsRegularEpiインスタンスは原文の有限極限・正則エピとmonoの分解・底変換安定性の三条件を直接返す。三条件から核対余等化子という逆向きはこの引用で確認していない。

宣言：`CategoryTheory.Regular`、`CategoryTheory.Regular.hasStrongEpiMonoFactorisations`、`CategoryTheory.Regular.strongEpiMonoFactorisation`

:::

# 10.2.1 Sieves

%%%
number := false
tag := "kerodon-10-2-1"
%%%

Kerodon [Tag 04TZ](https://kerodon.net/tag/04TZ)

:::definition "kerodon_10_2_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration")
Kerodon Definition 10.2.1.1（[Tag 04U0](https://kerodon.net/tag/04U0)）。対応表の状態：本体にある。

同じ単体集合Cの部分集合S:C.SubcomplexについてRightFibration S.ιという既存の型が原文の定義全体に一致する。通常圏Sieveではなく任意の単体集合の包含を入力する。

:::

:::proposition "kerodon_10_2_1_5"
Kerodon Proposition 10.2.1.5（[Tag 04U4](https://kerodon.net/tag/04U4)）。対応表の状態：なし。

B6再照合：通常圏の前合成閉性はある。任意の単体について終頂点の所属から単体全体の所属を得る iff は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::corollary "kerodon_10_2_1_6"
Kerodon Corollary 10.2.1.6（[Tag 04U5](https://kerodon.net/tag/04U5)）。対応表の状態：なし。

B6再照合：通常圏の Sieve は射で定義され、原文は対象の充満部分∞圏と入射の始点閉性を比較する。対応する iff は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::corollary "kerodon_10_2_1_8"
Kerodon Corollary 10.2.1.8（[Tag 04U7](https://kerodon.net/tag/04U7)）。対応表の状態：一部。

同じsieveの包含のRightFibrationからinner fibrationを得て、quasicategory\_of\_innerFibrationを適用すると原文最後の同じ部分集合の準圏性を直接得る。repleteとfullの両条件全体は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibration_innerFibration`、`SSet.quasicategory_of_innerFibration`

:::

:::proposition "kerodon_10_2_1_12"
Kerodon Proposition 10.2.1.12（[Tag 04UA](https://kerodon.net/tag/04UA)）。対応表の状態：なし。

B6再照合：一般の右ファイブレーションはある。各頂点ファイバーが高々一点である right covering を部分 sieve と同型にする判定は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::corollary "kerodon_10_2_1_13"
Kerodon Corollary 10.2.1.13（[Tag 04UB](https://kerodon.net/tag/04UB)）。対応表の状態：なし。

B6再照合：通常圏の固定対象上の sieve はある。hC の部分圏の nerve を C に引き戻す全単射は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_2_1_18" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection")
Kerodon Definition 10.2.1.18（[Tag 04UD](https://kerodon.net/tag/04UD)）。対応表の状態：本体にある。

同じYのsliceOver(point Y)の単体部分集合SについてRightFibration S.ιを課すと、原文の「Y上のsieveはslice上のsieve」という定義全体を直接表す。通常圏Sieveの名前付き型を∞圏版の代用にしない。

:::

:::proposition "kerodon_10_2_1_22"
Kerodon Proposition 10.2.1.22（[Tag 04UH](https://kerodon.net/tag/04UH)）。対応表の状態：なし。

B6再照合：通常圏の対象上の sieve と∞圏の slice は別々にある。hC の slice の sieve と C の slice の sieve の全単射は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_2_1_24"
Kerodon Notation 10.2.1.24（[Tag 04UL](https://kerodon.net/tag/04UL)）。対応表の状態：なし。

B6型照合：通常圏の sieve は f との後合成による逆像として引き戻せる。∞圏のスライスの充満部分圏としての構成は引用型にない。 通常圏の候補から、原文で指定された準圏の同じ対象・射・述語へ比較する型を確認していないためnone。

宣言：`CategoryTheory.Sieve.pullback`

:::

:::definition "kerodon_10_2_1_26" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone")
Kerodon Definition 10.2.1.26（[Tag 04UN](https://kerodon.net/tag/04UN)）。対応表の状態：本体にある。

同じsieveの包含δと同じsliceOverProjection Fについて∀c, IsColimitCone (leftKanCanonicalCocone δ F c)と課せば、原文の忘却関手がそのsieveから左Kan延長されるというdenseの定義全体を直接表す。

:::

:::proposition "kerodon_10_2_1_29"
Kerodon Proposition 10.2.1.29（[Tag 04UR](https://kerodon.net/tag/04UR)）。対応表の状態：なし。

B6再照合：通常圏で sieve の余錐に関する述語はある。二項積の仮定下で、忘却関手の左 Kan 延長とスライス内部の稠密性を比較する iff は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::proposition "kerodon_10_2_1_33"
Kerodon Proposition 10.2.1.33（[Tag 04UV](https://kerodon.net/tag/04UV)）。対応表の状態：なし。

B6再照合：通常圏で sieve を引き戻す演算はある。任意の∞圏での稠密性の引き戻し安定性の宣言は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::proposition "kerodon_10_2_1_34"
Kerodon Proposition 10.2.1.34（[Tag 04UW](https://kerodon.net/tag/04UW)）。対応表の状態：なし。

B6再照合：通常圏の有効エピ的 sieve と被覆の公理を確認した。∞圏の稠密 sieve に対する、指定した稠密 sieve の各射での引き戻しからの推移性は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

# 10.2.2 Quotient Morphisms

%%%
number := false
tag := "kerodon-10-2-2"
%%%

Kerodon [Tag 04WG](https://kerodon.net/tag/04WG)

:::definition "kerodon_10_2_2_1"
Kerodon Definition 10.2.2.1（[Tag 04WH](https://kerodon.net/tag/04WH)）。対応表の状態：なし。

B6型照合：Mathlib では一射の生成する sieve と、対応する余錐の余極限性による effective epimorphic の定義がある。原文の∞圏で生成された sieve の余錐による定義は未確認。 通常圏の候補から、原文で指定された準圏の同じ対象・射・述語へ比較する型を確認していないためnone。

宣言：`CategoryTheory.Sieve.EffectiveEpimorphic`、`CategoryTheory.Sieve.generateSingleton`

:::

:::definition "kerodon_10_2_2_2"
Kerodon Notation 10.2.2.2（[Tag 04WJ](https://kerodon.net/tag/04WJ)）。対応表の状態：なし。

B6再照合：通常圏の EffectiveEpi はデータを忘れた述語。∞圏の quotient morphism を二重矢印で示す記法は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::proposition "kerodon_10_2_2_4"
Kerodon Proposition 10.2.2.4（[Tag 04WL](https://kerodon.net/tag/04WL)）。対応表の状態：なし。

B6再照合：通常圏の増強 Čech nerve と effective epi の核対の余等化子を確認した。∞圏の全 Čech 図式の余極限性による iff は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::lemma_ "kerodon_10_2_2_5"
Kerodon Lemma 10.2.2.5（[Tag 04WM](https://kerodon.net/tag/04WM)）。対応表の状態：なし。

B6再照合：通常圏で一対象の Čech nerve を構成できる。その nerve から対象で生成された sieve への右 cofinal 性は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_2_2_6"
Kerodon Variant 10.2.2.6（[Tag 04WN](https://kerodon.net/tag/04WN)）。対応表の状態：なし。

B6再照合：一射から通常圏の sieve を生成する構成はある。指定した増強 Čech nerve の制限からその∞スライスへの右 cofinal 性は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::corollary "kerodon_10_2_2_7"
Kerodon Corollary 10.2.2.7（[Tag 04WP](https://kerodon.net/tag/04WP)）。対応表の状態：なし。

B6型照合：通常圏で一射の生成 sieve の余極限条件は EffectiveEpi と同値で、引き戻しがあれば IsRegularEpi とも同値。原文が指定する nerve 内の∞余錐との比較は引用に含まれない。 通常圏の候補から、原文で指定された準圏の同じ対象・射・述語へ比較する型を確認していないためnone。

宣言：`CategoryTheory.Sieve.effectiveEpimorphic_singleton`、`CategoryTheory.isRegularEpi_iff_effectiveEpi`

:::

:::definition "kerodon_10_2_2_9"
Kerodon Variant 10.2.2.9（[Tag 04WR](https://kerodon.net/tag/04WR)）。対応表の状態：なし。

B6型照合：通常圏の一射の生成 sieve の余極限性から EffectiveEpi を経由して Epi を得る。原文の∞圏の quotient 述語と通常圏の sieve 条件との比較は未形式化。 通常圏の候補から、原文で指定された準圏の同じ対象・射・述語へ比較する型を確認していないためnone。

宣言：`CategoryTheory.Sieve.effectiveEpimorphic_singleton`、`CategoryTheory.epi_of_effectiveEpi`

:::

:::proposition "kerodon_10_2_2_11"
Kerodon Proposition 10.2.2.11（[Tag 04WT](https://kerodon.net/tag/04WT)）。対応表の状態：なし。

B6再照合：通常圏で有効エピ性を保つ関手と反映する関手を扱う。∞圏の同値による指定 quotient 述語の保存・反映は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::corollary "kerodon_10_2_2_12"
Kerodon Corollary 10.2.2.12（[Tag 04WU](https://kerodon.net/tag/04WU)）。対応表の状態：なし。

B6型照合：通常圏の矢の同型に沿って RegularEpi を運ぶ型がある。∞関手圏 Fun(Δ¹,C) の同型による quotient の iff ではない。 通常圏の候補から、原文で指定された準圏の同じ対象・射・述語へ比較する型を確認していないためnone。

宣言：`CategoryTheory.RegularEpi.ofArrowIso`

:::

:::proposition "kerodon_10_2_2_14"
Kerodon Proposition 10.2.2.14（[Tag 04WW](https://kerodon.net/tag/04WW)）。対応表の状態：なし。

B6再照合：通常圏の有効エピと Over の図式はある。任意の q に対する∞スライスへの商射の反映を結論とする型は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_2_2_17"
Kerodon Variant 10.2.2.17（[Tag 04X0](https://kerodon.net/tag/04X0)）。対応表の状態：なし。

B6再照合：一般の正方形の引き戻し性は扱える。原文の指定有限順序圏の正方形と quotient 性が引き戻しで壊れる例は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

# 10.2.3 Images

%%%
number := false
tag := "kerodon-10-2-3"
%%%

Kerodon [Tag 04X1](https://kerodon.net/tag/04X1)

:::definition "kerodon_10_2_3_1"
Kerodon Definition 10.2.3.1（[Tag 04X2](https://kerodon.net/tag/04X2)）。対応表の状態：なし。

B6再照合：通常圏の厳密な strong epi・mono 分解はある。ホモトピー類が quotient morphism を通じて因子化する∞圏の像の定義は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::proposition "kerodon_10_2_3_6"
Kerodon Proposition 10.2.3.6（[Tag 04X8](https://kerodon.net/tag/04X8)）。対応表の状態：なし。

B6再照合：通常圏の HasImage は最小の mono 分解の存在。終域自身が像になる条件と∞商射との iff は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::lemma_ "kerodon_10_2_3_9"
Kerodon Lemma 10.2.3.9（[Tag 04XB](https://kerodon.net/tag/04XB)）。対応表の状態：なし。

B6再照合：射族に対する局所対象の述語はある。各 subterminal が指定 quotient に局所となる結論は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::lemma_ "kerodon_10_2_3_10"
Kerodon Lemma 10.2.3.10（[Tag 04XC](https://kerodon.net/tag/04XC)）。対応表の状態：なし。

B6型照合：通常圏で EffectiveEpi から StrongEpi を得て mono に対する持ち上げが存在する。∞圏での直交性に必要な持ち上げ空間の可縮性は型にない。 通常圏の候補から、原文で指定された準圏の同じ対象・射・述語へ比較する型を確認していないためnone。

宣言：`CategoryTheory.strongEpi_of_effectiveEpi`

:::

:::proposition "kerodon_10_2_3_11"
Kerodon Proposition 10.2.3.11（[Tag 04XD](https://kerodon.net/tag/04XD)）。対応表の状態：なし。

B6型照合：通常圏の strong epi・mono 分解を選ばれた像と比較でき、別の mono 分解への lift がある。原文の指定二単体と∞圏での普遍性は引用にない。 通常圏の候補から、原文で指定された準圏の同じ対象・射・述語へ比較する型を確認していないためnone。

宣言：`CategoryTheory.Limits.image.isoStrongEpiMono`、`CategoryTheory.Limits.image.lift`

:::

:::definition "kerodon_10_2_3_12"
Kerodon Notation 10.2.3.12（[Tag 04XG](https://kerodon.net/tag/04XG)）。対応表の状態：なし。

B6型照合：通常圏では選ばれた像対象がある。原文の∞圏での像の Sub(Y) における同型類を指定する記法は未確認。 通常圏の候補から、原文で指定された準圏の同じ対象・射・述語へ比較する型を確認していないためnone。

宣言：`CategoryTheory.Limits.image`

:::

:::corollary "kerodon_10_2_3_13"
Kerodon Corollary 10.2.3.13（[Tag 05HS](https://kerodon.net/tag/05HS)）。対応表の状態：なし。

B6型照合：通常の圏では mono かつ strong epi から同型を得る補題がある。原文は∞圏で quotient morphism を用いる両方向の判定。 通常圏の候補から、原文で指定された準圏の同じ対象・射・述語へ比較する型を確認していないためnone。

宣言：`CategoryTheory.isIso_of_mono_of_strongEpi`

:::

:::proposition "kerodon_10_2_3_14"
Kerodon Proposition 10.2.3.14（[Tag 04XH](https://kerodon.net/tag/04XH)）。対応表の状態：なし。

B6再照合：通常圏の個別分解のデータはある。像分解の充満部分関手圏から矢の関手圏への制限の主張は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::proposition "kerodon_10_2_3_17"
Kerodon Proposition 10.2.3.17（[Tag 0738](https://kerodon.net/tag/0738)）。対応表の状態：なし。

B6再照合：通常正則圏では核対の余等化子から像分解を作る。原文の全 Čech 図式の普遍余極限を像にする∞圏の結論は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_2_3_18"
Kerodon Definition 10.2.3.18（[Tag 04XM](https://kerodon.net/tag/04XM)）。対応表の状態：なし。

B6型照合：Mathlib の HasImages は通常の圏の全ての射が像を持つことを表す。原文は∞圏の subobject における像の存在。 通常圏の候補から、原文で指定された準圏の同じ対象・射・述語へ比較する型を確認していないためnone。

宣言：`CategoryTheory.Limits.HasImages`

:::

:::proposition "kerodon_10_2_3_21"
Kerodon Proposition 10.2.3.21（[Tag 04XQ](https://kerodon.net/tag/04XQ)）。対応表の状態：なし。

B6再照合：通常圏の StrongEpi は epi と mono への LLP を課す。∞圏で像の存在から商射・直交・弱直交を同値にする型は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::corollary "kerodon_10_2_3_22"
Kerodon Corollary 10.2.3.22（[Tag 04XR](https://kerodon.net/tag/04XR)）。対応表の状態：なし。

B6型照合：通常圏の strong epi の合成から後因子の strong epi を得る。原文の像を持つ∞圏での quotient の合成・消去の iff のうち一方向に相当。 通常圏の候補から、原文で指定された準圏の同じ対象・射・述語へ比較する型を確認していないためnone。

宣言：`CategoryTheory.strongEpi_of_strongEpi`

:::

:::corollary "kerodon_10_2_3_23"
Kerodon Corollary 10.2.3.23（[Tag 04XS](https://kerodon.net/tag/04XS)）。対応表の状態：なし。

B6再照合：通常圏で LLP を持つ strong epi の定義はある。原文の像の存在を仮定した∞圏の押し出し後の quotient 性は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::corollary "kerodon_10_2_3_24"
Kerodon Corollary 10.2.3.24（[Tag 04XT](https://kerodon.net/tag/04XT)）。対応表の状態：なし。

B6再照合：通常圏の射のクラスの retract 閉性と LLP の補題はある。像を持つ∞圏での quotient の矢の retract 閉性は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

# 10.2.4 Universal Quotient Morphisms

%%%
number := false
tag := "kerodon-10-2-4"
%%%

Kerodon [Tag 04XV](https://kerodon.net/tag/04XV)

:::definition "kerodon_10_2_4_1"
Kerodon Definition 10.2.4.1（[Tag 04XW](https://kerodon.net/tag/04XW)）。対応表の状態：なし。

B6再照合：通常圏の有効エピ的 sieve は一つの余錐の普遍性。∞スライスの全対象での稠密性により定義する universal quotient は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::proposition "kerodon_10_2_4_6"
Kerodon Proposition 10.2.4.6（[Tag 04Y1](https://kerodon.net/tag/04Y1)）。対応表の状態：なし。

B6再照合：通常正則圏の全正則エピの引き戻し安定性はある。指定した普遍商射が引き戻し後も普遍商射となる∞圏の型は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::corollary "kerodon_10_2_4_7"
Kerodon Corollary 10.2.4.7（[Tag 04Y3](https://kerodon.net/tag/04Y3)）。対応表の状態：なし。

B6再照合：通常正則圏の正則エピの底変換はある。任意の∞圏で一射の universal quotient 性を全引き戻しの quotient 性と比べる iff は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::corollary "kerodon_10_2_4_8"
Kerodon Corollary 10.2.4.8（[Tag 04Y4](https://kerodon.net/tag/04Y4)）。対応表の状態：なし。

B6再照合：通常圏の Regular は引き戻し安定性を公理に含める。全∞商射の普遍性とクラスの閉性との iff は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::corollary "kerodon_10_2_4_9"
Kerodon Corollary 10.2.4.9（[Tag 04Y5](https://kerodon.net/tag/04Y5)）。対応表の状態：なし。

B6型照合：Mathlib：Type で epi ↔ 全射、epi は split なので正則 epi。「universal quotient morphism」（基底変換で保たれる）としての明示的な同値はない。 通常圏の候補から、原文で指定された準圏の同じ対象・射・述語へ比較する型を確認していないためnone。

宣言：`CategoryTheory.epi_iff_surjective`、`CategoryTheory.RegularEpi.ofSplitEpi`

:::

:::corollary "kerodon_10_2_4_10"
Kerodon Corollary 10.2.4.10（[Tag 04Y6](https://kerodon.net/tag/04Y6)）。対応表の状態：なし。

B6再照合：通常圏の一般の普遍余極限はある。∞圏の Čech nerve の普遍余極限性を普遍商射と比較する型は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::proposition "kerodon_10_2_4_12"
Kerodon Proposition 10.2.4.12（[Tag 04Y8](https://kerodon.net/tag/04Y8)）。対応表の状態：なし。

B6再照合：通常圏の有効エピの合成に関する消去はある。普遍商射二つの合成が普遍商射である∞圏の型は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_2_4_13"
Kerodon Variant 10.2.4.13（[Tag 04Y9](https://kerodon.net/tag/04Y9)）。対応表の状態：なし。

B6再照合：通常圏の strong epi の合成結果はある。先行する普遍商射と後続する商射を組み合わせる指定の結論は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::corollary "kerodon_10_2_4_14"
Kerodon Corollary 10.2.4.14（[Tag 04YA](https://kerodon.net/tag/04YA)）。対応表の状態：なし。

B6再照合：通常圏の射のクラスに対する retract 閉性はある。∞圏での universal quotient のクラスは見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::proposition "kerodon_10_2_4_15"
Kerodon Proposition 10.2.4.15（[Tag 04YB](https://kerodon.net/tag/04YB)）。対応表の状態：なし。

B6再照合：通常圏と∞圏のスライス構成を確認した。台の射の普遍商性を任意の図式 q 上の∞スライスの射へ移す型は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::lemma_ "kerodon_10_2_4_16"
Kerodon Lemma 10.2.4.16（[Tag 04YC](https://kerodon.net/tag/04YC)）。対応表の状態：なし。

B6再照合：写像空間比較の充満忠実性と稠密性の例はある。稠密部分圏の対象ごとの hC の Hom の全射性で普遍商性を検出する型は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::proposition "kerodon_10_2_4_17"
Kerodon Proposition 10.2.4.17（[Tag 04YD](https://kerodon.net/tag/04YD)）。対応表の状態：なし。

B6再照合：ファイバー包含の π₀ 全射性は指定された写像の商性の判定と異なる。任意の Kan 複体間の射についての三条件の iff は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

# 10.2.5 Regular ∞-Categories

%%%
number := false
tag := "kerodon-10-2-5"
%%%

Kerodon [Tag 04YE](https://kerodon.net/tag/04YE)

:::definition "kerodon_10_2_5_1"
Kerodon Definition 10.2.5.1（[Tag 04YF](https://kerodon.net/tag/04YF)）。対応表の状態：なし。

B6型照合：通常の圏の Regular は有限極限、核対の余等化子、正則エピの引き戻し安定性を要求する。原文の∞圏の像・普遍商射に関する定義は未確認。 通常圏の候補から、原文で指定された準圏の同じ対象・射・述語へ比較する型を確認していないためnone。

宣言：`CategoryTheory.Regular`

:::

:::proposition "kerodon_10_2_5_3"
Kerodon Proposition 10.2.5.3（[Tag 04YH](https://kerodon.net/tag/04YH)）。対応表の状態：なし。

B6再照合：通常圏の正則性の定義は底変換安定性を課す。像を持つ∞圏の複数の正則性条件を比較する型は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::corollary "kerodon_10_2_5_5"
Kerodon Corollary 10.2.5.5（[Tag 04YM](https://kerodon.net/tag/04YM)）。対応表の状態：なし。

B6再照合：通常正則圏の核対からの分解はある。有限極限を持つ∞圏で普遍商射と単射への全分解から正則性も得る iff は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::corollary "kerodon_10_2_5_6"
Kerodon Corollary 10.2.5.6（[Tag 04YN](https://kerodon.net/tag/04YN)）。対応表の状態：なし。

B6再照合：空間の∞圏は小極限を持つ。像分解と全商射の引き戻し安定性を組にした正則性の型は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::corollary "kerodon_10_2_5_9"
Kerodon Corollary 10.2.5.9（[Tag 0739](https://kerodon.net/tag/0739)）。対応表の状態：なし。

B6再照合：通常圏で一般の普遍余極限を定義する。全ての∞Čech nerve が普遍余極限を持つ条件による正則性判定は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::proposition "kerodon_10_2_5_10"
Kerodon Proposition 10.2.5.10（[Tag 04YR](https://kerodon.net/tag/04YR)）。対応表の状態：なし。

B6再照合：通常圏の正則性のクラスはある。全対象上の∞スライスに正則性を移す型は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_2_5_11"
Kerodon Definition 10.2.5.11（[Tag 04YS](https://kerodon.net/tag/04YS)）。対応表の状態：なし。

B6型照合：通常圏の有限極限保存と有効エピ保存を別々に表す述語がある。正則∞圏で quotient を保つ原文の述語は見つからない。 通常圏の候補から、原文で指定された準圏の同じ対象・射・述語へ比較する型を確認していないためnone。

宣言：`CategoryTheory.Functor.PreservesEffectiveEpis`、`CategoryTheory.Limits.PreservesFiniteLimits`

:::

:::proposition "kerodon_10_2_5_13"
Kerodon Proposition 10.2.5.13（[Tag 04YU](https://kerodon.net/tag/04YU)）。対応表の状態：なし。

B6再照合：通常圏で有効エピを保つクラスはある。引き戻しを保つ∞関手について像の二単体の保存と商射保存を比べる iff は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::corollary "kerodon_10_2_5_15"
Kerodon Corollary 10.2.5.15（[Tag 04YW](https://kerodon.net/tag/04YW)）。対応表の状態：なし。

B6再照合：通常圏の像の存在と像の射影はある。∞関手が Sub(Y) の像を保つ条件による正則性判定は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::proposition "kerodon_10_2_5_17"
Kerodon Proposition 10.2.5.17（[Tag 04YY](https://kerodon.net/tag/04YY)）。対応表の状態：なし。

B6再照合：幾何実現を保つ∞関手の述語はある。有限極限と合わせて quotient 保存を導く宣言は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::proposition "kerodon_10_2_5_18"
Kerodon Proposition 10.2.5.18（[Tag 04YZ](https://kerodon.net/tag/04YZ)）。対応表の状態：なし。

B6再照合：通常圏で有効エピを反映する関手のクラスはある。引き戻しに閉じた充満部分∞圏への商性・普遍商性の移送は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::corollary "kerodon_10_2_5_19"
Kerodon Corollary 10.2.5.19（[Tag 04Z0](https://kerodon.net/tag/04Z0)）。対応表の状態：なし。

B6再照合：通常圏の正則性は定義される。有限極限と像に閉じた充満部分∞圏に正則性を移す型は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::proposition "kerodon_10_2_5_20"
Kerodon Proposition 10.2.5.20（[Tag 04Z1](https://kerodon.net/tag/04Z1)）。対応表の状態：なし。

B6再照合：∞圏の反射部分圏の述語はある。左随伴の有限極限保存から標的と関手の正則性を得る型は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::corollary "kerodon_10_2_5_21"
Kerodon Corollary 10.2.5.21（[Tag 04Z4](https://kerodon.net/tag/04Z4)）。対応表の状態：なし。

B6再照合：反射部分∞圏の極限や余極限を扱う宣言はある。反射関手の有限極限保存から正則性を回収する型は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

