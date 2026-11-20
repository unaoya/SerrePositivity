# EN-W1 段1　豊穣化の全体調査

main `336b54610` と追加指示の `662cd9182` を取り込んだ `6f5d0dd6c` が調査基準。固定 Mathlib は `e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`。SU-W1 段14の実装は保留したまま。[構成の目録](../../../research/cleanup-zero-base/enrichment/constructions.csv) · [受け取り側](../../../research/cleanup-zero-base/enrichment/consumers.md) · [一般論と dg 比較](../../../research/cleanup-zero-base/enrichment/general-theory.md)

## 母集団と数え方

Archive を除く追跡済み Lean 本体34,049モジュールを母集団とし、カーネル宣言359,335件を照合した。既存の成果物から宣言の Π 型の結論、別名の右辺、構造のパラメータを除いた生成子のフィールドの型を読んだ。研究枠を取り、開始時に `coord` の保持がないことを確認した。定義名の綴りは選択条件に使っていない。 型が対象構造でも、既存の値を登録する instance は `record_kind` で分けた。構造の射影・生成された補助名は集計から除いた。

記録監査の本体一覧と全モジュールを照合した。監査の基準 `7d0968dad` と調査基準の Lean 差分は SU-W1 段12・13の範囲にあり、該当モジュールの依存は段13の採取、位置は現行の `.ilean` を使った。 `users_by_area` はソース位置のある利用宣言の型・本体の直接参照を合算し、同一利用宣言は一度数えた。 `main_dependency` は `SerrePositivity.main_statement` の型と証明からの推移閉包。公開されている 11-21 の下調べ582件のうち570件が一致した。外れた12件は `Iso`、dg 関手、または豊穣圏を仮定するだけのセルデータだった。一方、結論の型を直接読むことで261件（局所登録・別名・束を含む）が加わった。[下調べの表](../../../research/cleanup-zero-base/enrichment/constructions-draft.csv)

本体の行は **831件・2,717行**。Mathlib の既存構造を型や本体に渡す使用例は、豊穣化の種類と圏・基底・関手の引数の形で **532組**。 一つの適用が複数の宣言に入る場合は、型・本体で同じ組を用いる宣言数を領域別に記した。型・値を別々に数えず、局所変数の結合位置による綴りの違いは共通のパラメータとして扱った。型と値の参照から選んだ利用宣言は7,371件。適用組ごとの利用宣言を領域別に足した延べ件数は12,336件。 Mathlib の適用組に本体の行数を割り付けると二重計上になるため、行数は構成・登録が実際に書かれた本体宣言だけを数えた。

採取と照合の証拠は git 外の `~/serre-evidence/enrichment/6f5d0dd6c-stage1/` に置いた。圏・基底・関手への適用と、各組を使った宣言の対応を JSON Lines に保存した。

## やり方ごとの件数と行数

セルは件数 / 行数。宣言のコマンドから末尾までを数えた。下表の「その他」には既存 instance の登録、構造を束ねる定義、ホモトピー的な構成が含まれる。

| 領域 | 直接 | 作用から | 基底の取り替え | Mathlib そのまま | その他 |
|---|---:|---:|---:|---:|---:|
| `CategoryTheory` | 1 / 26 | 2 / 26 | 2 / 16 | 0 / 0 | 2 / 24 |
| `DifferentialGraded` | 26 / 207 | 0 / 0 | 1 / 1 | 0 / 0 | 12 / 60 |
| `EInfinity` | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 5 / 9 |
| `InfinityCategories.HA` | 6 / 95 | 0 / 0 | 1 / 3 | 1 / 2 | 7 / 86 |
| `InfinityCategories.HTT` | 0 / 0 | 0 / 0 | 0 / 0 | 1 / 2 | 0 / 0 |
| `InfinityCategories.Kerodon` | 24 / 213 | 0 / 0 | 4 / 16 | 0 / 0 | 2 / 17 |
| `InfinityCategories.Project` | 21 / 205 | 0 / 0 | 10 / 48 | 1 / 2 | 14 / 27 |
| `KST.Comparison` | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 1 / 1 |
| `KST.DerivedBlowup` | 4 / 33 | 0 / 0 | 0 / 0 | 0 / 0 | 2 / 8 |
| `KST.DerivedGeometry` | 2 / 9 | 0 / 0 | 0 / 0 | 0 / 0 | 2 / 5 |
| `KST.Fibration` | 0 / 0 | 0 / 0 | 0 / 0 | 2 / 4 | 23 / 44 |
| `KST.LocalizingInvariants` | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 114 / 207 |
| `KST.NonConnective` | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 89 / 172 |
| `KST.SConstruction` | 17 / 158 | 0 / 0 | 0 / 0 | 8 / 22 | 157 / 328 |
| `KST.Spectra` | 11 / 74 | 0 / 0 | 3 / 12 | 35 / 97 | 201 / 377 |
| `Spectra.General` | 0 / 0 | 4 / 49 | 0 / 0 | 0 / 0 | 7 / 14 |
| `Spectra.ModelCategory` | 0 / 0 | 0 / 0 | 1 / 7 | 0 / 0 | 2 / 5 |
| `Spectra.Stable` | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 2 / 4 |
| `Spectra.SymmetricSpectrum` | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 1 / 2 |
| **計** | 112 / 1,020 | 6 / 75 | 22 / 103 | 48 / 129 | 643 / 1,390 |

Mathlib 適用 64件、ホモトピー的構成 9件、型別名 2件、束 11件、構成 94件、構造の型 7件、登録 614件、通常圏との比較 30件。局所 instance の反復で行数の大きいものは、`OmegaSpectrum.simplicialCategory`、`PointedEnrichment.simplicialCategory` の既存値の登録が中心。別の豊穣化を作る例と区別した。

主定理の閉包にある本体の構成・型は 6件。[`DGCategory`](../../../SerrePositivity/DifferentialGraded/Category/Basic.lean#L62)、[`ofHomObjects`](../../../SerrePositivity/DifferentialGraded/Category/Basic.lean#L80)、[`complexEnrichment`](../../../SerrePositivity/DifferentialGraded/Category/Basic.lean#L555)、[`ringEnrichment`](../../../SerrePositivity/DifferentialGraded/Category/Basic.lean#L566)、[`dgFullSubcategoryEnrichment`](../../../SerrePositivity/DifferentialGraded/Category/Tensor.lean#L317)、[`moduleEnrichment`](../../../SerrePositivity/DifferentialGraded/Module/Left/CategoryComparison.lean#L96)。

## 法則を自分で書く場所

単位律・結合律と通常射の恒等・合成保存を、構造またはその直近の法則用の補題で書く箇所は **39件**。構造の法則フィールドで直接書く部分は計 **381 行**。 別の法則補題の行数は参照先の宣言スパンで、同じ補題を複数の構成が呼ぶ場合は表にそれぞれ示した。計算のために他の補題を経由する部分の総行数は含めていない。

| 宣言 | フィールド内の行 | 呼び出す局所法則の行 |
|---|---:|---:|
| [`ordinaryCategory`](../../../SerrePositivity/CategoryTheory/Enriched/RepresentedMapping.lean#L637) | 4 | 0 |
| [`enrichedCategory`](../../../SerrePositivity/CategoryTheory/Enriched/Transport.lean#L138) | 15 | 0 |
| [`ordinaryCategory`](../../../SerrePositivity/CategoryTheory/Enriched/Transport.lean#L253) | 11 | 0 |
| [`complexEnrichment`](../../../SerrePositivity/DifferentialGraded/Category/Basic.lean#L555) | 3 | 36 |
| [`ringEnrichment`](../../../SerrePositivity/DifferentialGraded/Category/Basic.lean#L566) | 5 | 0 |
| [`complexEnrichedOrdinary`](../../../SerrePositivity/DifferentialGraded/Category/Basic.lean#L651) | 12 | 0 |
| [`dgCategory`](../../../SerrePositivity/DifferentialGraded/Resolution/Free/Evaluation.lean#L989) | 12 | 0 |
| [`enrichedCategory`](../../../SerrePositivity/InfinityCategories/HA/ModelCategoryComparison/Hammock/MarkedSpineEnrichedCategory.lean#L24) | 9 | 0 |
| [`freeHammockEnrichedCategory`](../../../SerrePositivity/InfinityCategories/HA/ModelCategoryComparison/SimplicialLocalization/ComparisonEnrichment.lean#L34) | 30 | 0 |
| [`localizationEnrichedCategory`](../../../SerrePositivity/InfinityCategories/HA/ModelCategoryComparison/SimplicialLocalization/Enrichment.lean#L35) | 21 | 0 |
| [`walkingAdjunctionEnrichedCategory`](../../../SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionEnrichment.lean#L56) | 12 | 0 |
| [`walkingMonadEnrichedCategory`](../../../SerrePositivity/InfinityCategories/HA/Monads/WalkingMonadEnrichment.lean#L40) | 19 | 0 |
| [`dgAlgebraPointEnrichment`](../../../SerrePositivity/InfinityCategories/HA/Section7_1_1/DGAlgebraDerivedInfinity.lean#L29) | 3 | 0 |
| [`stableCategory_enrichedCategory`](../../../SerrePositivity/InfinityCategories/HA/StableInfinityCategories/Infinity/ExactEnrichment.lean#L79) | 19 | 0 |
| [`stableCategory_simplicialCategory`](../../../SerrePositivity/InfinityCategories/HA/StableInfinityCategories/Infinity/StableInfinity.lean#L46) | 18 | 0 |
| [`enrichedCategory`](../../../SerrePositivity/InfinityCategories/Kerodon/AdjointFunctors/Localization/DiscreteEnrichment.lean#L46) | 9 | 0 |
| [`enrichedCategory`](../../../SerrePositivity/InfinityCategories/Kerodon/AdjointFunctors/Localization/EnrichedCategory.lean#L31) | 9 | 0 |
| [`standardEnrichedCategory`](../../../SerrePositivity/InfinityCategories/Kerodon/ExamplesOfInfinityCategories/DifferentialGradedCategories/Enrichment.lean#L30) | 18 | 0 |
| [`doldKanSimplicialCategory`](../../../SerrePositivity/InfinityCategories/Kerodon/ExamplesOfInfinityCategories/DifferentialGradedCategories/SimplicialCategory.lean#L34) | 22 | 0 |
| [`kanDiagramObject_simplicialCategory`](../../../SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/KanDiagramSimplicialCategory.lean#L56) | 2 | 0 |
| [`strictTransportDiagramObject_simplicialCategory`](../../../SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/StrictTransportDiagramInfinity.lean#L60) | 3 | 0 |
| [`presentableEnrichedCategory`](../../../SerrePositivity/InfinityCategories/Kerodon/LargeInfinityCategories/PresentableInfinityCategories/PresentableEnrichedCategory.lean#L152) | 0 | 43 |
| [`edgewiseEnrichedObject_simplicialCategory`](../../../SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/ConjugateAndDualFibrations/EdgewiseEnrichedCategory.lean#L148) | 2 | 0 |
| [`cellZeroInputDGCategory`](../../../SerrePositivity/InfinityCategories/Project/DerivedCategories/ClosureFunctoriality/CellZeroObstruction.lean#L37) | 3 | 0 |
| [`dgModuleFunctorResolutionDGCategory`](../../../SerrePositivity/InfinityCategories/Project/DerivedCategories/MappingAndStability/DGModules/Resolutions/DGModuleFunctorResolutionCategory.lean#L27) | 15 | 0 |
| [`dgFunctorCommaDGCategory`](../../../SerrePositivity/InfinityCategories/Project/DerivedCategories/MappingAndStability/FunctorComparisons/DGFunctors/DGFunctorCommaCategory.lean#L27) | 15 | 0 |
| [`simplicialPairObject_enrichedCategory`](../../../SerrePositivity/InfinityCategories/Project/FibrationAuxiliaries/Simplicial/SimplicialPairCategory.lean#L41) | 24 | 0 |
| [`enrichedCategory`](../../../SerrePositivity/InfinityCategories/Project/KanComplexAuxiliaries/Subdivision/EnrichedOrderedCylinder.lean#L109) | 0 | 23 |
| [`enrichedCategory`](../../../SerrePositivity/InfinityCategories/Project/KanComplexAuxiliaries/Subdivision/EnrichedParameterCylinderCategory.lean#L108) | 0 | 58 |
| [`pointEnrichedCategory`](../../../SerrePositivity/InfinityCategories/Project/KanComplexAuxiliaries/Subdivision/EnrichedParameterCylinderPoint.lean#L27) | 18 | 0 |
| [`enrichment`](../../../SerrePositivity/KST/DerivedGeometry/LinearComplexEnrichment.lean#L135) | 1 | 38 |
| [`enrichedFunctorCollage_enrichedCategory`](../../../SerrePositivity/KST/SConstruction/EnrichedFunctorCollage.lean#L202) | 0 | 71 |
| [`perfDGInputNativeEnrichment`](../../../SerrePositivity/KST/SConstruction/PerfDGInputSimplicial.lean#L29) | 19 | 0 |
| [`perfDGInputSimplicialCategory`](../../../SerrePositivity/KST/SConstruction/PerfDGInputSimplicial.lean#L88) | 1 | 10 |
| [`smallDGNativeEnrichment`](../../../SerrePositivity/KST/SConstruction/SmallDGNativeSimplicialCategory.lean#L30) | 16 | 0 |
| [`smallBundledDGNativeSimplicialCategory`](../../../SerrePositivity/KST/SConstruction/SmallDGNativeSimplicialCategory.lean#L83) | 1 | 10 |
| [`pointedEnrichment`](../../../SerrePositivity/KST/Spectra/SpectrumPointedEnrichment.lean#L20) | 0 | 17 |
| [`mappingEnrichedCategory`](../../../SerrePositivity/KST/Spectra/SpectrumSimplicialCategory.lean#L71) | 0 | 36 |
| [`simplicialCategory`](../../../SerrePositivity/KST/Spectra/SpectrumSimplicialCategory.lean#L85) | 10 | 0 |

## 同じ M・V と別の表示

| M と V | 作り方と比較の有無 |
|---|---|
| 非有界複体 Ch(A) を Ch(A) で | Hom 複体を直接使う `complexEnrichment` と、閉構造からの Mathlib 自己豊穣化。 `complexEnrichment_eq_closed` が豊穣構造の一致を証明する。`complexEnrichedOrdinary` は同じ Hom に通常の鎖写像との同値を足す。 [比較](../../../SerrePositivity/DifferentialGraded/Complexes/HomLimits.lean#L121) |
| 基点付き単体集合を基点付き単体集合で、SSet を SSet で | 局所登録に現れる `enrichedCategorySelf` と `enrichedOrdinaryCategorySelf` は Mathlib の同じ自己豊穣化を供給。通常圏を接続する値から親の豊穣化を再利用できる。基点付き単体集合を SSet で豊穣化する忘却版は基底が異なる。 [忘却版](../../../SerrePositivity/KST/Spectra/PointedEnrichment.lean#L34) |
| 一般対称スペクトルを C で | `mappingEnrichedCategory` と `mappingEnrichedOrdinaryCategory` は同じ作用・同じ右随伴を与える。後者は通常射との同値を足す。豊穣 Hom と第0段の写像右随伴は `mappingEnrichedHomFunctorIso` で比較済み。 [豊穣化](../../../SerrePositivity/Spectra/General/MappingEnrichment.lean) · [比較](../../../SerrePositivity/Spectra/General/MappingFunctorComparison.lean) |
| Ω スペクトルとその比較用対象 | `mappingEnrichedCategory` の厳密合成、`pointedEnrichment`、その忘却を使う BF の比較用 Hom がある。点付き版と SSet 版では基底が異なり、`Object`・`FullObject`・`CommonObject` は別の対象型。 `productToSmash_pointedComposition` が合成の成分を比較し、`commonOriginalInfinityEquivalence` が神経の同値を与える。構造全体の等号をそれらの主張からは取らない。 [合成](../../../SerrePositivity/KST/Spectra/RawSpectrumPointedCompositionComparison.lean#L23) · [神経](../../../SerrePositivity/KST/Spectra/D3CommonCoherentComparison.lean#L47) |
| 本体の SSet 可表 Hom 関手 | Kerodon の `representableHomFunctor` と FrameHom の `enrichedHomFunctor` が同じ単体的圏で Hom と前後合成を定める。 `enrichedHomFunctor_eq_representableHomFunctor` で一致済み。 [比較](../../../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/FrameHom/EnrichedHomYoneda.lean#L26) |

## 作用と基底変更を共通化できる場所

- **一般・円周の対称スペクトル。** 自由第0段と評価の随伴、および相対テンソルの閉構造による `Ev₀ [X,Y]` の表示がある。(イ) は各段作用の結合子・単位子で評価則を組み立てる。(ウ) は自由第0段を強モノイダル関手として比較し、随伴からの `Ev₀` の lax 構造を使う。現行 `legacyOrdinaryCategory` はその後に基点を忘れる別の基底変更。順番と単位点の比較を一般論で揃えられる。 [作用と随伴](../../../SerrePositivity/Spectra/General/MappingObject.lean) · [忘却を含むモデル比較](../../../SerrePositivity/Spectra/ModelCategory/SimplicialHomComparison.lean#L25)
- **基点付き単体集合を SSet で豊穣にする場合。** `adjoinBasepointAdjunction` と、基点付加が積を smash に送る比較・単位比較がある。(ウ) は閉 smash の自己豊穣化を忘却で輸送する現行の構成。(イ) は基点付加した係数を smash する作用と内部 Hom の随伴。同じ二つの表示を結ぶ一般定理の最小の試験例になる。 [基点付加](../../../SerrePositivity/Spectra/PointedSimplicialSet/AdjoinBasepoint.lean#L25) · [積の比較](../../../SerrePositivity/Spectra/PointedSimplicialSet/AdjoinBasepointProduct.lean#L22) · [現行の輸送](../../../SerrePositivity/KST/Spectra/PointedEnrichment.lean#L34)
- **KST の Ω スペクトル。** 基点の忘却による (ウ) の適用は BF の比較用豊穣化に実在する。各段 cotensor と BF 置換射影の比較は単体的 Hom のファイブレーション性を伴うが、厳密な二変数随伴をこの比較だけからは得られない。(イ) として同じ選択を表すにはその随伴を照合する。 [BF の余テンソル比較](../../../SerrePositivity/KST/Spectra/SpectrumCotensorPointedComparison.lean#L29)
- **dg と SSet の変換。** Dold–Kan と Alexander–Whitney の Hom・単位・合成をその場の次数で書いており、lax monoidal な基底変更 (ウ) の候補。正規化を強モノイダルと仮定して (イ) との比較に入れることはできない。 [dg からの単体的合成](../../../SerrePositivity/InfinityCategories/Kerodon/ExamplesOfInfinityCategories/DifferentialGradedCategories/Enrichment.lean#L30)

## ホモトピー的な構成

弱同値の語、解消、Kan 置換から初めて Hom を作るもの。既存の強モノイダル左随伴の mate やテンソルの表現に置き換える候補からは外す。採取した箇所は次のとおり。

- `EInfinity` の [`algebraHammockEnrichedCategory`](../../../SerrePositivity/EInfinity/BarrattEccles/HammockEnrichedCategory.lean#L39)
- `InfinityCategories.HA` の [`enrichedCategory`](../../../SerrePositivity/InfinityCategories/HA/ModelCategoryComparison/Hammock/MarkedSpineEnrichedCategory.lean#L24)
- `InfinityCategories.HA` の [`hammockEnrichedCategory`](../../../SerrePositivity/InfinityCategories/HA/ModelCategoryComparison/SimplicialLocalization/ComparisonEnrichment.lean#L27)
- `InfinityCategories.HA` の [`freeHammockEnrichedCategory`](../../../SerrePositivity/InfinityCategories/HA/ModelCategoryComparison/SimplicialLocalization/ComparisonEnrichment.lean#L34)
- `InfinityCategories.HA` の [`localizationEnrichedCategory`](../../../SerrePositivity/InfinityCategories/HA/ModelCategoryComparison/SimplicialLocalization/Enrichment.lean#L35)
- `InfinityCategories.HA` の [`localizationSimplicialCategory`](../../../SerrePositivity/InfinityCategories/HA/ModelCategoryComparison/SimplicialLocalization/Enrichment.lean#L73)
- `InfinityCategories.HA` の [`kanHammockSimplicialCategory`](../../../SerrePositivity/InfinityCategories/HA/ModelCategoryComparison/SimplicialLocalization/KanComparisonNerves.lean#L29)
- `InfinityCategories.HA` の [`kanFreeHammockSimplicialCategory`](../../../SerrePositivity/InfinityCategories/HA/ModelCategoryComparison/SimplicialLocalization/KanComparisonNerves.lean#L31)
- `InfinityCategories.Kerodon` の [`enrichedCategory`](../../../SerrePositivity/InfinityCategories/Kerodon/AdjointFunctors/Localization/EnrichedCategory.lean#L31)

## dg と SSet を一般論に通すときの負担

- **軽くなる見込み。** dg と SSet の双方にある豊穣関手圏の恒等・合成・評価、対象対の豊穣化と包含、充満部分圏、可表 Hom の組み立て。SSet 側の単体ごとの積の外延性と dg 側の成分別の組紐計算は、一つの構造の法則から場合分けできる。既存の Mathlib の反対と基底変更は適用を共有できる。
- **重くなる見込み。** V 双加群の合成では二変数の余極限保存、豊穣 coend の Fubini、単位・結合の比較が新たに表に出る。豊穣関手圏・V 米田には添字の宇宙と選んだ end の射影の照合が要る。基底変更と end/coend の交換では保存仮定が増える。符号、微分、純テンソル、K-flat と導来化の短い成分計算は、一般論の証明に置き換えるとむしろ長くなる。
 [dg の構成別照合](../../../research/cleanup-zero-base/enrichment/general-theory.md#d-dg-で実装されている-v-に一般な構成)

## 段2で決める点

1. 三つの構成の入力型と出力型。既存の `MonoidalLeftAction`、二つの `ParametrizedAdjunction`、`TensorCotensor`、`EnrichedRepresentability` のどこで選択を持たせるか。
2. (イ) の自己作用との一致、(ウ) の随伴付き基底変更との一致、テンソル表現からの作用復元。対象同型で足りる用途と、Hom の射・単位・合成・転置の比較が必要な用途を定める。
3. 元の通常圏と単位点の同値の扱い。忘却による基底変更は単位点の全単射を別に必要とする。閉自己豊穣化、基点付き単体集合、円周スペクトルで同じインターフェースを試す。
4. V 関手圏の end、V 圏のテンソル、充満部分圏、米田、V 加群、V 双加群の順で、選ぶ極限・余極限の大きさと保存性を決める。普通の添字圏の end と豊穣自然性の end は別の型として照合する。
5. 登録を一か所にできる型と、閉自己豊穣化・基底変更による複数の構造から scoped にする型。局所登録が集中する Ω スペクトル等は LI-W1 と調整する。
6. 先に既存の法則と比較をつなぐ。次数・符号・ホモロジーを使う計算 API、局所化で新しく作る Hom はそれぞれの理論側に置く。
