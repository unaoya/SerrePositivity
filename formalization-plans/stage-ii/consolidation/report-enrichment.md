# EN-W1 報告

現在地は段3aの事前照合で停止。A3 の既存宣言5件の改名と、段2bの新しい型を同じ名前に割り当てる指定が衝突した。

## 段1　豊穣化の全体調査

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

## 段2　一般論の型と配置

main `6fc90a31e` を取り込んだ `e991924fd` で、A3・A2、B1–B4、C-軽と二つの試験例の型をまとめた。既存の120宣言は残す33、改名7、移す37、消える見込み43に割り振った。SU-W1 段14a の型案58件から、作用と豊穣 Hom の部分を A3・B3、二重転置の部分を B1 に引き継いだ。 [型案・行き先・段3の分け方](../../../research/cleanup-zero-base/enrichment/stage2-types.md)

- A3 では、左作用と写像対象の随伴から通常の圏付きの豊穣化を作る。余テンソルの随伴を加えると B3 の `TensorCotensor` を得る。B1 では二つの通常随伴から対象の同型すら従わない三元鎖の反例がある。自然な作用結合子と既存の `unitIso` に対する左右単位の整合を、別の入力 `TensorAssociativity` に置いた。 `TensorCotensor` と `EnrichedRepresentability` の欄は現行の形で足りる。
- B2 は通常圏を持つ元の対象型上に戻せる。固定 Mathlib の `TransportEnrichment.enrichedOrdinaryCategory` の値を型別名なしの戻り型に置く照合が通った。B4 の単位・合成・通常射と二つの転置を、Hom・テンソル・余テンソルの自然同型で比べる。B4 の合成には `F.Braided` を加えた。
- 可換モノイド上の加群の対称性と閉性、自由加群の強モノイダル性と組紐は既存の本体 instance が供給する。スペクトルの自由第0段全体の強モノイダル性は推論できず、列の自由第0段で比較の自然性と整合を組む必要がある。内部 Hom 二変数関手の定義的一致と、相対テンソル・余テンソルから各段の表示への既存の二つの自然同型を確認した。基点付き単体集合でも smash の対称性・閉性と基点付加の随伴は揃っている。基点付加の強モノイダル構造を組み、随伴の右 lax 構造と現行の忘却の比較を照合する。
- main `662cd9182` の dg 追加に沿い、段1の構成別表を受けて C-軽の型を dg・SSet の利用先に結び付けた。軽くなるのは充満部分圏、対と挿入、豊穣関手圏の合成・評価、可表 Hom に重複する構造則。負担が増えるのは全豊穣 Hom に関する自然性を実装する等化子、添字の大きさ、基底変更との交換に必要な保存性。符号・微分・各次数の計算は利用側の表示に要る。豊穣米田・余米田の同型と双加群の合成は保留。 [dg の表](../../../research/cleanup-zero-base/enrichment/general-theory.md#d-dg-で実装されている-v-に一般な構成)
- 型ヘッダー71件を既存成果物の import と `lake env lean --stdin` で精査した。新設する値と補題は宣言の型として検査し、依存する型で定義的な還元が必要なところは既存の構成による検査用の値を stdin 上で組んだ。二つの試験例の B2 適用も、強モノイダル性を引数に取った形で具体化した。これは型検査で、設計した法則の証明は実装段に残る。リポジトリの Lean、監査、対応表の変更は0。ビルドは実行せず、SU-W1 段14の保留は継続。

改名を除く新規の入口は型案上64件、型・実装を合わせ990–1,890行の見積もり。旧宣言43件・296行の削減見込みは利用側の移行後。段3は A2・A3・B3、B1、B2・B4、基点付き単体集合の順に切る。段4はスペクトル、段5は C-軽の dg と SSet への適用。

## 段2b　閉じた加群を入口にした設計改訂

main `bfc902136` を取り込んだ `abc86598b` で、Git 外の Riehl・Hovey・Kelly・Hovey 論文の本文と、固定 Mathlib `e6bbacd0e1b7307ff6e17da09cd2455f60804fa6` のソースを照合した。四文献の番号を型案に付け、原典が直接述べない補助と、対応表にあるが独立の型を立てない項目を記した。文献対応表 §2 の確認箇所を埋め、R (3.4.4) の二項 lax 比較と、通常圏を保つための単位点の全単射を区別した。 [文献対応表](enrichment-literature-map.md) · [型案](../../../research/cleanup-zero-base/enrichment/stage2-types.md)

- 供給口は `ClosedModule`。H 4.1.6 の整合を持つ左作用と随伴二つを束ねる。既存の `TensorCotensor` は取り出せる随伴部分として残す案にした。モデル適合と関数複体・局所化には明示的な引数型が62箇所あり、個々の射影まで直接書き換える場合は重複を除いて191行。スペクトルの名前付きの供給と参照は8ファイル23行。型・射影の集計で、実装時の import や転置の整合の証明行は別。ファイルと行を型案に掲げた。
- B1 の二つの係数自然性と二つの単位点の式には、自然な結合子と左右単位の整合で足りる。A3 の結合律には作用の五角形が要る。次数付きベクトル空間で自然な結合子だけを変えたときに合成が結合的でなくなる例を記した。B1 と B2 の対象同型は四本の全単射の列を試験射に自然に作り、通常の米田で取り出す。
- B2 の加群 M は任意。U の自己閉加群を入れた場合として、対称スペクトル（現行の HS の (C=D) の場合）と基点付き単体集合の型を照合した。B4 は、文献順と Mathlib 順の合成の間の組紐を F が保つことを明示する。R 3.7.12 は制限作用由来の豊穣化で型を立て、G による輸送表示との比較には同じ組紐の条件を使う。
- B6 は Mathlib の `Functor.LaxLeftLinear`（R 10.1.5）と `Functor.LeftLinear`（H 4.1.7 の左版）を使う。Mathlib の `EnrichedNatTrans` と `EnrichedCat.bicategory` は通常圏に忘れた自然性を使うため、V 随伴には全 Hom 上の単位・余単位の自然性を課す。スペクトルの149行を照合し、通常射との比較5行、固定原対象での随伴の式6行、懸垂・ループの比較候補1行を印した。名簿外の `freeAtAdjunction n` と懸垂の随伴には、テンソル比較の整合を確かめる手順を記した。 [スペクトルの対応表](../../../research/cleanup-zero-base/spectra/stage14.csv)
- 132件の署名を `lake env lean --stdin` で既存成果物に対して検査した。証明を省いた宣言に加え、制限作用、随伴二つの接続、二つの試験例への適用、四本の `Equiv.trans` の接続を stdin 上で照合した。実装の証明とビルドは後段。Lean ソースの変更は0。

新しい入口と補助は125件、既存名の改名・置換は7件、実装の見積もりは1,670–3,100行。段3a は A2・A3・B3 と自己閉加群、3b は B1、3c は一般の B2 と B4、3d は B6、3e は基点付き単体集合。段3の実装と SU-W1 段14は引き続き監査の区切りを待つ。

## 段3a　事前照合と停止箇所

main `3ed0c1724` を取り込んだ。R Definition 10.1.3・Proposition 10.1.4 と H Definition 4.1.6・4.1.12 を Git 外の本文で確認した。R の閉じた加群は二変数随伴・結合・単位を取り、段2bの採用案はさらに H の四重結合と単位の整合を備える。H の右作用は左作用に読み替える。 [指示と停止条件](enrichment-w1.md) · [段2bの型と移行表](../../../research/cleanup-zero-base/enrichment/stage2-types.md)

### 最初の二点

- `ClosedModuleOn.tensor_eq` は `tensorIso : @MonoidalLeftAction.curriedAction V M _ _ _ action ≅ adjunctions.tensor` に替えられる。単位の比較は `tensorIso.hom` の単位での成分、旧 `unitIso.hom)、作用単位子の順射の三つで述べる。`ParametrizedAdjunctionTransport.left` に `tensorIso.symm` を渡して余テンソル随伴を移し、`CategoryTheory.flipFunctor` がその逆同型を写したものを渡して写像随伴を移す。この二つを束ねる `ClosedModuleOn.toClosedModule` は stdin 上の定義まで照合した。
- 主張中のインスタンスは明示引数で渡せる。閉加群の二つの随伴の定義域に `@MonoidalLeftAction.curriedAction V M _ _ _ action` を使い、B3 の戻り型は `@TensorCotensor V _ _ M _ (ofAction L)` と書く。前者は構造欄、後者は同じ戻り型を使う例で検査した。型の意味は段2bの局所インスタンスによる指定と同じ。

### 停止条件に当たった所

段2bの行き先の表で「改名」とした A3 の下記5件は、旧宣言と、同じ表が改名先に指定する新宣言のカーネルの型が異なる。既存成果物に対する `#check @…` と、段2bの署名を照合した。新しい方はすべて `L : ClosedModule V M` を入口とする。

| 旧名（`SerrePositivity.` を省略） | 表の改名先 | 旧宣言が受け取るもの |
| --- | --- | --- |
| `RepresentedMappingEnrichment.evaluation` | `actionEvaluation` | `H : V ⥤ M ⥤ M`、`R : M → M ⥤ V`、対象ごとの写像随伴。V のモノイダル構造も仮定しない |
| `RepresentedMappingEnrichment.unit` | `actionUnit` | 上のデータに `H.obj (𝟙_ V) ≅ 𝟭 M` を加える |
| `RepresentedMappingEnrichment.arrowEquiv` | `actionHomEquiv` | `unit` と同じ入力。通常射と点の同値を取る |
| `RepresentedMappingEnrichment.ordinaryCategory` | `ofAction` | `H`、結合・単位の比較、対象ごとの写像随伴、豊穣化の法則を個別に受け取る |
| `RepresentedHomFunctor.homFunctorIso_ofParametrized` | `ofActionHomIso` | `H`、結合と単位の比較・整合の一部、写像側のパラメータ付き随伴、個別の豊穣化の法則 |

`evaluation` の旧入力の具体例として、V を終対象だけのモノイダル圏、M を二元鎖、H の値を最小元への定値関手にできる。固定した各 X について `H.flip.obj X` の値は初期対象なので写像側の右随伴がある。一方、最大元 X では単位の作用が X と同型にならず、この H を保った閉じた加群は作れない。従って旧署名を保つ改名と、表の同じ改名先で閉じた加群を受け取る新 API は、一つの宣言には収まらない。既存のスペクトルの利用側が、評価・単位・通常射の同値・通常豊穣化を現に旧署名で呼び出している。 [旧宣言](../../../SerrePositivity/CategoryTheory/Enriched/RepresentedMapping.lean#L429) · [スペクトルでの呼出し](../../../SerrePositivity/Spectra/General/MappingEnrichment.lean#L24)

型保存の改名と新 API を別の宣言名に配置するか、この5件を改名から置換に変更して利用側を移行するかで、表と前後監査の判定が変わる。段3aのこの指定を確定できるまで、略号登録・Lean 差分・利用側の変更は0件。従って新規宣言ごとの検査時間、制限対象の出現箇所、長い新規証明は該当なし。既存成果物を限定して読む `lake env lean --stdin` の事前照合は bulk 鍵の下で終了値0。全モジュールのビルド、linter・`#lint`、`scripts/audit2/premerge.py` は実装候補ができる段階の検査として未実行。
