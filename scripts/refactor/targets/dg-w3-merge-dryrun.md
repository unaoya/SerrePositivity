# DG-W3 土台の統合草案・検証（§11.1）

基点 `e14680ad0`、命名案 [dg-w3-names.md](dg-w3-names.md)。対応表の 611 元を git ls-files と照合し、除外 0。48 統合先の元は重複なし。D3 と重なる 3 元は (b) の後に再照合する。

`python3 -B scripts/refactor/merge_modules.py scripts/refactor/targets/dg-w3-merge-plan.json --area SerrePositivity.DifferentialGraded --check --max-lines 1700 --report REPORT.md` は終了 0。private 衝突 0（paste_associator を 2 か所、post_paste を 1 か所改名する案）。最大 1601 行、上限超過 0。604 警告はすべて無名 section の補完。各警告を下に掲載。

## 611 元への直接 import と下流

Archive・scripts を除外。直接辺は **611 元を import する元集合外のファイル**から数え、逆閉包は道具の downstream（元・先・利用元を起点とする本番ソース）を数えた。Paper と Asymptotic も行に含め、直接依存と間接依存を区別する。末尾の自動出力の 1,183 辺は DG 全体への外部辺。

| 領域 | 611 元への直接辺 | 逆閉包のファイル |
| --- | ---: | ---: |
| Asymptotic | 0 | 0 |
| BhattScholze | 0 | 12 |
| CLMST | 0 | 91 |
| CommutativeAlgebra | 0 | 1 |
| DG 内の統合元以外 | 655 | 0 |
| DifferentialGraded | 611 | 1895 |
| EInfinity | 50 | 1775 |
| HomologicalAlgebra | 0 | 3 |
| InfinityCategories | 56 | 3324 |
| InfinityCategories.Derived | 453 | 3686 |
| Inputs | 0 | 1 |
| KST | 281 | 5519 |
| Paper | 0 | 11 |
| SerrePositivity | 0 | 1 |

DifferentialGraded 行の直接辺 611 本は DG 集約から 611 元への辺である。DG 内のその他の直接辺 655 本は別行に載せた。外部領域からの直接辺は IC/Derived 453、その他の IC 56、KST 281、EInfinity 50 の計 840。逆閉包の DG は DifferentialGraded 行にまとめた。逆閉包 16319 本、単独換算 272.0–408.0 分（1.0–1.5 秒/本）。ソース段階の見積もりで、Paper の主定理へ届く。

# モジュール統合 dry-run

統合先 48、元 611 本。move/split 草案 0 件は未適用。
生成行数：最小 292、中央値 1082、平均 1058.1、最大 1601。

| 統合先 | 元本数 | 元行数 | 生成行数 | import 和 | 外部 importer | 警告数 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `SerrePositivity.DifferentialGraded.Derived.BimoduleComposition.Coherence` | 15 | 1327 | 1406 | 4 | 12 | 15 |
| `SerrePositivity.DifferentialGraded.Derived.BimoduleComposition.Resolution` | 17 | 1481 | 1566 | 5 | 24 | 17 |
| `SerrePositivity.DifferentialGraded.Complexes.Perturbation` | 16 | 1137 | 1214 | 13 | 91 | 15 |
| `SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct` | 16 | 1040 | 1116 | 16 | 71 | 13 |
| `SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain` | 9 | 611 | 667 | 4 | 32 | 9 |
| `SerrePositivity.DifferentialGraded.Complexes.TensorShift` | 14 | 760 | 835 | 12 | 29 | 14 |
| `SerrePositivity.DifferentialGraded.Complexes.TensorJoin` | 22 | 977 | 1075 | 5 | 57 | 22 |
| `SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying` | 13 | 963 | 1034 | 7 | 76 | 12 |
| `SerrePositivity.DifferentialGraded.Complexes.HomComplex` | 4 | 254 | 292 | 3 | 46 | 4 |
| `SerrePositivity.DifferentialGraded.Complexes.HomLimits` | 6 | 602 | 644 | 7 | 35 | 6 |
| `SerrePositivity.DifferentialGraded.Category.Basic` | 16 | 1364 | 1446 | 21 | 122 | 15 |
| `SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence` | 8 | 494 | 546 | 7 | 118 | 8 |
| `SerrePositivity.DifferentialGraded.Category.Tensor` | 13 | 697 | 770 | 7 | 68 | 12 |
| `SerrePositivity.DifferentialGraded.Functor.Closed` | 10 | 461 | 526 | 11 | 43 | 10 |
| `SerrePositivity.DifferentialGraded.Module.Basic` | 13 | 1363 | 1433 | 11 | 61 | 13 |
| `SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison` | 9 | 656 | 708 | 4 | 61 | 9 |
| `SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations` | 18 | 1381 | 1465 | 11 | 105 | 18 |
| `SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison` | 14 | 1018 | 1089 | 7 | 95 | 14 |
| `SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom` | 16 | 1289 | 1365 | 13 | 57 | 16 |
| `SerrePositivity.DifferentialGraded.Module.ConeConstruction` | 13 | 1293 | 1348 | 5 | 63 | 13 |
| `SerrePositivity.DifferentialGraded.Module.Graded` | 12 | 1054 | 1117 | 11 | 82 | 12 |
| `SerrePositivity.DifferentialGraded.Module.ActionLimits` | 3 | 622 | 653 | 4 | 24 | 3 |
| `SerrePositivity.DifferentialGraded.Module.TensorFree` | 5 | 720 | 758 | 4 | 27 | 5 |
| `SerrePositivity.DifferentialGraded.Module.Disk` | 8 | 864 | 910 | 12 | 34 | 8 |
| `SerrePositivity.DifferentialGraded.Module.ShiftResolution` | 22 | 1498 | 1601 | 19 | 69 | 22 |
| `SerrePositivity.DifferentialGraded.Module.ConeRotation` | 6 | 625 | 667 | 7 | 15 | 6 |
| `SerrePositivity.DifferentialGraded.Module.MaurerCartanTriangulated` | 14 | 953 | 1030 | 10 | 28 | 14 |
| `SerrePositivity.DifferentialGraded.Derived.Projective` | 17 | 1224 | 1304 | 7 | 56 | 17 |
| `SerrePositivity.DifferentialGraded.Derived.ScalarExtension` | 11 | 843 | 908 | 11 | 25 | 11 |
| `SerrePositivity.DifferentialGraded.Complexes.Cone` | 17 | 1312 | 1401 | 8 | 37 | 17 |
| `SerrePositivity.DifferentialGraded.Functor.ModuleValued` | 7 | 456 | 512 | 10 | 17 | 7 |
| `SerrePositivity.DifferentialGraded.Functor.ModuleShift` | 5 | 362 | 399 | 9 | 15 | 5 |
| `SerrePositivity.DifferentialGraded.Derived.Tensor` | 10 | 698 | 757 | 6 | 13 | 10 |
| `SerrePositivity.DifferentialGraded.Derived.BimoduleTensor` | 17 | 1296 | 1381 | 16 | 22 | 17 |
| `SerrePositivity.DifferentialGraded.Derived.Basic` | 26 | 1341 | 1446 | 26 | 98 | 26 |
| `SerrePositivity.DifferentialGraded.Derived.KFlat` | 10 | 821 | 878 | 6 | 15 | 10 |
| `SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.ModelIndependence` | 16 | 1421 | 1498 | 9 | 20 | 16 |
| `SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.IteratedModels` | 10 | 1047 | 1101 | 11 | 16 | 10 |
| `SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.FunctorCoherence` | 12 | 1433 | 1500 | 6 | 8 | 12 |
| `SerrePositivity.DifferentialGraded.Derived.Functor` | 12 | 926 | 990 | 13 | 34 | 12 |
| `SerrePositivity.DifferentialGraded.Module.FreeSphere` | 9 | 453 | 513 | 12 | 29 | 9 |
| `SerrePositivity.DifferentialGraded.Module.Functor` | 20 | 1216 | 1321 | 25 | 25 | 20 |
| `SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction` | 15 | 1342 | 1414 | 25 | 38 | 15 |
| `SerrePositivity.DifferentialGraded.Derived.Bimodule` | 14 | 1473 | 1545 | 12 | 22 | 14 |
| `SerrePositivity.DifferentialGraded.Derived.LeftUnit` | 8 | 751 | 798 | 8 | 7 | 8 |
| `SerrePositivity.DifferentialGraded.Derived.AssociatorLeft` | 18 | 1484 | 1571 | 6 | 12 | 18 |
| `SerrePositivity.DifferentialGraded.Derived.AssociatorMiddle` | 17 | 1461 | 1543 | 4 | 6 | 17 |
| `SerrePositivity.DifferentialGraded.Derived.Paired` | 8 | 679 | 730 | 11 | 8 | 8 |

## 警告

### `SerrePositivity.DifferentialGraded.Derived.BimoduleComposition.Coherence`

- SerrePositivity.DifferentialGraded.Derived.CompositionFamilies: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionAssociatorIndependence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionAssociatorKFlat: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionAssociatorComponents: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionAssociatorComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionTriangle: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionTriangleFamily: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionPentagonPaths: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionPentagonInner: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionPentagonComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionPentagonShort: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionPentagonKFlat: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionFamilies: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionPentagonFamilies: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionPentagon: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Derived.BimoduleComposition.Resolution`

- SerrePositivity.DifferentialGraded.Derived.BimoduleRestriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleRestrictionEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionResolution: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionResolutionValues: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionRightUnit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionLeftUnit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionLeftUnitComputation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionPairResolution: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionPairNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionValueNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionInnerNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionAssociatorResolution: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionAssociatorNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionAssociatorFunctors: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionAssociator: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleResolutionLift: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Complexes.Perturbation`

- SerrePositivity.DifferentialGraded.Complexes.UnitTensor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.UnitBoundary: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.Cells: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.SphereHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.Composition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.CompositionLaws: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.AcyclicCone: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.Perturbation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.PerturbationMap: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.PerturbationRestriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.MapComponentFunctions: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.ExactColimits: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.DiskGenerator: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.DiskFiltration: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.DiskContractible: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct`

- SerrePositivity.DifferentialGraded.Complexes.CellCriterion: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorCylinder: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorCoproductExt: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorInterchange: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorRightTwoCoproductExt: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.ProductAcyclic: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.ParameterCross: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.FilteredCycles: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TowerPrimitives: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TowerLimitAcyclic: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.CoproductSupport: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.CoproductSubfamily: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain`

- SerrePositivity.DifferentialGraded.Complexes.TensorEnriched: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorRightHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorRightComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorGradedZero: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorCochainInterchange: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorCochainComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorClosedZero: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochainNaturality: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Complexes.TensorShift`

- SerrePositivity.DifferentialGraded.Complexes.TensorShift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorShiftSecondNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.QuasiIsoCycles: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.KProjectiveHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.KProjectiveTensor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.CycleTransport: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.SphereTensorShift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.SphereTensorShiftNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.PrefixTensorCochain: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.PrefixTensorCochainPostcompose: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.PrefixTensorCochainAction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.RightTripleCochainExt: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.SphereCochainExt: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorJoinEvaluation: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Complexes.TensorJoin`

- SerrePositivity.DifferentialGraded.Complexes.HomogeneousTransport: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.UnitorCochainNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.RightUnitorEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.UnitSandwichEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.CoproductHomologySupport: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.PrefixTensorCochainPrecomp: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.AssociatorCochainNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.AssociatorCochainFactors: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorCarryCochain: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochainLaws: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochainLeftMap: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochainEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorJoinHomNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorJoinAssociativity: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorCarryAssociativity: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorJoinUnit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorCarryUnit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorUnitInsertion: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorJoinRightAction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorJoinActionNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorTwoUnitInsertion: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.TensorCompositionAssociativity: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying`

- SerrePositivity.DifferentialGraded.Complexes.Currying: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.Braiding: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.Closed: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.AssociatorReindex: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.CurryingNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.CurryingEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.CochainInterchange: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.LowerTruncationSequence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.MaurerCartanPerturbation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.MaurerCartanHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.MaurerCartanHomMap: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.MaurerCartanTargetHom: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Complexes.HomComplex`

- SerrePositivity.DifferentialGraded.Complexes.HomComplex: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.HomFunctor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.Unit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.GradedConjugationComposition: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Complexes.HomLimits`

- SerrePositivity.DifferentialGraded.Complexes.Enrichment: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.ClosedMaps: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.Zero: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.HomLimits: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.HomColimits: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.Biproduct: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Category.Basic`

- SerrePositivity.DifferentialGraded.Category.Basic: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Category.Homotopy: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Category.HomotopyHomology: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Category.HomotopyHomologyLinear: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Category.HomotopyHomologyNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Category.Examples: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Category.Components: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Category.Comparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Category.HomTransport: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Category.LocalizationHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Category.TriangleComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Category.QuotientComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Category.IdempotentTelescope: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Category.TriangulatedTransport: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Category.FaithfulHomConstruction: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence`

- SerrePositivity.DifferentialGraded.Functor.Basic: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.Small: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.HomIso: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.Components: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.FullHomLift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.ComplexValued: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.QuasiIsoHomology: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Category.Tensor`

- SerrePositivity.DifferentialGraded.Category.Tensor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Category.TensorElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Category.TensorReindex: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Category.TensorComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Category.Induced: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Category.FullSubcategory: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Category.Restriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Category.RestrictionComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Category.OppositeHomotopy: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Category.TensorInclusions: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Category.TensorMixed: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Category.ComplexHomotopyComparison: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Functor.Closed`

- SerrePositivity.DifferentialGraded.Functor.Tensor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.Opposite: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.QuasiEquivalenceOpposite: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.ClosedComplex: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.ClosedConjugationPasting: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.ClosedConjugationTensorComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.ModuleCone: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.InducedClosedConjugate: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.InducedClosedTransport: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.InducedClosedParameter: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Module.Basic`

- SerrePositivity.DifferentialGraded.Module.Basic: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Hom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Left: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.TriangleShiftMap: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Representable: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Action: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Yoneda: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Tensor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.LeftAction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.LeftActionComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.LeftRepresentable: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.HomElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Composition: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison`

- SerrePositivity.DifferentialGraded.Module.Category: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Ring: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.RingDGComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.RingHomotopyComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.LeftRing: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.LeftCategory: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.LeftHomElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.LeftEquivalence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.LeftParamNaturality: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations`

- SerrePositivity.DifferentialGraded.Module.Homotopy: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.QuasiIso: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Underlying: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ClosedMaps: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Zero: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Free: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Cone: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ConeDesc: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Shift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.LeftZero: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.LeftQuasiIso: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.LeftQuasiIsoInverse: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Biproduct: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.HomFunctor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.HomWhisker: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.HomIsoSquare: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.HomSquareComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.HomElementComposition: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison`

- SerrePositivity.DifferentialGraded.Module.ConeMaps: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ConeFunctor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ConeGradedSplit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ConeElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ConeTransportIso: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Cylinder: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Precomposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Postcomposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.HomCone: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.HomConeIso: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.HomCycles: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.HomClosedInsertion: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.HomRestrictionComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.HomPostcompositionComposition: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom`

- SerrePositivity.DifferentialGraded.Module.EvaluationReflects: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.TensorSource: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ParamCurry: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ColimitHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.CoproductHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.RestrictionTensor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.RestrictionColimits: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.RestrictionCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.RestrictionGradedSplit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.HomotopyCoproduct: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.HomotopyCoproductUniversal: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.HomRight: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.HomRightContra: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.HomRightContraMaps: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.HomRightFunctor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.HomRightEnriched: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Module.ConeConstruction`

- SerrePositivity.DifferentialGraded.Module.ShiftHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ShiftElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Restriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.RestrictionAction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.RestrictionEnriched: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ConeLift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ConeHomotopyDesc: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ConeShiftElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ConeShift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ConeElementRelations: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ConeCompositionInputs: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ConeCompositionDesc: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ConeCompositionHomotopy: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Module.Graded`

- SerrePositivity.DifferentialGraded.Module.Isomorphism: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.GradedSplit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.GradedSplitElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.GradedSplitHomExact: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.GradedSplitCokernel: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.YonedaFunctor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.YonedaClosedPreimage: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.LeftMorphisms: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.LeftClosedMaps: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.LeftYonedaFunctor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.LeftMapNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ShiftCoherence: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Module.ActionLimits`

- SerrePositivity.DifferentialGraded.Module.ActionChain: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Limits: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Colimits: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Module.TensorFree`

- SerrePositivity.DifferentialGraded.Module.TensorShift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.TensorAdjunction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.TensorUnit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.FreeHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.FreeHomNaturality: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Module.Disk`

- SerrePositivity.DifferentialGraded.Module.GradedCoproduct: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.HomotopyQuasiIso: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Acyclic: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Cells: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.CellLifting: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.DiskCover: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.DiskFiltration: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.DiskCoverFiltration: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Module.ShiftResolution`

- SerrePositivity.DifferentialGraded.Module.KernelCells: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ShiftHomotopy: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ShiftHomotopyComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ShiftCompatibility: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ShiftComparisonEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Semifree.Basic: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.FreeSphereShift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ShiftCoproduct: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ConeShiftSquares: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ConeShiftTriangleOrdinary: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.LeftShiftElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ShiftUnitElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ShiftUnitRelations: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ShiftUnitDifferential: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ShiftBlocks: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ShiftBlockLinear: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ShiftBlockComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ResolutionSequence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ResolutionQuasiIso: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ResolutionGradedSteps: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ResolutionFreeQuotients: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Semifree.Resolution: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Module.ConeRotation`

- SerrePositivity.DifferentialGraded.Module.ConeHomotopyMap: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ConeRotationInputs: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.HomotopyConeTriangle: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ConeContractible: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ConeRotation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ConeRotationHomotopy: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Module.MaurerCartanTriangulated`

- SerrePositivity.DifferentialGraded.Module.MaurerCartanEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.MaurerCartan: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.MaurerCartanTargetHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.MaurerCartanTargetHomDifferential: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ContractibleTriangleIso: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.DistinguishedTriangles: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ConeShiftTriangle: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ConeRotationTriangle: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ConeCompositionTriangle: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Pretriangulated: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.Triangulated: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.HomotopyEvaluationTriangles: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.HomotopyConeEndpointTransport: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.AcyclicTriangulated: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Derived.Projective`

- SerrePositivity.DifferentialGraded.Derived.ProjectiveHomQuasiIso: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.ProjectiveHomotopyLifting: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.ProjectiveHomotopyHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.ProjectivePrecomposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.ProjectiveLocalizationHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.ProjectiveDerivedLifting: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.HomOut: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.HomOutPrecomposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.ResolutionComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.ProjectiveResolution: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.ProjectiveResolutionLift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.HomChoice: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.HomBifunctor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.HomBifunctorChoice: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.ResolutionHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.ResolutionFunctor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.ResolutionFunctorChoice: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Derived.ScalarExtension`

- SerrePositivity.DifferentialGraded.Derived.BimoduleBasic: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleLiftIso: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.ScalarExtensionHomotopy: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.ScalarExtension: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.ScalarExtensionExact: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.ScalarExtensionKFlat: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.ScalarExtensionComplex: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.ScalarExtensionNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.ScalarExtensionComplexNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.ScalarExtensionTensor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.ScalarExtensionTensorCoherence: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Complexes.Cone`

- SerrePositivity.DifferentialGraded.Complexes.Shift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.ShiftCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.ShiftRepresentation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.Cone: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.ConeHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.ConeMaps: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.ConeDesc: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.ConeShift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.ConeRotation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.ConeElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.ConeGradedSplit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.ConeComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.ConeCompositionDesc: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.ConeRepresentation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.HomCovariant: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.HomContravariant: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Complexes.HomContravariantMaps: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Functor.ModuleValued`

- SerrePositivity.DifferentialGraded.Functor.HomotopyAdjunction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.ContractingElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.HomogeneousNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.CoproductMatrixComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.ModuleValuedCone: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.ModuleValuedConeTransport: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.ModuleExtensionConjugation: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Functor.ModuleShift`

- SerrePositivity.DifferentialGraded.Functor.ModuleShift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.ModuleShiftOpposite: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.ModuleConeRelations: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.ModuleConeIso: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Functor.QuasiEquivalenceTensor: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Derived.Tensor`

- SerrePositivity.DifferentialGraded.Derived.RightTensor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.RightTensorResolution: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.RightTensorLeftFunctor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.TensorChoiceLeft: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.LeftTensorInversion: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.TensorBifunctor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.TensorBifunctorChoice: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.TensorResolutionComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.TensorComputationNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.TensorBifunctorComputationChoice: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Derived.BimoduleTensor`

- SerrePositivity.DifferentialGraded.Derived.BimoduleComposeHomotopy: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleSemifreeComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleSemifreeComposeComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleSemifreeLift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleSourceHomotopy: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleRestrictionProjective: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleRightProjective: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleTensor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleTensorMaps: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleTensorUnit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleTensorFunctor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleTensorComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleTensorAssociator: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleTensorEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleTensorTriangle: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleTensorNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleTensorKFlatComparison: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Derived.Basic`

- SerrePositivity.DifferentialGraded.Derived.Basic: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.LeftBasic: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.Evaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.Shift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.Ring: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.Restriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.RestrictionCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.HomotopyComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.HomotopyShift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.Triangulated: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.Linear: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AcyclicZero: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.ConeTriangles: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.HomotopyLinear: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.VerdierComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.EvaluationTriangles: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.HomotopicallyProjective: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.FreeProjective: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.FreeSphereProjective: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.ProjectiveHomotopy: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.ProjectiveContraction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.CoproductProjective: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.GradedExtensionProjective: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.SemifreeProjective: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.RestrictionProjective: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.ProjectiveFiniteOperations: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Derived.KFlat`

- SerrePositivity.DifferentialGraded.Derived.RightKFlatComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleTensorPentagon: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleLocalization: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleHomotopy: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleResolution: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleReplacement: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleAugmentation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleLeftRestriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleGlobalAugmentation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleEquivalence: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.ModelIndependence`

- SerrePositivity.DifferentialGraded.Derived.BimoduleResolutionLiftTensor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleHomotopy: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleCalculation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleComparisonFamily: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleComparisonLocalization: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleIndependence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleSecondFactor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleKFlatIndependence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleSemifreeIndependence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleSemifreeSecondFactor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleSecondFamily: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleKFlatFamily: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleFullComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleModuleEquivalence: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.IteratedModels`

- SerrePositivity.DifferentialGraded.Derived.RestrictionShift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.RestrictionTriangles: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.CompactAdjunctionCoproducts: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleComparisonComputation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleCompositeFamily: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleCompositePresentation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleTransportComputation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleFullCalculation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleRestrictionModelCalculation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleRestrictionSourceNormalization: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.FunctorCoherence`

- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleQuasiIso: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleEquivalence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleResolvedCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleIdentity: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleFunctorComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleCanonicalComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleIdentityFamily: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleIdentityFull: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleAugmentedSource: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleAugmentedTransport: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleIteratedComputation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleFullComposition: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Derived.Functor`

- SerrePositivity.DifferentialGraded.Derived.Coproducts: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.RingCoproducts: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.IdempotentComplete: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.CoproductProjection: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.ModuleFunctorProjective: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.RightKFlatIsoLift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.RightKFlatIsoLiftComputation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionResolved: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorSecondMiddleRestrictionResolved: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.FunctorExtension: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.FunctorExtensionNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.FunctorExtensionRepresentable: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Module.FreeSphere`

- SerrePositivity.DifferentialGraded.Module.FunctorExtension: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.FunctorExtensionMaps: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.RingComplexFunctor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.FreeSphereClosedLinear: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.FreeSphereClosedCoefficient: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.FreeSphereClosedCoefficientCycles: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.FreeSphereClosedCoproductSupport: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.FreeSphereCoproductClosedMatrix: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.RestrictionRepresentable: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Module.Functor`

- SerrePositivity.DifferentialGraded.Module.RingProjective: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.RepresentableClosedCycles: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.RepresentableClosedCoproductSupport: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.FreeRestrictionComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ExtensionRepresentableComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ExtensionRepresentableClosedNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.RepresentableCoproductClosedMatrix: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.FunctorGraphActions: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.FunctorExtensionEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.FunctorExtensionCounit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.FunctorExtensionCounitNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.FunctorExtensionInsertion: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.FunctorExtensionUnit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.FunctorExtensionUnitNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.FunctorExtensionAdjunction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.FunctorExtensionRepresentableUnit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ExtensionFreeAdjunction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ExtensionFreeUnitComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.ExtensionFreeNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Module.FreeSphereImageCoefficient: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction`

- SerrePositivity.DifferentialGraded.Derived.LeftUnitRestrictionModel: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.FunctorExtensionProjective: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.FunctorExtensionHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.FunctorExtensionProjectiveNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.FunctorExtensionHomNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.FunctorExtensionTriangles: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.FunctorExtensionPerfect: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.FunctorExtensionUnitComputation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.FunctorExtensionRepresentableUnit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.FunctorExtensionUnitAll: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.RestrictionConservative: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.FunctorDerivedEquivalence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.FunctorExtensionKFlatUnit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleRestrictionEquivalence: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Derived.Bimodule`

- SerrePositivity.DifferentialGraded.Derived.MiddleRestrictionIdentification: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.MiddleRestrictionComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.MiddleRestrictionIteratedPresentation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleLeftRestrictionBase: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleLeftRestrictionFamily: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleLeftRestrictionFull: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleLeftRestrictionComputation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleRightRestrictionBase: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleRightRestrictionFamily: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleRightRestrictionFull: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleRightRestrictionResolution: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleOutputRestriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleSourceIdentification: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleSourceFull: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Derived.LeftUnit`

- SerrePositivity.DifferentialGraded.Derived.RightUnitRestriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.RightUnitRestrictionFull: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.RightUnitRestrictionCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.LeftUnitRestrictionFull: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.LeftUnitRestrictionNormalization: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.LeftUnitRestrictionSource: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.LeftUnitRestrictionTransport: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.LeftUnitRestrictionCoherence: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Derived.AssociatorLeft`

- SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleMiddleComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorLeftRestrictionBase: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorLeftRestrictionKFlat: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorLeftRestrictionPresentation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorLeftRestrictionInner: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorLeftRestrictionNested: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorLeftRestrictionPair: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorLeftRestrictionModel: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorLeftRestrictionFamilies: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorLeftRestrictionCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorRightRestrictionBase: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorRightRestrictionKFlat: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorRightRestrictionPresentation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorRightRestrictionNested: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorRightRestrictionPair: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorRightRestrictionModel: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorRightRestrictionFamilies: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorRightRestrictionCoherence: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Derived.AssociatorMiddle`

- SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionKFlat: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionPresentation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionFactors: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionAugmentation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionInner: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionInnerModel: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionNested: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionPair: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionModel: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionFamilies: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorSecondMiddleRestrictionKFlat: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorSecondMiddleRestrictionInner: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorSecondMiddleRestrictionNested: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorSecondMiddleRestrictionPair: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorSecondMiddleRestrictionModel: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.AssociatorSecondMiddleRestrictionFamilies: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Derived.Paired`

- SerrePositivity.DifferentialGraded.Derived.AssociatorSecondMiddleRestrictionCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.LeftUnitOuterRestriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.PairedRestrictionIdentification: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.PairedRestrictionCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.DiagonalRestriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.DiagonalRestrictionCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleEndpointRestriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Derived.BimoduleSimultaneousRestriction: close 1 anonymous section(s)


## 対象領域の外からの import 辺（Archive・scripts を除く現行ソース）

- EInfinity: 51
- InfinityCategories: 686
- KST: 445
- SerrePositivity: 1

合計 1183 辺。

## 下流見積もり

統合元・D3 移動元/先・import 書換利用元の逆閉包：16319 本（現存本番ソース、Archive を除く）。単独 1.0–1.5 秒/本なら 272.0–408.0 分。監査時間は別。
import のみの書換候補 1077 ファイル。

## move/split 草案


## D5 の dry-run（§11.2）

`python3 -B scripts/refactor/targets/rewrite_dg_docs.py --dry-run`。DG の .lean の外側の /-! … -/ だけを対象とし、通常コメント・文字列・宣言 docstring・コード中の旧参照は全体の書き込み前に STOP。元の相対パスの深さ・anchor・改行を保持する。

| 案内 | 現役 DG（検査を含む） | Archive/DifferentialGraded | 合計（ファイル数＝出現数） |
| --- | ---: | ---: | ---: |
| dg-theory-u12e-general-inventory.md | 453 | 68 | 521 |
| dg-theory-m5-status.md | 9 | 0 | 9 |

期待 521／9 と一致。Archive の 68 は棚卸しの内数。移動済み文書を確認し、実際の統合後に `--plan <その束の計画> --document inventory|status --dry-run` を再実行する。適用モードは同じ指定に `--apply` を渡したときだけ、その計画の統合先に限って書き込む。統合後は複数の参照が同一ファイルになるため、ファイル数と出現数を別々に集計する。
