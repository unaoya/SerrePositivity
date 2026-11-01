# モジュール統合 dry-run

統合先 25、元 95 本。move/split 草案 12 件は未適用。
生成行数：最小 59、中央値 320、平均 404.1、最大 926。

| 統合先 | 元本数 | 元行数 | 生成行数 | import 和 | 外部 importer | 警告数 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `SerrePositivity.CategoryTheory.Monoidal.Mod.Free` | 1 | 127 | 148 | 2 | 6 | 1 |
| `SerrePositivity.CategoryTheory.Monoidal.Mod.Limits` | 3 | 324 | 345 | 2 | 7 | 3 |
| `SerrePositivity.CategoryTheory.Monoidal.Mod.BalancedTensor` | 4 | 571 | 592 | 7 | 7 | 4 |
| `SerrePositivity.CategoryTheory.Monoidal.Mod.Monoidal` | 6 | 871 | 888 | 2 | 13 | 6 |
| `SerrePositivity.CategoryTheory.Monoidal.Mod.Symmetric` | 3 | 288 | 306 | 2 | 7 | 3 |
| `SerrePositivity.CategoryTheory.Monoidal.Mod.FreeTensor` | 6 | 823 | 841 | 4 | 13 | 6 |
| `SerrePositivity.CategoryTheory.Monoidal.Mod.InternalHom` | 4 | 562 | 582 | 4 | 9 | 4 |
| `SerrePositivity.CategoryTheory.Monoidal.Mod.InternalHomFree` | 5 | 482 | 499 | 2 | 10 | 5 |
| `SerrePositivity.CategoryTheory.Monoidal.TensorPower.Basic` | 2 | 217 | 238 | 2 | 10 | 2 |
| `SerrePositivity.CategoryTheory.Monoidal.TensorPower.Permutation` | 4 | 387 | 407 | 5 | 12 | 3 |
| `SerrePositivity.CategoryTheory.Monoidal.TensorPower.Blocks` | 5 | 492 | 510 | 5 | 8 | 5 |
| `SerrePositivity.CategoryTheory.Monoidal.TensorPower.FinBijection` | 2 | 86 | 106 | 4 | 5 | 2 |
| `SerrePositivity.CategoryTheory.Monoidal.Action` | 2 | 211 | 231 | 2 | 3 | 2 |
| `SerrePositivity.CategoryTheory.Monoidal.Braided` | 2 | 97 | 120 | 3 | 5 | 1 |
| `SerrePositivity.CategoryTheory.Enriched.RepresentedMapping` | 8 | 904 | 926 | 8 | 11 | 5 |
| `SerrePositivity.CategoryTheory.Enriched.Transport` | 4 | 286 | 305 | 6 | 11 | 2 |
| `SerrePositivity.CategoryTheory.Enriched.Simplicial` | 1 | 39 | 59 | 1 | 2 | 0 |
| `SerrePositivity.CategoryTheory.Enriched.TensorCotensor` | 3 | 299 | 320 | 4 | 10 | 1 |
| `SerrePositivity.CategoryTheory.Adjunction.Comparison` | 8 | 535 | 559 | 10 | 18 | 5 |
| `SerrePositivity.CategoryTheory.Quiver.FreePathComonad` | 2 | 223 | 247 | 4 | 6 | 1 |
| `SerrePositivity.CategoryTheory.Quiver.PathMap` | 1 | 171 | 193 | 1 | 3 | 0 |
| `SerrePositivity.CategoryTheory.Simplex.Prefix` | 2 | 199 | 223 | 2 | 5 | 0 |
| `SerrePositivity.CategoryTheory.Simplex.GenRelEquivalence` | 3 | 466 | 493 | 2 | 3 | 1 |
| `SerrePositivity.CategoryTheory.Under` | 2 | 82 | 102 | 2 | 3 | 0 |
| `SerrePositivity.CategoryTheory.Limits` | 12 | 822 | 863 | 20 | 17 | 7 |

## 警告

### `SerrePositivity.CategoryTheory.Monoidal.Mod.Free`

- SerrePositivity.CategoryTheory.Monoidal.FreeModule: close 1 anonymous section(s)

### `SerrePositivity.CategoryTheory.Monoidal.Mod.Limits`

- SerrePositivity.CategoryTheory.Monoidal.ModuleLimits: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.ModuleTransport: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.ModuleColimits: close 1 anonymous section(s)

### `SerrePositivity.CategoryTheory.Monoidal.Mod.BalancedTensor`

- SerrePositivity.CategoryTheory.Monoidal.BalancedTensor: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.TensorRightModule: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.BalancedTensorModule: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.BalancedTensorIterated: close 1 anonymous section(s)

### `SerrePositivity.CategoryTheory.Monoidal.Mod.Monoidal`

- SerrePositivity.CategoryTheory.Monoidal.BalancedTensorAssociator: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.BalancedTensorLeftUnit: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.BalancedTensorRightUnit: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.BalancedTensorPentagon: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.BalancedTensorTriangle: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.BalancedTensorMonoidal: close 1 anonymous section(s)

### `SerrePositivity.CategoryTheory.Monoidal.Mod.Symmetric`

- SerrePositivity.CategoryTheory.Monoidal.BalancedTensorSymmetry: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.BalancedTensorHexagon: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.BalancedTensorSymmetric: close 1 anonymous section(s)

### `SerrePositivity.CategoryTheory.Monoidal.Mod.FreeTensor`

- SerrePositivity.CategoryTheory.Monoidal.BalancedTensorFreeRight: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.BalancedTensorFreeLeft: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.BalancedTensorFreePair: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.FreeModuleMonoidal: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.BalancedTensorFreeUnit: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.BalancedTensorFreeAssociator: close 1 anonymous section(s)

### `SerrePositivity.CategoryTheory.Monoidal.Mod.InternalHom`

- SerrePositivity.CategoryTheory.Monoidal.ModuleInternalHom: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.ModuleInternalHomAction: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.ModuleClosed: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.ModuleInternalHomFunctor: close 1 anonymous section(s)

### `SerrePositivity.CategoryTheory.Monoidal.Mod.InternalHomFree`

- SerrePositivity.CategoryTheory.Monoidal.ModuleInternalHomFree: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.ModuleInternalHomFreeNaturality: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.ModuleInternalHomFreeLeftEvaluation: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.ModuleInternalHomTransport: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.ModuleInternalHomTransportComparison: close 1 anonymous section(s)

### `SerrePositivity.CategoryTheory.Monoidal.TensorPower.Basic`

- SerrePositivity.CategoryTheory.Monoidal.TensorPowers: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.TensorPowerCoherence: close 1 anonymous section(s)

### `SerrePositivity.CategoryTheory.Monoidal.TensorPower.Permutation`

- SerrePositivity.CategoryTheory.Monoidal.TensorPermutations: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.AdjacentTranspositions: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.AdjacentBraid: close 1 anonymous section(s)

### `SerrePositivity.CategoryTheory.Monoidal.TensorPower.Blocks`

- SerrePositivity.CategoryTheory.Monoidal.TensorPowerBlockGenerators: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.TensorPowerLeftBlock: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.TensorPowerFirstCrossing: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.TensorPowerBlockPermutations: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.TensorPowerFirstCrossingAction: close 1 anonymous section(s)

### `SerrePositivity.CategoryTheory.Monoidal.TensorPower.FinBijection`

- SerrePositivity.CategoryTheory.Monoidal.PowerBijectionFunctor: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.PowerBijectionAppend: close 1 anonymous section(s)

### `SerrePositivity.CategoryTheory.Monoidal.Action`

- SerrePositivity.CategoryTheory.Monoidal.ActionProductComparison: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.TensorActionTransport: close 1 anonymous section(s)

### `SerrePositivity.CategoryTheory.Monoidal.Braided`

- SerrePositivity.CategoryTheory.Monoidal.InternalHomExchange: close 1 anonymous section(s)

### `SerrePositivity.CategoryTheory.Enriched.RepresentedMapping`

- SerrePositivity.CategoryTheory.Monoidal.MappingAdjunction: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.MappingParametrizedAdjunction: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.RepresentedMappingEnrichment: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.MappingWhiskering: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.RepresentedHomFunctor: close 1 anonymous section(s)

### `SerrePositivity.CategoryTheory.Enriched.Transport`

- SerrePositivity.CategoryTheory.Monoidal.TransportEnrichmentComparisons: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.TransportOrdinaryEnrichment: close 1 anonymous section(s)

### `SerrePositivity.CategoryTheory.Enriched.TensorCotensor`

- SerrePositivity.CategoryTheory.Enriched.TensorUnit: close 1 anonymous section(s)

### `SerrePositivity.CategoryTheory.Adjunction.Comparison`

- SerrePositivity.CategoryTheory.Monoidal.ActionComparisonAdjunction: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.ActionUnitAdjunction: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.PointwiseAdjunction: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.ParametrizedAdjunctionTransport: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Monoidal.ActionComparisonNaturality: close 1 anonymous section(s)

### `SerrePositivity.CategoryTheory.Quiver.FreePathComonad`

- SerrePositivity.CategoryTheory.Quiver.FreePathComonad: close 1 anonymous section(s)

### `SerrePositivity.CategoryTheory.Simplex.GenRelEquivalence`

- SerrePositivity.CategoryTheory.Simplex.PresentationEquivalence: close 1 anonymous section(s)

### `SerrePositivity.CategoryTheory.Limits`

- SerrePositivity.CategoryTheory.Limits.InitialColimits: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Limits.SequentialExtension: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.LiftingProperties.ParametrizedGeneration: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.Groupoid.ThinComponents: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.RelativeArrow: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.FiniteBijectionAction: close 1 anonymous section(s)
- SerrePositivity.CategoryTheory.FiniteBijectionInduction: close 1 anonymous section(s)


## 対象領域の外からの import 辺（Archive・scripts を除く現行ソース）

- Asymptotic: 36
- BhattScholze: 1
- CommutativeAlgebra: 3
- DifferentialGraded: 9
- EInfinity: 25
- HomologicalAlgebra: 5
- HomotopicalAlgebra: 79
- InfinityCategories: 5
- IntersectionMultiplicity: 1
- KST: 18
- KTheory: 9
- LengthAlgebra: 5
- Paper: 1
- PerfectComplex: 10
- SerrePositivity: 8
- Spectra: 98

合計 313 辺。

## 下流見積もり

統合元・D3 移動元/先・import 書換利用元の逆閉包：11888 本（現存本番ソース、Archive を除く）。単独 1.0–1.5 秒/本なら 198.1–297.2 分。監査時間は別。
import のみの書換候補 126 ファイル。

## move/split 草案

- move: `SerrePositivity.CategoryTheory.NerveHomotopy` → `SerrePositivity.HomotopicalAlgebra.Simplicial.NerveHomotopy`。モジュール単位の移動。宣言・名前空間・本文を保持し、全利用元の import を対応表で更新する。
- move: `SerrePositivity.CategoryTheory.NerveHomotopyUniverse` → `SerrePositivity.HomotopicalAlgebra.Simplicial.NerveHomotopyUniverse`。モジュール単位の移動。宣言・名前空間・本文を保持し、全利用元の import を対応表で更新する。
- move: `SerrePositivity.CategoryTheory.NerveSimplexEndpoint` → `SerrePositivity.HomotopicalAlgebra.Simplicial.NerveSimplexEndpoint`。モジュール単位の移動。宣言・名前空間・本文を保持し、全利用元の import を対応表で更新する。
- move: `SerrePositivity.CategoryTheory.NerveSimplexStart` → `SerrePositivity.HomotopicalAlgebra.Simplicial.NerveSimplexStart`。モジュール単位の移動。宣言・名前空間・本文を保持し、全利用元の import を対応表で更新する。
- move: `SerrePositivity.CategoryTheory.NerveSimplexFirstFunctor` → `SerrePositivity.HomotopicalAlgebra.Simplicial.NerveSimplexFirstFunctor`。モジュール単位の移動。宣言・名前空間・本文を保持し、全利用元の import を対応表で更新する。
- move: `SerrePositivity.CategoryTheory.NerveVertices` → `SerrePositivity.HomotopicalAlgebra.Simplicial.NerveVertices`。モジュール単位の移動。宣言・名前空間・本文を保持し、全利用元の import を対応表で更新する。
- move: `SerrePositivity.CategoryTheory.SimplexChainVertices` → `SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexChainVertices`。モジュール単位の移動。宣言・名前空間・本文を保持し、全利用元の import を対応表で更新する。
- move: `SerrePositivity.CategoryTheory.ElementsChainLifting` → `SerrePositivity.HomotopicalAlgebra.Simplicial.ElementsChainLifting`。モジュール単位の移動。宣言・名前空間・本文を保持し、全利用元の import を対応表で更新する。
- move: `SerrePositivity.CategoryTheory.ElementsNaturalPrecomp` → `SerrePositivity.HomotopicalAlgebra.Simplicial.ElementsNaturalPrecomp`。モジュール単位の移動。宣言・名前空間・本文を保持し、全利用元の import を対応表で更新する。
- move: `SerrePositivity.Inputs.Homotopy.KanQuillen` → `SerrePositivity.InfinityCategories.ModelBridge.Inputs.KanQuillen`。モジュール単位の移動。宣言・名前空間・本文を保持し、全利用元の import を対応表で更新する。
- move: `SerrePositivity.Inputs.Homotopy.ResolutionHom` → `SerrePositivity.InfinityCategories.ModelBridge.Inputs.ResolutionHom`。モジュール単位の移動。宣言・名前空間・本文を保持し、全利用元の import を対応表で更新する。
- move: `SerrePositivity.Inputs.Homotopy.SimplicialLevel` → `SerrePositivity.InfinityCategories.ModelBridge.Inputs.SimplicialLevel`。モジュール単位の移動。宣言・名前空間・本文を保持し、全利用元の import を対応表で更新する。
