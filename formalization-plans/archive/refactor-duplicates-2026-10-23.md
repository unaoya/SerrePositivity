# 正規化ハッシュによる重複一覧

- 基準 HEAD: `1b32cd7a87e5298a2b90815063d2a3f8bf5e166d`（追跡済みファイルの作業ツリー）。
- 対象: `SerrePositivity/InfinityCategories`、11632 Lean ファイル。未追跡ファイルは除外。
- 正規化: コメント（入れ子を含む）、import 行、namespace/end 行を除き、
  文字列外の空白をトークン区切りに統一し、`KanSection.` 修飾を除く。
- 名前空間・import を無視する候補検出であり、型・証明の同一性は変更前に個別確認する。
- 実体の重複: 18 群、余分なコピー 18 本。
- 宣言を持たない一致: 1 群（集約・シム等、実体の重複には数えない）。

## 実体 `cc583141e26d689548cf099dddef8df2f6b985200479b1c4780ad2f5e92ef399`

- `SerrePositivity/InfinityCategories/F1/CocartesianCrossingComparison.lean` (95 行)
- `SerrePositivity/InfinityCategories/F1B/KanSectionCocartesianCrossingComparison.lean` (95 行)

## 実体 `c8f6a8a3e42cdcaae554881f0bcf2aa738c4da11e1d2d1f7e38a7e86773fc2bb`

- `SerrePositivity/InfinityCategories/F1/CosliceFiberCoordinates.lean` (189 行)
- `SerrePositivity/InfinityCategories/F1B/KanSectionCosliceFiberCoordinates.lean` (190 行)

## 実体 `ac040ae778e8455571942a3e5be6485758e376fc49ec93ad6a5b2699b4fb4541`

- `SerrePositivity/InfinityCategories/F1/CosliceFiberDiagramChange.lean` (79 行)
- `SerrePositivity/InfinityCategories/F1B/KanSectionCosliceFiberDiagramChange.lean` (79 行)

## 実体 `88aa68ba2c9ab3b1531da7396f04104ed9a658ae0d03262cfb40642b4e4ca103`

- `SerrePositivity/InfinityCategories/F1/CosliceFiberPostcomposition.lean` (100 行)
- `SerrePositivity/InfinityCategories/F1B/KanSectionCosliceFiberPostcomposition.lean` (100 行)

## 実体 `82e4459d401bc534e298235a8c6e92f372882f35e23be75804ee02c5104f31a8`

- `SerrePositivity/InfinityCategories/F1/CosliceFiberUniversal.lean` (116 行)
- `SerrePositivity/InfinityCategories/F1B/KanSectionCosliceFiberUniversal.lean` (116 行)

## 実体 `67039ef17971ec5047c02af89b1b8b77ddf4eb5f440bdcc4ee34ef750ac2e41a`

- `SerrePositivity/InfinityCategories/F1/CosliceIntervalNaturality.lean` (128 行)
- `SerrePositivity/InfinityCategories/F1B/KanSectionCosliceIntervalNaturality.lean` (128 行)

## 実体 `a76ae445063b2441d0f00588619e72e660aa8b764d2b58e839ab5fcf3b847128`

- `SerrePositivity/InfinityCategories/F1/CoslicePinchedIso.lean` (140 行)
- `SerrePositivity/InfinityCategories/F1B/KanSectionCoslicePinchedIso.lean` (140 行)

## 実体 `046967814f62b7f06113b14f69173c7d0bcf1f46bfbf340eb72e15be9a89f700`

- `SerrePositivity/InfinityCategories/F1/InnerAnodynePrismExtension.lean` (113 行)
- `SerrePositivity/InfinityCategories/F1B/KanSectionInnerAnodynePrismExtension.lean` (113 行)

## 実体 `3a5aa7b04bdb1218b8b5b0280cc44ee513265fb8c05396f86f1209dddda73b64`

- `SerrePositivity/InfinityCategories/F1/IntervalComparisonMono.lean` (111 行)
- `SerrePositivity/InfinityCategories/F1B/KanSectionIntervalComparisonMono.lean` (111 行)

## 実体 `fe69e52adcc039c5dfacb334770c1218f842f989f55a6cb30f16547454d60902`

- `SerrePositivity/InfinityCategories/F1/JoinDiagramRightRelativeRetraction.lean` (62 行)
- `SerrePositivity/InfinityCategories/F2/JoinRightRelativeRetraction.lean` (62 行)

## 実体 `ee891d8b6e0643a1be39a0d11d031cc9d37d5e1b08eb72ea63755d4436f8185c`

- `SerrePositivity/InfinityCategories/F1/MappingCylinderGeneralComparison.lean` (83 行)
- `SerrePositivity/InfinityCategories/F1B/KanSectionMappingCylinderGeneralComparison.lean` (83 行)

## 実体 `b63521b8f1e4b293b62bbeb1d9b3bd89bbae4eca09bd7025b1ace92e4f4811f3`

- `SerrePositivity/InfinityCategories/F1/MappingCylinderIntervalEquivalence.lean` (49 行)
- `SerrePositivity/InfinityCategories/F1B/KanSectionMappingCylinderIntervalEquivalence.lean` (49 行)

## 実体 `2990e3b68a6124f0d2ea13b5afaaccd8eac2d345f7435958f9bf9245b0714815`

- `SerrePositivity/InfinityCategories/F1/MappingCylinderQuasicategoryComparison.lean` (59 行)
- `SerrePositivity/InfinityCategories/F1B/KanSectionMappingCylinderQuasicategoryComparison.lean` (59 行)

## 実体 `02d7e0ca178595f40b2c0ba77e79b53f5ff74c7af934b706de530b250432323b`

- `SerrePositivity/InfinityCategories/F1/MappingSpaceIntervalComparison.lean` (135 行)
- `SerrePositivity/InfinityCategories/F1B/KanSectionMappingSpaceIntervalComparison.lean` (135 行)

## 実体 `7f0d4d567ebd2a893a853e1de720f1d71e87968a44bc4f3e010f1a90fa6fd9a3`

- `SerrePositivity/InfinityCategories/F1/RelativeFunctorEvaluation.lean` (41 行)
- `SerrePositivity/InfinityCategories/F1B/KanSectionRelativeEvaluation.lean` (41 行)

## 実体 `d5121866a27b451066ae81b6ce4d6f045a364246097820c508b09add388fc540`

- `SerrePositivity/InfinityCategories/F1/RelativeJoinCocartesianFibration.lean` (72 行)
- `SerrePositivity/InfinityCategories/F1B/KanSectionRelativeJoinCocartesianFibration.lean` (72 行)

## 実体 `839661f849eb56544186ce2c8029736b8b7985b3b1820da945e841d213419126`

- `SerrePositivity/InfinityCategories/F1/RelativeJoinCrossingCocartesian.lean` (81 行)
- `SerrePositivity/InfinityCategories/F1B/KanSectionRelativeJoinCrossingCocartesian.lean` (81 行)

## 実体 `ee7b33fc47ac7f2cd2b99d4c4e0d5489f5845546f5094279d0c0cea8209e398c`

- `SerrePositivity/InfinityCategories/F1/RelativeJoinExtensionEquivalence.lean` (86 行)
- `SerrePositivity/InfinityCategories/F1B/KanSectionRelativeJoinExtensionEquivalence.lean` (86 行)

## 宣言なし `120970d812836f19888625587a4606a5ad23cef31c8684e601771552548fc6b9`

- `SerrePositivity/InfinityCategories/Coherent.lean` (31 行)
- `SerrePositivity/InfinityCategories/Core.lean` (433 行)
- `SerrePositivity/InfinityCategories/Core/InvertibleEdge.lean` (10 行)
- `SerrePositivity/InfinityCategories/Core/MappingSpaceKan.lean` (10 行)
- `SerrePositivity/InfinityCategories/DGNerve.lean` (63 行)
- `SerrePositivity/InfinityCategories/Derived.lean` (2238 行)
- `SerrePositivity/InfinityCategories/Derived/Gluing.lean` (670 行)
- `SerrePositivity/InfinityCategories/Derived/Perfect.lean` (14 行)
- `SerrePositivity/InfinityCategories/Derived/Support.lean` (22 行)
- `SerrePositivity/InfinityCategories/DoldKanComparison.lean` (76 行)
- `SerrePositivity/InfinityCategories/F1.lean` (3283 行)
- `SerrePositivity/InfinityCategories/F1/CocartesianBaseChangeSecondHomDecompositionEndpoints.lean` (4 行)
- `SerrePositivity/InfinityCategories/F1B.lean` (737 行)
- `SerrePositivity/InfinityCategories/F2/Compact.lean` (89 行)
- `SerrePositivity/InfinityCategories/F2/Idempotent.lean` (171 行)
- `SerrePositivity/InfinityCategories/F2/Ind.lean` (550 行)
- `SerrePositivity/InfinityCategories/F2/Presentable.lean` (39 行)
- `SerrePositivity/InfinityCategories/Stable.lean` (644 行)

<!-- duplicate-pairs-v1
[["SerrePositivity/InfinityCategories/F1/CocartesianCrossingComparison.lean", "SerrePositivity/InfinityCategories/F1B/KanSectionCocartesianCrossingComparison.lean"], ["SerrePositivity/InfinityCategories/F1/CosliceFiberCoordinates.lean", "SerrePositivity/InfinityCategories/F1B/KanSectionCosliceFiberCoordinates.lean"], ["SerrePositivity/InfinityCategories/F1/CosliceFiberDiagramChange.lean", "SerrePositivity/InfinityCategories/F1B/KanSectionCosliceFiberDiagramChange.lean"], ["SerrePositivity/InfinityCategories/F1/CosliceFiberPostcomposition.lean", "SerrePositivity/InfinityCategories/F1B/KanSectionCosliceFiberPostcomposition.lean"], ["SerrePositivity/InfinityCategories/F1/CosliceFiberUniversal.lean", "SerrePositivity/InfinityCategories/F1B/KanSectionCosliceFiberUniversal.lean"], ["SerrePositivity/InfinityCategories/F1/CosliceIntervalNaturality.lean", "SerrePositivity/InfinityCategories/F1B/KanSectionCosliceIntervalNaturality.lean"], ["SerrePositivity/InfinityCategories/F1/CoslicePinchedIso.lean", "SerrePositivity/InfinityCategories/F1B/KanSectionCoslicePinchedIso.lean"], ["SerrePositivity/InfinityCategories/F1/InnerAnodynePrismExtension.lean", "SerrePositivity/InfinityCategories/F1B/KanSectionInnerAnodynePrismExtension.lean"], ["SerrePositivity/InfinityCategories/F1/IntervalComparisonMono.lean", "SerrePositivity/InfinityCategories/F1B/KanSectionIntervalComparisonMono.lean"], ["SerrePositivity/InfinityCategories/F1/JoinDiagramRightRelativeRetraction.lean", "SerrePositivity/InfinityCategories/F2/JoinRightRelativeRetraction.lean"], ["SerrePositivity/InfinityCategories/F1/MappingCylinderGeneralComparison.lean", "SerrePositivity/InfinityCategories/F1B/KanSectionMappingCylinderGeneralComparison.lean"], ["SerrePositivity/InfinityCategories/F1/MappingCylinderIntervalEquivalence.lean", "SerrePositivity/InfinityCategories/F1B/KanSectionMappingCylinderIntervalEquivalence.lean"], ["SerrePositivity/InfinityCategories/F1/MappingCylinderQuasicategoryComparison.lean", "SerrePositivity/InfinityCategories/F1B/KanSectionMappingCylinderQuasicategoryComparison.lean"], ["SerrePositivity/InfinityCategories/F1/MappingSpaceIntervalComparison.lean", "SerrePositivity/InfinityCategories/F1B/KanSectionMappingSpaceIntervalComparison.lean"], ["SerrePositivity/InfinityCategories/F1/RelativeFunctorEvaluation.lean", "SerrePositivity/InfinityCategories/F1B/KanSectionRelativeEvaluation.lean"], ["SerrePositivity/InfinityCategories/F1/RelativeJoinCocartesianFibration.lean", "SerrePositivity/InfinityCategories/F1B/KanSectionRelativeJoinCocartesianFibration.lean"], ["SerrePositivity/InfinityCategories/F1/RelativeJoinCrossingCocartesian.lean", "SerrePositivity/InfinityCategories/F1B/KanSectionRelativeJoinCrossingCocartesian.lean"], ["SerrePositivity/InfinityCategories/F1/RelativeJoinExtensionEquivalence.lean", "SerrePositivity/InfinityCategories/F1B/KanSectionRelativeJoinExtensionEquivalence.lean"]]
-->
