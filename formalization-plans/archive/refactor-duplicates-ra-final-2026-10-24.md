# 正規化ハッシュによる重複一覧

- 基準 HEAD: `b225f2ad39c25fee36283b1bcd81202385da5fbc`（追跡済みファイルの作業ツリー）。
- 対象: `SerrePositivity/InfinityCategories`、11711 Lean ファイル。未追跡ファイルは除外。
- 正規化: コメント（入れ子を含む）、import 行、namespace/end 行を除き、
  文字列外の空白をトークン区切りに統一し、`KanSection.` 修飾を除く。
- 名前空間・import を無視する候補検出であり、型・証明の同一性は変更前に個別確認する。
- 実体の重複: 0 群、余分なコピー 0 本。
- 宣言を持たない一致: 1 群（集約・シム等、実体の重複には数えない）。

## 宣言なし `120970d812836f19888625587a4606a5ad23cef31c8684e601771552548fc6b9`

- `SerrePositivity/InfinityCategories/Coherent.lean` (31 行)
- `SerrePositivity/InfinityCategories/Core.lean` (499 行)
- `SerrePositivity/InfinityCategories/Core/Fibrations.lean` (25 行)
- `SerrePositivity/InfinityCategories/Core/InvertibleEdge.lean` (10 行)
- `SerrePositivity/InfinityCategories/Core/MappingSpace.lean` (33 行)
- `SerrePositivity/InfinityCategories/Core/MappingSpaceKan.lean` (10 行)
- `SerrePositivity/InfinityCategories/DGNerve.lean` (65 行)
- `SerrePositivity/InfinityCategories/Derived.lean` (2246 行)
- `SerrePositivity/InfinityCategories/Derived/Gluing.lean` (702 行)
- `SerrePositivity/InfinityCategories/Derived/Perfect.lean` (14 行)
- `SerrePositivity/InfinityCategories/Derived/Support.lean` (22 行)
- `SerrePositivity/InfinityCategories/DoldKanComparison.lean` (76 行)
- `SerrePositivity/InfinityCategories/F1.lean` (2685 行)
- `SerrePositivity/InfinityCategories/F1/Cocartesian.lean` (609 行)
- `SerrePositivity/InfinityCategories/F1/Cocartesian/BaseChangeSecondHomDecompositionEndpoints.lean` (4 行)
- `SerrePositivity/InfinityCategories/F1/Fibrations.lean` (33 行)
- `SerrePositivity/InfinityCategories/F1/Yoneda/PresheafDensity.lean` (8 行)
- `SerrePositivity/InfinityCategories/F1B.lean` (745 行)
- `SerrePositivity/InfinityCategories/F2/CatInfinity.lean` (36 行)
- `SerrePositivity/InfinityCategories/F2/Compact.lean` (89 行)
- `SerrePositivity/InfinityCategories/F2/FilteredExchange.lean` (1074 行)
- `SerrePositivity/InfinityCategories/F2/Idempotent.lean` (171 行)
- `SerrePositivity/InfinityCategories/F2/Ind.lean` (562 行)
- `SerrePositivity/InfinityCategories/F2/Presentable.lean` (138 行)
- `SerrePositivity/InfinityCategories/HomotopyLimits.lean` (1079 行)
- `SerrePositivity/InfinityCategories/Stable.lean` (644 行)

<!-- duplicate-pairs-v1
[]
-->
