# 群 A′ の入口と実参照

10 個の HotA モジュールからの 13 辺。各行の「定数」は、そのモジュールが元の禁止 import の定義元から使う例。直接参照が 0 でも、再公開された定数は別途たどった。中核の入口 7 本・全経路・ユーザー宣言ごとの集合・split の keep/moved は [群 A の記録](w2c-a.json) に収録。

| HotA.Simplicial の入口 | 中核からの経路例（末端にモデル側を付記） | 定数の例 | 草案 |
| --- | --- | --- |
| BoundaryReedyFactorization | `IC.F1.Joins.CosliceTwistedHomEquivalence` → `HA.Simplicial.DiagonalLocalizedEquivalence` → `HA.Simplicial.BoundaryReedyFactorization` → `HA.HomotopyFunctionComplex.Reedy.BoundaryClasses` | `matchingEvaluation_mem_right`、`weakFactorizationSystem` | model 側を split（7 宣言） |
| DiagonalAnodyne | `IC.F1.Joins.CosliceTwistedHomEquivalence` → `HA.Simplicial.DiagonalLocalizedEquivalence` → `HA.Simplicial.DiagonalKanTests` → `HA.Simplicial.DiagonalAnodyne` → `HA.HomotopyFunctionComplex.Reedy.Lifting` | `hasLiftingProperty` | import を付け替え・prune |
| DiagonalDiagram | `IC.F1.TwistedArrow.TwistedHomDiagonal` → `HA.Simplicial.DiagonalAdjunction` → `HA.Simplicial.DiagonalDiagram` → `HA.HomotopyFunctionComplex.Reedy.SimplexResolution` | 直接の定義元の参照 0。再公開を個別照合 | import を付け替え・prune |
| DiagonalInternalHom | `IC.F1.Joins.CosliceTwistedHomEquivalence` → `HA.Simplicial.DiagonalLocalizedEquivalence` → `HA.Simplicial.DiagonalKanTests` → `HA.Simplicial.DiagonalAnodyne` → `HA.Simplicial.DiagonalRelativeMatching` → `HA.Simplicial.DiagonalMatching` → `HA.Simplicial.DiagonalInternalHom` → `HA.HomotopyFunctionComplex.AdjunctionHom` | `adjunctionHomIsoSameUniverse` | import を付け替え・prune |
| DiagonalMatching | `IC.F1.Joins.CosliceTwistedHomEquivalence` → `HA.Simplicial.DiagonalLocalizedEquivalence` → `HA.Simplicial.DiagonalKanTests` → `HA.Simplicial.DiagonalAnodyne` → `HA.Simplicial.DiagonalRelativeMatching` → `HA.Simplicial.DiagonalMatching` → `HA.HomotopyFunctionComplex.Reedy.BoundaryHom` | `comparison`、`iso`、`iso_naturality` | model 側を split（5 宣言） |
| FiniteTensorAdjunction | `IC.F1.Joins.CosliceTwistedHomEquivalence` → `HA.Simplicial.DiagonalLocalizedEquivalence` → `HA.Simplicial.DiagonalKanTests` → `HA.Simplicial.DiagonalAnodyne` → `HA.Simplicial.DiagonalRelativeMatching` → `HA.Simplicial.DiagonalMatching` → `HA.Simplicial.FiniteTensorAdjunction` → `HA.HomotopyFunctionComplex.FiniteTensorBoundary` | 直接の定義元の参照 0。再公開を個別照合 | model 側を split（5 宣言） |
| Generators | `IC.F1.Pointed.FreeInterval` → `HA.Simplicial.Generators` → `HA.Transfer.EvaluationSmallness` | 直接の定義元の参照 0。再公開を個別照合 | import を付け替え・prune |
| LatchingDegeneracies | `IC.F1.Joins.CosliceTwistedHomEquivalence` → `HA.Simplicial.DiagonalLocalizedEquivalence` → `HA.Simplicial.BoundaryReedyFactorization` → `HA.Simplicial.BisimplicialCofibrancy` → `HA.Simplicial.LatchingMonomorphisms` → `HA.Simplicial.LatchingDegeneracies` → `HA.HomotopyFunctionComplex.Reedy.SimplexFinite` | 直接の定義元の参照 0。再公開を個別照合 | model 側を split（2 宣言） |
| LocalizedMonoReedy | `IC.F1.Joins.CosliceTwistedHomEquivalence` → `HA.Simplicial.DiagonalLocalizedEquivalence` → `HA.Simplicial.LocalizedMonoReedy` → `HA.HomotopyFunctionComplex.Reedy.ClosedObjectwise` | `reedyLeft_inf_iff` | model 側を split（1 宣言） |
| StandardSimplexCosimplicialHom | `IC.HomotopyLimits.KanTensorFrameAdjunction` → `HA.Simplicial.StandardSimplexCosimplicialHom` → `HA.HomotopyFunctionComplex.ResolutionHom` | `cosimplicialHom` | import を付け替え・prune |

## 上移動の停止条件

`CosliceTwistedHomEquivalence` の証明は `localized_diagonal_map` を経て Reedy の latching、lifting、弱分解系を使う。ModelBridge への上移動は未適用。F1 の集約 import を外しても次の実参照が残る。

| 中核の利用元 | 利用宣言 | 必要な宣言 |
| --- | --- | --- |
| IC.F1.TwistedArrow.SourceInitial | `cosliceToTwistedArrowSource_isPrecompositionEquivalence` | `cosliceTwistedHomMap_isQCatEquivalence` |
| IC.F1.Yoneda.RightRepresentableTwistedArrowEquivalence | `rightRepresentableTwistedArrowFiberMap_isQCatEquivalence` | `cosliceTwistedHomMap_isQCatEquivalence` |
| IC.HomotopyLimits.TwistedHomFunctorMap | `twistedHomFunctorMap_isQCatEquivalence` | `cosliceTwistedHomMap_isQCatEquivalence` |

A・A′ 後の禁止 74 本は HA 66 と ModelBridge 8。診断用グラフから CosliceTwistedHomEquivalence が使う DiagonalLocalizedEquivalence への辺だけを外すと、残りは 0 になる。この除去では証明が成立しないため、対象 JSON には含めていない。
