# IF-W2b 停止点 3

検証コミット `4a2c23ad4`。verify は **PASS / gate:true**。ビルド 2、監査 99、sorry 閉包 1、準備 1 が成功。失敗 0、再試行 0。6 並列、40 GB、1,944.859 秒。

## 下流と保存比較

- 停止点 2 `a6ff3946a` に main `b7881adac` を取り込んだ（`eb68203f1`、衝突 0）。差分は解説・計画・BS 草稿。下流 13,149 本を 23 根で覆い、round 1 で PASS、新規 Built 1,514 本。失敗・再発・未検証の根・下流の追加補充はいずれも 0。草案 7,856.200 秒、実測 1,721.042 秒。
- §17 の最終成果物から v3b snapshot を 1,928 本再採取し、正規化した 6,890 宣言を比較。型 42、本体 6、補助 1 の差はいずれも停止点 2 の個別照合結果と一致。archive 1,726 本も一致。
- 初回 verify は 94/99 監査成功。§18 で F1B → F1 の 17 移動（R38 8、R73 9）を行い、17 本と直接利用者・両入口を含む 87 モジュールのビルドが 555.281 秒で PASS。影響範囲の v3b 比較は 250 → 250 宣言、差 0。束全体も既知の 49 件だけで未説明 0。archive 1,726 本を最終パスで再照合。
- 既存の F1B 入口の straightening 禁止と Ind-S の制約を維持。現行入口・F1B 監査の閉包ともに straightening 0。従来から入口の外にある 2 本は W2c または段 F への引き継ぎ。

## 監査の追従

対象 A 368（うち PiCriterion の支え 3）、B 1,726、C 33。A・C の移動・分割先 405 本を監査に収録し、旧 exchange 監査を削除。PiCriterion の定義元を Derived に更新。R37 のコミットで Stable.ColimitFamilyExtension は import 先だけが Stable.ColimitCoconeFamilies から F1.ColimitCoconeFamilies へ変わった。宣言の定義元は Stable にあるため、Stable 監査で直接 import し、公理を検査した。旧 Stable 監査が宣言の存在を個別に要求していた移動先 115 本は、その検査も各移動先へ移した。

対象監査のコマンド数（配置修正前 → 最終）。#check と #print axioms の各総数を保存。

| 領域 | #check | #print axioms |
| --- | ---: | ---: |
| Core | 1,465 → 1,737 | 1,592 → 1,892 |
| F1 | 8,673 → 9,070 | 38 → 140 |
| F1B | 2,059 → 2,127 | 28 → 28 |
| HomotopyLimits | 5,551 → 5,592 | 5,553 → 5,498 |
| Stable | 356 → 374 | 2,754 → 2,342 |
| F2 | 1,361 → 561 | 0 → 65 |
| Derived | 356 → 360 | 2,313 → 2,313 |
| 合計 | 19,821 → 19,821 | 12,278 → 12,278 |

移管した宣言の数。同じ宣言に複数の検査がある場合、宣言は一度数える。

| 移管 | 前 | 後 |
| --- | ---: | ---: |
| F2 → Core | 272 | 272 |
| F2 → Derived | 4 | 4 |
| F2 → F1 | 397 | 397 |
| F2 → F1B | 68 | 68 |
| F2 → HomotopyLimits | 106 | 106 |
| F2 → Stable | 18 | 18 |
| HomotopyLimits → F2 | 65 | 65 |
| Stable → Core | 300 | 300 |
| Stable → F1 | 102 | 102 |
| Stable → F1B | 0 | 0 |
| Stable → HomotopyLimits | 10 | 10 |

F1B から F1 へ移した 17 本の宣言数（生成宣言を含む v3b snapshot 行）。

| モジュール（F1B 以下 → 同名の F1 以下） | 前 | 後 |
| --- | ---: | ---: |
| Compact.CanonicalCoconeWeakEquivalence | 3 | 3 |
| Compact.RepresentableCoslice | 11 | 11 |
| Compact.UniverseColimits | 3 | 3 |
| FilteredExchange.CoherentTotalObject | 10 | 10 |
| FilteredExchange.ContinuousKanCoconeContraction | 1 | 1 |
| FilteredExchange.ContinuousKanFilteredUnit | 3 | 3 |
| FilteredExchange.ContinuousKanHomotopy | 1 | 1 |
| FilteredExchange.FilteredPointwiseWeakEquivalences | 2 | 2 |
| FilteredExchange.FiniteRelativeWeakCriterion | 2 | 2 |
| FilteredExchange.FunctorIsoComponentPost | 3 | 3 |
| FilteredExchange.IntervalReplacementSection | 5 | 5 |
| FilteredExchange.SpaceHomotopyClasses | 1 | 1 |
| Idempotent.PresheafClosure | 14 | 14 |
| Idempotent.PresheafComplete | 3 | 3 |
| Ind.DensityFiberTransformationRestriction | 16 | 16 |
| Ind.InitialBoundaryCoconeRestriction | 4 | 4 |
| Ind.TwistedElementsReconstructionPointed | 8 | 8 |
| 合計 | 90 | 90 |

キャッシュ付き再検査は監査 62/99 本を再利用し PASS（gate:false）。この回の root / 監査対象ビルドは 1,964.196 / 568.938 秒。続いて全 99 本を実行し gate:true を確認。生成監査の DG・CLMST・Adams・Shared は生成結果と一致。BS の差は取り込んだ main からの既存差。

## 層・閉包・時間

| 指標 | W2b 前 | 最終 |
| --- | ---: | ---: |
| 直接違反 | 294 | 18 |
| 中核層間の順序違反 | 266 | 0 |
| 禁止モジュール W1 / W2a / W2b | 1 / 166 / 166 | 0 / 150 / 150 |
| 影響を受ける中核 W1 / W2a / W2b | 11 / 3,379 / 3,379 | 0 / 2,531 / 2,531 |
| ルート閉包（DG-W3 後の基準） | 24,253 | 24,232 |
| verify の root ビルド（秒） | 2,743.749 | 17.471 |
| verify の監査対象ビルド（秒） | 1,048.696 | 17.916 |
| verify 全体（秒） | 5,561.170 | 1,944.859 |

ビルド時間はいずれも当該 verify の実測で、各作業木のキャッシュ状態を含む。中核層の順序違反・新しい直接禁止辺・上限を超えた集計値はすべて 0。W2b の enforcement 上限は承認済みの値のまま。最終 ratchet 基準は別ファイルに保存。

## 処置一覧と W2c

R73 は move 401・split 4・reimport 9・archive 1,726。R37 は move 115・split 1・reimport 1。R38 は move 218・split 6・reimport 66（追加配置を含む）。適用後の補充は延べ 188 import。各 import・配置・監査コマンドの対応は [w2b-section18-stop3.json](w2b-section18-stop3.json) の inventory と [w2b-section18-audits.json](w2b-section18-audits.json) に記録。

W2c の 180 本は停止点 3 JSON に全名を収録。6 根の W2a/W2b 各指標を記す。F1B 入口は §18 で停止点 2 の 137 から 0 になった。Compact.UniverseColimits は F1 配下に移った。

| 根（W2a/W2b） | 前 → 最終 | import 経路（SerrePositivity 以下） |
| --- | ---: | --- |
| InfinityCategories.F1.Presentable.SigmaLiftedHomRestriction | 0 → 127 | `InfinityCategories.F1.Presentable.SigmaLiftedHomRestriction` → `InfinityCategories.F1.MappingSpaces.HomInfinityBifunctor` → `InfinityCategories.F1.Yoneda.YonedaInfinityFullyFaithful` → `InfinityCategories.F1.Yoneda.YonedaEvaluatedTransportEquivalence` → `InfinityCategories.F1.TwistedArrow.SourceInitial` → `InfinityCategories.F1.Joins.CosliceTwistedHomEquivalence` → `HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence` → `HomotopicalAlgebra.Simplicial.BoundaryReedyFactorization` → `HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryClasses` |
| InfinityCategories.F1B | 0 → 0 | §18 で到達 0（停止点 2 は 137）。以前の経路は JSON に記録 |
| InfinityCategories.F1.Compact.UniverseColimits | 0 → 137 | `InfinityCategories.F1.Compact.UniverseColimits` → `InfinityCategories.HomotopyLimits.Compact.WeakUniverse` → `InfinityCategories.HomotopyLimits.KanSourceReplacement` → `HomotopicalAlgebra.Simplicial.AnodyneKanReplacement` → `HomotopicalAlgebra.Simplicial.Generators` → `HomotopicalAlgebra.Transfer.EvaluationSmallness` |
| InfinityCategories.F2 | 0 → 137 | `InfinityCategories.F2` → `InfinityCategories.F2.Presentable.CoherentProductComparisonEdge` → `InfinityCategories.HomotopyLimits.KanTensorAdjunction` → `HomotopicalAlgebra.HomotopyFunctionComplex.AdjunctionHom` |
| InfinityCategories.F2.Filtered | 0 → 51 | `InfinityCategories.F2.Filtered` → `InfinityCategories.Stable.Filtered.TotalKanProductEquivalence` → `InfinityCategories.HomotopyLimits.KanTensorAdjunction` → `HomotopicalAlgebra.HomotopyFunctionComplex.AdjunctionHom` |
| InfinityCategories.HomotopyLimits.Presentable.SigmaHomWeightRestriction | 0 → 137 | `InfinityCategories.HomotopyLimits.Presentable.SigmaHomWeightRestriction` → `InfinityCategories.HomotopyLimits.PresheafHomWeights` → `InfinityCategories.F1.Compact.HomCovariantComparison` → `InfinityCategories.F1.TwistedArrow.SourceInitial` → `InfinityCategories.F1.Joins.CosliceTwistedHomEquivalence` → `HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence` → `HomotopicalAlgebra.Simplicial.BoundaryReedyFactorization` → `HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryClasses` |

## 作業コミット

作業ブランチの first-parent 順。最後にこの報告と ratchet 基準を記録する。

- ed1981cdd infra(verify): default to 40 GB and document cache cleanup policy
- d00018229 docs(infinity): record W2b R73 draft stop conditions
- 95f95cde4 test(layers): allow multiple negative-rank foundations
- 809f5518a docs(infinity): record W2b forward-closure preflight stop
- 3ac6cf89d docs(infinity): record W2b declaration-level placement blockers
- 96fbbab87 docs(infinity): plan W2b upward chain and record archive validator mismatch
- 34f2afa6d infra(targets): allow explicit archive importer exclusions
- aa95d2f97 docs(infinity): record W2b full draft and ratchet review points
- fc047fd80 infra(layers): enforce W2b approved aggregate boundary
- 408b0f05a Merge branch 'main' into infra/if-w2b
- 4d02ee532 refactor(infinity): archive old exchange path and place retained foundations
- d12e85d0e refactor(infinity): lower stable general lemmas
- 9c38c984e refactor(infinity): resolve F2 layer order by declaration dependencies
- 32cd95abc refactor(infinity): 配置の修正
- 8c0548f02 refactor(infinity): 補充の import
- d135a715f Merge branch 'main' into infra/if-w2b
- 11e7c8644 ratchet 基準の設定ハッシュ
- df6790351 refactor(snapshot): accept proof-irrelevant v3b batch snapshots
- e1d2b7183 配置の修正
- 2b01641ef 補充
- 9a1723f2c 補充（内部ビルド round 3）
- 40ade3a3d 補充（round 5）
- dd292abd1 補充（round 6）
- 240abf012 補充（round 7）
- 6cbc4d06c 補充（round 8）
- a6ff3946a 記録（IF-W2b 停止点2）
- eb68203f1 Merge branch 'main' into infra/if-w2b
- 6d7be7a3a 配置の修正（F1B → F1）
- 4a2c23ad4 監査の追従

詳細ログは `.lake/verify/ifw2b-section17/` と `.lake/verify/ifw2b-section18/`。正式な verify summary は後者の `verify-gate/summary.json`。
