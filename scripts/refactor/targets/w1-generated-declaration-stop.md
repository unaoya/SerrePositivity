# IF-W0-3 §10.6 再開後の停止報告：外部定義の生成補題

**改訂版 §7-1 は未完了。既存の分割道具の制約で停止した。**
基準 `502e78840e9b336e55175bb65ab5221025477fe7`、ブランチ `infra/if-w0-3`。main 502e78840 の §10.6 を取り込んで作業した。コミットはしていない。

## 停止したコマンドと結果

```text
/opt/homebrew/opt/python@3.14/bin/python3.14 -B scripts/refactor/split_module.py SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoChainTransport SerrePositivity.InfinityCategories.Core.FunctorIsoChainTransport --moved SerrePositivity.InfinityCategories.F2.functorIso_postcomp_heq_of_map_eq --snapshot /Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/.lake/verify/ifw0-3-addendum6/splits/chain-transport/before.json --output /Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/.lake/verify/ifw0-3-addendum6/splits/chain-transport/plan.json --dry-run
exit_code: 1
seconds: 0.09
```

出力は1行（先頭3行を抜き出しても、この1行だけ）：

```text
split_module: STOP: cannot associate generated declaration: SerrePositivity.InfinityCategories.F2.functorEqIso.eq_1
```

基準の `lake build` は終了0（5.054秒）、変更前 snapshot は終了0（25.726秒）。dry-run が変更前に停止したため、このケースで一時的な Lean 編集は行っていない。失敗ログは `.lake/verify/ifw0-3-addendum6/splits/chain-transport/dry-run.log`。

## 原因と止めた理由

snapshot は明示された5宣言のほか、次の2宣言を `FunctorIsoChainTransport` 所属として記録している。

| snapshot の宣言 | snapshot の parent | 親の定義が書かれたファイル |
| --- | --- | --- |
| `SerrePositivity.InfinityCategories.F2.functorEqIso.eq_1` | `SerrePositivity.InfinityCategories.F2.functorEqIso.eq_1` | `SerrePositivity/InfinityCategories/F2/CatInfinity/FunctorEqIso.lean` |
| `SerrePositivity.InfinityCategories.F2.functorIsoOfEq.eq_1` | `SerrePositivity.InfinityCategories.F2.functorIsoOfEq.eq_1` | `SerrePositivity/InfinityCategories/F2/CatInfinity/FunctorIsoTransport.lean` |

`FunctorIsoChainTransport.lean` の62・73行には `simp only [functorEqIso, functorIsoOfEq, ...]` があり、展開時に生成された等式補題と考えられる。確定している事実は、上の2宣言が snapshot に入り、元ファイルの明示宣言5件には対応する親がないこと。

既存の `lean_source.py:166–178` は snapshot の各宣言を元ファイルの宣言に `owner` で対応付け、対応しないものを拒否する。今回の停止箇所は178行。`lean_source.py` 自体の差分は空で、今回新しく書いた対応付け処理の誤りではない。§10.2・§10.4・§10.6 の所有範囲にもこのファイルは含まれていない。

[IF-W0-1 §0](../../../formalization-plans/infinity-codex-w0-1.md) は、既存のコード等の想定外の失敗について「直さずに止め、コマンドとエラーをそのまま報告する」としている。このため修正せず停止した。snapshot から2宣言を黙って除外する回避もしていない。

再開時に判断が必要なのは、外部定義に由来して利用側に現れる生成補題を、宣言の所属・分割時の依存・保存比較でどう扱うか。必要なら `lean_source.py` とその試験を所有範囲に追加し、`decl_snapshot.lean`・`split_module.py`・`compare_snapshots.py`・`prune_imports.py` の扱いを揃える。単に照合を通すために生成補題の検査を落とす変更は提案しない。

## ここまでの実試験

| 対象 | 結果 | ソース復元 | 補足 |
| --- | --- | --- | --- |
| UniverseHomotopy | PASS | 済み | 全2宣言を保存。Core.SimplicialHomotopyEquivalence の import に縮小。ComparisonEquivalence に ResolutionComparisonEquivalence を直接補充し、下流・復元ビルドまで成功。 |
| FirstTriangleIndex | PASS | 済み | Mathlib.Order.Fin.Basic のみへ縮小。JoinFirstTriangle に SpanJoinCells を補充。 |
| RoofPinchedSlicePostcomp | PASS | 済み | RoofSliceTransport を外し、SliceOverEqualityTransport を直接 import。下流6モジュールを補充。 |
| CoreTrivialFibration | split PASS | 済み | 2宣言を F1 へ、1宣言を残す試験に成功。残す側も F1 閉包に収まるため、全3宣言の move 1本の比較を予定したが、まだ実行していない。 |
| SpaceLimitShapes | split PASS | 済み | 2宣言を分け、両側を prune。分割先の import は F1.Coherent.SpaceSmallLimits の1本。最終の閉包・JSON 採否は未実施。 |
| FunctorIsoTransportAlgebra | split PASS | 済み | 1宣言の分割先は Core.Equivalence のみを import。残す側は FunctorEqIsoAlgebra。下流4モジュールを補充。 |
| FunctorIsoChainTransport | dry-run FAIL | 編集なし | 今回の停止箇所。 |
| FunctorIsoWhiskerCancellation | 未実施 | — | 直列実行が停止し、開始していない。 |
| 全体 move 比較試験 | 未実施 | — | 開始前に停止。 |

すべての完了した split は、分割全体の snapshot 比較と復元後ビルドも終了0。途中の下流失敗は、§10.6 で許可された直接 import の補充を行い、各補充先の元 snapshot と比較してから再ビルドした。途中も「失敗なし」だったとは扱わない。

### 下流へ追加して検証した import

| 試験 | 下流モジュール | 追加した import |
| --- | --- | --- |
| universe/ifw0-3-addendum6 | `SerrePositivity.InfinityCategories.DoldKanComparison.ComparisonEquivalence` | `SerrePositivity.InfinityCategories.DoldKanComparison.ResolutionComparisonEquivalence` |
| FirstTriangleIndex/roof | `SerrePositivity.InfinityCategories.Derived.JoinFirstTriangle` | `SerrePositivity.InfinityCategories.Derived.SpanJoinCells` |
| RoofPinchedSlicePostcomp/roof | `SerrePositivity.InfinityCategories.Derived.DGPinchedCompositionFamilyGeneral` | `SerrePositivity.InfinityCategories.DGNerve.Functor` |
| RoofPinchedSlicePostcomp/roof | `SerrePositivity.InfinityCategories.Derived.DGModuleAllResolvedExact` | `SerrePositivity.InfinityCategories.Derived.DGModuleStability` |
| RoofPinchedSlicePostcomp/roof | `SerrePositivity.InfinityCategories.Derived.RightKanSliceRoof` | `SerrePositivity.InfinityCategories.Core.InnerPullback`、`SerrePositivity.InfinityCategories.F1.Fibrations.CartesianFibration` |
| RoofPinchedSlicePostcomp/roof | `SerrePositivity.InfinityCategories.Derived.TerminalConeSectionEdges` | `SerrePositivity.InfinityCategories.Derived.DGRoofSliceVertices` |
| RoofPinchedSlicePostcomp/roof | `SerrePositivity.InfinityCategories.Derived.DGModuleResolvedFunctorExact` | `SerrePositivity.InfinityCategories.Derived.DGModuleStability` |
| RoofPinchedSlicePostcomp/roof | `SerrePositivity.InfinityCategories.Stable.LoopEquivalenceCofiberExists` | `SerrePositivity.InfinityCategories.Stable.CofiberPushoutComparison` |
| plan/core-trivial | `SerrePositivity.InfinityCategories.F2.CatInfinity.QCatHomPostcomposition` | `SerrePositivity.InfinityCategories.F1.Categories.QCatSimplicial` |
| plan/core-trivial | `SerrePositivity.InfinityCategories.F2.CatInfinity.QCatPullbackCone` | `SerrePositivity.InfinityCategories.Core.InnerPullback` |
| plan/core-trivial | `SerrePositivity.InfinityCategories.F2.CatInfinity.QCatPullbackHom` | `SerrePositivity.InfinityCategories.F2.CatInfinity.CorePullbackIso` |
| plan/core-trivial | `SerrePositivity.KST.LocalizingInvariants.ArrowContractionSquares` | `SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation` |
| plan/core-trivial | `SerrePositivity.InfinityCategories.F1.MappingSpaces.QCatPostcompositionFiberComparison` | `SerrePositivity.InfinityCategories.F1.Fibrations.PullbackTransport`、`SerrePositivity.InfinityCategories.F1.Universe.InnerFibration` |
| plan/space-limits | `SerrePositivity.InfinityCategories.F2.Compact.Definition` | `SerrePositivity.InfinityCategories.Stable.TrivialFibrationCocone` |
| plan/space-limits | `SerrePositivity.InfinityCategories.F2.Compact.CoconeUniverseImage` | `SerrePositivity.InfinityCategories.Stable.TrivialFibrationCocone` |
| plan/space-limits | `SerrePositivity.InfinityCategories.F2.Presentable.SourceColimitMapping` | `SerrePositivity.InfinityCategories.Stable.TrivialFibrationCocone` |
| plan/transport-algebra | `SerrePositivity.InfinityCategories.Derived.FunctorHomotopyStrictBasePrecomp` | `SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorEqIsoTransport` |
| plan/transport-algebra | `SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoWhiskerCancellation` | `SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorEqIsoTransport` |
| plan/transport-algebra | `SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanCommonRightCorrectionImage` | `SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorEqIsoTransport` |
| plan/transport-algebra | `SerrePositivity.InfinityCategories.F2.Ind.FullyFaithfulSquareRelativeIsoReflection` | `SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorEqIsoTransport` |

追加も含めて復元済み。正確なコマンド・段別の秒数・比較結果・失敗した各試行のログは各 plan の `pruning.commands` と `pruning.preservation_checks`。

### 時間

直列実行の壁時計（先行 UniverseHomotopy の完了待ちを含む）は **25703.365秒＝約7時間8分23秒**。報告作成・コードの事前修正時間はこの計測に含まない。UniverseHomotopy の記録されたコマンド時間の合計は2462.858秒。

| 直列試験 | 全体の秒数 | 終了コード |
| --- | ---: | ---: |
| FirstTriangleIndex | 6431.223 | 0 |
| RoofPinchedSlicePostcomp | 4723.026 | 0 |
| core-trivial | 4514.879 | 0 |
| space-limits | 4306.897 | 0 |
| transport-algebra | 3318.774 | 0 |
| chain-transport | 30.965 | 1 |

| split 試験 | 基準build | before snapshot | dry-run | apply/prune | split build | after snapshot | compare | 復元build |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| core-trivial | 4.009 | 22.936 | 27.847 | 4344.449 | 4.3 | 19.815 | 0.081 | 91.298 |
| space-limits | 4.401 | 19.923 | 28.185 | 4149.878 | 5.014 | 25.385 | 0.06 | 73.924 |
| transport-algebra | 4.918 | 21.84 | 31.321 | 3023.811 | 4.67 | 22.318 | 0.079 | 209.645 |
| chain-transport | 5.054 | 25.726 | 0.09 | 未実施 | 未実施 | 未実施 | 未実施 | 未実施 |

### ログ全体の検査

`rg` で Lake と Lean 直接実行の両方の error 形式を226ログ全体から検索した。error 行のあるログは35（下流試行19、import 除去試行16）。詳細は `full-log-audit.json` に記録。終了0なのに error または traceback があるログは0。個別 import を外す試行の意図的な失敗と、補充前の下流失敗を含む。さらに `(error[:(]|STOP:|Traceback|FAIL)` を同じ全ログに適用し、dry-run の STOP も確認した。記録は `full-log-audit.json`・`stop-log-markers.json`。失敗した下流の署名・先頭3行も前者に保存している。

単体試験は計76件 PASS（targets imports 29、targets builder 26、single prune 7、refactor tools 11、empty snapshot 3）。これは今回の生成補題のケースまで対応済みという意味ではない。

## roof 分析は完了

[roof 分析](w1-roof-analysis.md)・[除外一覧](w1-roof-excluded.md) に保存した。C=23、除外356、漏れ3辺のうち2辺の prune・保存・下流・復元検査は成功。配置案は Core 9・F1B 7・Stable 5・保留2、既存 move と6本重複。提案先の既存ファイル名との衝突はなかった。

残る漏れは SpanUnknownIndex→SpanSuffixIndex。2宣言（spanSuffixFaces・mem_spanSuffixFaces）を出す案を記載した。ただし prune 後に3入口から必要になる Derived 内の集合は15本で、そこに SpanUnknownIndex・SpanIndexGeometry は含まれない。元の C 全体の課題と3入口に必要な範囲を区別している。roof の3入口は JSON の外の保留のまま。

## 未完了部分・作業木

三案比較の実測資料は `three-options.json`（原保留22件・入口45辺、利用元の全一覧つき）と `pure-moves-draft.json`（49本）。しかし残る試験が未完了なので、これを改訂版の確定 JSON としてはいない。
`w1.json` は旧 27 件のまま。今回の最終 CLI 検査と手作業込み W1 判定は未実施で、§7-1 に到達したとは報告しない。後続の待機処理も失敗状態で終了し、最終 JSON や報告を自動更新していない。

`git status --porcelain --untracked-files=all -- SerrePositivity SerrePositivity.lean` は空。プロジェクトの Lean ソースに差分・新規ファイルはない。Lean の恒久差分は許可された `scripts/refactor/decl_snapshot.lean` だけ。main の作業木でビルド・編集していない。コミットなし。

## 変更ファイル

```text
 M scripts/refactor/compare_snapshots.py
 M scripts/refactor/decl_snapshot.lean
 M scripts/refactor/prune_imports.py
 M scripts/refactor/targets/README.md
 M scripts/refactor/validate_targets.py
?? formalization-plans/archive/if-w0-3-r61b-reading-2026-10-29.md
?? scripts/refactor/targets/w1-generated-declaration-stop.md
?? scripts/refactor/targets/w1-revision-stop.md
?? scripts/refactor/targets/w1-roof-analysis.md
?? scripts/refactor/targets/w1-roof-excluded.md
?? scripts/refactor/targets/w1-roof-stop.md
?? scripts/refactor/targets/w1-universe-import-stop.md
?? scripts/refactor/targets/w1.json
?? scripts/refactor/targets/w1.md
?? scripts/refactor/targets_builder.py
?? scripts/refactor/test_prune_single.py
?? scripts/refactor/test_snapshot_empty.py
?? scripts/refactor/test_targets_builder.py
?? scripts/refactor/test_targets_imports.py
?? scripts/refactor/test_targets_split_evidence.py
```
