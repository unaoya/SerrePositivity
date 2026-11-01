> **最新の状態：既存の生成補題の対応付け制約で停止。改訂版 §7-1 は未完了。詳細は [停止報告](w1-generated-declaration-stop.md)。以下は前回までの記録。**

# IF-W0-3 §10.5 作業中の停止報告：UniverseHomotopy の下流 import

基準 `e93f4aff5419235316a8f0deba24f1914eb93fca`。`git merge --ff-only main` で取り込み済み。
専用 worktree `SerrePositivity-ifw0-3`、ブランチ `infra/if-w0-3` のみで作業した。
**改訂版 §7-1 は未完了。既存の下流モジュールが失敗したため、IF-W0-1 §0 に従い停止した。**

## 試験と失敗

worktree で実行したコマンド：

```sh
nohup python3 -B scripts/refactor/prune_imports.py \
  SerrePositivity.InfinityCategories.DoldKanComparison.UniverseHomotopy \
  --output .lake/verify/ifw0-3-final/universe-prune.json \
  > .lake/verify/ifw0-3-final/universe-prune.log 2>&1
```

UniverseHomotopy の import は `DoldKanComparison.ResolutionComparisonEquivalence` から
`Core.SimplicialHomotopyEquivalence` へ縮小できた。自身のビルドは成功し、snapshot 比較は
前後とも2宣言、変更なしの PASS（候補・2回の import 除去で計3回）。
しかし、影響する7,122モジュールを28個の極大ターゲットで検査する下流ビルドで、既存の
`DoldKanComparison/ComparisonEquivalence.lean` が失敗した。
ログに記録された失敗ビルドはこの1モジュールで、`error:` 行は36行。先頭3行：

```text
error: SerrePositivity/InfinityCategories/DoldKanComparison/ComparisonEquivalence.lean:20:20: unknown namespace `DifferentialGraded`
error: SerrePositivity/InfinityCategories/DoldKanComparison/ComparisonEquivalence.lean:21:49: Unknown identifier `DGCategory`
error: SerrePositivity/InfinityCategories/DoldKanComparison/ComparisonEquivalence.lean:27:67: Unknown identifier `ClosedCategory`
```

失敗の署名は、UniverseHomotopy 経由の公開 import が縮まり、ComparisonEquivalence で
DG 系の名前と resolutionComparison 系の宣言が見えなくなること。
ComparisonEquivalence 自身は UniverseHomotopy と Core.FullyFaithfulEquivalence を public import しており、
元の ResolutionComparisonEquivalence の再公開に依存していた。
修正候補は、ComparisonEquivalence に ResolutionComparisonEquivalence の直接 import を追加すること。
**この既存ファイルの修正は行っていない。** ソース自身の保存検査だけでは下流への再公開の保存を保証できない例となった。

失敗発見後、自分の下流 Lake プロセスへ SIGINT を送り、prune の finally による復元を完了させた。
下流の記録は終了コード -2（SIGINT）であり、自然終了の結果ではない。上記コンパイルエラーは中断前に記録済み。
prune CLI の終了コードは1。予定した universe-prune.json は生成されなかった。
中間 results.json には status キーがないが、sources_restored は true。これを PASS とは扱わない。

## 所要時間と復元

prune 内で記録された各段の時間（秒）：

| 段 | 終了コード | 秒 |
| --- | ---: | ---: |
| `unpruned-build` | 0 | 4.093 |
| `min-imports` | 0 | 18.780 |
| `candidate` | 0 | 5.401 |
| `candidate-build` | 0 | 5.425 |
| `candidate-snapshot` | 0 | 15.250 |
| `remove-import` | 0 | 5.625 |
| `remove-import-build` | 0 | 5.622 |
| `remove-import-snapshot` | 0 | 16.180 |
| `remove-import` | 0 | 5.503 |
| `remove-import-build` | 0 | 5.684 |
| `remove-import-snapshot` | 0 | 16.536 |
| `remove-import` | 1 | 3.748 |
| `pruned-build` | 0 | 3.394 |
| `downstream-build-0` | -2 | 4293.447 |
| `restore-build-0` | 0 | 9.636 |

最後の remove-import の終了コード1は、必要な最後の import を外せないことを調べる内部試行。
停止理由はそれではなく downstream-build-0 の既存コードのエラーである。
復元後、失敗したモジュールを追加で検査した：

```sh
lake build SerrePositivity.InfinityCategories.DoldKanComparison.ComparisonEquivalence
```

**終了コード0、6.322秒。** `git diff --exit-code -- SerrePositivity` も0。
プロジェクトの Lean ソースは復元済み。残る .lean 差分は所有範囲の `scripts/refactor/decl_snapshot.lean` のみ。
待機していた remaining-results.json と r26-trial-results.json はともに commands が空で、後続試験は未実行。
コミットは行っていない。

## roof 分析（途中結果）

Derived 内の到達集合379本から、指定の code_contains 方式で語彙を判定した C は **14本**、除外365本。
外への直接漏れは **5辺**。uses_modules で2辺が未使用候補、3辺は使用あり。
ただし未使用候補の prune は、上記停止により **未実施**。移し先の閉包検査も未完了。
`dg` が `Edge` にも部分一致するため、この除外365本は意味的に DG が必要な365本という意味ではない。

一覧・使用宣言・分割の提案は [w1-roof-analysis.md](w1-roof-analysis.md)、
除外365本の全件は [w1-roof-excluded.md](w1-roof-excluded.md) に分離した。
roof の3参照先は引き続き JSON の外の「分析中の保留」。

## その他の進捗と未実施

- w1.json は前回の27 move のまま。改訂版として検査済みではない。
- 純粋な下ろし候補49 move の草案と閉包検査の中間証拠を `.lake/verify/ifw0-3-final/` に保存した。
  公式 JSON には取り込んでいない。
- 保留22件の実際の入口45辺について三案の比較用データを three-options.json に保存した。
  上げる案は45辺とも中核の利用元があり条件を満たさない。分割案の実証が未完了のため最終比較表・採用案は未確定。
- R61a 組1の読解記録は F1/Universe/PinchedHom を残す判断へ修正した。
- 手作業の import 変更・重複削除の模擬入力は作成したが、改訂 JSON の検査と手作業込みの W1 終了条件の再判定は未実施。
- CoreTrivialFibration、SpaceLimitShapes、追加の R26 の3分割、roof の2 prune は実行していない。

今回までの道具の変更：空 snapshot・uses_modules、move の imports、単一モジュールの prune 入口、
複数 split の本文変更と利用元 import 追加の合成、roof 集合の計数、手作業の模擬と W1 判定。
自作の試験で、直接の層違反を増やすのに成功を期待していた fixture を修正し、再試験した。
個別に確認済みの単体試験は imports 21件、builder 25件、single prune 3件、既存 tools 11件、empty snapshot 3件。
これらの成功は、上記の実下流ビルドの失敗を取り消すものではない。

## 証拠と報告の訂正

- `.lake/verify/prune-xejzenca/results.json`：各段、imports、保存検査、復元記録。
- `.lake/verify/prune-xejzenca/13-downstream-build-0.log`：失敗した下流ビルドの全ログ。
- `.lake/verify/ifw0-3-final/universe-prune.log`：prune CLI の終了時例外。
- `.lake/verify/ifw0-3-final/restored-comparison.json` と同名 .log：復元後の成功。
- `.lake/verify/ifw0-3-final/roof/`：集合・宣言依存の分析証拠。

途中の「失敗なし」という進捗報告は誤りだった。ログ末尾の進捗のみを確認し、前方に出ていたエラーを見落とした。
全ログを検査して発見した時点で停止・復元した。下流ビルド全体が成功したという結果はない。

## 変更ファイル（これまでの未コミット分を含む）

- `formalization-plans/archive/if-w0-3-r61b-reading-2026-10-29.md`
- `scripts/refactor/compare_snapshots.py`
- `scripts/refactor/decl_snapshot.lean`
- `scripts/refactor/prune_imports.py`
- `scripts/refactor/targets/README.md`
- `scripts/refactor/targets/w1-revision-stop.md`
- `scripts/refactor/targets/w1-roof-analysis.md`
- `scripts/refactor/targets/w1-roof-excluded.md`
- `scripts/refactor/targets/w1-roof-stop.md`
- `scripts/refactor/targets/w1-universe-import-stop.md`
- `scripts/refactor/targets/w1.json`
- `scripts/refactor/targets/w1.md`
- `scripts/refactor/targets_builder.py`
- `scripts/refactor/test_prune_single.py`
- `scripts/refactor/test_snapshot_empty.py`
- `scripts/refactor/test_targets_builder.py`
- `scripts/refactor/test_targets_imports.py`
- `scripts/refactor/test_targets_split_evidence.py`
- `scripts/refactor/validate_targets.py`
