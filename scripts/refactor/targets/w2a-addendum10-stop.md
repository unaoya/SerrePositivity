# IF-W0-3 §10.10 実装・R72 preflight 停止報告

**§7-2 は未達。w2a.json・w2a.md は未作成。** 位置情報と属性処理の実装・105件の試験は成功したが、R72の分割計画作成で§10.7-7の「親が見つからない生成宣言」に当たり停止した。Leanソースの分割適用・pruneには進んでいない。

基準 `0b10ccff6894fa839c0b85a47fc3df423ba66a47`。専用worktree `SerrePositivity-ifw0-3`、ブランチ `infra/if-w0-3` にmainをfast-forwardで取り込んだ。取り込んだmainには§10.10以外に可換代数の再編も含まれる。main作業木では作業・ビルドしていない。W1は8e6e75d8eでのPASS・gate:true・retried0と今回のユーザー承認を維持。現在のmainに対して全体verifyを追加実行していない。

## 今回実装したこと

- `decl_snapshot.lean`：Lean.findDeclarationRanges?から開始・終了行/列と選択位置をsource_rangeに保存。取得できない補助宣言はnull。
- `lean_source.py`：位置情報付きsnapshotで無名instanceの環境名を照合。位置の曖昧さ・名前との不一致は拒否する。
- ファイル内宣言へのattributeは宣言側へ、宣言直後に元の順序で配置。複数の対象名は帰属ごとに分ける。外部local/scoped属性は同じスコープで両側へ。外部グローバル属性はkeepだけにし、後続movedに影響しうる場合はSTOP。`[-simp]`も対象。混在した複数属性指定や宣言と異なるスコープは保守的に拒否する。
- `open … in`・`set_option … in`・`variable … in`等は宣言と一緒に保持。同一行の前置きにも対応。`include hgen`の継続するスコープも保持。
- split/validate/compareに位置情報の利用を接続。pruneは分割後に位置が変わるため、その時点のsnapshotを採って対応づけるよう変更（実分割のprune検証は今回の停止により未実施）。
- 新規13試験。無名instance、属性の帰属とスコープ、外部グローバル属性のSTOP、前置き、位置の曖昧さ等を検証。既存のvariable…in拒否試験は新規則に合わせて更新。

## 検査結果

| 検査 | 結果 | 秒 |
| --- | --- | ---: |
| snapshotスクリプトのコンパイル | 終了コード0 | 未計測 |
| HA12本だけのlake build | 終了コード0 | 5.500 |
| 位置情報付きsnapshot | 終了コード0・159定数 | 25.366 |
| 新規位置・属性試験 | 13件成功 | 0.018 |
| 関連回帰試験（新規13件を含む） | 105件成功 | 0.163 |
| git diff --check | 終了コード0 | — |

関連回帰試験：test_refactor_tools、test_source_positions、test_lean_source_generated、test_targets、test_targets_imports、test_targets_reimport_evidence、test_targets_split_evidence、test_snapshot_empty、test_prune_single、test_targets_builder。105件の結果は実行ツール出力で確認、新規13件のログはtest-source-positions.log。

12本すべてでソース宣言の抽出は成功（合計90宣言）。DiagonalFrameの82行は、環境名 `SerrePositivity.HomotopyFunctionComplex.DiagonalFrame.instModelCategoryFunctorSimplexCategory_serrePositivity` に一致。旧来の属性/無名instanceによるパーサー拒否は解消した。

Generatorsの分割計画は moved1・keep7、変更対象14ファイルで作成できた（未適用）。次のFixedBoundaryExtensionsで依存方向の検査がSTOP。残る10本のsplit prepareは実行していない。Generated.FunctorClosure・Transfer.FullyFaithfulLifting・HomotopyFunctionComplex.BoundaryOneにはModelを仮定する宣言がなく、空splitを作らず純粋部分の移動を後の窓へ記録する見込みだった。

## 停止理由と判断が必要な点

§10.7-7は、ソースにない定数の親を「環境の中で、その名前の最長の真の接頭辞で、宣言として存在するもの」とし、「親が見つからないものだけを、いままでどおりエラー（STOP）にする」と定めている。この拒否条件を拡張せずに停止した。

最初の診断：

```text
lean_source.Unsupported: cannot associate generated declaration: SerrePositivity.SimplicialModel.RelativeChoiceSpace.ofExtension_inclusion_assoc
```

`ofExtension_inclusion_assoc`のenvironment_parentとparent_moduleはnull。元の`ofExtension_inclusion`はドット区切りの真の接頭辞ではない。位置は73行の`@[reassoc (attr := simp)]`を指し、元の宣言の範囲は73〜76行（名前の選択位置74行）なので、生成元を位置から判断する証拠はある。ただし、生成補題の親なしSTOPの例外としてこの証拠を採用する規則はまだ入れていない。

12本のsnapshot全体を読み、同じ親の照合で未対応となるものを列挙した（追加の分割・ビルドは行っていない）：

| 宣言 | 環境の親 | 位置 |
| --- | --- | --- |
| `SerrePositivity.SimplicialModel.RelativeChoiceSpace.ofExtension_inclusion_assoc` | None | {'start_line': 73, 'start_column': 2, 'selection_start_line': 73, 'selection_end_line': 73, 'end_line': 73, 'end_column': 24} |
| `SerrePositivity.SimplicialModel.RelativeChoiceSpace.ofExtension_projection_assoc` | None | {'start_line': 78, 'start_column': 2, 'selection_start_line': 78, 'selection_end_line': 78, 'end_line': 78, 'end_column': 24} |
| `SerrePositivity.SimplicialModel.RelativeChoiceSpace.over_assoc` | None | {'start_line': 63, 'start_column': 2, 'selection_start_line': 63, 'selection_end_line': 63, 'end_line': 63, 'end_column': 9} |
| `SerrePositivity.SimplicialModel.LargeParameterExtension.extend_initial_assoc` | None | {'start_line': 57, 'start_column': 2, 'selection_start_line': 57, 'selection_end_line': 57, 'end_line': 57, 'end_column': 9} |
| `SerrePositivity.SimplicialModel.LargeParameterExtension.extend_prescribed_assoc` | None | {'start_line': 61, 'start_column': 2, 'selection_start_line': 61, 'selection_end_line': 61, 'end_line': 61, 'end_column': 9} |
| `SerrePositivity.SimplicialModel.LargeParameterExtension.relativeExtend_initial_assoc` | None | {'start_line': 88, 'start_column': 2, 'selection_start_line': 88, 'selection_end_line': 88, 'end_line': 88, 'end_column': 9} |
| `SerrePositivity.HomotopyFunctionComplex.QuillenStandardFrame.augmentation_weakEquivalence._proof_1_1` | None | None |
| `SerrePositivity.HomotopyFunctionComplex.StandardCosimplicial.ι_tensorIso_hom_assoc` | None | {'start_line': 38, 'start_column': 2, 'selection_start_line': 38, 'selection_end_line': 38, 'end_line': 38, 'end_column': 9} |

内訳はreassoc由来の`_assoc`7件と、QuillenStandardFrameの証明補助宣言1件。後者はsource_rangeもnullで、従来のparent欄は元の定理名を指すが、environment_parentはnull。private名の正規化と環境の親の照合を区別する必要がある。

次に必要な判断：属性位置が一つのソース宣言に含まれる生成補題をその宣言の補助として扱ってよいか。またprivateな証明補助宣言について、正規化した名前の環境上の接頭辞を親の照合に使ってよいか。名前の末尾だけで親を推測したり、これらをtransientとして除外したりしていない。

## ログと変更範囲

記録は `.lake/verify/ifw0-3-addendum10/`。`ha-commands.json` にビルドとsnapshotのコマンド・終了コード・時間、`ha-position-inventory.json` に12本の宣言一覧、`unassociated-declarations.json` に上記8件の証拠、`stop.json` に状態を保存した。preflightコマンドは `python3 -B /tmp/ifw03-10-10-preflight.py`、終了コード1。

全ログをエラー語で検索した。コンパイル・HAビルド・snapshotのエラーは0。preflightは上のUnsupportedとTraceback。試験ログのSTOPに相当する語は成功した試験名で、試験失敗ではない。

今回編集：decl_snapshot.lean、lean_source.py、split_module.py、validate_targets.py、compare_snapshots.py、prune_imports.py、test_refactor_tools.py、新規test_source_positions.py、本報告、w1.mdの承認状態。すべて承認された所有範囲。数学のLean・監査・W1 JSONは編集していない。gitのLean差分は以前から所有しているdecl_snapshot.leanだけ。

§7-2の閉包表と対象JSONの累積検査は未実施。既存のw1.jsonは承認済みのまま保持した。全体verify追加実行・コミットはしていない。
