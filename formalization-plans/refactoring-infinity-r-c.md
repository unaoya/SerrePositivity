# R-C：∞ 圏基盤のリファクタリング

## 引き継ぎ

- 現在地：R17 a45c92306、R19 2c1fa3384、R20 aa124065c 完了。3-1 の完全一致4宣言族の共有化を検証済み：ビルド・指定4監査・Rectification監査・bar評価2チェックが全て終了コード0。型の異なる準重複は保存して一覧化。
- 残り：R16。R15 は R-A 取り込み・合図後の rebase を待つ。準重複の原8組の残2組については質問を提示済み（現存する両ファイル族の全調査で継続中）。
- 主要宣言：`SerrePositivity.InfinityCategories.F2.hasSpaceLimitsOfShape`。既存の宣言型・証明は保存。
- 依存と提供：F1 の `hasLimit_coherentSpaceDiagram` を使用。R-A の `scripts/move_module.py` 到着までは機械的変更の対応表を archive に残す。
- 未コミット：なし（完全一致共有化の本コミットに含む）。
- 既知の問題：なし。main の未追跡作業ファイルは取り込まない。
- 次の一手：R16 を `/tmp/r-c-r16.py` で適用（R-A の move_module.py は未着、手動対応表を保存）。本文照合後 `/tmp/r-c-check-item.sh r16` で4集約ビルド・指定4監査。

## 方針

指定の所有範囲で直接移動・参照置換する。互換シムなし。数学的内容・既存の宣言型・証明は保存し、sorry・公理を追加しない。各項目末に F2・HomotopyLimits の集約ビルドと audit_infinity_f2・audit_infinity_presentable・audit_homotopy_limits・audit_einfinity を実行する。R-A 取り込み後はコーディネータの合図で rebase と .lake の再クローンを行う。

## 検証

R17：`lake build SerrePositivity.InfinityCategories.F2 SerrePositivity.InfinityCategories.HomotopyLimits` および `lake env lean scripts/{audit_infinity_f2,audit_infinity_presentable,audit_homotopy_limits,audit_einfinity}.lean` を各実行し終了コード0。F2 19,485 宣言、Presentable 852 宣言、EInfinity 25,780 宣言が標準三公理のみ。ログは `/tmp/r-c-r17-*`。

R17 は既存の条件付き宣言の引数・証明を保存し、条件を任意の形について供給する `hasSpaceLimitsOfShape` を無条件の極限存在定理の系として追加した。F1 の既存2ファイルを変更せず利用できる。

準重複に関する追加指示（2026-10-23）：型の異なる組は変更しない。完全一致する宣言のみを共有化し、差分のある組は `archive/refactor-near-duplicates-einfinity-2026-10-23.md` に両ファイル・類似度・型の差・一般化案を記録する。実施は所有レーンの再開後の判断。

R19：Cat*・Lax* とその F2 最上位への依存閉包 290 本を CatInfinity、残る 1,921 本を FilteredExchange へ。既存の4サブディレクトリ集約は位置を保つ。`archive/refactor-r-c-r19-moves.json` に移動・import 変更を保存。複数行 import を含め全移動元のコミット済み本文と照合し、差は import のモジュール名だけ。旧モジュールへの import は0。F2 の既存説明・#check は保存し、新しい2入口を追加。EInfinity にも import 変更があるためビルド対象に含める。

R20：5入力の定義・供給元・一致行／ファイルを現 worktree から再採取し §6 と archive を更新。準重複一覧は同名 EInfinity 33 組と HomotopicalAlgebra 6 組。R8 の8組の元一覧は未保存で、残る2組との対応は未確定（低類似度の別構成を数合わせで追加しない）。再調査 `/tmp/r-c-ha-match.py` は6組だけを再同定した。

3-1 の追加検証：`OrdinaryBarFirstAction.output` と `ResolutionBarFirstAction.output` は同じ型・同じ本文。両既存宣言との等式を `rfl` で確認（`/tmp/r-c-ha-output-probe.lean`、終了コード0）、最小 import の probe も通過（`/tmp/r-c-ha-output-minimal-probe.lean`）。局所 Reedy instance・変数を保存して `BarOutput.output` 一箇所に移す準備済み。共有化後は指定四監査に加え `audit_homotopical_rectification` と既存の ordinary/resolution bar 評価チェックも実行する。

3-1 準備：`EInfinity/HomotopyWeight/DoubleOpposite.lean` と `HomotopicalAlgebra/Rectification/HomotopyFunctionComplex/BarOutput.lean` を、通過済みの独立 probe から新規追加。既存モジュールはまだ import しておらず、R19 の依存グラフは変わらない。R19 の四監査後、既存宣言の削除・参照置換を適用する。

R19 検証進捗：主ビルドは15,713 jobsで終了コード0、F2監査も終了コード0（19,486宣言、標準三公理）。Presentable監査は旧 `F2.CoconeParameterPrism` の cached olean と新配置の混在で停止したため、`F2.Presentable` を追加ビルド中。ソースの旧 import は存在せず、互換シムで回避しない。以後の項目ゲート `/tmp/r-c-check-item.sh` は監査が使う4集約すべてを明示ビルドするよう修正済み。

R19/R20 最終検証：主集約（F2・HomotopyLimits・EInfinity）15,713 jobs、追加 Presentable 集約7,750 jobsが成功。`audit_infinity_f2`（19,486宣言）・`audit_infinity_presentable`（852宣言）・`audit_homotopy_limits`・`audit_einfinity`（25,780宣言）は全て終了コード0。公理は標準三公理のみ。最終ログは `/tmp/r-c-r19-audit_{infinity_f2,infinity_presentable,homotopy_limits,einfinity}.log`。最初の Presentable cached olean 失敗は `/tmp/r-c-r19-presentable-stale-cache.log` に分離して保存。

R20 完了：§6 の5入力の定義位置・供給元・使用数を更新し、全一致行を archive に保存。R17・R19 の完了行も正本に反映。R19 と同じ検証済みソース状態で指定4監査が通過し、文書変更はその後のみ。

3-1 実装：EInfinity の `doubleOpWeights`・`framedLimitWeight`・`framedLimitWeight_cofibrant` と HomotopicalAlgebra の `output` を各共有モジュールへ接続し、元の宣言を削除。旧名の参照は0。`archive/refactor-r-c-shared-source-verification.json` に HEAD aa124065c との機械的変更の照合・55ファイルのハッシュを保存。共有宣言の型・本文は保存。

3-1 完全一致部の最終検証：全変更モジュール・4集約・Rectification.Foundations のビルド成功（16,795 jobs）。指定4監査・Rectification監査・bar評価2チェックの7コマンドは全て終了コード0。EInfinity 25,777宣言（重複3宣言分減）、Rectification 14,894宣言・1,040モジュール、標準公理のみ。実行結果・対象一覧・新規モジュールハッシュを `archive/refactor-r-c-shared-validation.json` に保存。
