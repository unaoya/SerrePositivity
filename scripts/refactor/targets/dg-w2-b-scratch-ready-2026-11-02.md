# DG-W2(b) §15：heartbeat と before の復元

> 過去の停止・準備時点の記録です。その後の解消と停止点 2 の結果は [§16 の完了報告](dg-w2-b-universe-replay-2026-11-02.md) を参照。

- heartbeat の単独コミット：`023b0c098`。
- `Resolution/Cells/Boundary.lean` の `BoundaryInterchange` section に `set_option maxHeartbeats 800000` を 1 行追加。宣言・証明の変更なし。内部 111 本 PASS は既報。D8 の調査候補として残す。
- before scratch：`../SerrePositivity-dgw1-before`、detached HEAD `887896bba`。追跡ファイルの変更なし。
- toolchain と依存 manifest の一致を確認し、DG worktree の `.lake/packages` を APFS clone で独立コピー。プロジェクトの `.lake/build` はコピーせず、Lake キャッシュから復元。
- fresh login shell の `LAKE_ARTIFACT_CACHE=true`、`LAKE_RESTORE_ARTIFACTS=true`、`LAKE_CACHE_DIR=/Users/sugakubunka/.cache/lake` を確認。
- 他の `lake build` がないことを ps で確認し、`with_build_lock.sh --wait 0` で共有鍵を取得して実行。終了後に解放。
- 元の before 採取対象 2,259 本：**PASS、19,722 jobs、33.362 秒、新規コンパイル 0 本**。
- 記録：`.lake/verify/dg-w2-b-s15/restore-state.json`、`restore.log`、`modules.json`、`restore.py`（作業原本 `/tmp/dgw2b-s15/`）。

確認時の main は `87046c67a`。証明無関係なハッシュの実装はまだ入っておらず、`decl_snapshot.lean` の識別子は `normalized Expr DAG mixHash v1` のまま。新しい道具の取り込みを待つ。旧規則の 2,585 件は履歴として保持する。

取り込み後、scratch の Lean ソースを `887896bba` に保ったまま両側へ同じ新規則の道具を適用し、before／after を採り直す。残りは §10.34 の pp 比較。それまでは外からの import・監査一覧の付け替え、下流ビルド、layers.json、verify は未実施。
