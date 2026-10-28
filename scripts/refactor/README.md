# 検証の合否判定

## 概要

`zsh scripts/refactor/verify.sh` はルート・監査対象のビルド、全監査、sorry 閉包を検証し、
最後に PASS / FAIL を表示する。専用 worktree で実行し、同じ worktree のビルドを並行させない。

## 方針

ルートと監査対象のビルド、監査、sorry 閉包、一覧の照合が通れば終了コード 0。
一つでも未承認の失敗があれば非零。監査失敗のうち、承認済み署名と完全一致するものだけは既知として除外する。
監査一覧にあるファイルの欠落は FAIL。新しい監査も実行し、一覧への追加が必要と表示する。
許可された sorry は 3 件と厳密に一致させ、kanQuillen_model_exists の到達も拒否する。

## 規約

- `audit_manifest.txt` は監査パスを一行ずつ持つ。追加・改名・削除の意図を確認し、
  `scripts/audit_*.lean` と `scripts/audit/*.lean` のソート済み一覧に更新する。初期基準は 99 本。
- `verify_baseline.txt` はコメント見出しとタブ区切り 4 項目からなる。
  監査パス、40 桁の基準コミット、署名 JSON、理由と担当を記す。
  **Claude またはコーディネータの承認なしに変更しない。**
  基準実行の `summary.json` にある署名を報告し、承認されたものだけを登録する。
- 署名は `error_count` と順序付き `errors`。各エラーは `file`・`line`・`declaration`・`message` を持つ。
  ファイルはリポジトリ相対、行は数値。宣言は直近の宣言または監査コマンドのソース行。
  エラー文は先頭行（ヘッダが空なら次の行）、空白を単一化し ANSI 装飾を除く。
  エラー数・順序・行・宣言・文のいずれかが変われば FAIL。解析できないプロセスエラーも FAIL。
  既知の監査が成功したら「一覧から外せる」と表示する。
- `scripts/refactor/audit_targets.txt` は追跡しない。生成先は `.lake/verify/audit_targets.txt`。
  `.lake/verify/summary.json` に全体・各段の秒数、終了コード、署名、件数、合否を保存する。
  段ごとの完全ログは `.lake/verify/*.log`、実行ログは `scripts/refactor/verify.log` に追記する。

## 使われ方

基準実行と検収は試験用環境変数を設定せずに実行する。
`VERIFY_EXTRA_AUDITS`（空白区切りのパス）、`VERIFY_SKIP_BUILD=1`、`VERIFY_BASELINE=<path>` は試験専用。
これらを設定した実行は、要約に `(non-gate)`、JSON に `"gate": false` が付き、検収には使えない。
`SORRY_AUDIT_ROOT`（完全修飾定数名）、`SORRY_AUDIT_ALLOWED`（空白区切り、空文字で空集合）も試験専用で、
verify.sh では同様に non-gate となる。根が未読込なら、名前の接頭辞に対応する既存のソースモジュールを読み込む。
試験モジュールは先にビルドしておく。

初回は `.lake` の複製と不足モジュールのビルドに時間がかかる。
所要時間の数値は基準実行の `summary.json` の `seconds` と各 `stages[].seconds` を目安にする。
2026-10-28、基準コミット `4ab7665b3` の専用 worktree（`.lake` 複製済み）では、
99 本の監査・6,603 個の対象で全体 4,134.926 秒（約 69 分）だった。
内訳は準備 2.592 秒、ルートビルド 52.538 秒、監査対象ビルド 188.455 秒、
全監査 3,782.371 秒、sorry 閉包 108.531 秒。キャッシュと同時実行の負荷で変わる。
