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


## 層検査（IF-W0-2、報告段階）

`python3 scripts/refactor/layer_check.py --report` はビルドせずに import グラフを作り、
`.lake/verify/layers.json` に全結果を保存する。入れ子コメント・文字列を除き、
`public import` と改行された import も読む。`.lake`・隠しディレクトリ・node_modules は走査しない。
外部パッケージの import は終端として扱い、リポジトリ内の全 Lean ソースの閉包を集計する。

設定は `layers.json`。PinchedHom は Core に分類し、同じ層の内部 import は許す。
Core の層外 import は Simplicial と Mathlib、Kan は Core 以下と Mathlib に制限する。
禁止集合は W1 ⊆ W2a = W2b。ModelBridge も計画 §3 に従って W2a 以降は禁止する。
モデル圏判定は指定 HA ディレクトリと、コメント・文字列を除いた本文の ModelCategory による。
層・forbidden・allowed_until_move・restricted_imports の接頭辞は、すべて
`m == p` または `m.startswith(p + ".")` で照合する。複数の層に一致するときは最長の接頭辞を優先する。
restricted_imports の層名もこの分類結果を参照する。Spectra の二つの暫定許可はディレクトリ配下にも適用する。

- `--report` は違反があっても 0（入力・実行エラーは 2）。直接違反辺、各 tier の禁止閉包、入口辺、
  層未分類のモジュールを表示する。JSON は未分類の全モジュールをディレクトリ別に保存する。
- `--enforce W1|W2a|W2b` は指定段階の違反があれば 1。
  W2b では中核の層順序と Core/Kan の制限も強制する。
- `--ratchet BASELINE.json` は直接辺の層組別件数、tier ごとの禁止集合の総数、
  中核各モジュールの禁止閉包件数、入口辺数のいずれかが増えれば 1。
  同じグラフは 0。設定が異なる基準は拒否する（2）。承認済みの report JSON を別名で保存して基準にする。
- `--root`・`--config`・`--output` は試験と移動後グラフの試算用。
  Python の `read_graph`・`analyze`・`ratchet_increases` も後続の道具から利用できる。
- 例外は `{from, to, reason, expires}`。期限は W1 / W2a / W2b。
  指定窓までは当該辺を閉包・強制判定から除き、それより後は再び数える。
  例外適用前の全違反辺も保存する。初期の例外一覧は空。

`forbidden_module_count` は全中核の閉包の和集合（重複なし）、`closure_pair_count` は
中核モジュールと禁止依存先の組の数、`by_module` は各中核モジュールの件数。
`external_closure_core_leaves` は層の入口ファイルを除く中核の葉を根とした外部閉包で、
計画の 1,817 本と比較する。入口を含めた値は `external_closure_all_core` に分ける。
`direct_by_pair` は規則が重なっても各直接辺を一度だけ数える。

verify.sh の準備時に report を実行し、`summary.json` の `layer_check` に結果と終了コードを含める。
現段階では層の違反を verify の合否に加えない。強制への切り替えはコーディネータの判断を待つ。
試験は `python3 scripts/refactor/test_layer_check.py`。

## 対象一覧・分割・保存検査（IF-W0-2）

対象 JSON の書式と検査方法は [targets/README.md](targets/README.md) を参照。
以下は専用 worktree 内で、同時に別のビルドや編集をしない状態で使う。

### スナップショットと保存比較

```sh
lake build SerrePositivity.X.Y
lake env lean --run scripts/refactor/decl_snapshot.lean \
  --modules SerrePositivity.X.Y --output .lake/verify/before.json
# 移動・分割後に、その影響範囲をビルドしてから採取する。
lake env lean --run scripts/refactor/decl_snapshot.lean \
  --modules SerrePositivity.X.Y,SerrePositivity.X.Z --output .lake/verify/after.json
python3 scripts/refactor/compare_snapshots.py .lake/verify/before.json .lake/verify/after.json
```

`--modules` は読込対象のコンマ区切り一覧。`--namespace Example` を付けると、その読込環境全体から
名前空間で選ぶ（モジュールを省略したときは `SerrePositivity` を読む）。
スナップショットには公開宣言と親に属する private 補助宣言を保存する。
通常の private 宣言自体は公開 API の一覧から除き、参照中の private 名はモジュール接頭辞を除く。
型と定理以外の本体は Expr の構造・ハッシュを保存し、比較時は構造を直接照合する。
定理の証明本体と証明専用の補助宣言は比較せず、定理の型・公理・属性は比較する。
それ以外の補助宣言は親にまとめ、増減・変更も検査する。

instance の優先度、simp、reducibility、公開された本体の有無（expose）を取得する。
宣言の種類・型・本体・公理・属性・名前の増減に差分があれば終了コード 1、同一なら 0、入力不備は 2。
`--output result.json` で結果を保存できる。
改名は `--name-map map.json`（例：`{"Old.Namespace":"New.Namespace"}`）を指定する。
完全一致またはドット区切りの最長接頭辞で、変更前の宣言名・定数参照を正規化する。
文字列リテラルは改名しない。

### 宣言単位の分割

```sh
python3 scripts/refactor/split_module.py SerrePositivity.X.Y SerrePositivity.X.Z \
  --moved Example.modelLemma Example.otherLemma \
  --snapshot .lake/verify/before.json --dry-run --output .lake/verify/split-plan.json
```

既定は dry-run。差分と新しいファイルの内容（plan の `changes`）を確認してから `--apply` に替える。
snapshot を省略すると元モジュールをビルドして採取するので、dry-run でも `.lake` は更新される。
ソースと snapshot が一致しない場合は拒否する。

抽出を `validate_targets.py` と共有し、docstring・属性・宣言本文・改行コードを変更せず切り出す。
入れ子の namespace / section と必要な variable / open / universe / set_option を引き継ぐ。
型・本体・証明の定数依存から import の方向を決め、両方向なら適用前に拒否する。
移した宣言を本文で使う直接利用者には import を追加する。
公開 import による再公開、および simp / instance（補助宣言を含む）の暗黙利用も保つため、
その場合は直接利用者に保守的に import を追加する。

境界を確実に扱える、行頭から始まるコマンドを対象とする。
`mutual`、インデントされたトップレベルコマンド、無名 instance、`variable ... in`、
未対応の構文や複雑な局所スコープ、snapshot に現れない通常の private 宣言は自動分割せず拒否する。
これは Lean の任意の構文を再実装する道具ではないため、拒否された箇所は手動で検討する。
分割後は影響するモジュールのビルドと保存比較を必ず行う。

### 試験

- `python3 scripts/refactor/test_refactor_tools.py`：境界・文字列保存・依存・拒否・比較の試験。
- `python3 scripts/refactor/test_targets.py`：対象 JSON の正例と負例。
- `python3 scripts/refactor/test_preservation.py`：本体変更・simp 除去・名前空間移動。
- `python3 scripts/refactor/test_split.py`：R72 の FixedBoundaryExtensions から Model の 7 宣言を
  一時的に切り出して、影響範囲のビルドと保存比較を行い、元ソースに戻して再ビルドする。

試験のログと JSON は `.lake/verify/ifw0-2-*` に保存する。
一時ソースは finally で復元・削除するが、プロセスを強制終了したときは、保存された
`ifw0-2-split-test/plan.json` と git diff を確認して復元する。

## import の最小化と新しい module docstring

`split_module.py` の `--prune-imports` は、分割した二つのファイルだけを対象に
Mathlib の `minImports` linter と `#min_imports` の候補を合わせる。
候補で Lean のコンパイルと元のスナップショットとの保存比較を通し、さらに import を一本ずつ外して両方を再検査する。
それ以上一本も外せない集合になるまで繰り返す（コンパイルと保存の条件下での包含最小性であり、全ての代替集合を探索する意味での最小性ではない）。
import の削減で型クラス推論が変わる場合もあるため、生成補助定理の型も含めて比較する。
初期候補が保存比較に失敗した場合は、その宣言と補助宣言の元の依存モジュールを補ってから削減する。
このためスナップショットには `used_modules` も記録する。古いスナップショットでこの情報が必要になった場合は再生成を求めて止まる。
不要になった名前空間への単純な `open` が候補のコンパイルを妨げる場合は、
その文脈指定だけを取り除いて再検査する。宣言本文・宣言の docstring は変えない。
最後に直接利用者だけでなく、元の import グラフの推移的な下流をビルドする。
引数長の制限を避けるため、下流の末端を 100 本ずつビルドしてその依存を覆う。

このオプションでは dry-run も一時的に分割ソースを書き、Lean を実行する。
終了時にソースを復元し、変更したモジュールを再ビルドするので、必ず専用 worktree で排他的に使う。
下流のビルドキャッシュ全体は復元しない。下流を再び利用する際は `lake build <module>` を先に実行し、
Lake の依存検査によって必要な生成物を更新する。
`--apply` が成功した場合は、検査に通った最小化後のソースを残す。
途中で失敗した場合は元ソースに戻す。各候補の失敗は不要 import の検査記録として保存する。
ログとビルド対象、前後の import 一覧は `.lake/verify/prune-*/results.json` に残る。
中断・強制終了時は、分割前の plan と git diff を確認して復元する。

新しいファイルの説明は `--module-doc description.txt` で指定する。
UTF-8 の通常の文章（`/-!` と `-/` は含めない）を渡す。
未指定なら元の module docstring をコピーし、先頭に
「分割で生成：docstring を書き直すこと」を加える。
実ファイルでの最小化・保存・閉包比較の試験は `python3 scripts/refactor/test_prune.py`。

## 中断レーンの import 付け替え

```sh
python3 scripts/refactor/rebase_helper.py --worktree /absolute/path/to/worktree \
  --moves moves.json --split split-plan.json --dry-run
```

`moves.json` は既存の `scripts/move_module.py` と同じ `moves` オブジェクトを読み、
分割 plan は `declaration_modules` を読む。`--split` は複数指定できる。
選んだ Git worktree の未追跡・未コミットの `.lean` だけを調べ、
モジュール改名は import 内だけに反映する。移された宣言の使用には新しい import を追加する。
本文・コメント・文字列は変更しない。単純でない import の構文は手動確認として拒否する。
差分を確認してから `--apply` で反映する。レーンの担当者が自分で実行するための道具である。

## 監査の並列化・キャッシュ・絞り込み

- `VERIFY_JOBS` は正の整数、既定 3。1 なら監査を順番に実行する。並列化だけなら gate:true。
  監査ごとのログ・終了コード・時間を保存し、監査名順に統合する。
  `summary.json` の `runner.audit_wall_seconds` が並列監査の実時間で、個別時間の合計とは異なる。
- `VERIFY_CACHE=1` は成功結果のキャッシュを読む。この実行は gate:false。
  キャッシュを読まない実行でも成功結果を書き、次回の照合に使う。
  鍵には監査のパス・本文、その import のリポジトリ内推移閉包の全 `.olean.hash`、
  `lean-toolchain`、`lake-manifest.json`、verify.sh と同ディレクトリの実装ファイルを含める。
  依存の hash が欠けている場合はキャッシュを使わず実行する。失敗結果はキャッシュしない。
  sorry 閉包も同じ方法で扱い、sorry 試験用の上書きがある場合はキャッシュを使わない。
  保存先は追跡されない `.lake/verify/cache/`。
- `VERIFY_ONLY_AUDITS` は監査パスの空白区切りの一覧。この実行は gate:false。
  空・重複・未知のパスは拒否し、絞り込みの前に監査 manifest 全体を照合する。
  `audit_count` は発見した全監査数、`executed_audit_count` は選択後の監査数。
  ビルドを省略しない場合、ルートと選択した監査の import 先をビルドする。
- `summary.json` の各 audit/sorry 段には `cached` と `cache_key` が付く。
  `.lake/verify/audit-progress.json` には完了数を記録する。

窓の合否は、試験用の絞り込み・キャッシュ・ビルド省略を設定せず、
`VERIFY_JOBS=3 zsh scripts/refactor/verify.sh` で全監査を実行して判定する。
IF-W0-2 の受入試験は `test_verify.py preflight`、`full`、`cache` の順。
`full` は一度だけ実行するためのマーカーを保存し、再実行を拒否する。
ほかの段は監査を絞り、cache 段では監査一つの一時変更と復元も検査する。
各実行の終了コード・要約・完全ログは `.lake/verify/ifw0-2-acceptance/` に保存する。

新しい 12 個の入口は空の骨組みで、ルートや既存集約には登録しない。
層の配置と依存規則を守って後続の窓で実装を移す。
