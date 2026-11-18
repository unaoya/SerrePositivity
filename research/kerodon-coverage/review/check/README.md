# Kerodon 対応表：段1の機械的検査

`check_declarations.py` は `items.csv` の **status に関係なく宣言欄の全記載**を採取し、
モジュールごとに `#check @名前` と `#print axioms 名前` を実行する。
Python 3.9 以降とリポジトリ指定の Lean/Lake を使う。外部 Python ライブラリは不要。
数学的な主張の一致や「なし」の探索は段2・段3で行う。このスクリプトは章の最終 CSV を作らない。

## 実行

main から切った専用 worktree のルートで実行する。
依存パッケージとビルドキャッシュは、その worktree 自身の `.lake` に用意する。
main の `.lake` への書き込み用シンボリックリンクは使わない。

```sh
source ~/.zshenv
python3 -B research/kerodon-coverage/review/check/check_declarations.py prepare --run-dir runs/all-01
python3 -B research/kerodon-coverage/review/check/check_declarations.py run --run-dir runs/all-01
```

`prepare` は全章が既定。`--chapter 1`（複数指定可）で章を限定できる。
`run --limit 1` は1モジュールだけ実行し、`run --resume --limit 10` は checked 済みのモジュールを
飛ばして次の10モジュールまで実行する。`--module Mathlib.AlgebraicTopology.SimplexCategory.Defs`
のようにモジュールを指定することもできる。A〜D の417項目を含むモジュールを先に並べる。
全体ビルドや verify は実行しない。

各モジュールの前に `ps -axo command=` を確認し、他の `lake build` があれば停止する。
保存する ps の標準出力は `lake build` に該当する行のみ（該当なしなら空）とする。
ps に失敗した場合も停止する。続いて、必ず次の順に直列実行する。

```sh
zsh scripts/refactor/with_build_lock.sh --wait 0 -- lake build <Module>
lake env lean --json research/kerodon-coverage/review/check/<run-dir>/modules/<Module>/Check.lean
```

子プロセスは `source ~/.zshenv` 後に実行される。ビルド失敗時は Lean 検査を実行しない。
既存の raw 出力は上書きしない。失敗・中断したモジュールを再試行する場合は新しい run-dir で
prepare して `run --module <Module>` する。複数 run の結果を勝手に混ぜない。
prepare 後の HEAD・入力・toolchain・スクリプト・Lean ソースの変更は run が拒否する。
Mathlib の revision と tracked Lean ソースの変更も run 前に確認する。

## 解析のみをやり直す

```sh
python3 -B research/kerodon-coverage/review/check/check_declarations.py parse --run-dir runs/all-01
```

Lean の JSON 診断の **行番号**と生成済みコマンド表で型・公理を各記載に対応させる。
型は宇宙レベルと暗黙引数を表示する。`propext`、`Classical.choice`、`Quot.sound` のみを標準とし、
`sorryAx` も含め、それ以外を `extra_axioms_json` に残す。公理名の `.{u}` 等の宇宙引数を除いて比較し、
元の表示も保存する。追加公理があっても宣言自体の実在は
`found`、監査の終了コードは1となる。

主な状態は次のとおり。

| state | 意味 |
| --- | --- |
| `found` | #check と #print axioms の両方を確認できた |
| `not_found` | Lean が Unknown identifier/constant を報告。名前空間の不足もありうる |
| `unresolved_reference` | 匿名 instance、略記、説明文、複数名、場所の欠けなど。段2で手動解決 |
| `not_run` | 計画にはあるが未実行 |
| `source_missing` | 記載ファイルがない。未導入の Mathlib もこの状態になる |
| `build_busy` / `preflight_failed` | 別ビルドが稼働中、またはプロセス確認不可 |
| `build_failed` | 対象モジュールの準備に失敗。宣言の不存在とは扱わない |
| `check_failed` / `axioms_unparsed` / `output_invalid` | 型検査失敗、出力不足・未対応形式、プロセス異常等 |
| `started` / `checking` | 実行途中で中断された可能性あり |

終了コードは `0` = 全記載 found・追加公理なし、`1` = 未検査/要確認/追加公理あり、
`2` = 入力・設定・実行例外。prepare の0は計画作成の成功だけを意味する。
`item-results.csv` の `no_declarations` は「欄が空」であり、「確認済み・なし」ではない。
段2で名前を補正した場合は章 CSV の `check=renamed` と根拠を記入し、改めて同じ2コマンドで確認する。

## 保存物

- `plan.json`：入力の SHA-256、Git HEAD、対象項目・全記載・モジュール一覧。
- `inventory.json`、`references.csv`、`unresolved.csv`：件数、原記載との対応、未解決の記載。
- `modules/<Module>/Check.lean`、`commands.json`：実行した検査と行番号。
- 同ディレクトリの `execution.json`、`ps.*.txt`、`build.*.txt`、`lean.stdout.jsonl`、`lean.stderr.txt`：終了コード・時刻・ソース hash・生出力。
- `declaration-results.csv`、`item-results.csv`、`summary.json`：再生成できる機械的判定。

同じ記載は一度だけ検査し、`references.csv` で全出現箇所に結び付ける。
名前が同じでも出典モジュールが違えば別記載として検査する。行番号がない `@ path.lean` も扱う。
記法や複数名を推測で一つの定数に縮めることはしない。

## スクリプトの検査

```sh
python3 -B -m unittest discover -s research/kerodon-coverage/review/check -p 'test_check_declarations.py' -v
```

異常公理、名前不明、import 失敗、型推論失敗、欠落・不正出力、Unicode名とコマンド帰属を検査する。
実際の Lean 出力形式との互換性は、小さい対象モジュールで別途 smoke run を行う。

## §4の待機条件（2026-11-07）

上記の旧待機条件に代えて、プロセスの作業ディレクトリと引数を確認する。
別プロジェクトのビルドと SerrePositivity のモジュール単位のビルドは待たない。
SerrePositivity の全ビルド・verify が稼働中の場合、またはビルドロック取得が
終了コード75で失敗した場合は10秒後に再試行する。ロック競合時のログは試行ごとに残す。

## KB-W1 / B6（2026-11-17）：partial・none の紙の再照合

`b6-ch<N>.md` は対象全行の判定・変更一覧、`b6-own-issues.md` は書換え対象外の own・both・mathlib で見つけた誤りの問題票。原文の項目Tagと現在の宣言のソースの仮定・結論を並べ、§8.1の「同じ対象・射について直接導ける部分」だけをpartialにする。保持するpartialはspecial・direction・stronger-hyp・componentの一つを記す。Archiveの宣言はown・partialの根拠にしない。

KB-W1ではソースを読むだけで、ここにある旧段1スクリプトのLean実行・kernelの確認・ビルド・鍵の取得を行わない。既存CSVのaxioms/checkは過去の記録のままで今回の検証結果ではない。新しい大きい原文採取・候補型・検索・比較結果はgit外 `~/serre-evidence/cited/kerodon-b6/`、目録だけを `evidence/cited/kerodon-b6/manifest.json` に保存する。
