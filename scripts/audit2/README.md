# AR-W1 段3の並行検証

リポジトリの root で実行する。`OUT` は Git 外の実行用ディレクトリ。すべての Lean 実行を bulk 鍵で行う。

```sh
export AUDIT2_QUEUED_AT=$(date +%s)
zsh scripts/refactor/with_build_lock.sh --class bulk -- python3 scripts/audit2/audit.py build "$OUT/build"
export AUDIT2_QUEUED_AT=$(date +%s)
zsh scripts/refactor/with_build_lock.sh --class bulk -- python3 scripts/audit2/audit.py run "$OUT/full"
python3 scripts/audit2/recompute.py "$OUT/compare" "$OUT/full/audit.sqlite"
```

- `build` は Git の追跡モジュールを通常の Lake CLI に渡す。ファイル一覧で渡すため長いプロセス引数を必要としない。Archive・tools・Verso・研究用 Lean は別集計。
- `run` は読み取り前に Lake の `--no-build --rehash --no-cache` を同じ対象にかける。個々の `.trace` の成果物一覧と、その時点の `.olean/.server/.private/.ilean` の実ハッシュを検証する。Lake の入力トレースと固定依存の信頼を前提とする。Lake のハッシュは再ビルド判定用であり、改ざんに対する暗号学的な署名には使わない。編集中の作業木からの読み取りは避ける。
- `run --previous PATH/audit.sqlite` は同じバージョンで、同じ依存トレース・成果物ハッシュの行を再利用する。再利用時も全対象を読み取り前に検証する。中断した補完は、同じ版・成果物のまま `--resume` でチェックポイントから再開する。`--modules FILE` は手元の部分検査で、明示的な一覧を指定する。全体判定には全モジュールを渡す。部分範囲は証拠経路の構成に必要な import を含める。
- `recompute.py` は本体一覧を再列挙してから塊ごとに bulk 枠を取り、全 kernel 行に対して `collectAxioms` を呼ぶ。保存側とキー・集合を照合する。相違、未知、余分・欠落があれば不合格とし、記録監査の判定を取り込みに使わず調査する。同名の生成宣言が隠れる場合は該当所有元の型と値を一時の別名で核に通し、そのレコードの公理を調べる。失敗した対象を省略しない。コマンド本体が鍵を取る。外側から重ねて鍵を取ると待ち合わせになる。同じ出力先を渡すと完了した塊から再開する。余裕が変わったときは `--replan --limit N` で未実行分を組み直す。同じ Lean/Mathlib 版の完全な外部 import 索引を `--external-ownership` で渡した場合、`--limit` は外部を含む。宣言0件の import 専用モジュールには、ソース全体が import だけであることと現在の trace を照合する。詳細は [再計算監査案](../../formalization-plans/stage-ii/consolidation/recompute-audit-design.md)。

`run` は `audit.sqlite` の `module`、`decl` を出す。キーは所有モジュールとカーネル名、主張と値の指紋は同一 Lean 版の構造ハッシュ。値の欠如、位置の欠如、未保存公理を NULL で表す。採取後の公理 `axioms` は空集合と未判定を区別する。型、値、コンストラクタの辺はそれぞれ定数名を保持し、外部名も残す。保存された instance 登録はスコープと優先度を含む。`internal` は Lean の内部名フラグ。ソースコマンドと生成由来の区分は `origins.py audit.sqlite origins.sqlite` で別の所有元付き表に出せる。保留を明示し、`partial_source` は保存された `_unsafe_rec` の親を含む。他モジュールの属性追加を含む実効 instance 探索は別の検査とする。

`sets.json`、`g2.json`、`comparison.json`、`timings.json` に母集団・判定・時間・個別結果を保存する。終了0は合格、1は判定違反、2は取得・環境・前提エラー。未判定を空の公理集合として扱わない。資源上限の診断は生ログに残し、他の大きな読み込みがない枠でやり直す。

ソース、Lake の trace、成果物は検証前後にバイト数と SHA-256 を照合する。別の作業木がビルドで共有ハードリンクを張り替えたときは、監査側のファイルの内容が同じなら続行する。内容の変化はサイズや mtime が同じ場合も検出する。`selftest.py` は二つの一時 worktree で実際の Lake ビルドと採取を重ね、同じサイズのソース・trace・成果物の編集を個別に拒むことも確かめる。旧版で作った表を差分採取や再計算に使う場合は、現行版で採取し直す。

旧76本の照合と概念の木への出力も行える。

```sh
python3 scripts/audit2/legacy.py "$OUT/full/audit.sqlite" "$HOME/serre-evidence/ar-w1/eac7d1e57" "$OUT/legacy"
python3 scripts/audit2/concepts.py "$OUT/full/audit.sqlite" "$OUT/concepts/dump" \
  --external-ownership "$HOME/serre-evidence/ar-w1/eac7d1e57" --prepare-tree
python3 research/cleanup-zero-base/whole/update.py "$OUT/concepts" --skip-dump
```

旧監査の照合は段1の同一ソースの実行結果、選択式、所有元索引を使用する。概念出力は同じ TSV を提供する。ID は所有元付きで割り当て、同名の候補を選んだ記録を `owners.json` に保存する。概念の木が使わない docstring 長と定理以外の Prop 補助欄は既定値を出す。`--prepare-tree` は畳み込み後の循環を扱えない既存の割り当て器に互換ビューを渡す。元の TSV と `W-raw.pkl`、変更した辺の一覧を保全する。

版を上げたら本体の `SerrePositivity.Util.Citation` を対象ビルドし、以下を実行する。試験用の Lake プロジェクトで、公理・private・opaque・instance・属性と同名の所有元を照合する。古いソース・不正な成果物ハッシュ・領域規則の負例も検査する。成功後に全体を再ビルドし、`run` と `recompute.py` を新しい出力先で実行する。

```sh
zsh scripts/refactor/with_build_lock.sh --class bulk -- python3 scripts/audit2/selftest.py "$OUT/selftest"
```

## 段4　文献対応表とブループリント

全対象を記録監査したコミットで実行する。本体の追跡ソースは先にコミットし、ビルドと記録監査を済ませる。固定 Mathlib は成果物を読み、参照の末尾名で絞った索引を作る。版や参照の末尾名が変わったら新しい出力先で索引を取り直す。

```sh
zsh scripts/refactor/with_build_lock.sh --class bulk -- python3 scripts/audit2/coverage.py external "$OUT/mathlib"
python3 scripts/audit2/coverage.py check "$OUT/full/audit.sqlite" "$OUT/mathlib/external.json" "$OUT/coverage-check.json"
python3 scripts/audit2/coverage.py resolve "$OUT/full/audit.sqlite" "$OUT/mathlib/external.json" "$OUT/coverage-plan.json"
python3 scripts/audit2/coverage_blueprint.py "$OUT/coverage-plan.json" "$OUT/blueprint"
python3 scripts/audit2/coverage_selftest.py
```

- 対応表の完全名を全母集団で引き、所有元とカーネル名を得る。一段の名前は `_root_.` でルートを明示する。短い名前の候補は一覧に残す。基準は `research/*-coverage/baseline.csv`。作成用の `baseline` は既存基準を置き換えるため、承認した基準採取時に使う。
- `check` は追加・消失・未承認の移動・指紋の変化・新しい未解決を列挙する。承認済みの改名・移動は `--moves` に `[{"old":["所有モジュール","カーネル名"],"new":["所有モジュール","カーネル名"]}]` 形式の JSON を渡す。合格したときに限り `--apply-locations` で位置と承認済みの名前を書き戻せる。書き戻し後は差分を確認し、`resolve` をやり直す。指紋変化を警告として試すときは `--warn-fingerprints` を明示する。
- 主張は Lean の型の構造指紋。意味は主張の型から到達する本体の定義・opaque の型と値、帰納型・構成子の型を集めた SHA-256。各定数名を含め、定理の証明はそこで止める。Mathlib の中は固定版を境界とする。
- 生成の前に未解決と基準を検査し、生成の後に全カードのリンク配列を別に照合する。Git 外の新しい出力先へ生成し、公開用の反映は `--publish` を明示する。現行の未解決を調べる `--preview` は診断用。省いた参照は `unresolved.json` に出る。診断用の成果物は公開できない。

固定版の VersoBlueprint `7bd0c10` が外部リンクとして受け付けないのは、コンストラクタ、再帰子、商型のカーネル組み込み宣言。該当する参照はカードに宣言名を表示し、生成先の `name-only.json` と取り込み検査の `blueprint_name_only` に載せる。判定の根拠は固定版の `Data.lean` と `ExternalRefSnapshot.lean`。公理と opaque 宣言は後者で受け付ける。来歴コメントを除くコード・本文がバイト単位で等しい Lean 生成物は、反映時に従来のファイルを使う。生成結果の `retained` にそのファイルとハッシュを記録する。

## 取り込み時の文献対応表の検査

対応表の宣言欄には、現行本体と固定 Mathlib に実在する宣言の `完全名 @ パス:行` を書く。ルート直下の名前は `_root_.` を明示する。未実装の計画、却下した候補、Archive の参照、原典番号の対応が未確認の候補は、備考列 `reference_note` に記録する。対応状態は照合の結果に従う。備考で参照が空になった理由を示した行は、宣言索引の対象行を持たない。ブループリントでリンクが必要な項目は生成器が引き続き検査する。

調整役は取り込み候補をコミットし、候補の記録監査に合格してから次を実行する。`BEFORE` には取り込み前の main のコミットを指定し、そのコミットの文献基準と比較する。手元で同じ版の基準を検査するときは `--baseline-ref` を省略できる。

```sh
python3 scripts/audit2/coverage_merge.py "$OUT/full/audit.sqlite" "$OUT/mathlib/external.json" \
  "$OUT/coverage-merge.json" --baseline-ref "$BEFORE"
```

終了0は合格。終了1は未解決、消失、未承認の改名、主張の型の変更、新しい基準を要する行などの不合格。終了2は記録監査の未合格、索引の不足などの前提エラー。終了3は意味の指紋だけの変化があり、レビューを待つ状態。指紋が変わった行と変更前後の値は `meaning_review` に出る。担当者が意味の変化を承認した行は、`file`、`item`、`ordinal`、`module`、`name`、`old_meaning`、`new_meaning` を持つ JSON オブジェクトの配列にし、`--accept-meaning FILE` を付けて再実行する。承認はその差分にだけ適用され、未使用の承認があれば不合格になる。基準値を承認し直す操作は別途行う。

実際の Lake ビルドと記録監査を経由する改名・型変更・意味変更の試験は、bulk 鍵で `python3 scripts/audit2/coverage_merge_selftest.py "$OUT/coverage-merge-selftest"` を実行する。

## 段7の残存条件と環境を読む検査

`residual.py BEFORE.sqlite AFTER.sqlite OUT` は、段2で残っていた条件を一覧にし、
旧書式で完全修飾名を一意に解決できた宣言の所有元、公開性、旧監査の import
閉包を記録と照合する。指定された移動先・import 境界・禁止型参照も検査する。
指定型での適用、局所的な推論、引用登録、deprecated 属性は旧 Lean 検査を引き続き実行する。
出力は `residual-summary.json`、条件ごとの `residual-classification.json`、
実際の述語と対象位置。基準表は取り込み前のものを指定する。

読み手1本の bulk 枠で、
`inspect_lean.py AUDIT.sqlite OUT` は宣言の型と値の telescope、
本体および Lake の依存パッケージに保存された instance 登録を照合する。
型の後続引数・結論だけが使う変数、値も使う変数、値の関数引数が取り出せない場合を区別する。
Lean の class 登録にある頭部を instance 登録と照合し、略記などの未展開の頭部と区別する。
候補表では引数に局所変数が現れるかも記録する。
一般の型に登録があることだけで、具体的 carrier に instance が供給されるとは判定しない。

`inspect_lean.py AUDIT.sqlite OUT --walk MODULE [--walk MODULE...]` は小規模な
独立公理照合。import した核定数の型、値、帰納型のコンストラクタをたどり、
保存された公理拡張を介さず、指定した全所有元の公理を記録と比べる。
同名の宣言が隠れる塊は、所有元を混同しないよう試作ではエラーにする。
