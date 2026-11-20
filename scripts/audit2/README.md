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
- `run` は読み取り前に Lake の `--no-build --rehash --no-cache` を同じ対象にかける。個々の `.trace` の成果物一覧と、その時点の `.olean/.server/.private/.ilean` の実ハッシュを検証する。途中でソース、trace、成果物のファイル印が変わった場合も失敗する。Lake の入力トレースと固定依存の信頼を前提とする。Lake のハッシュは再ビルド判定用であり、改ざんに対する暗号学的な署名には使わない。編集中の作業木からの読み取りは避ける。
- `run --previous PATH/audit.sqlite` は同じバージョンで、同じ依存トレース・成果物ハッシュの行を再利用する。再利用時も全対象を読み取り前に検証する。中断した補完は、同じ版・成果物のまま `--resume` でチェックポイントから再開する。`--modules FILE` は手元の部分検査で、明示的な一覧を指定する。全体判定には全モジュールを渡す。部分範囲は証拠経路の構成に必要な import を含める。
- `recompute.py` は本体一覧を再列挙してから塊ごとに bulk 枠を取り、全 kernel 行に対して `collectAxioms` を呼ぶ。保存側とキー・集合を照合する。相違、未知、余分・欠落があれば不合格とし、記録監査の判定を取り込みに使わず調査する。同名の生成宣言が隠れる場合は該当所有元の型と値を一時の別名で核に通し、そのレコードの公理を調べる。失敗した対象を省略しない。コマンド本体が鍵を取る。外側から重ねて鍵を取ると待ち合わせになる。同じ出力先を渡すと完了した塊から再開する。余裕が変わったときは `--replan --limit N` で未実行分を組み直す。同じ Lean/Mathlib 版の完全な外部 import 索引を `--external-ownership` で渡した場合、`--limit` は外部を含む。宣言0件の import 専用モジュールには、ソース全体が import だけであることと現在の trace を照合する。詳細は [再計算監査案](../../formalization-plans/stage-ii/consolidation/recompute-audit-design.md)。

`run` は `audit.sqlite` の `module`、`decl` を出す。キーは所有モジュールとカーネル名、主張と値の指紋は同一 Lean 版の構造ハッシュ。値の欠如、位置の欠如、未保存公理を NULL で表す。採取後の公理 `axioms` は空集合と未判定を区別する。型、値、コンストラクタの辺はそれぞれ定数名を保持し、外部名も残す。保存された instance 登録はスコープと優先度を含む。`internal` は Lean の内部名フラグ。ソースコマンドと生成由来の区分は `origins.py audit.sqlite origins.sqlite` で別の所有元付き表に出せる。保留を明示し、`partial_source` は保存された `_unsafe_rec` の親を含む。他モジュールの属性追加を含む実効 instance 探索は別の検査とする。

`sets.json`、`g2.json`、`comparison.json`、`timings.json` に母集団・判定・時間・個別結果を保存する。終了0は合格、1は判定違反、2は取得・環境・前提エラー。未判定を空の公理集合として扱わない。資源上限の診断は生ログに残し、他の大きな読み込みがない枠でやり直す。

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
