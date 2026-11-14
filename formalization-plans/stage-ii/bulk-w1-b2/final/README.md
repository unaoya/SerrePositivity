# B2 隔離プレビューの付表

固定した数学の基準は `0e8c854208151bc054e15ba3ba183a931b630b1c`。これは B3 の適用データの案であり、main への移動・凍結の承認ではない。後続 main の差分、層の例外案、R21 の説明の追記範囲は本文の確認事項を参照する。成果物のハッシュは `manifest.json`。

- `module-paths.json`：分割先を含む全パスの割当。分割は一つの元ファイルから複数の出力を持ち、各出力の元所有者は一つ。
- `module-map.json`・`namespace-map.json`：B2 基準からの import と宣言名の移行。スクリプトへ出す監査は通常の import の行き先にしない。
- `bulk-kl-module-map.json`・`bulk-kl-namespace-map.json`：KL 前からの変更を合成した配布案。名前空間全体の変更と、宣言ごとの行き先を区別する。
- `declaration-names.jsonl.gz`：定義元モジュール付きの実際の旧名・新名。private は raw kernel 名も保持。コンパイラの共有する補助名は順番で対応を捏造せず `compiler-inventory-only` として残す。
- `declaration-inventory-{before,after}.jsonl.gz`・`declaration-generated-groups.jsonl.gz`：前後の全宣言の一覧と、生成補助の保存比較。
- `comparison-module-plan.json`・`comparison-owned-name-map.json`：通常の private を含む保存比較専用の正規化。配布用の import 改名表とは用途が異なる。
- `attribute-declarations.json`：2,436 宣言参照の採否。付与1,884行・異なる1,883組、除外538、保留14。`attribute-rows.json` は元の全9,048行。大きいJSONは `.gz` に圧縮する。
- `location-refresh-ledger-187.json`：元187行を元の記述・順序・source付きで保持。29解決、82 Kerodon partial維持、76記録のみ。
- `preview-edits.json.gz`：固定した元ソースから数学の移動プレビューを再現する第一の束。先に準備済みの Citation.lean と bibliography.json が必要。元ソースのハッシュが違えば全体を拒否し、書き始めない。
- `bounded-doc-preview-edits.json.gz`：第一の束の後に、別途ビルド・保存比較した14本のmodule docstring補完だけを適用する第二の束。既存のモジュールコメント内に限る。広いR21の旧docstring全体の案は含まない。名前の全表の移動後の範囲は、第二の束の実際のLean索引で更新する。
- `bounded-doc-{before,after}.json.gz`・`bounded-doc-comparison.json`：第二の束の前後の採取と同一性の検証。第一の束の全体比較と合成して最終コメントまで検査する。
- `audit-discovery-preview-edits.json.gz`：scripts側だけの第三の束。nestedな監査4本の再帰的な発見とBS段階IIの登録を補う。実際の発見106本・manifest106本の一致をPythonで確認し、full verify自体はB3へ残す。共有の既存verifyスクリプトはこの枝では変更しない。
- `*-complete.json`・`*-check*.json`・`preservation-receipts.json.gz`：実測と検証の根拠。B3 の root・全監査・verify を実行した記録ではない。

圧縮した JSON / JSONL は Python 標準の `gzip` と `json` で読める。通常の配布表は展開後のファイル名を用いる。

再適用の事前検査（既定は読取りのみ）：

```sh
python3 scripts/refactor/bulk_apply_preview.py --root "$preview" --bundle "$tables/preview-edits.json.gz"
```

第二の束も既定は読取りのみで検査する。固定基準での隔離再現では、第一の束を適用してから第二の束を順に適用する。

```sh
python3 scripts/refactor/bulk_apply_preview.py --root "$preview" --bundle "$tables/bounded-doc-preview-edits.json.gz"
```

B3承認後は、更新済み main に対して表と三つの束を作り直してから適用する。固定基準用の束を、後続 main へ強制適用しない。

B4 の採取は元の import 環境で、元の作業木をカレントにして通常の鍵を取る。`$tools` は取り込み済みの scripts/refactor の絶対パス。昼は各回3〜5分以内になるファイルの組へ分ける。下の例は280秒で返却し、次の組は鍵を取り直す。`bulk_namespace.py collect` は元の共用採取器のファイルを変更せず、plain open の逐次解決と Lake の設定を引き継ぐ：

```sh
zsh "$tools/with_build_lock.sh" --wait 3600 --class bulk -- gtimeout --kill-after=3s 280 python3 "$tools/bulk_namespace.py" collect --root "$old_tree" --files "$files" --output "$before_index"
python3 "$tools/bulk_namespace.py" rewrite --root "$old_tree" --files "$files" --plan "$tables/bulk-kl-namespace-map.json" --index "$before_index" --output "$rewritten"
```

`rewrite` はプレビューを新しいディレクトリに出す。保留・変更差分を確認してから利用側へ反映する。明示的な宇宙や旧 open の意味を保存し、部分的な移動先のモジュール名を名前空間として open に追加しない。

保存比較の再現では、元と先の成果物を独立したディレクトリに置く。検証専用バイナリは共有の Lean 採取器を変更せず、次で生成する（コンパイルは通常の鍵の中で実行）：

```sh
python3 "$tools/bulk_snapshot.py" --root "$preview" --output-dir "$snapshot_dir" --compile
```

`comparison-owned-name-map.json` は実在する private kernel 名を所有元付きで照合するための表であり、利用側のソース書き換えには使わない。private ParserDescr の自己名は検証専用の追加フィールドで比較し、元の本体ハッシュは保持する。明示的に書いた ParserDescr 宣言はこの補助比較から除く。

第三の束も第一の束の後に適用する。第二のコメント束とは対象が重ならない。

```sh
python3 scripts/refactor/bulk_apply_preview.py --root "$preview" --bundle "$tables/audit-discovery-preview-edits.json.gz"
```

配布用の四つの地図はJSONへ展開してからcollect/rewriteへ渡す。適用の三つの束はgzipのまま使う。

検証専用ワーカーの原本は verification-code/ に保存する。機械依存の一時ディレクトリは当時の実行記録であり、次の凍結では作業木と入力の署名を作り直す。共有のLean採取器・比較器は変更していない。
