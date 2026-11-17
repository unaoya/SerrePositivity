# B3 後の追従資料

基準は main c5c4436c0 とその上の文書コミット a9dc71e46。移動前の本体を持つ枝で、main を取り込む前に参照を採取する。採取時の原ソースと索引を保存し、main の取り込み前にプレビューを作る。保留0と差分を確認してからmainを取り込み、生成した差分を新しい配置へ反映する。取り込み後のソースに古い索引を流用しない。

`module-map.json.gz` はこの凍結基準からの通常 import の地図、`namespace-rewrite-map.json.gz` は実名と所有元に基づく書き換え用の地図。`namespace-map.json.gz` は、元の kernel 名を保持する六つの拡張メソッドも明示した全表。書き換え用では、その六つの恒等行を除く。脚本に移した四つの監査は通常の import 先にしない。保存比較の private 所有元表はソース書き換えに使わない。

下では `$tools` が取り込み済みの `scripts/refactor` の絶対パス、`$tables` が JSON を展開したこの資料のディレクトリ、`$old_tree` が採取する移動前の枝、`$files` が対象のJSON配列、`$before_index` が採取先、`$rewritten` が空のプレビュー出力先。drafts は `$files` から外す。以下は各一行のコマンド。

```sh
zsh "$tools/with_build_lock.sh" --wait 3600 --class bulk -- gtimeout --kill-after=3s 280 python3 "$tools/bulk_namespace.py" collect --root "$old_tree" --files "$files" --output "$before_index"
python3 "$tools/bulk_namespace.py" rewrite --root "$old_tree" --files "$files" --plan "$tables/namespace-rewrite-map.json" --index "$before_index" --output "$rewritten"
```

通常のレーンの鍵の規則を用い、昼の採取は3〜5分以内の組に分ける。B3一括枝の鍵免除は利用側に適用しない。採取の時間切れや保留は成功扱いにせず、出力と診断を保持する。原ソースと索引の全バイト一致の検査を外さない。

通常の open は元の可視性を保ち、移った項を新しい完全名へ置き換える。制限付き open は、採取した全メンバーが同じ末尾名で一つの実名前空間へ移る場合だけ、その名前空間へ向ける。移動先モジュール名から名前空間を推定しない。新しい枝固有の曖昧な open は保留として確認する。

`b4-branch-impact.json` は git の参照だけから採取した時点の一覧。③-a `math/inf-supply`、③-b `math/inf-supply-b`、⑤a `math/bs-impl`、⑥ `math/scheme` の基準に未包含のコミットが触ったファイルを調べた。完全名と旧モジュール名の文字列が一致する件数であり、非修飾名の束縛を採取した結果ではない。取り込み前に各枝の HEAD を照合し、枝が進んでいれば再集計する。他レーンの作業木へはアクセスしない。

監査の `Lean.Name` には、モジュールを選ぶ名前と宣言を調べる名前がある。`env.header.modules` や `env.getModuleIdxFor?` から定義元を選ぶデータはモジュール表で照合し、`env.contains required` の必須宣言リストは所有元付きの実名表で照合する。ファイルだけを移し宣言の名前空間を保つ場合、宣言名もそのままになる。`collect/rewrite` の対象になる構文の参照と、こうした引用名のデータを区別し、モジュール表による全引用名の一括置換は行わない。今回の E∞ 監査では、その混同による2引用を訂正し、検査項目を保って正式監査を再実行する。
