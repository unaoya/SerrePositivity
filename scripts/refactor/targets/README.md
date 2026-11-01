# 窓ごとの対象一覧

## 概要・方針

`<name>.json` は move / split / archive / reimport の対象を確定する配列。
本作業の前に `validate_targets.py` で書式、宣言の網羅、import グラフの試算を検査する。
IF-W0-3 で窓ごとに一覧を作り、各 wN.md に検査結果と承認待ちの状態を記録する。

## 書式と規約

```json
[
  {
    "module": "SerrePositivity.X.Y",
    "action": "split",
    "dest": "SerrePositivity.InfinityCategories.ModelBridge.Y",
    "moved": ["Example.modelLemma"],
    "keep": ["Example.coreLemma"],
    "attributes": {"Example.modelLemma": ["simp"]},
    "candidate": "R72",
    "note": "末尾の Model の節を移す"
  }
]
```

上記の 8 フィールドはすべて必須。split・move・reimport に限り、任意フィールド `imports` と `downstream_imports` を認める。それ以外の追加フィールドは拒否する。
`module`・`dest` はプロジェクトのモジュール名（`SerrePositivity` または `SerrePositivity.` で始まる名前）。
`moved`・`keep` は完全修飾されたソース上の宣言名の配列（生成された補助宣言は親に従う）。
`attributes` は宣言名から属性名の配列への対応表、`candidate`・`note` は文字列。
属性表は移動時に確認する情報であり、実際の属性の一致は保存検査で確認する。

- `move`：モジュールをそのまま移す。`moved`・`keep` は空配列。
- `split`：`moved` は空でなく、`keep` と重複せず、公開宣言をすべて覆う。
  元の本文・docstring・属性をそのまま切り出す。構文の対応範囲は親の README を参照。
- `archive`：archive 用の場所へ移す。`moved`・`keep` は空配列。
  対象一覧の外に元モジュールの import が残っていれば拒否する。

元モジュール・移し先の二重登録、移し先と別の項目の元モジュールとの重複は原則として拒否する。
§10.30 の例外として、同じ `module` の `split` 1件に続く `move` 1件だけを許す。
これは split 後の keep 側の移動を意味し、模擬・適用とも split → move の順にする。
move 同士、split 同士、move → split、3件以上の同一 module 登録は拒否する。
move / split / archive の移し先は未作成か、コメントと `module` のみの空の骨組みファイルに限る。reimport は同じ既存ファイルを使う。
同じファイルの本文に複数の分割が作用する場合は別の窓に分ける。

## 使われ方

```sh
python3 scripts/refactor/validate_targets.py scripts/refactor/targets/<name>.json \
  --output .lake/verify/targets-result.json
```

複数 JSON も指定でき、全体をまとめて重複検査する。
分割の依存方向にはビルド済みの宣言を使うため、既定では対象をビルドして snapshot を採る。
事前採取したものを使う場合は `--snapshot SerrePositivity.X.Y=.lake/verify/before.json` を指定する
（複数指定可）。snapshot に保存されたソースが現在の内容と一致する必要がある。
検査は `.lean` を書き換えないが、ビルドと `.lake` 内への記録は行う。

移動・分割後の import グラフを模擬し、層組別の直接違反、tier ごとの禁止閉包、
中核各モジュールの禁止閉包、入口辺数を元のグラフと比較する。
いずれかが増えると FAIL。単なる改名では移動前後の中核の根を同一視する。
出力には前後の層組別件数・禁止モジュール総数、増えた指標、分割の依存方向を含める。
成功は終了コード 0、書式・参照・層検査の失敗は非零。

受入試験は `python3 scripts/refactor/test_targets.py`。
正しい move / split / archive の各 1 件と、未知の宣言・二重登録・archive の外部利用者・
層違反の増加を検査する。試験用のモジュールは終了時に削除する。
imports・downstream_imports・reimport の回帰試験は `python3 scripts/refactor/test_targets_imports.py`。

## 分割後の import の証拠（IF-W0-3 §10）

`imports` は元モジュール名と移し先モジュール名の **両方** をキーとする辞書で、
値はそれぞれの分割・最小化後の完全な import 一覧（重複なし）とする。
省略時は従来どおり元の import を保持した分割を模擬する。

```json
"imports": {
  "SerrePositivity.X.Y": ["Mathlib.Data.Nat.Basic"],
  "SerrePositivity.InfinityCategories.Core.Y": ["SerrePositivity.X.Y"]
}
```

この指定は、専用 worktree で `split_module.py --apply --prune-imports` を実行し、
前後の snapshot・保存比較・影響するモジュールのビルドが成功した記録から写す。
試験終了後は元のソースへ復元する。証拠のログと import 一覧の対応を各窓の文書に記載する。
`imports` 自体はビルド成功を証明するものではない。未検証の import を書いて閉包を小さく見せない。
validator はキー、値の型、自己 import、存在しないプロジェクトモジュール、
循環、および snapshot が要求する両側間の依存方向が保持されることを検査する。
複数 split でも、利用元への分割先 import は自動追加しない（§10.14）。
public import、simp・instance、本文中の名前だけから補充を決めず、元の import を保持する。
各試験の `imports` を適用後、明記された `downstream_imports` だけを合成し、全 move の改名を反映する。
互換性のため結果の `consumer_import_additions` は残すが常に空。補充は `downstream_imports` に記録する。
古い plan.json の利用元への自動追加は適用せず、宣言リストから計画を再生成する。

結果の before/after には tier ごとの `entry_edges` も含む。


### move の imports（IF-W0-3 §10.4）

move では `imports` のキーは移動先 `dest` の1件だけとし、値は縮めた import の完全な配列とする。
その場の最小化で証拠を取り、名前変更は validator が全対象へまとめて適用する。
`python3 -B scripts/refactor/prune_imports.py MODULE --output proof.json` は、
元のモジュール名のまま最小化・保存比較・下流ビルドを行い、既定でソースを復元する。
`--snapshot FILE` は現ソースと一致する既存 snapshot を使い、`--apply` は成功時だけ変更を残す。
move の証拠には前後の保存比較・下流ビルド・復元がすべて成功した記録を用いる。

### 下流の import 補充（IF-W0-3 §10.6）

`downstream_imports` は「移動前の下流モジュール名 → 追加した直接 import の配列」。
既存の import を置換せず追加し、最後に全 move の改名を反映する。
自己参照、循環、存在しない対象・依存先、重複は拒否する。省略は空の追加と同じ。
束は全 split・move を適用してから下流ビルドを一回行い、失敗した利用元だけを補充候補にする（§10.12–14）。
既存 prune の補充処理も、全ログと元の snapshot による使用定数の定義元を調べ、
移動した定数は分割先に対応させる。補充先が `layers.json` の `core`
（Simplicial・Core・Kan・Coherent・F1・F1B・HomotopyLimits・Stable・F2・StablePresentable）なら、
import を足す前に STOP。利用元、エラー行に対応する失敗宣言、使用する移動宣言を報告する。
位置が取れない場合は推測せずエラーの行を残す。中核への補充で分類の問題を隠してはならない。
中核でない利用元には不足分だけを補い、ビルド・保存比較・層検査を通す。
証拠試行では補充した下流も復元し、実証された追加だけを `downstream_imports` に写す。
既に承認された W1 の補充は validator が引き続き合成する。静的 PASS はビルド・保存の証拠ではない。

### reimport（IF-W0-3 §10.8）

`action: "reimport"` は移動せず import の完全な一覧を置換する。
`dest` は `module` と等しく、`moved`・`keep` は空配列。
`imports` は必須で、キーは当該モジュールの1件だけ。`downstream_imports` も使える。
この action では既存の同名ファイルを認めるが、他の項目との重複・自己参照・循環は拒否する。
ルート名 `SerrePositivity` も指定できる。Stable・F2・ルートの入口ファイルは保存比較をせず、
一時適用してビルドと層検査を確かめ、復元する。それ以外の宣言を持つファイルでは保存比較も必要。

### 外部定義の生成補題（IF-W0-3 §10.7）

snapshot の `environment_parent` は環境で宣言として存在する最長の真の名前接頭辞、
`parent_module` はその定義元。ソースの明示的宣言を優先する。同じモジュールの親は補助宣言として扱う。
別モジュールの親を持つソースにない定数は分割から除外し、比較結果の `transient.before/after`
と分割計画の `transient` に名前を記録する。親を解決できないソース外定数は分割を STOP する。

### 宣言位置・属性の帰属（IF-W0-3 §10.10–10.11）

snapshot の `source_range` は属性の行を含む開始・終了行と列、および宣言名の位置を記録する。
無名 instance は位置でコマンドと対応づけ、環境が付けた `inst…` 名を moved/keep に用いる。
生成定数の帰属は、ソース宣言の範囲内の位置、private 接頭辞を正規化した最長の真の宣言接頭辞、
同一モジュールの親名に続く承認済み接尾辞の順に決める。
接尾辞は `assoc`・`apply`・`symm_apply`・`fst`・`snd`・`coe`・`hom`・`inv`・`inj`・`injEq` に限る。
外部の親を持つものは transient とし、どの規則でも帰属しないものは STOP する。
保存比較は属性で生成された補題も含み、証明内部の `._proof_<数字>` 補助のみ比較から除く。

ファイル内の宣言への attribute は宣言の直後へ移し、外部名の local/scoped 属性は同じ section 内で両側へ写す。
外部名のグローバル属性は keep に残し、moved の後続宣言が依存しうる場合は STOP する。
`open … in`・`set_option … in`・`variable … in` は宣言と一体として扱う。
`#min_imports` の候補がコンパイルしない場合は元の import に戻してから、
ビルドと保存比較を満たす import の除去だけを採用する。結果に `min_imports_fallback` を記録する。
