# 窓ごとの対象一覧

## 概要・方針

`<name>.json` は move / split / archive の対象を確定する配列。
本作業の前に `validate_targets.py` で書式、宣言の網羅、import グラフの試算を検査する。
この段階では実際の窓の一覧を置かない。IF-W0-3 で確定する。

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

上記の 8 フィールドはすべて必須で、追加フィールドは拒否する。
`module`・`dest` は `SerrePositivity.` で始まるモジュール名。
`moved`・`keep` は完全修飾されたソース上の宣言名の配列（生成された補助宣言は親に従う）。
`attributes` は宣言名から属性名の配列への対応表、`candidate`・`note` は文字列。
属性表は移動時に確認する情報であり、実際の属性の一致は保存検査で確認する。

- `move`：モジュールをそのまま移す。`moved`・`keep` は空配列。
- `split`：`moved` は空でなく、`keep` と重複せず、公開宣言をすべて覆う。
  元の本文・docstring・属性をそのまま切り出す。構文の対応範囲は親の README を参照。
- `archive`：archive 用の場所へ移す。`moved`・`keep` は空配列。
  対象一覧の外に元モジュールの import が残っていれば拒否する。

元モジュール・移し先の二重登録、移し先と別の項目の元モジュールとの重複は拒否する。
移し先は未作成か、コメントと `module` のみの空の骨組みファイルに限る。
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
