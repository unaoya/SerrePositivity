# B2 配置のプレビュー（検証中）

本体の基準は `0e8c85420`。ここは移動を適用する指示ではない。全体のビルド・保存比較の結果をB2停止点で追記する。

- `module-paths.csv` は主対象6,466本の元パス・新パス・理由・元のSHA-256。
- `module-map.json.gz` は実際に変わる5,301モジュールの対応。
- `namespace-changes.json.gz` は所有モジュール付きの公開515名とprivate 15束縛の変更案。ディレクトリ分けだけの移動では公開名前空間を保つ。全宣言のidentity行を含む表は全体保存比較後に作る。
- `layers-proposed.json.gz` はファイル単位5段の設定の案。新しい1辺の例外を含むので、承認前に本体の設定へ入れない。
- `new-reverse-edge-proposal.json` はmainから引き継いだ1辺と理由。
- `actual-graph-summary.json` は実際の隔離プレビューを読んだ静的検査。上の未承認例外込みの層検査であり、無条件の承認済み0件という意味ではない。
- `preview-bundle-summary.json` は作業用の適用束の件数とハッシュ。検証中のため、Leanの修正後は再生成する。

全体の検証の完了までは「B2準備中」である。`directory-tree.md` で配置を比較できる。

`preview-edits.json.gz` は隔離作業木を再現するデータで、本体へは未適用。移動先・前提のビルドと保存比較はまだ実行中である。凍結時には最新mainとの差分を取り込んで作り直す。元ファイルが1個でも変わっていれば、適用道具が書込み前に止める。読取りだけの検査は専用枝のリポジトリ直下で次のとおり。

```sh
python3 scripts/refactor/bulk_apply_preview.py --root "$PWD" --bundle formalization-plans/stage-ii/bulk-w1-b2/layout/preview-edits.json.gz
```

`additional-script-rewrites.json` は `audit_*.lean` 以外のBS領域監査と任意のC2診断器の追従。`readme-manifest.json` は配置の説明とArchiveへのREADMEの追従。`public-target-collision-check.json` は改名する公開515名の行き先同士に衝突がない検査で、全宣言の検査の代用ではない。
