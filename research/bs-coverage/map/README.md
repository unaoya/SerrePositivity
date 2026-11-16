# Prisms 形式化マップ

公開先（非公開の Artifact）：https://claude.ai/artifact/YWUyntvwsGb2aX39kZnMyT

- `template.html`：ページの見た目と動き（データの部分は `{{DATA}}`）。`data.json`：埋め込むデータ。`index.html` は生成物（git に入れない）。
- 作り直し：`python3 scripts/docs/coverage_map.py build research/bs-coverage/map`。
- 対応表から状態・宣言・理由を取り込み直す：このページのデータは項目の形が違うので、`refresh` には対応していない（`data.json` を対応表から作り直すときは形を合わせる）。
- 2026-11-17 に、公開中のページから切り出した（`split`）。
