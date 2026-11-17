# HTT 形式化マップ

公開先（非公開の Artifact）：https://claude.ai/artifact/FqHTXBvb94z7c9xyMtXcjZ

- `template.html`：ページの見た目と動き（データの部分は `{{DATA}}`）。`data.json`：埋め込むデータ。`index.html` は生成物（git に入れない）。
- 作り直し：`python3 scripts/docs/coverage_map.py build research/htt-coverage/map`。
- 対応表から状態・宣言・理由を取り込み直す：`python3 scripts/docs/coverage_map.py refresh research/htt-coverage/map research/htt-coverage/review --format htt` の後に build。
- 2026-11-17 に、公開中のページから切り出した（`split`）。
