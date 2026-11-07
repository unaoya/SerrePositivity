# Ch 2 — Kerodon 対応表の照合

- 対象は `items.csv` の Ch 2 全 213 行。優先対象 34 行は ok 20、fix 14。
- 段 2 では Kerodon の各項の本文と Lean の型を照合し、対応が残る行の 203 種の宣言・ソースの組を `#check` と `#print axioms` の出力に結び付けた。このうち 48 種を章のレビューで追加検査した。標準 3 公理以外の依存および型中の `ModelCategory` 仮定は 0。
- 段 3 では元の none 80 行と、確認の結果 none に戻した 1 行を調べた。番号・タグ、双対・特例の検索語、近傍で読んだ宣言と採否を行ごとに記録した。作業木に `citations.csv` が見つからなかったので、`citations-summary.md` を参照し、現行の Lean ソースで同じ小節の番号とタグ URL を直接検索した。たとえば 2.1.2.3 の番号一致は HTT の slice・join の引用で、Kerodon で同行に引かれているのは §4.3.6 だった。
- `check` は最終引用に対する記録。元のまま型を確認した found 56、名称または引用先を更新して型を確認した renamed 83、最終引用を採らなかった not_found 74。

| 最終 status | ok | fix | 合計 |
|---|---:|---:|---:|
| own | 4 | 15 | 19 |
| both | 0 | 0 | 0 |
| mathlib | 28 | 12 | 40 |
| partial | 12 | 68 | 80 |
| none | 72 | 2 | 74 |
| 計 | 116 | 97 | 213 |

- [2.1.7.1](https://kerodon.net/tag/00EE) と 2.1.7.10 の豊穣合成は、Mathlib の `EnrichedCategory` とテンソル因子の順序が逆。任意の基礎モノイダル圏での比較は確認できず、単体集合で豊穣化する 2.4.1.1 と区別した。
- [2.2.8.9](https://kerodon.net/tag/00AL) は `Pith` を確認した。対象と 1 射を保ち、Hom 圏を可逆な 2 射に制限する。2.2.8.12 で求める Hom の同型類による商圏までは含まない。
- [2.5.5.15](https://kerodon.net/tag/00QP) には非正規化・正規化の相対複体が別々にある。相対ホモロジーの比較まで確認できたものを完全対応とするため、partial にした。
- [2.5.9.18](https://kerodon.net/tag/00SV) の原文は比較写像が自明 Kan fibration であることを要求する。採用した宣言の型で確認できるのは同じ写像が準圏の同値であることなので、partial とした。

証拠の項目番号は `ch2-kernel-evidence.json` の `items` にあり、タグ URL、参照の型・公理、検査元のコミットを引ける。段 3 の詳細は `ch2-none-search.json`。
