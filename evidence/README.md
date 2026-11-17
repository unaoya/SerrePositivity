# 検証の証拠

レーンが検証のために作った生成物（採取の json・gz・log、保存比較の出力、適用スクリプトと移動表の json）の置き場。文書ではないので `formalization-plans/` から分けた（文書の整理 段 1、2026-11-17、[doc-reorg/README.md](../formalization-plans/doc-reorg/README.md) §4）。

## 構成

| 場所 | 中身 |
| --- | --- |
| `bulk/` | 一括レーン（KL-W1 のチャット）：`bulk-5inf0`・`bulk-5inf3a`・`bulk-b3prime`・`bulk-b5`・`bulk-w1-b2`・`bulk-w1-b3`、KL-W1 の停止点 `kerodon-layout-stop-1-6`・`kerodon-layout-stop-3` |
| `bhatt-scholze/` | BS（⑤a・⑤b・⑤c・⑤d）：BS-Wn の移動表（`*-moves.json`・`*-merges.json`）と適用スクリプト、`b4-m15-2026-11-14`・`bulk-w1-b4`・`klw1-followup`、G12 の監査 53 本（`g12/`） |
| `inf-supply-b/` | ③-b（IS-W2）：`inf-supply-b4`・`inf-supply-e01-refactor-validation`・`is-w2-b4-20261114` |
| `scheme/` | ⑥：`scheme-w1-b4`（⑥ の停止点の後に移す） |

中身は記録なので書き換えない。参照は、それを作った報告（`formalization-plans/…/report-*.md`）から張る。

## これからの証拠の置き方（規則、2026-11-17）

1. **大きい生成物は git の外に置く。** gz・ログ・採取の json・保存比較の出力は `~/serre-evidence/<レーン>/<段>/` に置く（本体の作業木の外。バックアップは各自）。リポジトリには**目録だけ**をコミットする：`evidence/<レーン>/<段>/manifest.json`（列：`path`・`sha256`・`bytes`・`made_by`（手順かスクリプト）・`commit`（対象の枝の HEAD））。報告には目録のパスを書く。
2. **再利用する検査のスクリプトは `scripts/<話題>/`** に置く。その段限りのものは証拠と一緒に（git の外）。
3. **既にあるもの**（この下の 158 MB）は履歴を変えずにここに残す。Git LFS は採らない（公開リポジトリの帯域・容量の上限、既存の履歴は小さくならない）。
4. 各レーンの指示書には「証拠は git の外、目録だけをコミット」の一行を入れる（段 2 で、各レーンの停止点のときに）。
