# SerrePositivity ブループリント（試作）

Verso Blueprint（leanprover/verso-blueprint、Lean v4.35.0-rc4 の系列のコミット 7bd0c10）で、Kerodon の章ごとに SerrePositivity・Mathlib の宣言を結んだページを作る試作。まず第 1 章。

- **正本は対応表**：`research/kerodon-coverage/`（`review/ch<N>.csv` の状態・宣言・判定の理由、`item-tags.csv` の Tag、`toc.md` の見出し）。章のファイル `SerreBlueprint/Paper/*.lean`・`SerreBlueprint/Kerodon/*.lean`は `scripts/gen_chapter.py` が生成する。**生成物を手で直さない**（表を直して生成し直す）。
- 本文は対応表の判定の理由（日本語の要約）。Kerodon の本文は写さず、Tag へリンクする。
- Lean の宣言に結ぶのは、状態が own・mathlib・both で、宣言が今のソースで一意に解決できたものだけ（`(lean := "...")`）。partial は本文に宣言名を挙げるだけ。
- 本体（`..`）を path で require し、packages はリポジトリの `.lake/packages` を共有する（`packagesDir`）。依存の版は `lake-manifest.json` で SerrePositivity の manifest に揃えてある。`lake update` はしない（共有の Mathlib が動く）。

## 生成とビルド（リポジトリの root で、main の作業木ではしない）

```sh
python3 blueprint/scripts/gen_kerodon.py 1
cd blueprint
zsh ../../scripts/refactor/with_build_lock.sh --class impl --wait 3600 -- lake exe vbp build
# 出力：blueprint/_out/site/html-multi/
cd .. && python3 blueprint/scripts/style_site.py blueprint/_out/site/html-multi
```

見た目は `blueprint/style/serre.css`・`serre.js`（配色・書体・ノードのカード・目次の木）で、Verso の出力には手を入れず、ビルドの後に `style_site.py` が各ページに読み込ませる（ユーザー承認 11-18）。CSS・JS を直したときはビルドし直さず、`style_site.py` をかけ直すだけでよい。

本体の多くのモジュールと Verso の一式をコンパイルするので、昼の時間帯には流さない（`coordination.md` §2）。
