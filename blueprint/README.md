# SerrePositivity ブループリント（試作）

Verso Blueprint（leanprover/verso-blueprint、Lean v4.35.0-rc4 の系列のコミット 7bd0c10）で、Kerodon の章ごとに SerrePositivity・Mathlib の宣言を結んだページを作る試作。まず第 1 章。

- **正本は対応表**。`research/*-coverage/` の照合表と資料を使う。表を直し、生成器を通して章ファイルを更新する。
- 本文は対応表の判定の理由（日本語の要約）。Kerodon の本文は写さず、Tag へリンクする。
- Lean のリンク（`(lean := "...")`）は、記録監査が確認したカーネル名から作る。生成時に未解決があれば止まり、書き出したカードのリンクを項目ごとに照合する。
- 本体（`..`）を path で require し、packages はリポジトリの `.lake/packages` を共有する（`packagesDir`）。依存の版は `lake-manifest.json` で SerrePositivity の manifest に揃えてある。`lake update` はしない（共有の Mathlib が動く）。

## 生成とビルド（リポジトリの root で、main の作業木ではしない）

リポジトリの root で [文献対応表の手順](../scripts/audit2/README.md#段4文献対応表とブループリント) を通して、生成物を確認する。生成と反映を終えたら Verso をビルドする。

```sh
zsh scripts/refactor/with_build_lock.sh --class bulk --wait 3600 -- lake --dir blueprint exe vbp build
# 出力：blueprint/_out/site/html-multi/
python3 blueprint/scripts/style_site.py blueprint/_out/site/html-multi
```

見た目は `blueprint/style/serre.css`・`serre.js`（配色・書体・ノードのカード・目次の木）で、Verso の出力には手を入れず、ビルドの後に `style_site.py` が各ページに読み込ませる（ユーザー承認 11-18）。CSS・JS を直したときはビルドし直さず、`style_site.py` をかけ直すだけでよい。

本体の多くのモジュールと Verso の一式をコンパイルするので、昼の時間帯には流さない（`coordination.md` §2）。
