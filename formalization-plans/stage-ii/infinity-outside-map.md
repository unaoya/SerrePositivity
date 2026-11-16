# ∞ 圏の一般論が InfinityCategories の外にどれだけあるか（紙）

作成：2026-11-16 夜（調整役）。決定：ユーザー（11-16「頼みましょう」）。担当：⑤d。

## 0. 目的

ユーザーが Kerodon の内容を確かめて整理するにあたり、Kerodon・HTT・HA に当たる一般の部分が `InfinityCategories/` の外にどれだけあるかを分類する。EInfinity は OE-W1（③-b）が分類済み・整理中なので除く。台帳の R83（KST・HomotopicalAlgebra に ∞ の一般論が残る、保守）の具体化。

## 1. 範囲

`SerrePositivity/KST/`（8,645 本・約 667,000 行）、`SerrePositivity/HomotopicalAlgebra/`（1,147 本・約 109,000 行）、`SerrePositivity/Spectra/`（279 本・約 25,000 行）。`Archive/` は root に入らないので除く。

## 2. 分類（ファイルごと、OE-W1 の段 2 と同じ形）

- **一般の ∞ 圏論**：Kerodon・HTT・HA の項目に当たる、K 理論にも模型にも依らない主張（例：KST の Necklace、Tower、Verdier 分数、局所化不変量の一般部分）。移す先の案（`InfinityCategories/` の Kerodon・HTT・HA の節）と、当たる対応表の番号（`research/kerodon-coverage`・`htt-coverage`・`ha-coverage`）を書く。
- **一般のホモトピー論・モデル圏**：模型圏・相対圏・単体的な計算など、∞ 圏の項目には直接当たらないもの（`HomotopicalAlgebra/` に置くのが自然なもの）。
- **模型**：特定の模型の構成（KST の BF Ω スペクトル `Sp`、Spectra/ の対称スペクトルなど）。文献の定義との比較は後で作る対象（`p0-plan-draft.md` §6）。
- **K 理論に固有**：S 構成・局所化不変量・K 理論の比較など、K の文献に当たるもの。
- 判断がつかないものは「未定」とし、理由を書く。

## 3. 出力

`research/infinity-outside-map/` に：
- `files.csv`（列 `path,module,lines,classification,destination,coverage_items,external_importers,basis`。`coverage_items` は `Kerodon 5.3.1.2; HTT 3.2.1.4` のように。`external_importers` はそのディレクトリの外から import している本数）
- `summary.md`（分類ごと・サブディレクトリごとの本数と行数、一般の ∞ 圏論の主なまとまりと移す先の案、Kerodon の章ごとの対応）
- 判定は主な宣言の型と docstring から。Lean は動かさない。対応表の状態は写さない（正本は対応表）。

## 4. 規則

紙だけ。Lean の変更・ビルドはしない。main（最新）から枝を切り、報告をコミットしたら止まる。OE-W1 の移動先と重なりそうなもの（同じ Kerodon の節に置く案）は summary に書く。
