# 本論文のブループリント：対応表の作成（紙）

作成：2026-11-17（調整役）。決定：ユーザー（11-17「一旦本論文のブループリントを作ってみましょう」）。担当：⑤d（または ⑤a）。

## 0. 目的

本論文（OpenAI, *Positivity of Serre's Intersection Multiplicity*、2026-09-23、`paper/paper.pdf`）の Verso Blueprint を作る（Kerodon 第 1 章の試作 `blueprint/kerodon/` と同じ作り方、枝 `docs/kerodon-blueprint`）。今ある対応表 `research/k-coverage/maps/paper/`（63 項目）は §3・§4 だけなので、**論文全体の対応表**を作る。

## 1. 対応表

置き場所：`research/paper-coverage/`。形は HA・DAG XIII の対応表と同じ（`toc.md`、`items.csv`、`review/` に照合の結果）。
- 範囲：§1〜§5（序論の主定理・系を含む）の見出しと、番号つきの全項目（Theorem・Lemma・Proposition・Corollary・Definition・Remark・Example、番号つきの式）。今の §3・§4 の 63 項目は引き継ぐ（状態・宣言・理由を写すのではなく、`k-coverage/maps/paper/` の行を照合し直して同じ形に）。
- 照合：各項目に、対応する本体の宣言（主に `SerrePositivity/Paper/`、`Inputs/`、`IntersectionMultiplicity/`、`PerfectComplex/`、`KTheory/`、`BhattScholze/` の使われ方）と状態（own・mathlib・both・partial・interface・none）と理由。`sorry` の有無は宣言ごとに確かめる（`Inputs/Descent.lean` の `theorem_3_1_K0` など）。
- **依存の辺**：`edges.csv`（列 `number,depends_on,evidence_location,kind`）。項目の主張と証明が引く、論文の中の番号つきの項目（`kind=internal`）と、外の文献の番号（`kind=external`、`depends_on` は `BS19 8.4`・`LT 1.3`・`Stacks 0815` のように略号表の略号と番号）。
- 版は toc.md の冒頭に記録（`paper/SOURCE.md` の上流コミット）。

## 2. 規則

紙だけで、Lean の変更・ビルドはしない。既存の対応表は書き換えない。main（最新）から枝を切り、報告をコミットしたら止まる。調整役が対応表から本論文のブループリント（`blueprint/` の下、Kerodon と同じ生成スクリプトの形）を作る。

## 追記（2026-11-17、調整役）：担当の変更と設計の保留

- ⑤a・⑤d を閉じたので、§1 の対応表と `edges.csv` は **IC-W1 の後に開く新レーン（文書の生成）の最初の紙**にする。同じレーンが B5（宣言索引、`research/declaration-index/`）とブループリントの生成を持つ（ユーザー決定 11-17、案 A）。
- ブループリントの設計は**保留**（作りながら再検討、ユーザー 11-17）。調整役の案を記録しておく：文献ごとの部に加えて横断の部「P⁰ への道」（`research/p0-lurie/item-closure/order.md` の順序を章立てに）；項目の解説の原稿は `research/<文献>-coverage/notes/<項目>.md` に置いて生成器が読む（`exposition/` の分類 A はそこへ写す、Kerodon 第 1 章で試す）；読み物（分類 D）は `research/essays/` から「解説」の部へ；依存グラフは閉包の `edges.csv` を `(uses := …)` の源に；スタイルは後。

