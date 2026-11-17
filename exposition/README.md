# exposition/ — 人が読む解説（凍結中）

2026-11-17（ユーザー決定）から **凍結**：新しいページを書かない、既存のページを書き換えない（リンクの修正だけ可）。人が読む解説は将来 **ブループリント（`blueprint/`、Verso Blueprint）に一本化**する（[doc-reorg/README.md](../formalization-plans/doc-reorg/README.md) 追記 11-17）。一本化までの参照の向きは [../README.md](../README.md) の「Documents」を見る。

## 中身

| 場所 | 中身 | 状態 |
| --- | --- | --- |
| `ja/exposition-ja.tex`（PDF 同梱） | 本論文の形式化の解説（§3〜§9、付録 A〜D） | 凍結。本論文のブループリント（`blueprint/SerreBlueprint/Paper/`）が代わる |
| `ja/lech-ja.tex`（PDF 同梱） | Lech の重複度予想の解説 | 凍結（形式化は未着手） |
| `ja/six-functor-overview.html` | 六関手形式の概観（10-16 の Claude Doc の写し） | 凍結 |
| `ja/bs/` | BS『Prisms and prismatic cohomology』の節ごとの勉強ノート（00-map、02〜10） | 凍結。節ごとの見直しの提案は `research/bs-section-review/` |
| `ja/infinity/` | ∞ 圏基盤の解説。第 I 部（00〜08 と補章）、第 II 部（f-*）、第 III 部（t-01〜t-15）、読書ルート（route-*）、`build_artifact.py` | 凍結（最終更新 11-12） |

## 旧 Artifact との関係（2026-11-17 調査）

claude.ai に公開した三つの古い版「∞ 圏基盤の解説」（10-28）・「整備後の ∞ 圏基盤」（10-29）・「∞ 圏基盤（統合版）」（10-29）は、どれも `ja/infinity/` の古い写しで、正本はこのディレクトリ。旧版にしかないのは、整備計画の時点の「移し先」の表（git 履歴に残る）、リファクタの囲み（`research/infinity-refactor-audit/box-texts.md`）、R8 のページ（`research/infinity-refactor-audit/r8-duplication.html`）だけ。作り直しはしない。

## ブループリントへの行き先（分類）

| 分類 | ページ | 行き先 |
| --- | --- | --- |
| A　文献の項目の数学の解説 | infinity/t-01〜t-15、01〜08 の数学の部分、補章（unstraightening・coherent-nerve-diagrams・cocartesian-definition・fibered-descent・presentable-route・monoidal-prl・sixff-foundations・spectra-k-theory）、bs/02〜10 | ブループリントの該当する文献の章の本文の原稿 |
| B　Lean の所在・構造の表 | infinity/00-map、f-00〜f-05 の所在表、bs/00-map の所在表 | 宣言索引（B5、`scripts/docs/declaration_index.py` 予定）で生成に置き換え、手の表は廃止 |
| C　設計の記録 | infinity/k-nonconnective-design、f-06 の経路比較、bs の設計に関わる節 | `formalization-plans/`（`bhatt-scholze/design/design-status.md`、`k-restart-draft.md`） |
| D　文献に紐づかない読み物 | infinity/index の動画イントロ、route-arith、rep-cft、classifying-shape、six-functor-overview | ブループリントの「解説」の部（Lean の節に結びつけない） |
