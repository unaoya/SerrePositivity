# Higher Algebra の項目と Lean の宣言の対応表

作成：2026-11-07（段階 II の調整役）。Kerodon の対応表（`research/kerodon-coverage/`）と同じ形で、Lurie『Higher Algebra』（以下 HA）の項目を Lean の宣言に対応させる。実作業は Codex（`codex-review.md`）、検収と地図（HTML）は調整役。

**完了（2026-11-11）**：全 2,866 項目（own 38・mathlib 39・partial 465・none 2,324・unsure 0）。要約は `review/summary.md`。レーンは閉じ、worktree と枝を削除した。

宣言欄には現行本体・固定 Mathlib に実在する宣言の `完全名 @ パス:行` を書く。ルート直下は `_root_.` を付ける。計画、却下した候補、Archive の参照は備考列 `reference_note` に置く。

## 範囲

**本全体**（11-07 夜、ユーザー：HA の形式化そのものを本格的に検討する）。全章の Section・Subsection の見出しと全項目（定義・定理・構成など番号つきの環境）を一行ずつ作り、全項目を照合する。照合の順は、使われている所と HA の形式化で最初に要る所から。

| 順 | 章 | 理由 |
| --- | --- | --- |
| 1 | 第 1 章（安定 ∞ 圏） | Lean の HA の引用 2,547 件はすべて第 1 章（§1.1 約 40、§1.3.1 約 1,580、§1.4.2 約 930）。計画も §1.1.4・§1.2.1・§1.3.4・§1.3.5・§1.4.3・§1.4.4 を引く |
| 2 | 第 2 章（∞-オペラッド）・第 3 章（代数）・第 4 章（加群） | CAlg(D(R)) を HA の定義で作るときの土台。BS の設計が 3.2.3.1・3.2.3.5・3.2.4.7・4.5.4.7 などを引く。§4.1.7（モノイダルなモデル圏の局所化）と §4.5.4（可換代数の比較）は、E∞ の模型との比較に要る |
| 3 | 第 7 章（代数的な場合） | BS の設計が 7.1.2・7.1.3・7.2.2.10 を引く |
| 4 | 第 5 章（E_k）・第 6 章（Goodwillie 微積分）・付録 | 当面の計画では使わない |

§1.3.1（dg nerve）は Kerodon §2.5 と重なる。Lean の docstring の多くが両方を挙げている（例「HA 1.3.1.12、Kerodon 2.5.6」）。この節の項目は、Kerodon の対応する行（`research/kerodon-coverage/review/ch2.csv`）を参照し、主張の比較は HA の本文で行う。

## ファイル

- 一覧のページ（非公開の Artifact、調整役が照合の取り込みごとに更新）：https://claude.ai/artifact/SCyH9UhD3zoQKEKemS7WbQ

- `citations.csv`：Lean の docstring の HA の引用（番号つき、2,547 件、11-07 の main で採取）。列は `file,line,kind,number,section,directory`。番号のない「HA」（「HA 成分」「`ModelBridge.HA`」などの別の略号）は含めない。
- `plan-citations.csv`：計画（`formalization-plans/`、archive を除く）と `research/k-coverage/` の HA の引用（74 件）。どの項目が段階 II で要るかの印。
- `toc.md`・`items.csv`：Codex が段 0 で作る（`codex-review.md` §2）。
- `review/`：Codex の確認の結果（章ごとの `ch<N>.csv`、`check/` に証拠）。

## items.csv の列

`number,kind,title,section,status,declarations,reason,confidence,lean_citations,plan_citations,kerodon,goal`

- `status`：Kerodon と同じ語彙。`own`（SerrePositivity にある）・`mathlib`（Mathlib にある）・`both`・`partial`（特別な場合・片方向・仮定が強いなど一部だけ）・`none`。
- `declarations`：`完全な名前 @ path:line` を ` | ` で区切る。
- `reason`：Kerodon の確認の基準（`research/kerodon-coverage/codex-review.md` §7.1）の形。`仮定：…（HA と一致／Lean が強い：…／Lean が弱い：…）。結論：…（…）。`
- `lean_citations`・`plan_citations`：その番号の引用の件数（上の二つの CSV から）。
- `kerodon`：同じ内容の Kerodon の番号（docstring に並んで引かれている、または本文で同じと確かめたもの）。
- `goal`：段階 II で要るか。`BS`（BS の設計が引く）・`inf`（∞ 基盤の部品）・`K`（K 側、後回し）・`-`。`plan_citations` の引用元のファイルで決める。

## 原典

HA は Lurie のページの最新版（`https://www.math.ias.edu/~lurie/papers/HA.pdf`）を使う。リポジトリには置かない（`paper/refs/` と同じ扱い）。取得した版の日付と SHA-256 を `toc.md` の冒頭に書く。
