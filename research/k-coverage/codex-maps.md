# Codex への依頼：K 理論の文献ごとの項目と Lean の宣言の対応表

作成：2026-11-07（段階 II の調整役）。宛先：K の地図の Codex（worktree `../SerrePositivity-k-maps`、枝 `research/k-maps`）。検収と地図（HTML）は調整役。

## 0. 背景

`items.csv`（README）は、主定理の K 側の二つの sorry を消す経路で使う主張だけを集めた表（17 文献・208 項目）で、Lean を動かしての確認はしていない。K の計画は相談しながら見直す予定（README の「K の計画の問題」10 点）なので、その材料として、**主な文献について全項目の表**を作る。K のレーンは後回しなので、急がない。深さを優先する。

## 1. 対象

| 文献 | 範囲 | 置き場所 |
| --- | --- | --- |
| 本論文（`paper/paper.pdf`） | §3・§4 の全項目（K 側） | `maps/paper/` |
| KST（Kerz–Strunk–Tamme, Algebraic K-theory and descent for blow-ups） | 全項目 | `maps/kst/` |
| Land–Tamme（On the K-theory of pullbacks） | 全項目（付録を含む） | `maps/land-tamme/` |
| Tamme（Excision in algebraic K-theory revisited） | 全項目 | `maps/tamme/` |
| BGT（Blumberg–Gepner–Tabuada, A universal characterization of higher algebraic K-theory） | 全項目 | `maps/bgt/` |
| ほかの 12 文献（Waldhausen、Thomason–Trobaugh、Drinfeld、9 人論文、Neeman ほか） | `items.csv` にある項目だけ（全項目は作らない） | `maps/others.csv` |

- 原典は arXiv の最新版を使い、版（arXiv 番号と v 番号）を各 `toc.md` の冒頭に書く。`items.csv` の番号がどの版に従っているかも確かめ、ずれていれば対応を書く（README の問題 8 の BGT の番号のずれの疑いを含む）。PDF・TeX のソースはコミットしない。
- 文献の版が取れないものは止めて報告する。

## 2. 列と status

各文献の `items.csv`：`number,kind,title,status,declarations,reason,confidence,lean_citations,route,frozen`

- `status`：`own`・`mathlib`・`both`・`partial`・`interface`（Lean に仮定・界面として置いてあるだけ）・`none`。
- `declarations`：`完全な名前 @ path:line` を ` | ` で区切る。
- `reason`：§4 の形。
- `lean_citations`：Lean の docstring でのその番号の引用の件数（§3 の 1）。
- `route`：README の `items.csv` の `goal`（`required`・`not_required`・`unknown`）。`items.csv` にない項目は空。
- `frozen`：対応する宣言が凍結したコード（L2 の plus 構成、L6、`KST/ProExcision/` など。`formalization-plans/` の凍結の記録で確かめる）にあれば `yes`。

## 3. 段と止めて報告する点

| 段 | 内容 | 止めて報告 |
| --- | --- | --- |
| 段 0 | 1. Lean の docstring の、六つの文献の引用を集めた `maps/citations.csv`（`file,line,reference,number`。引用の書き方の揺れ（「KST Lemma 4.10」「[KST, 4.10]」「Kerz–Strunk–Tamme」など）を吸収する正規表現も残す）。2. 本論文・KST・Land–Tamme・Tamme・BGT の `toc.md` と `items.csv`（status は空）。`lean_citations`・`route` を埋める | **停止点 0**：文献ごとの件数、`citations.csv` の番号で原典にないもの、`items.csv`（README）とのずれ。調整役が確かめる |
| 段 1 | KST と Land–Tamme の照合（§4） | 停止点 1 |
| 段 2 | 本論文 §3・§4、Tamme、BGT の照合 | 停止点 2 |
| 段 3 | ほかの 12 文献の `items.csv` の行の照合（`maps/others.csv`）と、README の 208 項目の status を kernel で確かめた結果 | 停止点 3：要約 `maps/summary.md`（文献ごと・status ごとの件数、README の「K の計画の問題」10 点のそれぞれについて、照合でわかったこと） |

- 停止点 0 だけは調整役の承認を待つ。段 1〜3 は、報告してそのまま次へ進んでよい。

## 4. 確認の深さの基準

Kerodon の確認の基準（`research/kerodon-coverage/codex-review.md` §7.1）と、HA の依頼（`research/ha-coverage/codex-review.md` §4）と同じ。要点：

1. own・mathlib・both・partial の行は `仮定：…（原典と一致／Lean が強い：…／Lean が弱い：…）。結論：…（…）。` と書く。Lean の型は `#check` の出力から写す。
2. none の行は、(a) docstring の引用、(b) 双対・特別な場合（連結な場合だけ、K₀ だけ、Noether 環だけ、dg 圏の模型でだけ、など）、(c) 同じ節の宣言のファイルの中身、の三つで探して記録する。
3. 型に `ModelCategory` の仮定があれば instance の実在を確かめる（HA の依頼 §4 の 4）。
4. 凍結したコードの宣言は、型が合っていても `frozen` 列を `yes` にする（主経路で使えるかは調整役がユーザーと決める）。
5. unsure を残さない。

## 5. 規則

HA の依頼 §5 と同じ（読み取りだけ、書いてよいのは `research/k-coverage/maps/` の下だけ、小さなビルドだけで鍵を通す、自分のファイルを明示してコミット、取り込みは調整役）。README の `items.csv` は書き換えない（照合の結果は `maps/` に書く）。
