# Codex への依頼：Higher Topos Theory の項目と Lean の宣言の対応表

作成：2026-11-07（段階 II の調整役）。宛先：HTT の確認の Codex（worktree `../SerrePositivity-htt-review`、枝 `research/htt-review`）。検収：調整役。範囲と列は `README.md`。

## 0. 背景

Kerodon の対応表（`research/kerodon-coverage/`）と同じものを HTT について作る。HA の確認（`research/ha-coverage/`）も並行して走る。道具を作ったら互いに使ってよい（相手の枝が main に入った後）。Kerodon の確認では、浅い確認（定型文の理由、名前の検索だけの none）がやり直しになった。**最初から深さの基準（§4）で行う。速さより深さを優先する。**

## 1. 準備

1. main から切った worktree で作業する（main の作業木では作業しない）。
2. HTT の PDF を取得し（README の「原典」）、版の日付と SHA-256 を記録する。PDF はコミットしない。取得できなければ止めて報告する（ユーザーが用意する）。
3. Kerodon の確認の道具（`research/kerodon-coverage/review/check/README.md`、段 1・段 1′ のスクリプト：`#check` と `#print axioms` の一括実行、名前の自動補正）を読み、使えるものは使う。HTT 用に直すときは `research/htt-coverage/review/check/` に置く。

## 2. 段と止めて報告する点

| 段 | 内容 | 止めて報告 |
| --- | --- | --- |
| 段 0 | `toc.md` と `items.csv`（全章の全項目）を作る。各行の `lean_citations`・`plan_citations`・`goal`・`kerodon` を埋め、`status` は空のまま | **停止点 0**：件数（章・節・kind ごと）、`citations.csv`・`plan-citations.csv` の番号で `items.csv` にないもの、`kerodon` 列が埋まった件数。調整役が範囲を確かめる |
| 段 1 | 第 1・2 章の照合（§4 の基準、Kerodon の行を参照） | 停止点 1 |
| 段 2 | 第 4・5 章の照合 | 停止点 2：章ごとに報告 |
| 段 3 | 第 6 章の照合 | 停止点 3 |
| 段 4 | 第 3・7 章と付録の照合 | 停止点 4：要約 `review/summary.md` |

- 停止点 0 だけは調整役の承認を待つ。段 1〜4 は、報告してそのまま次へ進んでよい。
- 報告は短く：段の件数（status ごと）、`unsure` の件数（0 を目指す）、よくある誤りの型。

## 3. 返してほしいもの

- `research/htt-coverage/toc.md`・`items.csv`（段 0）。
- 章ごとに `review/ch<N>.csv`。列は `number,status,declarations,reason,axioms,check`（Kerodon と同じ意味。`check` は `found`・`not_found`・`renamed`）。章の途中でコミットするときは、節ごとに追記してよい。
- 証拠は `review/check/ch<N>-kernel-evidence.json`（`#check` の型）と `ch<N>-none-search.json`（none の行の検索の記録）。一つのファイルを 2 MB 以内に保つ（大きくなるなら節で分ける）。モジュールごとの生の出力はコミットしない（`.gitignore`）。

## 4. 確認の深さの基準（Kerodon §7.1 と同じ、HTT 用に読み替え）

1. **own・both・mathlib・partial の行**：`reason` に必ず
   `仮定：…（HTT と一致／Lean が強い：…／Lean が弱い：…）。結論：…（一致／Lean が弱い：…／Lean が強い：…）。`
   と書く。Lean の型は kernel の出力（`#check`）から写し、HTT の主張は本文から取る。仮定が強い（特別な場合だけ）・結論が弱い場合は `partial`。
2. **none の行**：次の三つで探し、行ごとに探した語と場所を記録する。
   - (a) `citations.csv` に、その番号や同じ Subsection の番号がないか。
   - (b) 双対・特別な場合の版：反対圏、左右の入れ替え、片方向の含意、より強い仮定の下の形（例：任意の ∞ 圏ではなく Kan 複体や nerve の場合だけ）、Mathlib の概念名（`Quasicategory`・`SSet.horn`・`Nerve`・`Limits`・`Localization`・`GrothendieckTopology`・`Sheaf` など）。
   - (c) 同じ Subsection と隣の Subsection で引用されている宣言のファイルを開き、型を読む。名前の検索だけで済ませない。
   none のまま残す行には、どの特別な場合を探し、なぜ当てはまらないかを一行で書く。定型文だけの理由は不可。
3. **unsure を残さない**：決められなければ、何が足りないかを具体的に書く。
3′. **Lean に何もない Subsection**：Subsection 全体で、(a) の引用が 0 件で、(b)・(c) の検索（その Subsection の主な概念の名前を、SerrePositivity と Mathlib の両方で）にも候補が一つもないときは、検索の記録を Subsection に一つ書き、各項目の `reason` はその記録を指してよい（「§7.3.1 の検索記録（none-search の 7.3.1）による」）。候補が一つでもあれば、その Subsection は項目ごとに確かめる。どの Subsection をこの扱いにしたかは報告に書く。
4. **モデル圏の仮定**：型に `ModelCategory` の仮定があれば、使う具体的な圏でその instance が本体に実在するかを確かめる。実在しなければ `partial` にして「instance なし」と書く。`[ModelCategory SSet]` を要求するものは own・both に数えない（Kerodon §6 と同じ）。
5. **∞ 圏の模型の違い**：HTT は準圏で述べ、本体は単体集合の準圏・Kan 豊穣圏・dg 圏など複数の模型を使う。模型が違うだけで主張が同じなら一致としてよいが、比較の宣言がないために使えない場合は `partial` にして、どの比較が欠けているかを書く。

## 5. 規則

- 読み取りの確認だけ。`SerrePositivity/` の Lean のファイルは編集しない。書いてよいのは `research/htt-coverage/` の下だけ（確認用の Lean のファイルも `review/check/` に置く）。
- ビルドは小さなものだけ（`lake build <module>` と `lake env lean`、`source ~/.zshenv`）。全体のビルドや verify はしない。`scripts/refactor/with_build_lock.sh --wait 0 -- …` を通し、鍵が取れなければ少し待って取り直す。別プロジェクトのビルドや、他の worktree の小さなビルドは待たない。
- コミットは自分のファイルを明示して行う（`git add -A`・`git add research/` は使わない）。
- 終わったら枝にコミットして報告する。main への取り込みは調整役が行う。

## 6. 追記（2026-11-07 夜、調整役）：停止点 0 の承認

**承認**：段 0（2ac9ea229、main に取り込み済み）。2017-04-09 版、1,730 項目。`plan-citations.csv` の「3.0」は計画側の誤記なので無視してよい。段 1（第 1・2 章の照合）に進んでよい。

1. **`kerodon` 列**：docstring の併記だけでは 16 行にとどまる（Lean が引く HTT の番号は 64 種類しかない）。照合で対応する宣言が決まった行は、同じ宣言が Kerodon の確認の行（`research/kerodon-coverage/review/ch<N>.csv` の `declarations_new`）に現れるかを機械的に突き合わせ、現れればその Kerodon の番号を候補として書く（主張が同じかは HTT の本文で確かめ、違えば書かない）。埋めた件数を停止点ごとに報告する。
2. **付録 A（モデル圏）**：§4 の 4（モデル圏の仮定）をそのまま当てる。主経路はモデル圏を使わないので、`goal` は計画が引くものを除いて `-`。
3. **`title`**：段 0 では空の行が多い。照合で本文を読むときに、HA の表と同じく日本語の短い題（内容がわかる 10〜25 字程度、例「内部 Hom の Kan 性」）を埋める（地図の表示に使う）。
4. 段 1 からは、報告してそのまま次の段へ進んでよい。

## 7. 追記（2026-11-10 夜、調整役）：停止点 1 の取り込みと、partial の基準

停止点 1（40586de92、第 1・2 章 287 件、unsure 0）と §4.1.1（b63a0e170）を main に取り込んだ。

**partial の基準を Kerodon §8.1 に合わせる**：Kerodon の確認では partial の幅が確認する人ごとに違い、抜き取りの差が収まらなかったので、`research/kerodon-coverage/codex-review.md` §8.1 で基準を絞った。HTT もこれに合わせる。

1. partial と数えるのは、Lean の宣言から原典の主張の一部が直接導ける場合だけ。`review/ch<N>.csv` に列 `partial_kind` を足し、`special`（仮定を特殊化）・`direction`（片方向）・`stronger-hyp`（仮定が強い）・`component`（結論の一部）のどれかを書く。
2. 証明の部品、似た構成、別の対象についての類似の主張、原典を導くのに追加の議論が要るものは none（候補として reason に書いてよい）。
3. 模型の違い（§4 の 5）で比較の宣言がないために partial にしたもの（例：直線化の準圏同値はあるが、HTT の Quillen 随伴との比較がない）は `stronger-hyp` ではなく `component` か none のどちらかに決め、理由を書く。
4. 段 2 以降はこの基準で照合する。第 1・2 章の partial（158 件）は、段 2 の合間か、段 4 の後にまとめて見直す（どちらでもよい。見直した件数を報告する）。
