# Codex への依頼：Kerodon の項目と Lean の宣言の対応表の確認

作成：2026-11-07（段階 II の調整役）。宛先：Codex（新しいチャット）。読み取りの確認作業で、新しい数学は書かない。**全項目を確認する（11-07、ユーザー）**。

## 0. 背景

`research/kerodon-coverage/items.csv` は、Kerodon（https://kerodon.net、11-06 取得）の本文 Ch 1〜10 の番号つきの項目 3,553 個について、SerrePositivity と Mathlib に対応する宣言があるかを判定した表である。対象は Definition・Theorem・Proposition・Lemma・Corollary・Construction・Variant・Notation の全部と、Lean が番号で引いている Example・Remark など。

- 列：`number`（Kerodon の番号）、`kind`、`status`、`declarations`（`宣言名 @ path:line` を ` | ` で区切る）、`note`、`confidence`、`lean_citations`（Lean の docstring がその番号を引いている件数）、`subsection_tag`。
- `status` の意味：
  - `own`：SerrePositivity にある
  - `mathlib`：Mathlib にある
  - `both`：両方にある
  - `partial`：特別な場合だけ、片方の向きだけ、など
  - `none`：見つからない
- 作り方：Claude のエージェントが、宣言名の索引と grep で探し、宣言の主張と docstring を読んで判定した。「なし」とした Definition・Theorem・Proposition は、別のエージェントがもう一度探した。**Lean を動かしての確認はしていない**。確度は `confidence`（high・med・low）。
- 集計は `items-summary.md`、各塊の所見は `items-remarks.md`、Subsection 単位の先行の調査は `README.md`・`coverage-ch*.md`。

## 1. 確認してほしいこと（全 3,553 項目）

`items.csv` の**全項目**を確認する。`review-targets.csv` の 417 項目（`reason` A〜D）は、誤りが多そうな所の印として**先に**見る。

| 段 | 対象 | やること |
| --- | --- | --- |
| 段 1（機械的、全件） | `declarations` 列に書かれた宣言のすべて | スクリプトで `#check @名前` と `#print axioms 名前` を流し、宣言が実在するか、標準 3 公理以外（`sorryAx` など）を使っていないかを一括で記録する。宣言名の解決（名前空間・Mathlib の名前）に失敗したものは段 2 で手で直す |
| 段 2（主張の照合） | `status` が `own`・`both`・`mathlib`・`partial` の 1,606 項目 | 宣言の型を Kerodon の項目の主張と比べ、判定が正しいかを決める（仮定が強すぎないか、特別な場合だけでないか、`partial` の欠けの記述が正しいか） |
| 段 3（「なし」の確認） | `status` が `none` の 1,947 項目 | 本当にないかを探す（言い換え・双対・特別な場合の版・Mathlib の命名・SerrePositivity の命名）。見つかれば宣言名と場所、見つからなければ「確認済み・なし」 |

確かめ方：

1. 段 1 の Lean のファイルは、宣言のファイルのモジュールを import して、宣言ごとに `#check` と `#print axioms` を並べる。宣言の数が多いので、モジュールの塊ごとに分けて `lake env lean` で流す。出力を解析するスクリプトも残す。
2. Kerodon の本文は `https://kerodon.net/tag/<Tag>`（Subsection の Tag は `subsection_tag` 列）。
3. `[ModelCategory SSet]` のように、主張の仮定に後で満たせないかもしれない型クラスが入っていないかも見る。
4. 章ごとに進める（Ch 1 → Ch 10）。一つの章が終わるたびに枝にコミットして、短く報告する。

## 2. 返してほしいもの

章ごとに `research/kerodon-coverage/review/ch<N>.csv` を作り、その章の全項目を一行ずつ書く。章ごとのファイルにするのは、Codex を並行で走らせても衝突しないようにするため。列は次のとおり。

- `number`
- `verdict`：`ok`（表のとおり）、`fix`（訂正）、`unsure` のいずれか
- `status_new`：訂正後の status
- `declarations_new`
- `reason`：短く、日本語
- `axioms`：`#print axioms` の結果が標準 3 公理以外なら、その中身
- `check`：段 1 の結果。`found`・`not_found`・`renamed`

段 1 のスクリプトと生の出力は `research/kerodon-coverage/review/check/` に置く。全章が終わったら、要約を `research/kerodon-coverage/review/summary.md` に書く。中身は次のとおり。

- 章ごと・status ごとの ok・fix・unsure の件数
- 理由 A〜D の項目での誤りの率（元の表の確度の見積もり）
- よくある誤りの型
- 主張がずれている宣言の例

## 2.1 並行で走らせる場合

調整役の指示で Codex を複数走らせるときは、章の範囲を分ける（例：Ch 1〜3、Ch 4〜6、Ch 7〜10）。worktree と枝はチャットごとに一つずつ切る（`../SerrePositivity-kerodon-review-a` と `research/kerodon-review-a` など）。書くのは自分の章の `review/ch<N>.csv` だけにする。段 1 のスクリプトは最初のチャットが作ってコミットし、ほかのチャットはそれを取り込んで使う。

## 3. 規則

- 読み取りの確認だけ。`SerrePositivity/` の Lean のファイルは編集しない。書いてよいのは `research/kerodon-coverage/review/` の下だけ（段 1 の確認用の Lean のファイルも `review/check/` に置く。`SerrePositivity/` の下には置かない）。
- worktree は main から切った作業用のものを使う（例 `../SerrePositivity-kerodon-review`、枝 `research/kerodon-review`）。main の作業木では作業しない。
- ビルドは小さなものだけ。`lake env lean` の前に、import するモジュールを `lake build <module>` で用意する（Lake のキャッシュが効く。`source ~/.zshenv`）。全体のビルドや verify はしない。始める前に `ps -axo command= | grep '[l]ake build'` で他の大きなビルドがないことを確かめ、`scripts/refactor/with_build_lock.sh --wait 0 -- lake build …` を通す。
- 終わったら枝にコミットして報告する。main への取り込みは調整役が行う。

## 4. 追記（2026-11-07、調整役）：ビルドの待ち合わせを緩める

段 1 の初回は、別プロジェクトの `lake build ArxivFormalization` を検出して止まった。§3 のビルドの待ち合わせを次のとおり緩める（ユーザー承認）。

- **止まるのは二つの場合だけ**：SerrePositivity の全ビルド（ルート・下流ビルド・verify、`verify.sh`）が走っているとき、または `scripts/refactor/with_build_lock.sh --wait 0` で鍵が取れないとき。鍵が取れなければ少し待って取り直す。
- **待たないもの**：別プロジェクト（`arxiv_formalization` など）のビルドと、SerrePositivity の他の worktree の小さなビルド（`lake build <module>`・`lake env lean`）。CPU は取り合うが、正しさには影響しない。
- 段 1 のスクリプトは main に入った（538f3a835）。HEAD が変わったので、README の手順どおり新しい run-dir を prepare してから全件を流す。
- 古い worktree `SerrePositivity-kerodon-review`（枝 `research/kerodon-review`）は使われていなかったので消した。以後は `-a`（と、並行にするときの `-b`・`-c`）を使う。

## 5. 追記（2026-11-07、調整役）：名前の自動補正、生の出力の扱い、並行の分担

段 1 の全件の結果（found 394、not_found 1,602、手動 111）と Ch 1 の結果（ok 121・fix 54・unsure 5）を main に取り込んだ（3c46c2efd）。not_found の大半は、表の名前に名前空間が欠けていたため（例：`PiZeroConstant.homEquiv` → `SerrePositivity.SimplicialModel.PiZeroConstant.homEquiv`）。Ch 1 で手で直したやり方を機械化する。

1. **名前の自動補正（段 1′）**：not_found と unresolved の記載について、記載の `path:line` のファイルを読み、その行での `namespace`・`section`・`open`（`open … in` を含む）の入れ子から完全な名前の候補を作る。候補を `#check` で試し、一つに決まれば `renamed` として記録する。決まらない・候補がないものだけを段 2 の手作業に回す。補正の規則と、補正前後の件数を報告する。
2. **生の出力は main に入れない**：`review/check/runs/*/modules/`（モジュールごとの検査用 Lean と生の出力）は、以後コミットしない（`.gitignore` に加える）。枝に既にある分はそのままでよい。main には、スクリプト・報告・`review/ch<N>.csv`・run ごとの集計の CSV と JSON だけを取り込む。
3. **並行の分担**：段 1′ が main に入ったら、調整役の指示で Codex を三本にする。
   - `-a`（このチャット）：Ch 2〜3
   - `-b`：Ch 4〜6
   - `-c`：Ch 7〜10
   
   `-b`・`-c` は main から `../SerrePositivity-kerodon-review-b`・`-c`（枝 `research/kerodon-review-b`・`-c`）を切る。どのチャットも、書くのは自分の章の `review/ch<N>.csv` と `review/check/ch<N>-*` の証拠ファイルだけ。Ch 1 の `ch1-review-report.md` と同じ形で、章ごとの報告を書く。

## 6. 追記（2026-11-07 15:40、調整役）：モデル圏の仮定つきの宣言

段 1′ で名前の補正に採用した宣言のうち 14 件は、型に `ModelCategory` の仮定がある（一覧は `review/check/runs/stage1-prime-01/verified-candidates.csv` の型の列）。この種の仮定は公理の監査を通るが、満たせないことがある。

1. **`[ModelCategory SSet]` を要求するもの**（`SerrePositivity.SimplicialModel.simplicial_anodyne_eq_trivialCofibrations` の 1 件）：満たせない仮定なので、Kerodon の項目の own・both としては数えない。`verdict` は `unsure`、`reason` に仮定を書く。
2. **一般の圏にモデル圏構造を仮定するもの**（13 件）：その項目で使われる具体的な圏（単体集合の圏など）で、その instance が本体に実在するかを確かめる。実在すれば判定どおり、実在しなければ `partial` にして `reason` に仮定と「instance なし」を書く。
3. 段 2 の型の確認では、ほかの宣言についても、型の仮定に `ModelCategory` が現れたら同じ扱いにする。
4. コミットは自分の章のファイル（`review/ch<N>.csv`、`review/check/ch<N>-*`）を明示して行う。`git add -A` や `git add research/` は使わない（古い枝の未追跡ファイル、特に `runs/stage1-prime-01/plan.json`（25 MB）が入るのを防ぐ）。

## 7. 追記（2026-11-07 16 時、調整役）：確認の深さの基準と、Ch 4〜10 のやり直し

ユーザーの希望：**徹底的に調べたい。速さより深さを優先する。** Ch 4〜10 の確認は、own・both・mathlib の行で仮定と結論を照らした跡が少なく（理由の中央値 35〜50 字、Ch 1 は 59 字）、none の行で同じ定型文が 1 章で最大 54 回繰り返されていた。次の基準で確認し直す。

### 7.1 行ごとの基準

1. **own・both・mathlib の行**：`reason` に必ず次の形で書く。
   `仮定：…（Kerodon と一致／Lean が強い：…／Lean が弱い：…）。結論：…（一致／Lean が弱い：…／Lean が強い：…）。`
   Lean の型は kernel の出力（`#check` の結果、`ch<N>-kernel-evidence.json`）から写し、Kerodon の主張は本文（`https://kerodon.net/tag/<Tag>`）から取る。仮定が強い（特別な場合だけ）・結論が弱い場合は `partial` にする。一致を言い切れなければ `unsure` にして、何が足りないかを書く。
2. **none の行**：文字列の検索に加えて、次の三つで探し、**探した語と場所を行ごとに記録する**（`ch<N>-none-search.json` に、行ごとの検索の語・ディレクトリ・候補と却下の理由）。
   - (a) docstring の Kerodon の引用（9,711 件、`citations-summary.md` と `citations.csv`）に、その番号や近い番号（同じ Subsection）がないか。
   - (b) 双対・特別な場合の版：反対圏（op）、左右の入れ替え、1 圏の版、Mathlib の名前（`#find` 相当の型の検索、命名規則）。
   - (c) 同じ Subsection の own・both の宣言のファイルの近く（同じファイル・同じディレクトリの宣言を読む）。
   定型文だけの理由は不可。
3. **unsure を残さない**：上の基準で `ok`（表のとおり）・`fix`・`partial` のどれかに決める。決められないものは、何が足りないか（例：「Lean の型で Δ¹ 上に限られているかを確かめられない」）を具体的に書く。
4. **モデル圏の仮定**：§6 のとおり。

### 7.2 やり直しの範囲と分担

- **-b**：Ch 4〜6。**-c**：Ch 7〜10。どちらも、own・both・mathlib の全行、unsure の全行、none の全行を 7.1 の基準で確認し直す（none の ok の行も含む）。結果は `review/ch<N>.csv` を上書きし、`ch<N>-review-report.md` に「やり直し（11-07）」の節を足す。
- **-a2**：Ch 2〜3。最初から 7.1 の基準で行う。
- Ch 1 は、own・both・mathlib の行の理由だけを 7.1 の 1 の形に書き直す（担当は -a2、Ch 2〜3 の後）。

### 7.3 交差の抜き取り検査

やり直しが終わったら、-b が -c の章から、-c が -b の章から、own・both・mathlib と none をそれぞれ **1 章 20 件ずつ**無作為に選んで、独立に確かめる（乱数の種を報告に書く）。誤りが 1 割を超えた章は、その status の行をもう一度全部やり直す。結果は `review/check/cross-<N>.md`。

追記（11-07、調整役）：第 1〜3 章は -a2 がやり直した（取り込み済み、829a2b041）。抜き取りの組み合わせを次のようにする。

| 抜き取る側 | 対象の章 | 始める時 |
| --- | --- | --- |
| -a2 | 第 4〜6 章（-b のやり直し） | -b のやり直しが main に入った後 |
| -b | 第 7〜10 章（-c のやり直し） | -c のやり直しが main に入った後 |
| -c | 第 1〜3 章（-a2 のやり直し） | -c 自身のやり直しが終わった後 |

件数・乱数の種・やり直しの基準は上と同じ。

### 7.4 進め方

- 速さより深さを優先する。1 章を一度に流さず、Subsection ごとに確かめてコミットしてよい。
- KL-W1 の段 2（Tag を付ける）・段 3（移動）は、このやり直しと交差の検査が終わってから（Tag は own・both だけに付けるので、own の照合の精度がそのまま Tag の精度になる）。

## 8. 追記（2026-11-07 夜、調整役）：partial の基準と、見直しの進め方（ユーザー承認）

第 4・5 章の再抜き取り（9b566492c、乱数の種 0x68583975）でも、四つの群すべてで差が 15〜20% だった。差は両方向（-b が none に残した行を -a2 は partial、-b が partial に変えた行を -a2 は none）で、原因は §7.1 の「関連する比較射の一部」の幅が人によって違うこと。own・both・mathlib の差は二回とも 0 件。

### 8.1 partial の基準

partial と数えるのは、**Lean の宣言から原文の主張の一部が直接導ける**場合だけ。次の四つのどれに当たるかを `partial_kind` 列に書く。

| `partial_kind` | 意味 | 例 |
| --- | --- | --- |
| `special` | 原文の主張の仮定を特殊化した形（対象・圏・次元を限る） | ∞-bicategory の主張の、準圏の場合 |
| `direction` | iff の片側、同値の片向き | |
| `stronger-hyp` | 原文より強い仮定の下で同じ結論 | |
| `component` | 結論が「A かつ B」のとき A だけ、構成の一部の成分だけ | |

次は **none**（`reason` に候補として書いてよいが、status は none）：証明の部品・補題にあたる主張、似た構成、別の射・別の対象についての類似の主張、原文の主張を導くのに追加の議論が要るもの。

### 8.2 進め方

1. 第 4・5 章は今はやり直さない。地図では第 4・5 章の partial・none を「未確定」と表示する。
2. 第 7〜10 章の抜き取り（-b が -c の章を、-c のやり直しが main に入った後）は、own・both・mathlib を優先し、partial・none は件数を 10 件ずつに減らしてよい。
3. 全章の own・both・mathlib の確認（抜き取りを含む）が済んだら、KL-W1 の段 2・3 を始める（Tag は own・both だけに付けるので、partial・none の見直しを待たない）。
4. 最後に、**一つの Codex** が全章の partial・none を 8.1 の基準で一度に見直す（担当は調整役が後で決める。判定の揺れをなくすため一本にする）。

### 8.3 追記（2026-11-10、調整役）：残りの抜き取りと KL-W1

-c の第 7〜10 章のやり直し（1,743 件）と第 4〜6 章の抜き取り（120 件）を取り込んだ（0d9e86356）。第 4〜6 章の own・both・mathlib の差は、-a2・-c の三回の抜き取りで計 0 件。none → partial の差（10〜20%）は §8.1 の基準の問題として、§8.2 の 4 の一括見直しに回す（`cross-4-c.md`〜`cross-6-c.md` の該当行も引き継ぐ）。

KL-W1 の段 2・3 の前に残る抜き取りは二つ。どちらも **own・both・mathlib を各章 20 件**（20 件に満たなければ全件）、partial・none は各章 10 件。結果は `review/check/cross-<N>.md`（既にあれば `cross-<N>-<担当>.md`）。

| 担当 | 対象 |
| --- | --- |
| -b | 第 7〜10 章（-c のやり直し） |
| -c | 第 1〜3 章（-a2 のやり直し） |

own・both・mathlib の差が 1 割を超えた章があれば止めて報告する（その章は KL-W1 の Tag の前にやり直す）。partial・none の差は記録だけ（§8.2 の 4）。
