# 元論文

- タイトル: Positivity of Serre's Intersection Multiplicity
- 著者: OpenAI
- 日付: 2026-09-23（31ページ）
- 出典: https://github.com/openai/math （ファミリー 193、Apache-2.0）
- パス: `preprints/Positivity-of-Serres-Intersection-Multiplicity-September-23-2026/paper.pdf`
- 取得時のコミット: `adc7f1241b42e322a6451854ab7e4b4c146bf78a`（2026-10-06）
- 上流での Lean 形式化: なし（CONTENTS.md にリンクなし、`lean/formalization.yaml` に未掲載。2026-10-07 時点）

取得コマンド（このディレクトリで実行）:

```sh
curl -L -o paper.pdf "https://raw.githubusercontent.com/openai/math/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positivity-of-Serres-Intersection-Multiplicity-September-23-2026/paper.pdf"
```

# 関連論文：Lech の重複度予想

- タイトル: Lech's multiplicity conjecture
- 著者: OpenAI
- 日付: 2026-09-23（41ページ）
- 出典: https://github.com/openai/math （Apache-2.0）
- パス: `preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf`
- 取得時のコミット: `adc7f1241b42e322a6451854ab7e4b4c146bf78a`（元論文と同じコミット。取得は 2026-10-13）
- このディレクトリでのファイル名: `lech.pdf`

取得コマンド（このディレクトリで実行）:

```sh
curl -L -o lech.pdf "https://raw.githubusercontent.com/openai/math/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf"
```

# 引用文献（PDF はリポジトリに置かない）

手元の参照用の PDF は `paper/refs/` に置く。このディレクトリは `.gitignore` で除外しており、commit しない（`git add -f` も使わない）。

- CLMST: H. Cai, S. Lee, L. Ma, K. Schwede, K. Tucker, *Perfectoid signature, perfectoid
  Hilbert–Kunz multiplicity, and an application to local fundamental groups*.
  arXiv:2209.04046（形式化で参照する版は v4、2025-07-03）。https://arxiv.org/abs/2209.04046v4
  掲載誌: Invent. Math. 244 (2026), 357–454（Lech の論文の文献表による）。DOI 10.1007/s00222-025-01399-w（検索結果から。未確認）。
  手元のファイル名: `paper/refs/CLMST-2209.04046v4.pdf`
- BS: B. Bhatt, P. Scholze, *Prisms and prismatic cohomology*.
  形式化で参照する版は著者公開版 https://people.mpim-bonn.mpg.de/scholze/prisms.pdf （2026-10-14 取得）。
  arXiv:1905.08229v3 とは §1・§2、§7.3 以降の §7、§8・§9 の番号がずれる
  （例：著者版 Thm 1.17 は perfectoid 化、André の補題は Thm 7.14、Cor 8.13 は 8.14）。
  プロジェクトが引用する 7.3・7.4・8.5・10.7・10.11 は両版で同じ番号。引用番号は常に著者版に従う。
  手元のファイル名: `paper/refs/BS-prisms-author.pdf`
