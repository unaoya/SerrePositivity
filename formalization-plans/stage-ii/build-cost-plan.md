# ビルドと監査の費用を減らす計画（2026-11-17）

作成：調整役。きっかけ：監視チャットの指摘（F1 の監査が 21 GB）と、ユーザー「全体として、ビルドや監査にかかる時間やメモリを減らす方法を徹底的に考えてほしい」。数字は ③-b の作業木の `.lake/verify/audit-stats.json`（11-17 の verify、106 監査）と、ソースの静的な集計。

## 1. 実測

### 1.1 監査（verify）

- 106 監査、合計 **7,071 秒**（直列換算約 2 時間）、RSS の合計 448 GB。中央値は 25 秒・3.6 GB。60 秒未満が 81 本、4 GB 超が 40 本。
- 上位：`audit_derived_infinity` 651 s / 6.8 GB、`audit_infinity_f1` 539 s / **21.8 GB**、`audit_axioms`（主定理の sorry 閉包）533 s / 10.1 GB、`audit_infinity_stable` 433 s、`audit_localizing_invariants` 358 s、`audit_bhatt_scholze_stage2` 334 s。
- `VERIFY_JOBS=3` なのは最長の監査が 22 GB だから（`VERIFY_MEMORY_GB=40`）。
- **RSS 13〜22 GB の三本（f1・f1b・core）だけが `importModules` で別環境を読み込んでいる**（f1 19 回・f1b 4 回・core 4 回。10-26 に Ind-S などのレーンが「新規葉を別環境で監査」として足した run_cmd）。`collectAxioms` のループの書き方や `#check` の数は主因ではない（`audit_einfinity` はループ 1 個・28,272 行で 7.3 GB、`audit_kst_s_construction` は `#check` 14,395 行で 7.9 GB）。
- **重複**：97 本の監査スクリプトの import 閉包の合計は 329,118 モジュール（リポジトリは 35,413）。9,431 モジュールが 10 本以上の監査に読み込まれ、`collectAxioms` もその分だけ繰り返される。`env.constants` 全体を舐めるループは合計 117 個。
- verify の runner には閉包のハッシュによる結果のキャッシュがあるが、**gate のときは使わない**方針（`VERIFY_CACHE=1` は gate:false）。

### 1.2 ビルド

- 35,413 ファイル・3,135,616 行。**中央値 70 行**、80 行以下が 22,322 本（63%）。InfinityCategories 約 11,000 本、KST 8,645 本、AlgebraicGeometry 1,362 本、BhattScholze 885 本。
- モジュールごとの固定費（数千の .olean の読み込み、環境の構築、.olean の書き出し、プロセスの起動）が、本文の elaboration と同じ程度かそれ以上にかかる構造。root 約 30,000 本の全ビルドは 3〜8 時間（`coordination.md` §2 の実測）。
- 土台の変更の連鎖：`Util/Citation.lean` の略号表は 896 本が直接 import（BR54）。DG-W1 の土台 6 本の書き換えで 11,250 本・6 時間。
- Lean 4.35 の module system（`module`・`public import`）は既に使っている。成果物キャッシュ（`LAKE_ARTIFACT_CACHE`）は全 worktree で共有。
- 監査のためだけにビルドするモジュールが root の外に 2,794 本ある（`lake build <audit targets>`）。

## 2. 対策（効果の大きい順）

| 番号 | 対策 | 見込み | 費用・時期 |
| --- | --- | --- | --- |
| **A1** | f1・f1b・core の別環境の再 import（27 回）をやめ、本体の環境の import 閉包（`env.header.moduleData` の import を辿る）で同じ禁止 import の検査をする。葉のモジュールは先頭の import に足す | 最長監査 22 → 8 GB 程度、f1 539 → 100 秒程度。`VERIFY_JOBS` 3 → 6 で verify の壁時間が半分近く | 小。**11-17 夜、調整役**（枝 `fix/audit-reimport`） |
| **A2** | gate でも閉包のハッシュが同じ監査はキャッシュの結果を使う（監査の結果は閉包の .olean とスクリプトと toolchain だけで決まるので健全）。取り込みで触ったモジュールを閉包に含む監査だけ走る | 取り込みごとの verify が、触った範囲に比例した時間になる（多くの夜で 106 本のうち数十本） | 小〜中（runner の gate 条件の変更と、キャッシュの鍵に toolchain・スクリプトの hash が入っていることの確認）。**A1 の後、調整役** |
| **A3** | レーン時代の 97 本を**領域ごとの監査**に統合する（`scripts/make_area_audits.py` の形：領域の全モジュールを一度 import、宣言ごとに公理・sorry・native_decide を一回ずつ）。各レーンの `#check` の目印は「宣言名の存在の一覧」（生成物、`env.contains` で検査）に、禁止 import の規則は `scripts/refactor/audit_imports.py`＋`layers.json`（Lean を使わない）に移す。`collectAxioms` は訪問済みを共有して領域で一回 | 閉包の合計 329k → 35k 程度（約 9 分の 1）。verify 合計 7,000 秒 → 1,500 秒程度の見込み | 中〜大。**∞ は IC-W1 で**（モジュールが動くので監査を書き直す回）、BS は BS の再開時、K は K の再開時。領域は Kerodon の章・HA・BS・K・古典 |
| **A4** | `env.constants` 全体を舐めるループを、モジュールの定数表（`moduleData[i].constNames`）に替える | 各監査で数秒〜数十秒 | 小。A3 と一緒に |
| **B1** | 小さすぎるファイルの統合：IC-W1 で章ごとに集めるとき、同じ章の葉（median 70 行）を章のファイルにまとめる。R8 の重複（同一本体 275 群・余分なコピー 364 個）も同時に消す | 模块数が減った分だけ固定費が減る（InfinityCategories 11,000 → 2,000 程度なら、全ビルドで時間の数割） | 大。**IC-W1 の設計に入れる**。名前の隠蔽・宇宙の捕捉の drift（elaboration-drift の教訓）に注意し、保存比較 v3b を通す |
| **B2** | module system の `import`（非 public）を使い分ける：証明にしか要らない依存を `public import` から `import` に落とすと、下流の閉包が小さくなる。Lean 4.35 で private な本体の変更が importer の再ビルドを要らなくするかは**要検証** | 検証次第。効けば取り込み後の再ビルドが大きく減る | 小（まず 1 モジュールで実験）。**調整役、A1 の後の夜** |
| **B3** | BR54：略号表を属性の定義元から分け、root の再ビルドを起こさない | 略号の追加で 896 本の再ビルドが 1 本に | 小。計画済み（B3′ の後継レーン） |
| **B4** | root の外の 2,794 本（監査のためだけにビルド）と BR8 の未使用モジュール 60 本を整理し、root の閉包に揃える | 監査のビルドの段が消える | 小〜中。A3 と一緒に |
| **B5** | 取り込みをまとめて夜に一回（複数レーンの取り込みを同じ root＋verify で） | 夜の root＋verify が取り込みの数に比例しない | 運用。今の規則に一行足す |
| **C1** | verify の RSS 予算は mmap した .olean を各プロセスで数えている（共有ページを重複して数える）。実測で予算を見直す | `VERIFY_JOBS` をさらに上げられる可能性 | 小。A1 の後に計測 |

## 3. 進め方

1. A1（今夜）：枝 `fix/audit-reimport` で三本を直し、runner の計測で前後を比べて取り込む。本体の Lean は触らないので root の再ビルドなし。
2. A2・B2・C1（A1 の次の夜）：runner の gate の条件、`import` の実験、RSS の数え方。
3. A3・A4・B1・B4：IC-W1 の指示書に入れる（∞ の分）。BS・K は再開時。
4. B3：計画どおり。B5：`coordination.md` §2 に一行。
