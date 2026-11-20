# IM-W1　使われていない import とファイルの掃除（一段ずつ）

2026-11-20。担当は、手が空いたレーン（⑧ の SU-W1 段 9 の後、または ⑦ の AR-W1 段 3 の後）。枝は main から新しく `refactor/import-cleanup`。経緯は [cleanup-log.md](cleanup-log.md)。

## 0. 背景

調整役が、全宣言の採取（`research/cleanup-zero-base/whole/imports_check.py`）から、本体のモジュールどうしの import を調べた（11-20、取り込みの前のデータ）。直接の import 113,886 本のうち：

- 使っている 69,502、間接だけ 5,811、候補（宣言のあるファイル）7,440、候補（宣言のない、import だけのファイル）31,133。
- 候補のうち、はっきり不要と分かるものが二種類ある。

**A. 古い名前の別名の取り残し。** 別名（`deprecated_alias`）は CF-W1 A（1691e0ee2）で全部消したが、その命令を定義する 2 ファイル（`SerrePositivity/Util/DeprecatedAlias.lean`、`SerrePositivity/InfinityCategories/Project/SimplicialCombinatorics/DeprecatedAlias.lean`、計 211 行）と、それへの import が約 1,075 本残っている。

**B. import だけのファイル。** 宣言を一つも持たないファイルが 550 本ある。うち 357 本は、別の 1 ファイルを import するだけ（過去の移動の旧い場所、中身を消した後の殻。`DifferentialGraded/Checks` に 307 本など）。本体のどのファイルからも import されていないものが 446 本。大きいもの（45 本、`EInfinity`、`Entrypoints/*` など）は、監査や root が領域をまとめて読み込むための入口で、役目がある。

調整役のデータは本体のモジュールだけで、`scripts/`・blueprint・lakefile からの import は入っていない。定数の依存だけを見ているので、記法・マクロ・属性（`@[cite]` を定義する `Util/Citation.lean` は誤検出）・`open` などの使い方は見えない。

## 1. 規則

- 一回の依頼は一段。**段 1 は一覧だけで、何も消さない。削除は、一覧をユーザーが見て承認した後（段 2）。**
- ビルドは bulk 鍵。main では作業しない。
- 残りの候補（宣言のあるファイルの、使っていない import 約 5,300 本と、間接だけの 5,811 本）は、この作業では扱わない（領域の整理のついでに行う）。

## 2. 段 1：一覧を作る（何も変えない）

### A. 別名の取り残し

1. 2 ファイルが定義するもの（命令 `deprecated_alias`・`deprecated_alias_util`、拡張、属性）を、本体・`scripts/`・blueprint・`research/` の Lean の中で使っている箇所を全部探す。CF-W1 A の報告にある「コマンドの回帰試験用の別名 13 件」（`scripts/refactor/tests/deprecated_alias.lean`、`scripts/refactor/check_deprecated_aliases.lean` など）がどうなっているかも確かめる。
2. 2 ファイルへの import を全部挙げる（本体、スクリプト）。import を外すと、そのファイル経由で届いていた別のファイルが届かなくなる箇所がないかを確かめる（2 ファイルが import しているもの）。
3. 2 ファイルと import を消してよいか、残すべき使い方があるかの判断と根拠。

### B. import だけのファイル

1. 宣言を持たない本体のファイルを全部挙げる（調整役の数え方では 550 本。`dump` の宣言の表でなく、ソースを読んで確かめる：宣言・`instance`・記法・`open … in`・属性・`initialize`・`#` で始まる命令など、import と名前空間とコメント以外に何かあるか）。
2. 一本ごとに：import の本数、何のためのファイルか（移動の旧い場所／中身を消した後の殻／ディレクトリの入口／監査の入口／その他）、誰が import しているか（本体、`scripts/` の監査・検査、root、blueprint、lakefile、文書の中の言及）。Git の履歴から、いつ・どのコミットでこの形になったか（一行）。
3. 扱いの案：消す（どこからも使われていない、または使う側を直せば消せる）／残す（入口として役目がある。誰が使っているかを書く）／判断できない。消す場合に直す必要のある使う側（ファイルと行）。
4. 消すと root からも監査からも届かなくなるモジュールがあるか（そのファイルが、root の外のモジュールを建てる唯一の経路になっていないか）。AR-W1 段 1 の表（`research/audit-review/stage1.csv`）の「単独 import」と照らす。

### 段 1 の完了の条件

- `research/import-cleanup/alias-leftovers.csv`（A：ファイル、行、種類＝定義／使用／import）、`research/import-cleanup/import-only-files.csv`（B：一本一行）。
- 報告 `formalization-plans/stage-ii/consolidation/report-import-cleanup.md`：A・B それぞれについて、消す案の件数（ファイル、import、行）、残す案の件数と理由、判断できないものの一覧、消したときに届かなくなるモジュール、直す必要のある使う側の数。調整役の数（1,075 本、550 本、357 本、446 本）と違う所があれば、その理由。
- Lean・スクリプト・manifest の差分が 0。コミットして止まる。

## 3. 段 2：承認された分を消す

段 1 の一覧のうち、ユーザーが承認した分を消す。使う側を直し、対象と使う側を建て、全モジュールが建つこと（root の外も）、宣言の集合が前後で同じこと（消したファイルに宣言がないので、カーネルの名前と主張が全部一致するはず）、公理と sorry が増えないこと、監査の成否が変わらないことを確かめる。報告に、前後のファイル数・行数・import の本数を書く。

### 段 2 の承認（ユーザー、11-20）と範囲

段 1 の報告（`report-import-cleanup.md`、c9bd9fb64）に対する承認。これ以外は消さない。

**A. 旧別名**
- 本体の `Util/DeprecatedAlias.lean` と `InfinityCategories/Project/SimplicialCombinatorics/DeprecatedAlias.lean` への import 1,075 本を外す。
- `Util/DeprecatedAlias.lean`（106 行）を消す。`…/SimplicialCombinatorics/DeprecatedAlias.lean` は、回帰試験（`scripts/refactor/tests/deprecated_alias.lean`）と移動の道具が使うので残す。
- 外して届かなくなるもの（`Mathlib.Util.AliasIn` など）は、実際に要るファイルにだけ直接 import を足す。一律には足さない。足した本数と理由を報告する。

**B. import 専用ファイル**
- 削除案 126 本のうち、`Spectra/SymmetricSequence/DisjointUnion.lean` と `FiniteBijection.lean` の 2 本を除く **124 本**を消す（2 本は ⑧ の作業範囲と重なるので、SU-W1 の側で消す）。旧 Rectification パスの互換はここで終える。使う側と配置の台帳（`direct_relocations`）は報告の案どおりに直す。
- 保留 16 本のうち **12 本**を消す：`InfinityCategories/Project/Entrypoints/` の 10 本（空の予約入口 8 本と `Kan`・`StablePresentable`）、局所設定だけが残った `HomologicalAlgebra/CompleteTwoCohomologyAnnihilator.lean` と `IdealPowerTorsionBaseChange.lean`。後の 2 本は、設定（局所 instance 属性を含む）がそのファイルの外に効いていないことを確かめてから消し、root と `scripts/audit/shared.lean` の import を付け替える。効いていたら消さずに報告する。予約入口の予約が計画の紙に書かれているなら、その記述はそのままでよい（ファイルは要るときに作る）。
- IC-2 §14 の 4 本は触らない。残す案 407 本は触らない。

**確かめること**
- 全モジュールが建つ（root の外も。成果物のないモジュールが 0）。import を 1,000 ファイル以上変えるので全体の再ビルドになる。bulk 鍵。始める前に調整役に知らせる（並列の枠を 1 にする）。
- 宣言の集合が前後で同じ：カーネルの名前と主張が全部一致（消すファイルに宣言はない）。補助名の差が出たら、`cleanup-rules.md` の規則で扱い、件数を報告する。
- 公理と sorry が増えない。監査の成否が変わらない（正式監査 108 本の対象と import の変更は、消したモジュールの分だけ）。
- 消したモジュールの名前が、本体・`scripts/`・blueprint・manifest の現行の参照に残っていない（過去の実行の記録と文書の言及は数えない）。
- 報告（`report-import-cleanup.md` に節を足す）：前後のファイル数・行数・import の本数、足した直接 import、付け替えた箇所、所要時間。コミットして止まる。
