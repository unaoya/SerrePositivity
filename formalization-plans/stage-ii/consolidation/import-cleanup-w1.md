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
